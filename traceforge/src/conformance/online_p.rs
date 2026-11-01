//! `PAR-ONLINE`: the online check on the partitioned Must
//! (`criteria/PAR-ONLINE.md`), what `online --threads N` runs above one thread.
//! Full mode and unbounded only: `program.rs` refuses `--stop-at-first` and
//! `--budget` here.
//!
//! **The specification** reads and refuses as `online.rs`. Its index is frozen
//! by move into a signature table, cloned per worker because `Sig` is `Send` but
//! not `Sync`, and one shared order store, as SVerify-P's implementation phase.
//!
//! **A completion** is what `online.rs`'s `step_of` makes of it, under **its own
//! graph's thread names** (PAR-EXPORT's fix): the line, parsed back into the
//! index's value domain, looked up. Worker maps are flushed by move at
//! `flush_entries` lines and at every task's end.
//!
//! **The first miss** is the earliest by the run's clock, which starts after the
//! index is built, as the sequential path's; ties go to the smaller line. It has
//! no iteration: there is no one order of completions.
//!
//! **A failure** is kept once, the first under its lock, and cancels the token. A
//! sink entered after the cancel returns `Stop` at its head and adds nothing;
//! what had already entered is kept. So a failed run's counters are what had been
//! counted by the final join, schedule-dependent observations and not a
//! sequential prefix. `--out` then writes the lines held, sorted, under the
//! `aborted` header, as the sequential path does.

use std::cell::RefCell;
use std::collections::HashSet;
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::conformance::compact::{
    CompactSummary, Covers, OrderStore, SetIndex, SigLookup, SigTable,
};
use crate::conformance::ctx::{ConfCtx, ConfMode, DiagnosticReason, SinkVerdict};
use crate::conformance::export_p::write_lines;
use crate::conformance::interchange::{
    encode_generic, line_of, model_name, parse_line, read_file, record_thread_names, sorted_names,
    Enumeration, ThreadNames,
};
use crate::conformance::measure::Shape;
use crate::conformance::online::{
    failed_assertion, out_header, panic_text, End, FirstMiss, MissKind, Mode, OnlineError,
    OnlineOut, OnlineReport,
};
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::parallel_verify::{verify_partitioned_rayon_with, CancelToken, PartitionHooks};
use crate::Config;

/// As `ConfConfig`'s default: the lines a worker holds before it flushes.
const FLUSH_ENTRIES: usize = 4096;

/// What the workers sum.
#[derive(Default)]
struct Acc {
    iterations: usize,
    lookups: usize,
    found: usize,
    signature_misses: usize,
    not_found: usize,
    uncovered_total: usize,
    complete: usize,
    blocked: usize,
    errors: usize,
    summarise: Duration,
    lookup: Duration,
    shape: Shape,
    /// The most lines a worker map held at a flush.
    max_worker_lines: usize,
    /// Sink entries turned away at the head, after the cancel.
    stopped_at_head: usize,
}

impl Acc {
    fn add(&mut self, o: Acc) {
        self.iterations += o.iterations;
        self.lookups += o.lookups;
        self.found += o.found;
        self.signature_misses += o.signature_misses;
        self.not_found += o.not_found;
        self.uncovered_total += o.uncovered_total;
        self.complete += o.complete;
        self.blocked += o.blocked;
        self.errors += o.errors;
        self.summarise += o.summarise;
        self.lookup += o.lookup;
        self.shape.merge(&o.shape);
        self.max_worker_lines = self.max_worker_lines.max(o.max_worker_lines);
        self.stopped_at_head += o.stopped_at_head;
    }
}

/// The earlier miss: the smaller wall, then the smaller line.
pub(crate) fn earlier(a: Option<FirstMiss>, b: Option<FirstMiss>) -> Option<FirstMiss> {
    match (a, b) {
        (Some(x), Some(y)) => {
            if (y.wall_ms, &y.line) < (x.wall_ms, &x.line) {
                Some(y)
            } else {
                Some(x)
            }
        }
        (x, None) => x,
        (None, y) => y,
    }
}

/// A thread's state for the `Must` it serves, kept across that `Must`'s tasks.
struct Worker {
    table: SigTable,
    lines: HashSet<String>,
    uncovered: HashSet<String>,
    first: Option<FirstMiss>,
    /// The context's errors and diagnostics already pushed.
    flushed: (usize, usize),
    acc: Acc,
}

thread_local! {
    static WORKER: RefCell<Option<Worker>> = const { RefCell::new(None) };
}

#[derive(Default)]
struct Merged {
    lines: HashSet<String>,
    uncovered: HashSet<String>,
    first: Option<FirstMiss>,
}

struct Shared {
    table: Mutex<SigTable>,
    store: Arc<OrderStore>,
    merged: Mutex<Merged>,
    acc: Mutex<Acc>,
    /// The first failure; never replaced.
    failure: Mutex<Option<String>>,
    cancel: Arc<CancelToken>,
    #[cfg(test)]
    completions: std::sync::atomic::AtomicUsize,
}

impl Shared {
    fn fail(&self, msg: String) {
        {
            let mut f = self
                .failure
                .lock()
                .expect("conformance: online-p's failure");
            if f.is_none() {
                *f = Some(msg);
            }
        }
        self.cancel.cancel();
    }

    /// By move, under one lock.
    fn flush(&self, w: &mut Worker) {
        w.acc.max_worker_lines = w.acc.max_worker_lines.max(w.lines.len());
        let lines = std::mem::take(&mut w.lines);
        let uncovered = std::mem::take(&mut w.uncovered);
        let first = w.first.take();
        let mut m = self.merged.lock().expect("conformance: online-p's lines");
        m.lines.extend(lines);
        m.uncovered.extend(uncovered);
        m.first = earlier(m.first.take(), first);
    }
}

/// `online_partitioned`'s test seams; inert outside tests.
#[derive(Clone, Default)]
pub(crate) struct OnlinePSeams {
    /// Cancel the token at this many completions, with no failure.
    #[cfg(test)]
    pub(crate) cancel_at: Option<usize>,
    /// Run at the head of the failure path, before the failure is recorded.
    #[cfg(test)]
    pub(crate) before_fail: Option<Arc<dyn Fn() + Send + Sync>>,
    /// Sleep this long in the indexing phase, before the clock.
    #[cfg(test)]
    pub(crate) index_delay: Option<Duration>,
    /// Replaces `FLUSH_ENTRIES`.
    #[cfg(test)]
    pub(crate) flush_entries: Option<usize>,
}

/// A run and what it held at its largest.
pub(crate) struct OnlinePRun {
    pub(crate) report: OnlineReport,
    /// The most lines a worker map held at a flush.
    pub(crate) max_worker_lines: usize,
    /// The distinct implementation lines' UTF-8 bytes.
    pub(crate) merged_bytes: usize,
    /// Sink entries turned away at the head, after the cancel.
    pub(crate) stopped_at_head: usize,
}

/// One completion, on its worker: `Stop` after a failure.
fn step(
    g: &ExecutionGraph,
    visible: &[String],
    names: &[String],
    shared: &Shared,
    started: Instant,
    flush_entries: usize,
    seams: &OnlinePSeams,
) -> SinkVerdict {
    let _ = seams;
    let fail = |msg: String| {
        #[cfg(test)]
        if let Some(f) = &seams.before_fail {
            f();
        }
        shared.fail(msg);
        SinkVerdict::Stop
    };
    let (events, messages) = Shape::graph_counts(g);
    let blocked = g.check_blocked().is_some();
    WORKER.with(|w| {
        let mut w = w.borrow_mut();
        let w = w.as_mut().expect("conformance: online-p's worker is set");
        if shared.cancel.is_cancelled() {
            w.acc.stopped_at_head += 1;
            return SinkVerdict::Stop;
        }
        #[cfg(test)]
        if let Some(n) = seams.cancel_at {
            use std::sync::atomic::Ordering;
            if shared.completions.fetch_add(1, Ordering::SeqCst) + 1 >= n {
                shared.cancel.cancel();
                w.acc.stopped_at_head += 1;
                return SinkVerdict::Stop;
            }
        }
        w.acc.iterations += 1;
        if blocked {
            w.acc.blocked += 1;
        } else {
            w.acc.complete += 1;
        }
        if let Some(msg) = failed_assertion(g) {
            return fail(msg);
        }
        let t = Instant::now();
        let cs = CompactSummary::at_completion(g, visible, "implementation");
        let mut threads = ThreadNames::new();
        record_thread_names(g, &mut threads);
        let text = match line_of(&cs.sig, &cs.ord, names, &|v| encode_generic(v, &threads)) {
            Ok(t) => t,
            Err(e) => {
                w.acc.summarise += t.elapsed();
                return fail(
                    e.to_string()
                        .replace("thread of the run", "thread of this graph"),
                );
            }
        };
        let (line, decoded) = parse_line(&text, names).unwrap_or_else(|e| {
            panic!("conformance: online: an encoded line does not parse back ({e}): {text}")
        });
        w.acc.summarise += t.elapsed();
        let (v, b, m, p) = Shape::summary_counts(&cs.sig, &cs.ord, names, line.len());
        w.acc.shape.add_graph_counts(events, messages);
        w.acc.shape.add_summary_counts(v, b, m, p);

        let t = Instant::now();
        let mut tests = 0;
        let answer = match w.table.resolve(decoded.hash, &decoded.sig, &mut tests) {
            SigLookup::NoBucket | SigLookup::NoSig => Covers::NoSig,
            SigLookup::Found(id) => shared.store.covers(id, &decoded.ord).0,
        };
        w.acc.lookup += t.elapsed();
        w.acc.lookups += 1;
        let kind = match answer {
            Covers::Found(_) => None,
            Covers::NoBucket | Covers::NoSig => Some(MissKind::NoSig),
            Covers::NotFound => Some(MissKind::NotFound),
        };
        match kind {
            None => w.acc.found += 1,
            Some(kind) => {
                match kind {
                    MissKind::NoSig => w.acc.signature_misses += 1,
                    MissKind::NotFound => w.acc.not_found += 1,
                }
                w.acc.uncovered_total += 1;
                let wall_ms = started.elapsed().as_millis() as u64;
                // A thread's wall only grows, so this clones only on a tie.
                let better = w
                    .first
                    .as_ref()
                    .map_or(true, |f| (wall_ms, &line) < (f.wall_ms, &f.line));
                if better {
                    w.first = Some(FirstMiss {
                        iteration: 0,
                        wall_ms,
                        line: line.clone(),
                        kind,
                    });
                }
                w.uncovered.insert(line.clone());
            }
        }
        w.lines.insert(line);
        if w.lines.len() >= flush_entries {
            shared.flush(w);
        }
        SinkVerdict::Continue
    })
}

/// The check, above one thread. `Err` is a refusal before the exploration; a run
/// that fails is an `Ok` whose end is `Failed`.
pub(crate) fn online_partitioned(
    config: &Config,
    threads: usize,
    visible: &[String],
    imp: Arc<dyn Fn() + Send + Sync>,
    spec_path: &Path,
    out: Option<OnlineOut>,
) -> Result<OnlineReport, OnlineError> {
    online_partitioned_with(
        config,
        threads,
        visible,
        imp,
        spec_path,
        out,
        OnlinePSeams::default(),
    )
    .map(|r| r.report)
}

/// [`online_partitioned`] with the test seams and the storage record.
pub(crate) fn online_partitioned_with(
    config: &Config,
    threads: usize,
    visible: &[String],
    imp: Arc<dyn Fn() + Send + Sync>,
    spec_path: &Path,
    out: Option<OnlineOut>,
    seams: OnlinePSeams,
) -> Result<OnlinePRun, OnlineError> {
    let names = sorted_names(visible);
    let index_started = Instant::now();
    let file = read_file(spec_path).map_err(|e| OnlineError::Spec(e.0))?;
    if file.head.enumeration != Enumeration::Complete {
        return Err(OnlineError::NotComplete {
            path: spec_path.display().to_string(),
            enumeration: file.head.enumeration.name().to_string(),
        });
    }
    if file.head.visible != names {
        return Err(OnlineError::Visible {
            file: file.head.visible.clone(),
            program: names,
        });
    }
    let model = match &out {
        Some(_) => {
            Some(model_name(config.cons_type).map_err(|e| OnlineError::Model(e.to_string()))?)
        }
        None => None,
    };
    #[cfg(test)]
    if let Some(d) = seams.index_delay {
        std::thread::sleep(d);
    }
    let mut index = SetIndex::new();
    for (_, _, summary) in &file.lines {
        index.insert(summary);
    }
    let held = index.stats().entries;
    let (table, store) = index.freeze();
    let index_ms = index_started.elapsed().as_millis();

    #[cfg(not(test))]
    let flush_entries = FLUSH_ENTRIES;
    #[cfg(test)]
    let flush_entries = seams.flush_entries.unwrap_or(FLUSH_ENTRIES);

    let mut run_config = config.clone();
    run_config.max_iterations = None;
    run_config.partitioned_parallelization = true;
    run_config.partitioned_num_threads = Some(threads);

    let cancel = Arc::new(CancelToken::new());
    let shared = Arc::new(Shared {
        table: Mutex::new(table),
        store: Arc::new(store),
        merged: Mutex::new(Merged::default()),
        acc: Mutex::new(Acc::default()),
        failure: Mutex::new(None),
        cancel: Arc::clone(&cancel),
        #[cfg(test)]
        completions: std::sync::atomic::AtomicUsize::new(0),
    });

    // The run's clock: after the index is built, as the sequential path's.
    let started = Instant::now();
    let on_must: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let config = run_config.clone();
        let visible = visible.to_vec();
        let names = names.clone();
        let shared = Arc::clone(&shared);
        let seams = seams.clone();
        Arc::new(move |must: &mut Must| {
            let table = shared
                .table
                .lock()
                .expect("conformance: online-p's signature table")
                .clone();
            WORKER.with(|w| {
                *w.borrow_mut() = Some(Worker {
                    table,
                    lines: HashSet::new(),
                    uncovered: HashSet::new(),
                    first: None,
                    flushed: (0, 0),
                    acc: Acc::default(),
                })
            });
            let mut ctx = ConfCtx::gate_disabled(
                config.clone(),
                visible.clone(),
                ConfMode::EnumeratePartitioned,
            );
            let visible = visible.clone();
            let names = names.clone();
            let shared = Arc::clone(&shared);
            let seams = seams.clone();
            ctx.set_sink(Box::new(move |g, _state| {
                step(g, &visible, &names, &shared, started, flush_entries, &seams)
            }));
            must.enable_conformance_partitioned(ctx);
        })
    };
    let on_task_end: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let shared = Arc::clone(&shared);
        Arc::new(move |must: &mut Must| {
            WORKER.with(|w| {
                let mut w = w.borrow_mut();
                let w = w
                    .as_mut()
                    .expect("conformance: online-p's worker is set at task end");
                shared.flush(w);
                let ctx = must
                    .conf_ctx()
                    .expect("conformance: online-p's task context is set before its flush");
                let errors = ctx.collect_errors().len();
                let diagnostics = ctx.diagnostics();
                let (fr, fd) = w.flushed;
                w.flushed = (errors, diagnostics.len());
                let invisible = diagnostics[fd..]
                    .iter()
                    .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
                    .count();
                let mut acc = std::mem::take(&mut w.acc);
                acc.errors = errors - fr + invisible;
                shared
                    .acc
                    .lock()
                    .expect("conformance: online-p's accumulator")
                    .add(acc);
            });
        })
    };
    let hooks = PartitionHooks {
        on_must,
        on_task_end,
        cancel,
    };

    let spawned = Instant::now();
    let worker = {
        let user_config = config.clone();
        std::thread::Builder::new()
            .name("online".to_string())
            .spawn(move || {
                crate::conformance::assert_config_in_scope(&user_config, "online");
                // A task's or the root's panic is re-raised by the runner after
                // its cleanup, and reaches the join below.
                verify_partitioned_rayon_with(run_config, move || imp(), hooks);
            })
            .expect("conformance: online: could not spawn the run thread")
    };
    let joined = worker.join();
    let enumerate_wall = spawned.elapsed();

    let acc = std::mem::take(
        &mut *shared
            .acc
            .lock()
            .expect("conformance: online-p's accumulator"),
    );
    let merged = std::mem::take(&mut *shared.merged.lock().expect("conformance: online-p's lines"));
    let failure = shared
        .failure
        .lock()
        .expect("conformance: online-p's failure")
        .take();
    let (end, failure) = match joined {
        Err(payload) => (End::Failed, Some(panic_text(payload))),
        Ok(()) => {
            if let Some(msg) = failure {
                (End::Failed, Some(msg))
            } else if acc.errors > 0 {
                (
                    End::Failed,
                    Some(format!(
                        "{} assertion failure(s) recorded by the engine and not seen at a \
                         completion",
                        acc.errors
                    )),
                )
            } else if shared.cancel.is_cancelled() {
                (End::Failed, Some("the run was cancelled".to_string()))
            } else {
                (End::Exhausted, None)
            }
        }
    };
    let merged_bytes = merged.lines.iter().map(String::len).sum();
    let mut report = OnlineReport {
        spec_path: spec_path.display().to_string(),
        spec: file.head.clone(),
        spec_lines: file.lines.len(),
        held,
        mode: Mode::Full,
        iterations: acc.iterations,
        lookups: acc.lookups,
        found: acc.found,
        signature_misses: acc.signature_misses,
        not_found: acc.not_found,
        uncovered_total: acc.uncovered_total,
        uncovered_distinct: merged.uncovered.len(),
        first: merged.first,
        end,
        failure,
        out_written: None,
        index_ms,
        explore_ms: enumerate_wall.as_millis(),
        summarise_ms: acc.summarise.as_millis(),
        lookup_ms: acc.lookup.as_millis(),
        export_ms: 0,
        enumerate_ms: enumerate_wall.as_millis(),
        graphs_complete: acc.complete,
        graphs_blocked: acc.blocked,
        impl_lines: merged.lines.len(),
        shape: acc.shape,
        parallel: true,
    };
    if let (Some(out), Some(model)) = (out, model) {
        let enumeration = match report.end {
            End::Exhausted => Enumeration::Complete,
            End::Budget => Enumeration::Bounded,
            End::FirstMiss | End::Failed => Enumeration::Aborted,
        };
        let export_started = Instant::now();
        let mut lines: Vec<String> = merged.lines.into_iter().collect();
        lines.sort_unstable();
        let count = lines.len();
        let header = out_header(
            &out.header,
            &report.spec.visible,
            model,
            enumeration,
            &report,
        );
        let written = write_lines(&out.path, &header, lines.into_iter());
        report.export_ms = export_started.elapsed().as_millis();
        match written {
            Ok(()) => report.out_written = Some((out.path.display().to_string(), count)),
            Err(e) => {
                report.end = End::Failed;
                report.failure = Some(e.to_string());
            }
        }
    }
    Ok(OnlinePRun {
        report,
        max_worker_lines: acc.max_worker_lines,
        merged_bytes,
        stopped_at_head: acc.stopped_at_head,
    })
}
