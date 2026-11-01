//! `PAR-EXPORT`: the summary export on the partitioned Must
//! (`criteria/PAR-EXPORT.md`), what `export --threads N` runs above one thread.
//!
//! **The run** is the specification phase of SVerify-P (`sverify_p.rs`, whose
//! `phase` is private to that frozen file): `verify_partitioned_rayon_with`
//! with a completion sink in every worker `Must`, its context in
//! `ConfMode::EnumeratePartitioned`.
//!
//! **Encoding per graph.** The sequential export records thread names over the
//! run and encodes at its end. Here every completion is encoded under the names
//! of its own graph, and the **line is the summary's identity**: two graphs with
//! equal `CompactSummary` and different thread names give two lines. A thread id
//! in a value must name a thread of that graph.
//!
//! **The merged result** maps a line to a fixed-size record. Worker maps are
//! flushed by move at `flush_entries` lines and at every task's end. A line met
//! with two signature-shape hashes refuses with `Collision` (X1): the hash holds
//! the observation kinds and the concrete message types, not values, so thread
//! renumbering leaves it alone, while `i32(1)` and `u32(1)`, whose encodings are
//! equal, do not meet. Two unequal values of one concrete type that encode alike
//! are not refused: this path keeps no values to compare.
//!
//! **The file** has the sequential header and the lines sorted bytewise, so its
//! bytes do not depend on the run. It is streamed to `<path>.tmp`, each line
//! dropped as it is written, and renamed into place.

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::conformance::compact::{CompactSummary, SigHash};
use crate::conformance::config::{ConfConfig, IndexKind};
use crate::conformance::ctx::{ConfCtx, ConfMode, DiagnosticReason, SinkVerdict};
use crate::conformance::interchange::{
    encode_generic, header_line, line_of, model_name, record_thread_names, sorted_names,
    ExportError, ExportHeader, ExportStats, ThreadNames,
};
use crate::conformance::measure::Shape;
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::parallel_verify::{verify_partitioned_rayon_with, CancelToken, PartitionHooks};

/// What is held per distinct line.
#[derive(Clone, Copy)]
struct Record {
    hash: SigHash,
    /// `Shape::summary_counts` of the line.
    counts: (u128, u128, u128, u128),
}

/// A thread's state for the `Must` it serves, kept across that `Must`'s tasks.
struct Worker {
    lines: HashMap<String, Record>,
    /// The context's `executions`, errors and diagnostics already pushed: the
    /// context keeps growing across the tasks a cached `Must` serves.
    flushed: (usize, usize, usize),
    acc: Acc,
}

/// What the workers sum.
#[derive(Default)]
struct Acc {
    executions: usize,
    graphs: usize,
    complete: usize,
    blocked: usize,
    errors: usize,
    summarise: Duration,
    /// The graph counters only; the summary counters come from the merged lines.
    shape: Shape,
    /// The most lines a worker map held at a flush.
    max_worker_lines: usize,
}

impl Acc {
    fn add(&mut self, o: Acc) {
        self.executions += o.executions;
        self.graphs += o.graphs;
        self.complete += o.complete;
        self.blocked += o.blocked;
        self.errors += o.errors;
        self.summarise += o.summarise;
        self.shape.merge(&o.shape);
        self.max_worker_lines = self.max_worker_lines.max(o.max_worker_lines);
    }
}

thread_local! {
    static WORKER: RefCell<Option<Worker>> = const { RefCell::new(None) };
}

struct Shared {
    merged: Mutex<HashMap<String, Record>>,
    acc: Mutex<Acc>,
    /// The first refusal; the only thing that cancels the token outside a test.
    first: Mutex<Option<ExportError>>,
    cancel: Arc<CancelToken>,
    #[cfg(test)]
    completions: std::sync::atomic::AtomicUsize,
}

impl Shared {
    fn refuse(&self, e: ExportError) {
        {
            let mut first = self.first.lock().expect("conformance: export-p's refusal");
            if first.is_none() {
                *first = Some(e);
            }
        }
        self.cancel.cancel();
    }

    /// By move, under one lock; a line already there keeps its record.
    fn flush(&self, lines: HashMap<String, Record>) {
        let mut collision = None;
        {
            let mut merged = self.merged.lock().expect("conformance: export-p's lines");
            for (line, r) in lines {
                match merged.entry(line) {
                    Entry::Vacant(e) => {
                        e.insert(r);
                    }
                    Entry::Occupied(e) => {
                        if e.get().hash != r.hash && collision.is_none() {
                            collision = Some(e.key().clone());
                        }
                    }
                }
            }
        }
        if let Some(line) = collision {
            self.refuse(ExportError::Collision { line });
        }
    }
}

/// `export_partitioned`'s test seam; inert outside tests.
#[derive(Clone, Copy, Default)]
pub(crate) struct ExportPSeams {
    /// Cancel the token at this many completions, with no refusal.
    #[cfg(test)]
    pub(crate) cancel_at: Option<usize>,
}

/// An export and what it held at its largest.
pub(crate) struct ExportPRun {
    pub(crate) stats: ExportStats,
    /// The most lines a worker map held at a flush.
    pub(crate) max_worker_lines: usize,
    /// The distinct lines' UTF-8 bytes, the merged map's strings.
    pub(crate) merged_bytes: usize,
}

/// One completion: its line under its own graph's names.
fn line_of_graph(
    g: &ExecutionGraph,
    s: &CompactSummary,
    names: &[String],
) -> Result<String, ExportError> {
    let mut threads = ThreadNames::new();
    record_thread_names(g, &mut threads);
    line_of(&s.sig, &s.ord, names, &|v| encode_generic(v, &threads)).map_err(|e| match e {
        ExportError::Thread { type_name, reason } => ExportError::Thread {
            type_name,
            reason: reason.replace("thread of the run", "thread of this graph"),
        },
        other => other,
    })
}

/// The header, then the lines in the order given, each dropped as it is
/// written, to `<path>.tmp`, renamed into place: the path holds its earlier
/// content or the whole export, and no `.tmp` stays behind (X4).
pub(crate) fn write_lines<I>(path: &Path, header: &str, lines: I) -> Result<(), ExportError>
where
    I: Iterator<Item = String>,
{
    let mut tmp = path.as_os_str().to_owned();
    tmp.push(".tmp");
    let tmp = PathBuf::from(tmp);
    let written = fs::File::create(&tmp)
        .and_then(|f| {
            let mut w = std::io::BufWriter::new(f);
            writeln!(w, "{header}")?;
            for line in lines {
                w.write_all(line.as_bytes())?;
                w.write_all(b"\n")?;
            }
            w.into_inner().map_err(|e| e.into_error())?.sync_all()
        })
        .and_then(|()| fs::rename(&tmp, path));
    written.map_err(|e| {
        let _ = fs::remove_file(&tmp);
        ExportError::Io(format!("{}: {e}", path.display()))
    })
}

/// `cc` is an `Engine::SverifyP` configuration with its `threads`.
pub(crate) fn export_partitioned<P>(
    cc: &ConfConfig,
    program: P,
    header: &ExportHeader,
    path: &Path,
) -> Result<ExportStats, ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    export_partitioned_with(cc, program, header, path, ExportPSeams::default()).map(|r| r.stats)
}

/// [`export_partitioned`] with the test seam and the storage record.
pub(crate) fn export_partitioned_with<P>(
    cc: &ConfConfig,
    program: P,
    header: &ExportHeader,
    path: &Path,
    seams: ExportPSeams,
) -> Result<ExportPRun, ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    let _ = &seams;
    if cc.index != IndexKind::Set {
        return Err(ExportError::NotSet);
    }
    let model = model_name(cc.config.cons_type)?;
    let names = sorted_names(&cc.visible);
    crate::conformance::assert_config_in_scope(&cc.config, "export");
    let mut config = cc.config.clone();
    config.max_iterations = None;
    config.partitioned_parallelization = true;
    config.partitioned_num_threads = Some(cc.threads);

    let cancel = Arc::new(CancelToken::new());
    let shared = Arc::new(Shared {
        merged: Mutex::new(HashMap::new()),
        acc: Mutex::new(Acc::default()),
        first: Mutex::new(None),
        cancel: Arc::clone(&cancel),
        #[cfg(test)]
        completions: std::sync::atomic::AtomicUsize::new(0),
    });
    let flush_entries = cc.flush_entries;

    let on_must: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let config = config.clone();
        let visible = cc.visible.clone();
        let names = names.clone();
        let shared = Arc::clone(&shared);
        Arc::new(move |must: &mut Must| {
            WORKER.with(|w| {
                *w.borrow_mut() = Some(Worker {
                    lines: HashMap::new(),
                    flushed: (0, 0, 0),
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
            ctx.set_sink(Box::new(move |g, _state| {
                if shared.cancel.is_cancelled() {
                    return SinkVerdict::Stop;
                }
                #[cfg(test)]
                if let Some(n) = seams.cancel_at {
                    use std::sync::atomic::Ordering;
                    if shared.completions.fetch_add(1, Ordering::SeqCst) + 1 >= n {
                        shared.cancel.cancel();
                        return SinkVerdict::Stop;
                    }
                }
                let (events, messages) = Shape::graph_counts(g);
                let blocked = g.check_blocked().is_some();
                let t = Instant::now();
                let s = CompactSummary::at_completion(g, &visible, "specification");
                let line = match line_of_graph(g, &s, &names) {
                    Ok(line) => line,
                    Err(e) => {
                        shared.refuse(e);
                        return SinkVerdict::Stop;
                    }
                };
                WORKER.with(|w| {
                    let mut w = w.borrow_mut();
                    let w = w.as_mut().expect("conformance: export-p's worker is set");
                    let mut collision = None;
                    match w.lines.entry(line) {
                        Entry::Vacant(e) => {
                            let bytes = e.key().len();
                            let counts = Shape::summary_counts(&s.sig, &s.ord, &names, bytes);
                            e.insert(Record {
                                hash: s.hash,
                                counts,
                            });
                        }
                        Entry::Occupied(e) => {
                            if e.get().hash != s.hash {
                                collision = Some(e.key().clone());
                            }
                        }
                    }
                    w.acc.summarise += t.elapsed();
                    w.acc.graphs += 1;
                    if blocked {
                        w.acc.blocked += 1;
                    } else {
                        w.acc.complete += 1;
                    }
                    w.acc.shape.add_graph_counts(events, messages);
                    if let Some(line) = collision {
                        shared.refuse(ExportError::Collision { line });
                        return SinkVerdict::Stop;
                    }
                    if w.lines.len() >= flush_entries {
                        w.acc.max_worker_lines = w.acc.max_worker_lines.max(w.lines.len());
                        shared.flush(std::mem::take(&mut w.lines));
                    }
                    SinkVerdict::Continue
                })
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
                    .expect("conformance: export-p's worker is set at task end");
                w.acc.max_worker_lines = w.acc.max_worker_lines.max(w.lines.len());
                shared.flush(std::mem::take(&mut w.lines));
                let ctx = must
                    .conf_ctx()
                    .expect("conformance: export-p's task context is set before its flush");
                let executions = ctx.counters().executions;
                let errors = ctx.collect_errors().len();
                let diagnostics = ctx.diagnostics();
                let (fe, fr, fd) = w.flushed;
                w.flushed = (executions, errors, diagnostics.len());
                let invisible = diagnostics[fd..]
                    .iter()
                    .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
                    .count();
                let mut acc = std::mem::take(&mut w.acc);
                acc.executions = executions - fe;
                acc.errors = errors - fr + invisible;
                shared
                    .acc
                    .lock()
                    .expect("conformance: export-p's accumulator")
                    .add(acc);
            });
        })
    };
    let hooks = PartitionHooks {
        on_must,
        on_task_end,
        cancel,
    };

    let run_started = Instant::now();
    // Returns only when every task ran its queue to the end, or returned at its
    // poll after the cancel; a panic is re-raised by the runner after cleanup.
    verify_partitioned_rayon_with(config, program, hooks);
    let explore_ms = run_started.elapsed().as_millis();

    // Taken out under the locks, not unwrapped: the pool's threads drop their
    // cached `Must`s, whose sinks hold the `Arc`, on their own time.
    let refusal = shared
        .first
        .lock()
        .expect("conformance: export-p's refusal")
        .take();
    if let Some(e) = refusal {
        return Err(e);
    }
    let acc = std::mem::take(
        &mut *shared
            .acc
            .lock()
            .expect("conformance: export-p's accumulator"),
    );
    if acc.errors > 0 {
        return Err(ExportError::SpecErrors(acc.errors));
    }
    if shared.cancel.is_cancelled() {
        return Err(ExportError::NotExhausted("cancelled".to_string()));
    }
    let merged = std::mem::take(&mut *shared.merged.lock().expect("conformance: export-p's lines"));

    let export_started = Instant::now();
    let mut lines: Vec<(String, Record)> = merged.into_iter().collect();
    lines.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    let count = lines.len();
    let merged_bytes = lines.iter().map(|(l, _)| l.len()).sum();
    let mut shape = acc.shape;
    let text = header_line(header, &names, model);
    write_lines(
        path,
        &text,
        lines.into_iter().map(|(line, r)| {
            let (v, b, m, p) = r.counts;
            shape.add_summary_counts(v, b, m, p);
            line
        }),
    )?;
    let export_ms = export_started.elapsed().as_millis();
    Ok(ExportPRun {
        stats: ExportStats {
            lines: count,
            orders_held: count,
            spec_graphs: acc.graphs,
            executions: acc.executions,
            explore_ms,
            summarise_ms: acc.summarise.as_millis(),
            export_ms,
            graphs_complete: acc.complete,
            graphs_blocked: acc.blocked,
            shape,
        },
        max_worker_lines: acc.max_worker_lines,
        merged_bytes,
    })
}
