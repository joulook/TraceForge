//! `C` (criteria `ONLINE.md`): the online check. A program's implementation is
//! explored once against a specification summary file (`SUMMARY-FORMAT.md`
//! version 1), each implementation graph summarised and looked up as it
//! completes, then dropped (semi-stateful).
//!
//! - **The specification:** J3's reader ([`read_file`]); a file that is not
//!   `complete`, or whose `visible` list is not the program's, is refused
//!   before any exploration. Its summaries go into a `SetIndex` as `conf_join`
//!   builds it.
//! - **The lookup:** each completion's `CompactSummary` is rendered to its
//!   normal line by G1's generic encoder and parsed back by J3's reader, so it
//!   lives in the index's decoded value domain, then queried with `covers`.
//! - **The two modes:** full (the default) counts every uncovered graph to the
//!   end of the exploration and keeps the first; bug-finder stops at the first.
//! - **Failures** (an assertion failure, a value the encoder refuses, a panic)
//!   end the run `failed` with the state of the last completed update; the
//!   exploration runs on a worker thread so that a panic reaches the join.
//!
//! The text is rendered in `report.rs` (S5 criterion 1); nothing here prints.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

use crate::conformance::compact::{CompactSummary, Covers, SetIndex};
use crate::conformance::ctx::{CompletionSink, ConfMode, DiagnosticReason, SinkVerdict};
use crate::conformance::interchange::{
    encode_generic, json_string, line_of, model_name, parse_line, read_file, record_thread_names,
    sorted_names, write_replacing, Enumeration, ExportHeader, FileHead, ThreadNames,
};
use crate::conformance::measure::Shape;
use crate::conformance::report::SearchEnd;
use crate::conformance::stateful;
use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::must::MustState;
use crate::Config;

/// The exploration mode (ONLINE-0.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mode {
    /// The default: every uncovered graph counted, the first kept.
    Full,
    /// `--stop-at-first`: the run stops at the first uncovered graph.
    BugFinder,
}

/// How the run ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum End {
    Exhausted,
    Budget,
    FirstMiss,
    Failed,
}

/// The index's answer for an uncovered summary, as JMC names it: `NoSig` is
/// `NoBucket` or `NoSig`, `NotFound` is `NotFound`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MissKind {
    NoSig,
    NotFound,
}

/// The first uncovered graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FirstMiss {
    /// 1-based, counting every completion (blocked ones included).
    pub(crate) iteration: usize,
    /// Since the clock started (after the index was built).
    pub(crate) wall_ms: u64,
    /// Its normal line.
    pub(crate) line: String,
    pub(crate) kind: MissKind,
}

/// The run's verdict (JMC's three words).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Verdict {
    Conforms,
    Reports,
    Partial,
}

/// What `--out` names: the file and the implementation's own header fields.
pub(crate) struct OnlineOut {
    pub(crate) path: PathBuf,
    pub(crate) header: ExportHeader,
}

/// The settings of one online run besides the program.
pub(crate) struct OnlineOpts {
    pub(crate) mode: Mode,
    /// `Config::max_iterations` for the exploration.
    pub(crate) budget: Option<u64>,
    pub(crate) out: Option<OnlineOut>,
    /// Test seam (M1): panic in the sink's unlocked computation at this
    /// iteration.
    #[cfg(test)]
    pub(crate) fault_at: Option<usize>,
    /// Test seam (M3): sleep this long in the indexing phase, before the clock.
    #[cfg(test)]
    pub(crate) index_delay: Option<std::time::Duration>,
    /// `B` test seam (MEAS-2): sleep this long in each completion's summarise
    /// phase.
    #[cfg(test)]
    pub(crate) summarise_delay: Option<Duration>,
    /// `B` test seam (MEAS-2): sleep this long in each completion's lookup.
    #[cfg(test)]
    pub(crate) lookup_delay: Option<Duration>,
    /// `B` test seam (MEAS-2): sleep this long in the `--out` write.
    #[cfg(test)]
    pub(crate) export_delay: Option<Duration>,
}

impl OnlineOpts {
    pub(crate) fn new(mode: Mode, budget: Option<u64>, out: Option<OnlineOut>) -> Self {
        OnlineOpts {
            mode,
            budget,
            out,
            #[cfg(test)]
            fault_at: None,
            #[cfg(test)]
            index_delay: None,
            #[cfg(test)]
            summarise_delay: None,
            #[cfg(test)]
            lookup_delay: None,
            #[cfg(test)]
            export_delay: None,
        }
    }
}

/// What one online run found (ONLINE-0.1).
#[derive(Clone, Debug)]
pub(crate) struct OnlineReport {
    pub(crate) spec_path: String,
    pub(crate) spec: FileHead,
    /// The specification file's summary lines.
    pub(crate) spec_lines: usize,
    /// The distinct summaries the index holds.
    pub(crate) held: usize,
    pub(crate) mode: Mode,
    /// Completions seen, 1-based count, blocked ones included.
    pub(crate) iterations: usize,
    pub(crate) lookups: usize,
    pub(crate) found: usize,
    pub(crate) signature_misses: usize,
    pub(crate) not_found: usize,
    /// Every uncovered graph, the first included.
    pub(crate) uncovered_total: usize,
    /// The distinct uncovered lines.
    pub(crate) uncovered_distinct: usize,
    pub(crate) first: Option<FirstMiss>,
    pub(crate) end: End,
    /// The failure's message when `end` is `Failed`.
    pub(crate) failure: Option<String>,
    /// The `--out` file written, if any, and its line count.
    pub(crate) out_written: Option<(String, usize)>,
    /// `B` (MEAS-1 K4): the phases, each the floor of its summed durations in
    /// milliseconds; `explore_ms` = `enumerate`'s wall − summarise − lookup.
    pub(crate) index_ms: u128,
    pub(crate) explore_ms: u128,
    pub(crate) summarise_ms: u128,
    pub(crate) lookup_ms: u128,
    pub(crate) export_ms: u128,
    /// `enumerate`'s wall, in milliseconds.
    pub(crate) enumerate_ms: u128,
    /// The completions, by Must's rule (`check_blocked`).
    pub(crate) graphs_complete: usize,
    pub(crate) graphs_blocked: usize,
    /// The distinct implementation lines (kept on every run, MEAS M2).
    pub(crate) impl_lines: usize,
    /// The shape counters over the completions and their summaries.
    pub(crate) shape: Shape,
}

impl OnlineReport {
    /// `reports` if a miss was seen; `conforms` if the run ended by exhaustion
    /// without a failure; `partial` otherwise.
    pub(crate) fn verdict(&self) -> Verdict {
        if self.first.is_some() {
            Verdict::Reports
        } else if self.end == End::Exhausted {
            Verdict::Conforms
        } else {
            Verdict::Partial
        }
    }

    /// JMC's exit codes: 0 with a verdict, 1 when the run failed.
    pub(crate) fn exit_code(&self) -> u8 {
        if self.end == End::Failed {
            1
        } else {
            0
        }
    }
}

/// A refusal before the exploration (exit 2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OnlineError {
    /// The specification file does not read (J3's reader's message).
    Spec(String),
    /// The specification is not `complete`.
    NotComplete { path: String, enumeration: String },
    /// The file's `visible` list is not the program's.
    Visible {
        file: Vec<String>,
        program: Vec<String>,
    },
    /// `--out` with a model the format cannot name.
    Model(String),
}

/// The sink's state, shared with the caller through the worker's join.
#[derive(Default)]
struct State {
    iterations: usize,
    lookups: usize,
    found: usize,
    signature_misses: usize,
    not_found: usize,
    uncovered_total: usize,
    uncovered: HashSet<String>,
    first: Option<FirstMiss>,
    failure: Option<String>,
    /// Every distinct implementation line: kept on every run (`B`, MEAS-1 K4,
    /// for `summaries_distinct`), and written by `--out`.
    lines: Option<HashSet<String>>,
    /// `B`: the summed phases, the completion classes, the shape counters.
    summarise: Duration,
    lookup: Duration,
    complete: usize,
    blocked: usize,
    shape: Shape,
}

/// `B`: what one completion measured, computed without the lock (step (2)) and
/// folded in by the locked update (step (3)).
struct Probe {
    blocked: bool,
    events: u128,
    messages: u128,
    /// The summary's visible events, line bytes, largest and non-zero order
    /// counts; `None` when the completion was not summarised (a failure).
    summary: Option<(u128, u128, u128, u128)>,
    summarise: Duration,
    lookup: Duration,
}

/// One completion's result, computed without the lock, with the line's copy
/// for each set it joins (`--out`'s copy only when `--out` is on).
enum Step {
    Found {
        out: Option<String>,
    },
    Miss {
        first: String,
        uncovered: String,
        out: Option<String>,
        kind: MissKind,
        wall_ms: u64,
    },
    Failed(String),
}

impl State {
    /// Step (1): the next iteration (1-based).
    fn next_iteration(&mut self) -> usize {
        self.iterations += 1;
        self.iterations
    }

    /// Step (3): the completion's result in one update that cannot unwind —
    /// counter increments, at most one insertion into each set, at most one
    /// first-miss assignment, a recorded failure; every value made in step (2)
    /// (`criteria/ONLINE.md` ONLINE-0.1, round 03 M1).
    fn commit(
        &mut self,
        (step, probe): (Step, Probe),
        iteration: usize,
        mode: Mode,
    ) -> SinkVerdict {
        if probe.blocked {
            self.blocked += 1;
        } else {
            self.complete += 1;
        }
        // MEAS-1 K4: the shape counters run over the summarised graphs only; a
        // completion that failed (an assertion, a refused value) is counted in
        // `graphs_*` but not in the shape (the tester's gate-3 finding).
        if let Some((visible, bytes, max, pairs)) = probe.summary {
            self.shape.add_graph_counts(probe.events, probe.messages);
            self.shape.add_summary_counts(visible, bytes, max, pairs);
        }
        self.summarise += probe.summarise;
        self.lookup += probe.lookup;
        match step {
            Step::Failed(msg) => {
                self.failure = Some(msg);
                SinkVerdict::Stop
            }
            Step::Found { out } => {
                self.lookups += 1;
                self.found += 1;
                if let (Some(ls), Some(l)) = (self.lines.as_mut(), out) {
                    ls.insert(l);
                }
                SinkVerdict::Continue
            }
            Step::Miss {
                first,
                uncovered,
                out,
                kind,
                wall_ms,
            } => {
                self.lookups += 1;
                match kind {
                    MissKind::NoSig => self.signature_misses += 1,
                    MissKind::NotFound => self.not_found += 1,
                }
                self.uncovered_total += 1;
                if self.first.is_none() {
                    self.first = Some(FirstMiss {
                        iteration,
                        wall_ms,
                        line: first,
                        kind,
                    });
                }
                if let (Some(ls), Some(l)) = (self.lines.as_mut(), out) {
                    ls.insert(l);
                }
                self.uncovered.insert(uncovered);
                match mode {
                    Mode::BugFinder => SinkVerdict::Stop,
                    Mode::Full => SinkVerdict::Continue,
                }
            }
        }
    }
}

/// Step (2): one completion's result, without the lock — the assertion check,
/// the summary, its normal line through G1's encoder, the line parsed back by
/// J3's reader into the index's value domain, `covers`, the clock, and the
/// line's copy for each set it joins.
fn step_of(
    g: &ExecutionGraph,
    visible: &[String],
    names: &[String],
    threads: &mut ThreadNames,
    index: &SetIndex,
    keep_lines: bool,
    started: Instant,
    seams: &Seams,
) -> (Step, Probe) {
    let (events, messages) = Shape::graph_counts(g);
    let mut probe = Probe {
        blocked: g.check_blocked().is_some(),
        events,
        messages,
        summary: None,
        summarise: Duration::ZERO,
        lookup: Duration::ZERO,
    };
    if let Some(msg) = failed_assertion(g) {
        return (Step::Failed(msg), probe);
    }
    let t = Instant::now();
    seams.summarise();
    let cs = CompactSummary::at_completion(g, visible, "implementation");
    record_thread_names(g, threads);
    let threads: &ThreadNames = threads;
    let text = match line_of(&cs.sig, &cs.ord, names, &|v| encode_generic(v, threads)) {
        Ok(t) => t,
        Err(e) => {
            probe.summarise = t.elapsed();
            return (Step::Failed(e.to_string()), probe);
        }
    };
    let (line, decoded) = parse_line(&text, names).unwrap_or_else(|e| {
        panic!("conformance: online: an encoded line does not parse back ({e}): {text}")
    });
    probe.summarise = t.elapsed();
    probe.summary = Some(Shape::summary_counts(&cs.sig, &cs.ord, names, line.len()));
    let out = keep_lines.then(|| line.clone());
    let t = Instant::now();
    seams.lookup();
    let answer = index.covers(&decoded).1;
    probe.lookup = t.elapsed();
    let kind = match answer {
        Covers::Found(_) => return (Step::Found { out }, probe),
        Covers::NoBucket | Covers::NoSig => MissKind::NoSig,
        Covers::NotFound => MissKind::NotFound,
    };
    let step = Step::Miss {
        first: line.clone(),
        uncovered: line,
        out,
        kind,
        wall_ms: started.elapsed().as_millis() as u64,
    };
    (step, probe)
}

/// `B`'s per-completion test seams, copied out of [`OnlineOpts`] for the
/// worker; inert outside tests.
#[derive(Clone, Copy, Default)]
struct Seams {
    #[cfg(test)]
    summarise: Option<Duration>,
    #[cfg(test)]
    lookup: Option<Duration>,
}

impl Seams {
    fn summarise(&self) {
        #[cfg(test)]
        if let Some(d) = self.summarise {
            std::thread::sleep(d);
        }
    }

    fn lookup(&self) {
        #[cfg(test)]
        if let Some(d) = self.lookup {
            std::thread::sleep(d);
        }
    }
}

/// The lock, recovered if a panic ever poisoned it.
fn lock(state: &Mutex<State>) -> MutexGuard<'_, State> {
    state.lock().unwrap_or_else(|p| p.into_inner())
}

/// The first `Block(Assert)` that is its thread's last paper event (the last
/// label, or the one before a trailing `End`), on any thread: the label the
/// engine installs at a failed assertion.
fn failed_assertion(g: &ExecutionGraph) -> Option<String> {
    for t in g.thread_ids() {
        let mut n = g.thread_size(t);
        if n == 0 {
            continue;
        }
        if n >= 2 && matches!(g.label(Event::new(t, (n - 1) as u32)), LabelEnum::End(_)) {
            n -= 1;
        }
        let e = Event::new(t, (n - 1) as u32);
        if let LabelEnum::Block(b) = g.label(e) {
            if matches!(b.btype(), BlockType::Assert) {
                let name = g.thread_name(t).unwrap_or("(unnamed)").to_string();
                return Some(format!("assertion failure on thread `{name}` at {e:?}"));
            }
        }
    }
    None
}

/// The panic payload's text.
fn panic_text(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_owned()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_owned()
    }
}

/// The `--out` header: the export's, with the run's `enumeration` and the
/// three online fields after it (JMC's `SummaryExporter.OnlineFields`; 0 for
/// none).
fn out_header(
    h: &ExportHeader,
    names: &[String],
    model: &str,
    enumeration: Enumeration,
    r: &OnlineReport,
) -> String {
    let visible: Vec<String> = names.iter().map(|n| json_string(n)).collect();
    let (iteration, wall) = r
        .first
        .as_ref()
        .map_or((0, 0), |f| (f.iteration, f.wall_ms));
    format!(
        "{{\"format\":1,\"tool\":\"traceforge\",\"program\":{},\"size\":{},\"visible\":[{}],\
         \"model\":{},\"enumeration\":\"{}\",\"first_miss_iteration\":{},\
         \"first_miss_wall_ms\":{},\"uncovered_total\":{},\"encoding\":1}}",
        json_string(&h.program),
        json_string(&h.size),
        visible.join(","),
        json_string(model),
        enumeration.name(),
        iteration,
        wall,
        r.uncovered_total
    )
}

/// `C`: the online check of `imp` (visible threads `visible`, under `config`)
/// against the specification file `spec_path`. `Err` is a refusal before the
/// exploration; a run that fails is an `Ok` whose end is `Failed`.
pub(crate) fn online(
    config: &Config,
    visible: &[String],
    imp: Arc<dyn Fn() + Send + Sync>,
    spec_path: &Path,
    opts: OnlineOpts,
) -> Result<OnlineReport, OnlineError> {
    let names = sorted_names(visible);
    // `B` (MEAS-1 K4): `index_ms` is the file read and the inserts.
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
    let model = match &opts.out {
        Some(_) => {
            Some(model_name(config.cons_type).map_err(|e| OnlineError::Model(e.to_string()))?)
        }
        None => None,
    };
    // The index seam sits between the file read and the inserts (inside the
    // indexing phase, before the clock), so a timer started after the read or
    // after the inserts would miss it (B's gate-3 finding).
    #[cfg(test)]
    if let Some(d) = opts.index_delay {
        std::thread::sleep(d);
    }
    let mut index = SetIndex::new();
    for (_, _, summary) in &file.lines {
        index.insert(summary);
    }
    let held = index.stats().entries;
    let index_ms = index_started.elapsed().as_millis();

    // `B`: the distinct implementation lines are kept on every run.
    let state = Arc::new(Mutex::new(State {
        lines: Some(HashSet::new()),
        ..State::default()
    }));
    let mut run_config = config.clone();
    run_config.max_iterations = opts.budget;
    let mode = opts.mode;
    let keep_lines = true;
    #[cfg(test)]
    let fault_at = opts.fault_at;
    let seams = Seams {
        #[cfg(test)]
        summarise: opts.summarise_delay,
        #[cfg(test)]
        lookup: opts.lookup_delay,
    };
    let spawned = Instant::now();
    let worker = {
        let state = Arc::clone(&state);
        let visible = visible.to_vec();
        let names = names.clone();
        std::thread::Builder::new()
            .name("online".to_string())
            .spawn(move || {
                crate::conformance::assert_config_in_scope(&run_config, "online");
                let mut threads = ThreadNames::new();
                let started = Instant::now();
                let sink_state = Arc::clone(&state);
                let sink_visible = visible.clone();
                let sink: CompletionSink = Box::new(move |g: &ExecutionGraph, _: &MustState| {
                    // (1) the iteration, under the lock.
                    let iteration = lock(&sink_state).next_iteration();
                    // (2) the result, without the lock.
                    #[cfg(test)]
                    if fault_at == Some(iteration) {
                        panic!("conformance: online test fault at iteration {iteration}");
                    }
                    let step = step_of(
                        g,
                        &sink_visible,
                        &names,
                        &mut threads,
                        &index,
                        keep_lines,
                        started,
                        &seams,
                    );
                    // (3) one locked update that cannot unwind.
                    lock(&sink_state).commit(step, iteration, mode)
                });
                let run = stateful::enumerate(
                    stateful::EnumRun {
                        config: run_config,
                        visible,
                        mode: ConfMode::Enumerate,
                        sink,
                        cut: false,
                        stop_at_first_report: false,
                        gate_sink: None,
                        paper_events: false,
                    },
                    &imp,
                );
                let enumerate_wall = started.elapsed();
                let errors = run.visible_errors.len()
                    + run
                        .diagnostics
                        .iter()
                        .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
                        .count();
                (run.end, errors, enumerate_wall)
            })
            .expect("conformance: online: could not spawn the run thread")
    };
    let joined = worker.join();
    let mut st = lock(&state);
    // On a panic the worker's clock is lost; the spawn-to-join wall stands in.
    let enumerate_wall = match &joined {
        Ok((_, _, w)) => *w,
        Err(_) => spawned.elapsed(),
    };
    let (end, failure) = match joined {
        Err(payload) => (End::Failed, Some(panic_text(payload))),
        Ok((search_end, errors, _)) => {
            if let Some(msg) = st.failure.take() {
                (End::Failed, Some(msg))
            } else if errors > 0 {
                (
                    End::Failed,
                    Some(format!(
                        "{errors} assertion failure(s) recorded by the engine and not seen at a \
                         completion"
                    )),
                )
            } else {
                match search_end {
                    SearchEnd::StateSpaceExhausted => (End::Exhausted, None),
                    SearchEnd::MaxIterations(_) => (End::Budget, None),
                    SearchEnd::StoppedAtFirstReport => (End::FirstMiss, None),
                    other => (
                        End::Failed,
                        Some(format!("the exploration ended {other:?}")),
                    ),
                }
            }
        }
    };
    let mut report = OnlineReport {
        spec_path: spec_path.display().to_string(),
        spec: file.head.clone(),
        spec_lines: file.lines.len(),
        held,
        mode,
        iterations: st.iterations,
        lookups: st.lookups,
        found: st.found,
        signature_misses: st.signature_misses,
        not_found: st.not_found,
        uncovered_total: st.uncovered_total,
        uncovered_distinct: st.uncovered.len(),
        first: st.first.clone(),
        end,
        failure,
        out_written: None,
        index_ms,
        explore_ms: enumerate_wall
            .saturating_sub(st.summarise)
            .saturating_sub(st.lookup)
            .as_millis(),
        summarise_ms: st.summarise.as_millis(),
        lookup_ms: st.lookup.as_millis(),
        export_ms: 0,
        enumerate_ms: enumerate_wall.as_millis(),
        graphs_complete: st.complete,
        graphs_blocked: st.blocked,
        impl_lines: st.lines.as_ref().map_or(0, HashSet::len),
        shape: st.shape.clone(),
    };
    if let (Some(out), Some(model)) = (opts.out, model) {
        let enumeration = match report.end {
            End::Exhausted => Enumeration::Complete,
            End::Budget => Enumeration::Bounded,
            End::FirstMiss | End::Failed => Enumeration::Aborted,
        };
        let mut lines: Vec<String> = st.lines.take().unwrap_or_default().into_iter().collect();
        lines.sort();
        let mut text = out_header(
            &out.header,
            &report.spec_visible_names(),
            model,
            enumeration,
            &report,
        );
        text.push('\n');
        for l in &lines {
            text.push_str(l);
            text.push('\n');
        }
        // `B` (MEAS-1 K4): `export_ms` is the write.
        let export_started = Instant::now();
        #[cfg(test)]
        if let Some(d) = opts.export_delay {
            std::thread::sleep(d);
        }
        let written = write_replacing(&out.path, &text);
        report.export_ms = export_started.elapsed().as_millis();
        match written {
            Ok(()) => report.out_written = Some((out.path.display().to_string(), lines.len())),
            Err(e) => {
                report.end = End::Failed;
                report.failure = Some(e.to_string());
            }
        }
    }
    Ok(report)
}

impl OnlineReport {
    /// The visible names, sorted (the file's list, equal to the program's).
    fn spec_visible_names(&self) -> Vec<String> {
        self.spec.visible.clone()
    }
}
