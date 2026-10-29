//! `SVERIFY-P` P-S: CVerify-P, the parallel stateless refinement check — the
//! parallel form of the complete-first engine (`cfirst.rs`), as
//! `MESSAGE-parallel.md` row P-S orders it, amended by the owner's rulings
//! (`ISSUE-parallel.md` §4), and as `criteria/SVERIFY-P-PS.md` (revision 1.4)
//! specifies it.
//!
//! **The outer run** explores the implementation in Must's partitioned mode
//! (`parallel_verify::verify_partitioned_rayon_with`, I3's hooked runner and
//! its cancel token), each worker's context in the twin mode
//! `ConfMode::CFirstOuterPartitioned` (plain-scheduled, enumerating, no cut).
//! At every completion a worker builds the compact summary and probes **the
//! shared witness cache** (`compact::SharedCache`: a per-worker signature
//! table synced from an append-only log, the order store behind a read-write
//! lock, one admission lock). On a hit it continues; on a miss **it sweeps
//! the specification itself, inline** (the owner's ruling Q7 a: the workers
//! are the pool, no thread per sweep): a fresh `Must` in `CFirstSweep` on this
//! thread, the outer `Must` saved and restored around it. A witness is
//! admitted under the admission lock after a re-probe (another worker may
//! have admitted a covering witness meanwhile: a redundant sweep, counted);
//! an exhausted sweep is a report, its summary kept in a counting set and
//! its graph as `all_reports` rules; an aborting sweep (a specification
//! assertion) records the first abort's errors and cancels the token.
//!
//! **What equals the sequential engine's** (ruling 1): the verdict, the
//! reports (as a multiset of summaries), the coverage of every implementation
//! completion, the per-completion counts; the cache's content does not (the
//! misses' order decides the admissions). The sequential engine is unchanged.
//!
//! `threads` is the one parameter; nothing here reads the machine.

use std::cell::RefCell;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::conformance::cfirst::{classify, note_first_report, spec_errors_of, SweepEnd, Swept};
use crate::conformance::compact::{
    Admission, CacheProbe, CompactSummary, OrdCounts, QueryCounts, SetIndex, SharedCache, Watch,
    WorkerTable,
};
use crate::conformance::config::{Capacity, CompletionCover, ConfConfig, Engine};
use crate::conformance::ctx::{
    CompletionSink, ConfCtx, ConfMode, Diagnostic, DiagnosticReason, SinkVerdict,
};
use crate::conformance::ctx::{Gate, ReportKind};
use crate::conformance::precheck;
use crate::conformance::report::{
    build_report_for, replay_snapshot, CFirstCounters, CFirstPCounters, ConfCounters, ConfError,
    ConfNote, ConfOutcome, ConfVerdict, Diagnostics, ReplaySnapshot, SearchEnd, SpecErrFreedom,
    UncoveredSummary,
};
use crate::conformance::sig::Sig;
use crate::conformance::stateful::{enumerate, EnumRun};
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;
use crate::must::{Must, MustState};
use crate::parallel_verify::{verify_partitioned_rayon_with, CancelToken, PartitionHooks};
use crate::Config;

/// The engine-level result (PS-4): what the tester compares, beyond the
/// public verdict.
pub(crate) struct CFirstPOutcome {
    pub(crate) counters: CFirstPCounters,
    /// The reports' graphs and snapshots, as `all_reports` rules (ruling 1):
    /// every one with the knob on, the first reporting worker's one off; in
    /// no particular order.
    pub(crate) reports: Vec<(ExecutionGraph, ReplaySnapshot)>,
    /// The reported summaries with their multiplicities (Σ = `reports`), in
    /// the merged counting set's order.
    pub(crate) uncovered: Vec<(Sig, OrdCounts, usize)>,
    /// The outer run's end: `StoppedAtFirstReport` iff the token was
    /// cancelled (a stop, an abort, a sweep panic), else `StateSpaceExhausted`.
    pub(crate) impl_end: SearchEnd,
    /// The first aborting sweep's assertion failures, canonically ordered.
    pub(crate) spec_errors: Vec<(String, Event, bool)>,
    pub(crate) impl_notes: Vec<Diagnostic>,
    /// Every outer execution (the contexts' `executions`, summed over tasks).
    pub(crate) executions: usize,
    /// `SVERIFY-P` V-C (VC-0): the outer run's complete and blocked endings,
    /// the partitioned runner's `stats.execs` and `stats.block` as they are.
    pub(crate) impl_complete: usize,
    pub(crate) impl_blocked: usize,
    pub(crate) max_paper_events: Option<usize>,
    pub(crate) aborted: bool,
    /// Rulings 1 and 16, test builds only: the final cache — its signatures
    /// by `SigId` and its held orders — for the coverage check under `w=inf`
    /// (gate 3, D-1: the cache is dropped with the run otherwise).
    #[cfg(test)]
    pub(crate) final_cache: (
        Vec<(crate::conformance::compact::SigHash, Sig)>,
        Vec<(crate::conformance::compact::SigId, u64, OrdCounts)>,
    ),
}

/// Ruling 20, test builds only: the engine's first-report reads (process-wide).
#[cfg(test)]
static FIRST_REPORT_READS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
/// Ruling 20, test builds only: the restores of the outer `Must` after a
/// sweep that did not put the saved value back (0 by construction).
#[cfg(test)]
static CURRENT_MUST_MISMATCHES: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
/// Ruling 20, test builds only: the completions the sinks saw, process-wide
/// (to show the workers stopped after a cancelled panic).
#[cfg(test)]
static SINK_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
/// Ruling 20, test builds only: the gate between a worker's sweep and its
/// admission's re-probe, held closed by a test to force the races.
#[cfg(test)]
pub(crate) static ADMISSION_GATE: crate::conformance::compact::TestGate =
    crate::conformance::compact::TestGate::new();

#[cfg(test)]
pub(crate) fn first_report_reads_for_test() -> usize {
    FIRST_REPORT_READS.load(std::sync::atomic::Ordering::SeqCst)
}
#[cfg(test)]
pub(crate) fn current_must_mismatches_for_test() -> usize {
    CURRENT_MUST_MISMATCHES.load(std::sync::atomic::Ordering::SeqCst)
}
#[cfg(test)]
pub(crate) fn sink_calls_for_test() -> usize {
    SINK_CALLS.load(std::sync::atomic::Ordering::SeqCst)
}
#[cfg(test)]
pub(crate) fn reset_counts_for_test() {
    FIRST_REPORT_READS.store(0, std::sync::atomic::Ordering::SeqCst);
    CURRENT_MUST_MISMATCHES.store(0, std::sync::atomic::Ordering::SeqCst);
    SINK_CALLS.store(0, std::sync::atomic::Ordering::SeqCst);
}

/// One worker's state, thread-local (as I3's), initialised by `on_must` and
/// flushed at every task end.
struct Worker {
    table: WorkerTable,
    /// The distinct implementation summaries (the `impl_distinct` knob),
    /// merged by move at task end.
    seen: Option<SetIndex>,
    /// The reported summaries, a counting set merged by move at task end.
    uncovered: SetIndex,
    /// The context's accumulators already flushed from this thread.
    flushed: (usize, usize),
    /// PS-7: whether this worker is the root (the first `Must` the runner
    /// hooks), whose first `warmup` completions are the sequential warmup.
    root: bool,
    tally: Tally,
}

thread_local! {
    static WORKER: RefCell<Option<Worker>> = const { RefCell::new(None) };
}

/// A thread's per-task tallies.
#[derive(Default)]
struct Tally {
    impl_graphs: usize,
    cache_probes: usize,
    cache_hits: usize,
    sweeps: usize,
    sweeps_successful: usize,
    sweeps_failing: usize,
    sweeps_aborted: usize,
    sweep_sizes: Vec<usize>,
    sweep_graphs: usize,
    sweep_graphs_max: usize,
    reports: usize,
    unprobed_after_cancel: usize,
    /// PS-7: where the sweeps fell — the root's warmup, the root's loop, the
    /// tasks.
    sweeps_in_warmup: usize,
    sweeps_in_root_loop: usize,
    sweeps_in_tasks: usize,
    /// Ruling 21: sweeps abandoned because the cache came to cover their
    /// summary, and the watches' re-probes.
    sweeps_abandoned: usize,
    watch_probes: usize,
    sweep_time: Duration,
    query: QueryCounts,
}

/// The run's accumulation across the tasks.
#[derive(Default)]
struct Acc {
    tally: Tally,
    uncovered: SetIndex,
    seen: Option<SetIndex>,
    executions: usize,
    max_paper: usize,
    diagnostics: Vec<Diagnostic>,
    syncs: usize,
    sig_tests: usize,
    flushes: usize,
}

impl Acc {
    fn add(&mut self, t: Tally) {
        let a = &mut self.tally;
        a.impl_graphs += t.impl_graphs;
        a.cache_probes += t.cache_probes;
        a.cache_hits += t.cache_hits;
        a.sweeps += t.sweeps;
        a.sweeps_successful += t.sweeps_successful;
        a.sweeps_failing += t.sweeps_failing;
        a.sweeps_aborted += t.sweeps_aborted;
        a.sweep_sizes.extend(t.sweep_sizes);
        a.sweep_graphs += t.sweep_graphs;
        a.sweep_graphs_max = a.sweep_graphs_max.max(t.sweep_graphs_max);
        a.reports += t.reports;
        a.unprobed_after_cancel += t.unprobed_after_cancel;
        a.sweeps_in_warmup += t.sweeps_in_warmup;
        a.sweeps_in_root_loop += t.sweeps_in_root_loop;
        a.sweeps_in_tasks += t.sweeps_in_tasks;
        a.sweeps_abandoned += t.sweeps_abandoned;
        a.watch_probes += t.watch_probes;
        a.sweep_time += t.sweep_time;
        a.query.exact_hits += t.query.exact_hits;
        a.query.containment_tests += t.query.containment_tests;
        a.query.coordinates_compared += t.query.coordinates_compared;
    }
}

/// The first report's record (E9), written once under its lock.
#[derive(Default)]
struct FirstReport {
    wall_ms: Option<u128>,
    vmhwm_kb: Option<u64>,
    spawned_at_stop: Option<u64>,
    /// A report's graph was kept (the first worker's one, `all_reports` off).
    kept_one: bool,
}

/// What the run shares across its workers.
struct Shared {
    cache: SharedCache,
    acc: Mutex<Acc>,
    first: Mutex<FirstReport>,
    reports: Mutex<Vec<(ExecutionGraph, ReplaySnapshot)>>,
    /// The first aborting sweep's errors, set once (ruling 5).
    abort: Mutex<Option<Vec<(String, Event, bool)>>>,
    cancel: Arc<CancelToken>,
    started: Instant,
    /// PS-7: set by the first `on_must`, the root's (the runner hooks the
    /// root before it spawns any task).
    root_claimed: std::sync::atomic::AtomicBool,
}

/// `MIN-ENGINES` E7a's compact sweep test, as `cfirst.rs` has it (private
/// there; the sequential engine does not change).
fn covers_compact(spec: &CompactSummary, query: &CompactSummary) -> bool {
    spec.hash == query.hash && spec.sig == query.sig && spec.ord.le(&query.ord)
}

/// The reported graph's label count, as `cfirst.rs` counts `events`.
fn label_count(graph: &ExecutionGraph) -> usize {
    graph
        .thread_ids()
        .into_iter()
        .map(|t| graph.thread_size(t))
        .sum()
}

/// One sweep of the specification **on this thread** (ruling 3): a fresh
/// `Must` in `CFirstSweep` with the compact test, exactly `cfirst::sweep_with`'s
/// body on its thread, without the thread. The caller saves and restores the
/// outer `Must` around it and catches a panic. Ruling 21: `watch`, when given,
/// is asked at each specification completion before the covering test; a
/// `true` stops the sweep at once, and the second result says it was
/// abandoned (no witness, no report: the caller handles it before
/// `classify`).
pub(crate) fn sweep_inline(
    config: &Config,
    visible: &[String],
    specification: &Arc<dyn Fn() + Send + Sync>,
    cs: CompactSummary,
    quiet: bool,
    watch: Option<Box<dyn FnMut() -> bool>>,
) -> (Swept, bool) {
    let mut spec_config = config.clone();
    spec_config.max_iterations = None;
    if quiet {
        spec_config.progress_report = usize::MAX;
    }
    // As `cfirst::sweep_with`: no observers and no trace/dot outputs on a
    // sweep.
    spec_config.callbacks = Arc::new(std::sync::Mutex::new(Vec::new()));
    spec_config.dot_file = None;
    spec_config.trace_file = None;
    spec_config.error_trace_file = None;
    spec_config.turmoil_trace_file = None;
    // The partitioned flags are the outer run's; a sweep is sequential.
    spec_config.partitioned_parallelization = false;
    spec_config.partitioned_num_threads = None;
    let visible_v = visible.to_vec();
    let query: Rc<RefCell<Option<CompactSummary>>> = Rc::new(RefCell::new(Some(cs)));
    let found_summary: Rc<RefCell<Option<CompactSummary>>> = Rc::new(RefCell::new(None));
    let tested = Rc::new(RefCell::new(0usize));
    let abandoned = Rc::new(RefCell::new(false));
    let sink = {
        let query = Rc::clone(&query);
        let found_summary = Rc::clone(&found_summary);
        let tested = Rc::clone(&tested);
        let abandoned = Rc::clone(&abandoned);
        let mut watch = watch;
        let visible = visible_v.clone();
        Box::new(move |m: &ExecutionGraph, _: &MustState| {
            // Ruling 21: the watch first; the cache now covers the summary.
            if let Some(w) = watch.as_mut() {
                if w() {
                    *abandoned.borrow_mut() = true;
                    return SinkVerdict::Stop;
                }
            }
            *tested.borrow_mut() += 1;
            let q = query.borrow();
            let cs = q
                .as_ref()
                .expect("conformance: the sweep's compact query is set");
            let spec = CompactSummary::at_completion(m, &visible, "specification");
            if covers_compact(&spec, cs) {
                *found_summary.borrow_mut() = Some(spec);
                return SinkVerdict::Stop;
            }
            SinkVerdict::Continue
        }) as CompletionSink
    };
    let run = enumerate(
        EnumRun {
            config: spec_config,
            visible: visible_v,
            mode: ConfMode::CFirstSweep,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        specification,
    );
    let witness_summary = found_summary.borrow_mut().take();
    let query = query.borrow_mut().take();
    let tested = *tested.borrow();
    let abandoned = *abandoned.borrow();
    (
        Swept {
            run,
            witness: None,
            witness_summary,
            query,
            tested,
            kept: Vec::new(),
            budgeted: false,
        },
        abandoned,
    )
}

/// The hooks' worker state at `on_must`.
fn init_worker(impl_distinct: bool, root: bool) {
    WORKER.with(|w| {
        *w.borrow_mut() = Some(Worker {
            table: WorkerTable::new(),
            seen: impl_distinct.then(SetIndex::new),
            uncovered: SetIndex::with_multiplicities(),
            flushed: (0, 0),
            root,
            tally: Tally::default(),
        })
    });
}

/// The engine's run (PS-1 to PS-4): the refusals, the outer run with the
/// inline sweeps, the outcome. Every path reaches this entry.
pub(crate) fn run_with(
    cc: &ConfConfig,
    implementation: &Arc<dyn Fn() + Send + Sync>,
    specification: &Arc<dyn Fn() + Send + Sync>,
) -> CFirstPOutcome {
    assert!(
        cc.threads >= 1,
        "conformance: complete-first-p needs threads(t) with t >= 1; threads(0) is not a \
         configuration (SVERIFY-P PS-1)"
    );
    assert!(
        cc.config.max_iterations.is_none(),
        "conformance: complete-first-p refuses max_iterations: the partitioned runner's chunk cap \
         is its own, never the user's (SVERIFY-P ruling)"
    );
    assert!(
        !cc.config.parallel,
        "conformance: complete-first-p refuses the shared-queue parallel mode; the partitioned \
         mode is its own (SVERIFY-P PS-1)"
    );
    assert!(
        cc.completion_cover != CompletionCover::Flat,
        "conformance: complete-first-p refuses completion_cover(Flat): the Flat adapter is the \
         sequential engine's (SVERIFY-P PS-1)"
    );
    assert!(
        !cc.early_error_cut,
        "conformance: complete-first-p refuses early_error_cut(true): the cut is the sequential \
         engine's (SVERIFY-P PS-1)"
    );
    assert!(
        cc.witness_cache != Capacity::Bounded(0),
        "conformance: witness_cache(Bounded(0)) is not a configuration; Capacity::Zero is its \
         spelling"
    );
    // §9's config-time layer on the user's configuration, as every engine.
    crate::conformance::assert_config_in_scope(&cc.config, "complete-first-p");

    // One instant: the outer run's wall and the first-report clock (I4's
    // ruling 6, carried over).
    let started = Instant::now();
    let cancel = Arc::new(CancelToken::new());
    let shared = Arc::new(Shared {
        cache: SharedCache::new(cc.witness_cache),
        acc: Mutex::new(Acc {
            seen: cc.impl_distinct.then(SetIndex::new),
            // Gate 3, D-2: the merged report set counts multiplicities, as
            // the workers' sets do (`absorb_by_move` sums them only into a
            // counting set).
            uncovered: SetIndex::with_multiplicities(),
            ..Acc::default()
        }),
        first: Mutex::new(FirstReport::default()),
        reports: Mutex::new(Vec::new()),
        abort: Mutex::new(None),
        cancel: Arc::clone(&cancel),
        started,
        root_claimed: std::sync::atomic::AtomicBool::new(false),
    });
    // The engine's own copy of the configuration carries the runner's knobs;
    // the public `ConfConfig` never does.
    let mut config: Config = cc.config.clone();
    config.partitioned_parallelization = true;
    config.partitioned_num_threads = Some(cc.threads);
    let visible = cc.visible.clone();
    let impl_distinct = cc.impl_distinct;
    let paper_events = cc.paper_events;
    let stop_at_first_report = cc.stop_at_first_report;
    let all_reports = cc.all_reports;
    let sweep_record = cc.sweep_record;
    let quiet = cc.quiet_sweeps;

    let on_must: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let config = config.clone();
        let visible = visible.clone();
        let shared = Arc::clone(&shared);
        let specification = Arc::clone(specification);
        Arc::new(move |must: &mut Must| {
            let root = !shared
                .root_claimed
                .swap(true, std::sync::atomic::Ordering::SeqCst);
            init_worker(impl_distinct, root);
            let mut ctx = ConfCtx::gate_disabled(
                config.clone(),
                visible.clone(),
                ConfMode::CFirstOuterPartitioned,
            );
            ctx.set_paper_events(paper_events);
            let sink = sink_for(
                Arc::clone(&shared),
                config.clone(),
                visible.clone(),
                Arc::clone(&specification),
                stop_at_first_report,
                all_reports,
                sweep_record,
                quiet,
            );
            ctx.set_sink(sink);
            must.enable_conformance_partitioned(ctx);
        })
    };
    let on_task_end: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let shared = Arc::clone(&shared);
        Arc::new(move |must: &mut Must| {
            let (execs, max_paper, new_diags, tally, uncovered, seen, syncs, sig_tests) = WORKER
                .with(|w| {
                    let mut w = w.borrow_mut();
                    let w = w
                        .as_mut()
                        .expect("conformance: complete-first-p's worker is set at task end");
                    let uncovered =
                        std::mem::replace(&mut w.uncovered, SetIndex::with_multiplicities());
                    let seen = w
                        .seen
                        .as_mut()
                        .map(|s| std::mem::replace(s, SetIndex::new()));
                    let ctx = must
                        .conf_ctx()
                        .expect("conformance: complete-first-p's task context is set");
                    let execs = ctx.counters().executions;
                    let diags = ctx.diagnostics();
                    let (fe, fd) = w.flushed;
                    w.flushed = (execs, diags.len());
                    let syncs = std::mem::take(&mut w.table.syncs);
                    let sig_tests = std::mem::take(&mut w.table.sig_tests);
                    (
                        execs - fe,
                        ctx.counters().max_paper_events_per_execution,
                        diags[fd..].to_vec(),
                        std::mem::take(&mut w.tally),
                        uncovered,
                        seen,
                        syncs,
                        sig_tests,
                    )
                });
            let mut a = shared
                .acc
                .lock()
                .expect("conformance: complete-first-p's accumulator");
            a.executions += execs;
            a.max_paper = a.max_paper.max(max_paper);
            a.diagnostics.extend(new_diags);
            a.add(tally);
            a.uncovered.absorb_by_move(uncovered);
            if let (Some(merged), Some(set)) = (a.seen.as_mut(), seen) {
                merged.absorb_by_move(set);
            }
            a.syncs += syncs;
            a.sig_tests += sig_tests;
            a.flushes += 1;
        })
    };
    let hooks = PartitionHooks {
        on_must,
        on_task_end,
        cancel: Arc::clone(&cancel),
    };
    let program = Arc::clone(implementation);
    let run = verify_partitioned_rayon_with(config, move || program(), hooks);
    let outer_wall_ms = started.elapsed().as_millis();

    // The run's state, taken under its locks (the pool's threads drop their
    // cached `Must`s on their own time).
    let a = std::mem::take(
        &mut *shared
            .acc
            .lock()
            .expect("conformance: complete-first-p's accumulator"),
    );
    let first = std::mem::take(&mut *shared.first.lock().expect("conformance: the first report"));
    let reports = std::mem::take(&mut *shared.reports.lock().expect("conformance: the reports"));
    let abort = shared
        .abort
        .lock()
        .expect("conformance: the abort record")
        .take();
    let stopped = cancel.is_cancelled();
    let cs = shared.cache.stats();
    let t = &a.tally;
    let uncovered: Vec<(Sig, OrdCounts, usize)> = a
        .uncovered
        .entries_counted()
        .map(|(_h, _id, sig, _seq, ord, count)| (sig.clone(), ord.clone(), count as usize))
        .collect();
    let uncovered_multiplicity: usize = uncovered.iter().map(|(_, _, m)| *m).sum();
    debug_assert_eq!(
        uncovered_multiplicity, t.reports,
        "conformance: complete-first-p's uncovered multiplicities sum to its reports"
    );
    let base = CFirstCounters {
        impl_graphs: t.impl_graphs,
        cache_probes: t.cache_probes,
        cache_hits: t.cache_hits,
        cache_tests: t.query.containment_tests,
        sweeps: t.sweeps,
        sweeps_successful: t.sweeps_successful,
        sweeps_failing: t.sweeps_failing,
        sweeps_aborted: t.sweeps_aborted,
        sweep_sizes: t.sweep_sizes.clone(),
        sweep_graphs: t.sweep_graphs,
        sweep_graphs_max: t.sweep_graphs_max,
        witnesses: cs.entries,
        witness_duplicates: 0,
        reports: t.reports,
        cut_reports: 0,
        precheck_ran: false,
        precheck_wall_time_ms: 0,
        outer_wall_time_ms: outer_wall_ms,
        sweep_wall_time_ms: t.sweep_time.as_millis(),
        invisible_ops_of_visible_threads: None,
        admissions: cs.admissions,
        evictions: cs.evictions,
        readmissions: cs.readmissions,
        wall_ms_at_first_report: first.wall_ms,
        vmhwm_kb_at_first_report: first.vmhwm_kb,
        ..CFirstCounters::default()
    };
    let counters = CFirstPCounters {
        base,
        threads: cc.threads,
        tasks: run.tasks_spawned + 1,
        tasks_nonempty: run.workers_reported,
        flushes: a.flushes,
        impl_distinct_summaries: a.seen.as_ref().map(SetIndex::len),
        cache_signatures: cs.signatures,
        cache_summary_bytes: cs.summary_bytes,
        redundant_sweeps: cs.redundant_sweeps,
        unadmitted_after_cancel: cs.unadmitted_after_cancel,
        unprobed_after_cancel: t.unprobed_after_cancel,
        sweeps_in_warmup: t.sweeps_in_warmup,
        sweeps_in_root_loop: t.sweeps_in_root_loop,
        sweeps_in_tasks: t.sweeps_in_tasks,
        sweeps_abandoned: t.sweeps_abandoned,
        watch_probes: t.watch_probes,
        signature_syncs: a.syncs,
        sig_tests: a.sig_tests,
        exact_hits: t.query.exact_hits,
        coordinates_compared: t.query.coordinates_compared,
        admission_lock_held_ms: cs.admission_lock_held_ms,
        admission_lock_wait_ms: cs.admission_lock_wait_ms,
        stopped_early: stopped,
        spawned_at_stop: first.spawned_at_stop.unwrap_or(0),
        uncovered_distinct: uncovered.len(),
        uncovered_multiplicity,
        uncovered: uncovered
            .iter()
            .map(|(sig, ord, multiplicity)| UncoveredSummary {
                signature: format!("{sig:?}"),
                counts: format!("{ord:?}"),
                multiplicity: *multiplicity,
            })
            .collect(),
    };
    CFirstPOutcome {
        counters,
        reports,
        uncovered,
        impl_end: if stopped {
            SearchEnd::StoppedAtFirstReport
        } else {
            SearchEnd::StateSpaceExhausted
        },
        spec_errors: abort.clone().unwrap_or_default(),
        impl_notes: a.diagnostics,
        executions: a.executions,
        impl_complete: run.stats.execs,
        impl_blocked: run.stats.block,
        max_paper_events: cc.paper_events.then_some(a.max_paper),
        aborted: abort.is_some(),
        #[cfg(test)]
        final_cache: (shared.cache.signatures(), shared.cache.entries()),
    }
}

/// The worker's completion sink (PS-3).
#[allow(clippy::too_many_arguments)]
fn sink_for(
    shared: Arc<Shared>,
    config: Config,
    visible: Vec<String>,
    specification: Arc<dyn Fn() + Send + Sync>,
    stop_at_first_report: bool,
    all_reports: bool,
    sweep_record: bool,
    quiet: bool,
) -> CompletionSink {
    Box::new(move |g: &ExecutionGraph, must_state: &MustState| {
        #[cfg(test)]
        SINK_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        // Ruling 13: the token first; a completion after the cancel is
        // counted, not probed.
        if shared.cancel.is_cancelled() {
            WORKER.with(|w| {
                let mut w = w.borrow_mut();
                let w = w
                    .as_mut()
                    .expect("conformance: complete-first-p's worker is set");
                w.tally.impl_graphs += 1;
                w.tally.unprobed_after_cancel += 1;
            });
            return SinkVerdict::Stop;
        }
        let cs = CompactSummary::at_completion(g, &visible, "implementation");
        // The probe (ruling 2), on the worker's own table and the shared store.
        let hit = WORKER.with(|w| {
            let mut w = w.borrow_mut();
            let w = w
                .as_mut()
                .expect("conformance: complete-first-p's worker is set");
            w.tally.impl_graphs += 1;
            if let Some(seen) = w.seen.as_mut() {
                seen.insert(&cs);
            }
            w.tally.cache_probes += 1;
            let (p, q) = shared.cache.probe(&mut w.table, &cs);
            w.tally.query.exact_hits += q.exact_hits;
            w.tally.query.containment_tests += q.containment_tests;
            w.tally.query.coordinates_compared += q.coordinates_compared;
            if p == CacheProbe::Hit {
                w.tally.cache_hits += 1;
            }
            p == CacheProbe::Hit
        });
        if hit {
            return SinkVerdict::Continue;
        }
        // The sweep, inline on this worker (ruling 3): the outer `Must` saved,
        // the sweep's run caught, the outer `Must` restored, a panic cancels
        // the token (ruling 12) and is re-raised as the runner re-raises a
        // task's.
        let sweep_started = Instant::now();
        let saved = Must::current();
        // Ruling 21: the watch — re-probe only when the cache's admission
        // counter moved since the sweep began (or since the last re-probe).
        let watch: Box<dyn FnMut() -> bool> = {
            let shared = Arc::clone(&shared);
            let cs = cs.clone();
            let mut seen = shared.cache.admission_version();
            Box::new(move || {
                // The one read of the counter per specification completion
                // (gate 4 round 03, m1); the common case borrows nothing.
                let current = shared.cache.admission_version();
                if current == seen {
                    return false;
                }
                WORKER.with(|w| {
                    let mut w = w.borrow_mut();
                    let w = w
                        .as_mut()
                        .expect("conformance: complete-first-p's worker is set");
                    match shared.cache.watch(&mut w.table, &cs, &mut seen, current) {
                        Watch::NotMoved => false,
                        Watch::Covered => {
                            w.tally.watch_probes += 1;
                            true
                        }
                        Watch::NotCovered => {
                            w.tally.watch_probes += 1;
                            false
                        }
                    }
                })
            })
        };
        let swept = catch_unwind(AssertUnwindSafe(|| {
            sweep_inline(
                &config,
                &visible,
                &specification,
                cs.clone(),
                quiet,
                Some(watch),
            )
        }));
        Must::set_current(saved.clone());
        #[cfg(test)]
        {
            let restored = match (Must::current(), saved.as_ref()) {
                (Some(a), Some(b)) => Rc::ptr_eq(&a, b),
                (None, None) => true,
                _ => false,
            };
            if !restored {
                CURRENT_MUST_MISMATCHES.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
        }
        let (swept, abandoned) = match swept {
            Ok(s) => s,
            Err(payload) => {
                // Every cancel under the cache's admission lock (gate 4 M1).
                shared.cache.under_admission(|| shared.cancel.cancel());
                resume_unwind(payload);
            }
        };
        let sweep_time = sweep_started.elapsed();
        #[cfg(test)]
        crate::conformance::compact::gate_wait(&ADMISSION_GATE);
        // Ruling 21: an abandoned sweep stopped without a witness; `classify`
        // has no row for it, so it is handled apart.
        let end = (!abandoned).then(|| classify(&swept, false));
        WORKER.with(|w| {
            let mut w = w.borrow_mut();
            let w = w
                .as_mut()
                .expect("conformance: complete-first-p's worker is set");
            w.tally.sweeps += 1;
            // PS-7: the root's first `warmup` completions are the warmup.
            if !w.root {
                w.tally.sweeps_in_tasks += 1;
            } else if w.tally.impl_graphs <= config.warmup {
                w.tally.sweeps_in_warmup += 1;
            } else {
                w.tally.sweeps_in_root_loop += 1;
            }
            if sweep_record {
                w.tally.sweep_sizes.push(swept.tested);
            }
            w.tally.sweep_graphs += swept.tested;
            w.tally.sweep_graphs_max = w.tally.sweep_graphs_max.max(swept.tested);
            w.tally.sweep_time += sweep_time;
            match end {
                None => {
                    // Ruling 21: covered by a held witness; nothing admitted
                    // or reported. D9: only a sweep that would have succeeded
                    // can be abandoned, so it carries no specification error.
                    debug_assert!(
                        swept.run.visible_errors.is_empty()
                            && !swept
                                .run
                                .diagnostics
                                .iter()
                                .any(|d| d.reason == DiagnosticReason::InvisibleThread),
                        "conformance: an abandoned sweep carries no specification error \
                         (SVERIFY-P ruling 21)"
                    );
                    w.tally.sweeps_abandoned += 1;
                    SinkVerdict::Continue
                }
                Some(SweepEnd::Aborted) => {
                    // Ruling 5: the first abort's errors, the token cancelled.
                    w.tally.sweeps_aborted += 1;
                    let mut abort = shared.abort.lock().expect("conformance: the abort record");
                    if abort.is_none() {
                        *abort = Some(spec_errors_of(&swept.run));
                        let spawned = shared.cache.under_admission(|| shared.cancel.cancel());
                        let mut first = shared.first.lock().expect("conformance: the first report");
                        first.spawned_at_stop.get_or_insert(spawned);
                    }
                    SinkVerdict::Stop
                }
                Some(SweepEnd::Witness) => {
                    w.tally.sweeps_successful += 1;
                    let ws = swept
                        .witness_summary
                        .as_ref()
                        .expect("conformance: a compact sweep stores its witness summary");
                    let probed = swept
                        .query
                        .as_ref()
                        .expect("conformance: a compact probe preceded the sweep");
                    // The live token, read inside the admission lock (gate 4 M1).
                    let admission = shared
                        .cache
                        .admit(&mut w.table, ws, probed, || shared.cancel.is_cancelled());
                    if admission == Admission::UnadmittedAfterCancel {
                        SinkVerdict::Stop
                    } else {
                        SinkVerdict::Continue
                    }
                }
                Some(SweepEnd::Exhausted) => {
                    w.tally.sweeps_failing += 1;
                    w.tally.reports += 1;
                    w.uncovered.insert(&cs);
                    // `MIN-ENGINES` E9, once across the workers, and the stop
                    // path (I3-6) and the kept graph (E6) under the same lock.
                    let mut first = shared.first.lock().expect("conformance: the first report");
                    if first.wall_ms.is_none() {
                        let fr: &mut FirstReport = &mut first;
                        note_first_report(&mut fr.wall_ms, &mut fr.vmhwm_kb, shared.started);
                        #[cfg(test)]
                        FIRST_REPORT_READS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        if stop_at_first_report {
                            let spawned = shared.cache.under_admission(|| shared.cancel.cancel());
                            fr.spawned_at_stop.get_or_insert(spawned);
                        }
                    }
                    if all_reports || !first.kept_one {
                        first.kept_one = true;
                        let snapshot = replay_snapshot(g, must_state, &config, None);
                        shared
                            .reports
                            .lock()
                            .expect("conformance: the reports")
                            .push((g.clone(), snapshot));
                    }
                    if stop_at_first_report || shared.cancel.is_cancelled() {
                        SinkVerdict::Stop
                    } else {
                        SinkVerdict::Continue
                    }
                }
                Some(SweepEnd::Budgeted) => unreachable!(
                    "conformance: an unlimited sweep of the specification ended Budgeted"
                ),
            }
        })
    }) as CompletionSink
}

/// The public entry (PS-1): the refusals as `KnobConflict`s, the sequential
/// precheck (ruling 10), `run_with`, then the verdict as the sequential
/// engine builds it (reports in no particular order; `report_count` the
/// total).
pub(crate) fn run(
    cc: ConfConfig,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
) -> Result<ConfVerdict, ConfError> {
    let started = Instant::now();
    if cc.threads == 0 {
        return Err(ConfError::KnobConflict {
            knob: "threads(0)",
            conflicts_with: "engine(CFirstP)",
        });
    }
    if cc.config.max_iterations.is_some() {
        return Err(ConfError::KnobConflict {
            knob: "max_iterations(Some(_))",
            conflicts_with: "engine(CFirstP)",
        });
    }
    if cc.config.parallel {
        return Err(ConfError::KnobConflict {
            knob: "parallel(true)",
            conflicts_with: "engine(CFirstP)",
        });
    }
    if cc.completion_cover == CompletionCover::Flat {
        return Err(ConfError::KnobConflict {
            knob: "completion_cover(Flat)",
            conflicts_with: "engine(CFirstP)",
        });
    }
    if cc.early_error_cut {
        return Err(ConfError::KnobConflict {
            knob: "early_error_cut(true)",
            conflicts_with: "engine(CFirstP)",
        });
    }
    if cc.witness_cache == Capacity::Bounded(0) {
        return Err(ConfError::KnobConflict {
            knob: "witness_cache(Bounded(0))",
            conflicts_with: "Capacity::Zero, which is its spelling",
        });
    }
    // §5.4, unbounded, sequential (ruling 10), as `cfirst::run`.
    let (spec_errfree, precheck_ran, precheck_wall_time_ms) = if cc.skip_spec_errfree_check {
        (SpecErrFreedom::Assumed, false, 0)
    } else {
        let precheck_started = Instant::now();
        let mut unbounded = cc.clone();
        unbounded.config.max_iterations = None;
        let _ = precheck::run(&unbounded, &specification)?;
        (
            SpecErrFreedom::Checked,
            true,
            precheck_started.elapsed().as_millis(),
        )
    };
    let mut out = run_with(&cc, &implementation, &specification);
    out.counters.base.precheck_ran = precheck_ran;
    out.counters.base.precheck_wall_time_ms = precheck_wall_time_ms;

    if let Some((thread, pos, visible)) = out.spec_errors.first() {
        let nth = out.counters.base.impl_graphs;
        let detail = if *visible {
            format!(
                "The visible thread `{thread}` failed an assertion at {pos} during a \
                 complete-first sweep of the specification (a sweep of the parallel engine, \
                 after {nth} complete implementation graphs)."
            )
        } else {
            format!(
                "The invisible thread `{thread}` failed an assertion at {pos} during a \
                 complete-first sweep of the specification (a sweep of the parallel engine, \
                 after {nth} complete implementation graphs). It is not a declared visible \
                 thread, which changes what a *report* would mean but not whether the \
                 specification is error-free."
            )
        };
        return Err(ConfError::SpecNotErrorFree { detail });
    }

    let reports = out
        .reports
        .into_iter()
        .map(|(graph, replay)| {
            let events = label_count(&graph);
            build_report_for(
                Engine::CFirstP,
                &ReportKind::NoCover,
                Some(Gate::Completion),
                events,
                &graph,
                replay,
                Diagnostics::NotProduced {
                    by: Engine::CFirstP,
                },
            )
        })
        .collect();
    let notes = out
        .impl_notes
        .iter()
        .map(|d| ConfNote::of(d.reason, d.thread.clone(), d.pos.to_string()))
        .collect();
    let report_count = out.counters.base.reports;
    let base = out.counters.base.clone();
    let counters = ConfCounters {
        executions: out.executions,
        max_paper_events_per_execution: out.max_paper_events.unwrap_or(0),
        wall_time_ms: started.elapsed().as_millis(),
        cfirst_p: Some(out.counters),
        ..ConfCounters::default()
    };
    Ok(ConfVerdict::of(ConfOutcome {
        report_count,
        reports,
        exhaustions: Vec::new(),
        notes,
        end: out.impl_end,
        spec_errfree,
        budget: cc.search_budget,
        triage_enabled: cc.triage,
        seed: cc.config.seed,
        counters,
        engine: Engine::CFirstP,
        stateful_counters: None,
        cfirst_counters: Some(base),
        gated_counters: None,
        flat_counters: None,
        flat_eligibility: None,
    }))
}
