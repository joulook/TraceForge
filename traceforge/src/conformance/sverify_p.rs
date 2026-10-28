//! `SVERIFY-P` I3: SVerify-P, the partitioned stateful refinement check on
//! the minimal core — the parallel form of SVerify-S (`stateful.rs`), as
//! `MESSAGE-parallel.md` row I3 orders it and `criteria/SVERIFY-P-I3.md`
//! (revision 2.3) specifies it.
//!
//! **The specification phase.** The specification is explored in Must's
//! partitioned mode (`parallel_verify::verify_partitioned_rayon_with`) with a
//! completion sink in every worker `Must`, whose context runs the twin mode
//! `ConfMode::EnumeratePartitioned` (plain-scheduled, `MIN-ENGINES` E1–E3).
//! Each completion's `CompactSummary` goes into the worker's own `SetIndex`;
//! when that set holds `flush_entries` orders, and at every task's end, it is
//! **moved** into the one merged index (`SetIndex::absorb_by_move`, under a
//! single lock). No queue of task sets and no second copy of the side exists
//! at any moment (I3-4). After the phase the merged index is **frozen by
//! move** (`SetIndex::freeze`) into a signature table, cloned per worker
//! because `Sig` is `Send` but not `Sync`, and a shared read-only order store
//! (I3-5).
//!
//! **The implementation phase** streams its queries (the owner's ruling (B)):
//! each worker resolves every completion's signature in its own table and
//! probes the shared store at that completion, as the sequential engine does
//! at its sink. Only the uncovered summaries are kept, in a counting set
//! flushed by move like the specification's. The first uncovered completion
//! seen by any worker takes the `MIN-ENGINES` E9 reads once, under a lock,
//! and with `stop_at_first_report` on also cancels the runner's token (I3-3):
//! every sink then returns `Stop`, every worker stops at its next poll, and no
//! further task is admitted.
//!
//! The phases end when the runner returns: it re-raises any task's or the
//! root's panic after cleanup, so a returned run is a completed one; the ends
//! are the engine's — `StoppedAtFirstReport` iff the token was cancelled,
//! else `StateSpaceExhausted` — and no context's `end()` is consulted (it is
//! first-writer-wins and the runner's chunk caps write `MaxIterations`).
//!
//! `threads`, `flush_entries` and the runner's `iterations_until_split` are
//! parameters; nothing here reads the machine.

use std::cell::RefCell;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::conformance::cfirst::note_first_report;
use crate::conformance::compact::{
    CompactSummary, Covers, OrdCounts, OrderStore, QueryCounts, SetIndex, SetStats, SigLookup,
    SigTable,
};
use crate::conformance::config::{ConfConfig, Engine};
use crate::conformance::ctx::{ConfCtx, ConfMode, Diagnostic, DiagnosticReason, SinkVerdict};
use crate::conformance::report::{
    ConfCounters, ConfError, ConfNote, ConfOutcome, ConfVerdict, SearchEnd, SpecErrFreedom,
    SverifyPCounters, UncoveredSummary,
};
use crate::conformance::sig::Sig;
use crate::event::Event;
use crate::must::Must;
use crate::parallel_verify::{verify_partitioned_rayon_with, CancelToken, PartitionHooks};
use crate::Config;

/// The engine-level result (I3-7): what the tester compares, beyond the
/// public verdict — the uncovered summaries as values, the counters, the
/// ends, the specification's errors.
pub(crate) struct SverifyPOutcome {
    pub(crate) counters: SverifyPCounters,
    /// The uncovered implementation summaries with their multiplicities, in
    /// the merged uncovered set's `entries_counted` order.
    pub(crate) uncovered: Vec<(Sig, OrdCounts, usize)>,
    pub(crate) spec_end: SearchEnd,
    pub(crate) impl_end: SearchEnd,
    /// The specification's assertion failures, canonically ordered (I3-4):
    /// by thread name, the position's rendering, then visibility.
    pub(crate) spec_errors: Vec<(String, Event, bool)>,
    pub(crate) impl_notes: Vec<Diagnostic>,
    /// The implementation side's completions (the contexts' `executions`,
    /// summed over the tasks).
    pub(crate) executions: usize,
    /// `Some` iff `paper_events` is on: the maximum over the workers.
    pub(crate) max_paper_events: Option<usize>,
}

/// I3-6 (e), test builds only: how many times the engine took the first-report
/// reads, process-wide (the sinks run on the pool's threads, so `cfirst.rs`'s
/// thread-local count is not readable from the caller's thread).
#[cfg(test)]
static FIRST_REPORT_READS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// I3-6 (e), test builds only: the engine's first-report reads so far.
#[cfg(test)]
pub(crate) fn first_report_reads_for_test() -> usize {
    FIRST_REPORT_READS.load(std::sync::atomic::Ordering::SeqCst)
}

/// I3-6 (e), test builds only: reset the count.
#[cfg(test)]
pub(crate) fn reset_first_report_reads_for_test() {
    FIRST_REPORT_READS.store(0, std::sync::atomic::Ordering::SeqCst);
}

/// I3-9, test builds only: the largest worker-set `entries` seen at a flush,
/// process-wide, and whether the merged index's `entries` ever decreased
/// between two flushes.
#[cfg(test)]
static FLUSH_MAX_ENTRIES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
static MERGED_DECREASED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// I3-9, test builds only: `(largest worker set at a flush, merged ever
/// decreased)` since the last reset.
#[cfg(test)]
pub(crate) fn flush_record_for_test() -> (usize, bool) {
    (
        FLUSH_MAX_ENTRIES.load(std::sync::atomic::Ordering::SeqCst),
        MERGED_DECREASED.load(std::sync::atomic::Ordering::SeqCst),
    )
}

/// I3-9, test builds only: reset the flush record.
#[cfg(test)]
pub(crate) fn reset_flush_record_for_test() {
    FLUSH_MAX_ENTRIES.store(0, std::sync::atomic::Ordering::SeqCst);
    MERGED_DECREASED.store(false, std::sync::atomic::Ordering::SeqCst);
}

/// I3-12 (i) and (iii), test builds only: the heap-buffer address of every
/// order a flush moved (read before the move) and of every order the frozen
/// store holds, process-wide. A flush that copies, or a freeze that clones,
/// gives the store addresses no flush recorded.
#[cfg(test)]
static ADDRESS_RECORD: Mutex<(Vec<usize>, Vec<usize>)> = Mutex::new((Vec::new(), Vec::new()));

/// I3-12 (i) and (iii), test builds only: `(flushed, frozen)` addresses since
/// the last reset.
#[cfg(test)]
pub(crate) fn address_record_for_test() -> (Vec<usize>, Vec<usize>) {
    ADDRESS_RECORD
        .lock()
        .expect("conformance: the address record")
        .clone()
}

/// I3-12 (i) and (iii), test builds only: reset the record.
#[cfg(test)]
pub(crate) fn reset_address_record_for_test() {
    *ADDRESS_RECORD
        .lock()
        .expect("conformance: the address record") = (Vec::new(), Vec::new());
}

/// The order's heap buffer (its identity through a move).
#[cfg(test)]
fn order_address(ord: &OrdCounts) -> usize {
    match ord {
        OrdCounts::U8(v) => v.as_ptr() as usize,
        OrdCounts::U16(v) => v.as_ptr() as usize,
    }
}

/// One worker's state for the phase its `Must` explores (I3-4, I3-6):
/// thread-local, initialised by `on_must` when the worker's `Must` is created
/// and kept across the tasks that `Must` serves on its pool thread; its set
/// is taken by every flush.
struct Worker {
    /// The worker set (the specification side) or the uncovered counting set
    /// (the implementation side), flushed by move at `flush_entries` and at
    /// task end.
    set: SetIndex,
    /// The implementation side's distinct-summary counting set, with
    /// `impl_distinct` on only; flushed like `set`.
    seen: Option<SetIndex>,
    /// The implementation side's per-worker clone of the signature table.
    table: Option<SigTable>,
    /// The context's accumulators already flushed from this thread —
    /// `executions`, the errors' length, the diagnostics' length — so that a
    /// flush pushes the task's own delta (the context keeps growing across
    /// the tasks a cached `Must` serves; `reset_for_reuse` keeps it).
    flushed: (usize, usize, usize),
    /// This thread's tallies, pushed into the phase's accumulator at task end.
    tally: Tally,
}

thread_local! {
    static WORKER: RefCell<Option<Worker>> = const { RefCell::new(None) };
}

/// What a thread tallies between two task ends: the flushes it made and the
/// implementation side's per-completion counters.
#[derive(Default)]
struct Tally {
    flushes: usize,
    flush_entries: usize,
    worker_duplicates: usize,
    seen_flush_entries: usize,
    seen_worker_duplicates: usize,
    lock_wait: Duration,
    lock_held: Duration,
    lookups: usize,
    signature_miss: usize,
    containment_tested: usize,
    succeeded: usize,
    failed_after_tests: usize,
    sig_tests: usize,
    query: QueryCounts,
    reports: usize,
}

/// One phase's accumulation across its tasks, behind one `Mutex` taken at
/// task end (the merged index has its own lock, taken at every flush).
#[derive(Default)]
struct PhaseAcc {
    complete: usize,
    blocked: usize,
    graphs: usize,
    max_paper: usize,
    errors: Vec<(String, Event)>,
    diagnostics: Vec<Diagnostic>,
    tally: Tally,
}

impl PhaseAcc {
    fn add(&mut self, t: Tally) {
        let a = &mut self.tally;
        a.flushes += t.flushes;
        a.flush_entries += t.flush_entries;
        a.worker_duplicates += t.worker_duplicates;
        a.seen_flush_entries += t.seen_flush_entries;
        a.seen_worker_duplicates += t.seen_worker_duplicates;
        a.lock_wait += t.lock_wait;
        a.lock_held += t.lock_held;
        a.lookups += t.lookups;
        a.signature_miss += t.signature_miss;
        a.containment_tested += t.containment_tested;
        a.succeeded += t.succeeded;
        a.failed_after_tests += t.failed_after_tests;
        a.sig_tests += t.sig_tests;
        a.query.exact_hits += t.query.exact_hits;
        a.query.containment_tests += t.query.containment_tests;
        a.query.coordinates_compared += t.query.coordinates_compared;
        a.reports += t.reports;
    }
}

/// The first report's record (I3-6, `MIN-ENGINES` E9), written once under
/// its lock by whichever worker sees the first uncovered completion; the lock
/// is the once-guard.
#[derive(Default)]
struct FirstReport {
    wall_ms: Option<u128>,
    vmhwm_kb: Option<u64>,
    /// The token's admitted count when the stop was cancelled (I3-8
    /// `spawned_at_stop`); `None` with the knob off or no report.
    spawned_at_stop: Option<u64>,
}

/// What one phase shares across its workers.
struct Shared {
    merged: Mutex<SetIndex>,
    /// The implementation side's merged distinct-summary set (`impl_distinct`).
    seen: Option<Mutex<SetIndex>>,
    acc: Mutex<PhaseAcc>,
    /// The implementation side only.
    frozen: Option<Frozen>,
}

/// The frozen specification index (I3-5), as the implementation phase holds
/// it: the table behind a lock (it is `Send`, not `Sync`), cloned per worker;
/// the store shared read-only.
struct Frozen {
    table: Mutex<SigTable>,
    store: Arc<OrderStore>,
    first: Mutex<FirstReport>,
    impl_started: Instant,
    stop_at_first_report: bool,
    cancel: Arc<CancelToken>,
}

/// One phase's result.
struct PhaseResult {
    merged: SetIndex,
    seen: Option<SetIndex>,
    tasks: usize,
    tasks_nonempty: usize,
    complete: usize,
    blocked: usize,
    graphs: usize,
    max_paper: usize,
    tally: Tally,
    errors: Vec<(String, Event)>,
    diagnostics: Vec<Diagnostic>,
    wall_ms: u128,
    first: FirstReport,
    stopped: bool,
}

fn fresh_set(counting: bool) -> SetIndex {
    if counting {
        SetIndex::with_multiplicities()
    } else {
        SetIndex::new()
    }
}

/// I3-4: the flush by move — the worker's set, taken whole, absorbed into the
/// merged index under its lock; the time waiting for the lock and the time
/// inside it are tallied, as are the set's `entries` and `duplicates` (the
/// conservation identities' terms).
fn flush_into(merged: &Mutex<SetIndex>, set: SetIndex, tally: &mut Tally, seen: bool) {
    let st = set.stats();
    if seen {
        tally.seen_flush_entries += st.entries;
        tally.seen_worker_duplicates += st.duplicates;
    } else {
        tally.flushes += 1;
        tally.flush_entries += st.entries;
        tally.worker_duplicates += st.duplicates;
    }
    #[cfg(test)]
    {
        if !seen {
            FLUSH_MAX_ENTRIES.fetch_max(st.entries, std::sync::atomic::Ordering::SeqCst);
            let mut r = ADDRESS_RECORD
                .lock()
                .expect("conformance: the address record");
            r.0.extend(set.entries().map(|(_, _, _, ord)| order_address(ord)));
        }
    }
    let waited = Instant::now();
    let mut m = merged
        .lock()
        .expect("conformance: sverify-p's merged index");
    let held = Instant::now();
    tally.lock_wait += held.duration_since(waited);
    #[cfg(test)]
    let before = m.len();
    m.absorb_by_move(set);
    #[cfg(test)]
    {
        if !seen && m.len() < before {
            MERGED_DECREASED.store(true, std::sync::atomic::Ordering::SeqCst);
        }
    }
    tally.lock_held += held.elapsed();
}

/// One side explored in the partitioned mode with the engine's hooks (I3-3,
/// I3-4, I3-6), its flushes merged as they come.
fn phase(
    cc: &ConfConfig,
    program: &Arc<dyn Fn() + Send + Sync>,
    side: &'static str,
    shared: Arc<Shared>,
    cancel: Arc<CancelToken>,
) -> PhaseResult {
    let started = Instant::now();
    // The engine's own copy of the configuration carries the runner's knobs;
    // the public `ConfConfig` never does (the builder refuses the flag).
    let mut config: Config = cc.config.clone();
    config.partitioned_parallelization = true;
    config.partitioned_num_threads = Some(cc.threads);
    let visible = cc.visible.clone();
    let flush_entries = cc.flush_entries;
    let counting = shared.frozen.is_some();
    let paper_events = counting && cc.paper_events;
    let impl_distinct = counting && cc.impl_distinct;

    let on_must: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let config = config.clone();
        let visible = visible.clone();
        let shared = Arc::clone(&shared);
        Arc::new(move |must: &mut Must| {
            let table = shared.frozen.as_ref().map(|f| {
                f.table
                    .lock()
                    .expect("conformance: sverify-p's signature table")
                    .clone()
            });
            WORKER.with(|w| {
                *w.borrow_mut() = Some(Worker {
                    set: fresh_set(counting),
                    seen: impl_distinct.then(|| fresh_set(true)),
                    table,
                    flushed: (0, 0, 0),
                    tally: Tally::default(),
                })
            });
            let mut ctx = ConfCtx::gate_disabled(
                config.clone(),
                visible.clone(),
                ConfMode::EnumeratePartitioned,
            );
            ctx.set_paper_events(paper_events);
            let visible = visible.clone();
            let shared = Arc::clone(&shared);
            ctx.set_sink(Box::new(move |g, _state| {
                // Every execution reaches the completion gate, blocked ones
                // included; `pruned` and `spec_error` are never set in an
                // enumerating mode (ctx.rs, the sink's call site).
                let Some(frozen) = shared.frozen.as_ref() else {
                    // The specification side (I3-4): insert, flush at F.
                    let s = CompactSummary::at_completion(g, &visible, side);
                    WORKER.with(|w| {
                        let mut w = w.borrow_mut();
                        let w = w.as_mut().expect("conformance: sverify-p's worker is set");
                        w.set.insert(&s);
                        if w.set.len() >= flush_entries {
                            let set = std::mem::replace(&mut w.set, fresh_set(false));
                            flush_into(&shared.merged, set, &mut w.tally, false);
                        }
                    });
                    return SinkVerdict::Continue;
                };
                // The implementation side (I3-6, (B)): the stop flag first.
                if frozen.stop_at_first_report && frozen.cancel.is_cancelled() {
                    return SinkVerdict::Stop;
                }
                let s = CompactSummary::at_completion(g, &visible, side);
                WORKER.with(|w| {
                    let mut w = w.borrow_mut();
                    let w = w.as_mut().expect("conformance: sverify-p's worker is set");
                    let table = w.table.as_ref().expect("conformance: sverify-p's table");
                    w.tally.lookups += 1;
                    let mut tests = 0;
                    let covered = match table.resolve(s.hash, &s.sig, &mut tests) {
                        SigLookup::NoBucket | SigLookup::NoSig => {
                            w.tally.signature_miss += 1;
                            false
                        }
                        SigLookup::Found(id) => {
                            let (c, q) = frozen.store.covers(id, &s.ord);
                            w.tally.query.exact_hits += q.exact_hits;
                            w.tally.query.containment_tests += q.containment_tests;
                            w.tally.query.coordinates_compared += q.coordinates_compared;
                            w.tally.containment_tested += 1;
                            match c {
                                Covers::Found(_) => {
                                    w.tally.succeeded += 1;
                                    true
                                }
                                Covers::NotFound | Covers::NoBucket | Covers::NoSig => {
                                    w.tally.failed_after_tests += 1;
                                    false
                                }
                            }
                        }
                    };
                    w.tally.sig_tests += tests;
                    if let Some(seen) = w.seen.as_mut() {
                        seen.insert(&s);
                        if seen.len() >= flush_entries {
                            let set = std::mem::replace(seen, fresh_set(true));
                            let m = shared.seen.as_ref().expect("conformance: the seen set");
                            flush_into(m, set, &mut w.tally, true);
                        }
                    }
                    if covered {
                        return SinkVerdict::Continue;
                    }
                    w.tally.reports += 1;
                    // `MIN-ENGINES` E9, once across the workers: the lock is
                    // the once-guard; a later report finds the wall set.
                    {
                        let mut fr = frozen.first.lock().expect("conformance: the first report");
                        let fr: &mut FirstReport = &mut fr;
                        if fr.wall_ms.is_none() {
                            note_first_report(
                                &mut fr.wall_ms,
                                &mut fr.vmhwm_kb,
                                frozen.impl_started,
                            );
                            #[cfg(test)]
                            FIRST_REPORT_READS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                            if frozen.stop_at_first_report {
                                fr.spawned_at_stop = Some(frozen.cancel.cancel());
                            }
                        }
                    }
                    w.set.insert(&s);
                    if w.set.len() >= flush_entries {
                        let set = std::mem::replace(&mut w.set, fresh_set(true));
                        flush_into(&shared.merged, set, &mut w.tally, false);
                    }
                    if frozen.stop_at_first_report {
                        SinkVerdict::Stop
                    } else {
                        SinkVerdict::Continue
                    }
                })
            }));
            must.enable_conformance_partitioned(ctx);
        })
    };
    let on_task_end: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let shared = Arc::clone(&shared);
        Arc::new(move |must: &mut Must| {
            let stats = must.stats();
            let (graphs, max_paper, new_errors, new_diags, tally) = WORKER.with(|w| {
                let mut w = w.borrow_mut();
                let w = w
                    .as_mut()
                    .expect("conformance: sverify-p's worker is set at task end");
                let set = std::mem::replace(&mut w.set, fresh_set(counting));
                flush_into(&shared.merged, set, &mut w.tally, false);
                if let Some(seen) = w.seen.as_mut() {
                    let set = std::mem::replace(seen, fresh_set(true));
                    let m = shared.seen.as_ref().expect("conformance: the seen set");
                    flush_into(m, set, &mut w.tally, true);
                }
                let ctx = must
                    .conf_ctx()
                    .expect("conformance: sverify-p's task context is set before its flush");
                let execs = ctx.counters().executions;
                let errors = ctx.collect_errors();
                let diags = ctx.diagnostics();
                let (fe, fr, fd) = w.flushed;
                w.flushed = (execs, errors.len(), diags.len());
                (
                    execs - fe,
                    ctx.counters().max_paper_events_per_execution,
                    errors[fr..].to_vec(),
                    diags[fd..].to_vec(),
                    std::mem::take(&mut w.tally),
                )
            });
            let mut a = shared
                .acc
                .lock()
                .expect("conformance: sverify-p's phase accumulator");
            a.complete += stats.execs;
            a.blocked += stats.block;
            a.graphs += graphs;
            a.max_paper = a.max_paper.max(max_paper);
            a.errors.extend(new_errors);
            a.diagnostics.extend(new_diags);
            a.add(tally);
        })
    };
    let hooks = PartitionHooks {
        on_must,
        on_task_end,
        cancel: Arc::clone(&cancel),
    };
    let program = Arc::clone(program);
    // Returns only when every task ran its queue to the end (or returned at
    // its poll after the cancel); a task's or the root's panic is re-raised by
    // the runner after its cleanup.
    let run = verify_partitioned_rayon_with(config, move || program(), hooks);
    let wall_ms = started.elapsed().as_millis();

    // The phase's state is taken out under its locks, not unwrapped: the
    // pool's threads drop their cached `Must`s (whose sinks hold the `Arc`)
    // after the runner returns, on their own time.
    let a = std::mem::take(
        &mut *shared
            .acc
            .lock()
            .expect("conformance: sverify-p's phase accumulator"),
    );
    let merged = std::mem::replace(
        &mut *shared
            .merged
            .lock()
            .expect("conformance: sverify-p's merged index"),
        SetIndex::new(),
    );
    let seen = shared.seen.as_ref().map(|m| {
        std::mem::replace(
            &mut *m.lock().expect("conformance: the seen set"),
            SetIndex::new(),
        )
    });
    let (first, stopped) = match shared.frozen.as_ref() {
        Some(f) => (
            std::mem::take(&mut *f.first.lock().expect("conformance: the first report")),
            f.cancel.is_cancelled(),
        ),
        None => (FirstReport::default(), false),
    };
    PhaseResult {
        merged,
        seen,
        tasks: run.tasks_spawned + 1,
        tasks_nonempty: run.workers_reported,
        complete: a.complete,
        blocked: a.blocked,
        graphs: a.graphs,
        max_paper: a.max_paper,
        tally: a.tally,
        errors: a.errors,
        diagnostics: a.diagnostics,
        wall_ms,
        first,
        stopped,
    }
}

/// The specification's errors as SVerify-S lists them (stateful.rs, the
/// index run's end): the visible assertion failures, then the invisible
/// threads' — canonically ordered (I3-4) so that the public detail names the
/// same first error on every run.
fn spec_errors_of(
    errors: Vec<(String, Event)>,
    diagnostics: &[Diagnostic],
) -> Vec<(String, Event, bool)> {
    let mut out: Vec<(String, Event, bool)> =
        errors.into_iter().map(|(t, p)| (t, p, true)).collect();
    out.extend(
        diagnostics
            .iter()
            .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
            .map(|d| (d.thread.clone(), d.pos, false)),
    );
    out.sort_by(|a, b| {
        (a.0.as_str(), a.1.to_string(), a.2).cmp(&(b.0.as_str(), b.1.to_string(), b.2))
    });
    out
}

/// The engine's run (I3-7): the refusals, the specification phase, the
/// freeze, the implementation phase. Every path reaches this entry (the
/// public `run` and the grid's call alike), so the refusals are here, before
/// any `Must` is created.
pub(crate) fn run_with(
    cc: &ConfConfig,
    implementation: &Arc<dyn Fn() + Send + Sync>,
    specification: &Arc<dyn Fn() + Send + Sync>,
) -> SverifyPOutcome {
    assert!(
        cc.threads >= 1,
        "conformance: sverify-p needs threads(t) with t >= 1; threads(0) is not a configuration \
         (SVERIFY-P I3-1)"
    );
    assert!(
        cc.flush_entries >= 1,
        "conformance: sverify-p needs flush_entries(f) with f >= 1; flush_entries(0) is not a \
         configuration (SVERIFY-P I3-1)"
    );
    assert!(
        cc.config.max_iterations.is_none(),
        "conformance: sverify-p refuses max_iterations: the partitioned runner's chunk cap is its \
         own, never the user's (SVERIFY-P ruling)"
    );
    assert!(
        !cc.config.parallel,
        "conformance: sverify-p refuses the shared-queue parallel mode; the partitioned mode is \
         its own (SVERIFY-P I3-2)"
    );
    // §9's config-time layer on the user's configuration, as every engine.
    crate::conformance::assert_config_in_scope(&cc.config, "sverify-p");

    // -- the specification phase (I3-4) ----------------------------------
    let spec_shared = Arc::new(Shared {
        merged: Mutex::new(SetIndex::new()),
        seen: None,
        acc: Mutex::new(PhaseAcc::default()),
        frozen: None,
    });
    let spec = phase(
        cc,
        specification,
        "specification",
        spec_shared,
        Arc::new(CancelToken::new()),
    );
    let spec_errors = spec_errors_of(spec.errors, &spec.diagnostics);
    let spec_set: SetStats = spec.merged.stats();
    let mut counters = SverifyPCounters {
        threads: cc.threads,
        flush_entries: cc.flush_entries,
        iterations_until_split: cc.config.iterations_until_split,
        spec_tasks: spec.tasks,
        spec_tasks_nonempty: spec.tasks_nonempty,
        spec_flushes: spec.tally.flushes,
        spec_complete: spec.complete,
        spec_blocked: spec.blocked,
        spec_graphs: spec.graphs,
        spec_wall_time_ms: spec.wall_ms,
        spec_merge_lock_held_ms: spec.tally.lock_held.as_millis(),
        spec_merge_lock_wait_ms: spec.tally.lock_wait.as_millis(),
        signatures: spec_set.signatures,
        buckets: spec_set.buckets,
        orders_held: spec_set.entries,
        spec_flush_entries: spec.tally.flush_entries,
        spec_worker_duplicates: spec.tally.worker_duplicates,
        spec_merge_duplicates: spec_set.duplicates,
        impl_distinct_summaries: cc.impl_distinct.then_some(0),
        spec_set,
        ..SverifyPCounters::default()
    };
    // One flush per task end, plus the flushes at F (gate 3, D1).
    debug_assert!(
        spec.tally.flushes >= spec.tasks,
        "conformance: sverify-p flushes at least once per task"
    );
    if !spec_errors.is_empty() {
        return SverifyPOutcome {
            counters,
            uncovered: Vec::new(),
            spec_end: SearchEnd::StateSpaceExhausted,
            impl_end: SearchEnd::Unknown,
            spec_errors,
            impl_notes: Vec::new(),
            executions: 0,
            max_paper_events: None,
        };
    }

    // -- the freeze (I3-5) -------------------------------------------------
    let freeze_started = Instant::now();
    let (table, store) = spec.merged.freeze();
    counters.freeze_wall_time_ms = freeze_started.elapsed().as_millis();
    #[cfg(test)]
    {
        let mut r = ADDRESS_RECORD
            .lock()
            .expect("conformance: the address record");
        r.1.extend(store.entries().map(|(_, _, ord)| order_address(ord)));
    }

    // -- the implementation phase (I3-6) -----------------------------------
    let cancel = Arc::new(CancelToken::new());
    let impl_shared = Arc::new(Shared {
        merged: Mutex::new(SetIndex::with_multiplicities()),
        seen: cc
            .impl_distinct
            .then(|| Mutex::new(SetIndex::with_multiplicities())),
        acc: Mutex::new(PhaseAcc::default()),
        frozen: Some(Frozen {
            table: Mutex::new(table),
            store: Arc::new(store),
            first: Mutex::new(FirstReport::default()),
            impl_started: Instant::now(),
            stop_at_first_report: cc.stop_at_first_report,
            cancel: Arc::clone(&cancel),
        }),
    });
    let imp = phase(cc, implementation, "implementation", impl_shared, cancel);
    let t = &imp.tally;
    counters.impl_tasks = imp.tasks;
    counters.impl_tasks_nonempty = imp.tasks_nonempty;
    counters.impl_flushes = t.flushes;
    counters.impl_complete = imp.complete;
    counters.impl_blocked = imp.blocked;
    counters.impl_graphs = imp.graphs;
    counters.impl_wall_time_ms = imp.wall_ms;
    counters.impl_merge_lock_held_ms = t.lock_held.as_millis();
    counters.impl_merge_lock_wait_ms = t.lock_wait.as_millis();
    counters.lookups = t.lookups;
    counters.lookups_signature_miss = t.signature_miss;
    counters.lookups_containment_tested = t.containment_tested;
    counters.lookups_succeeded = t.succeeded;
    counters.lookups_failed_after_tests = t.failed_after_tests;
    counters.sig_tests = t.sig_tests;
    counters.exact_hits = t.query.exact_hits;
    counters.containment_tests = t.query.containment_tests;
    counters.coordinates_compared = t.query.coordinates_compared;
    counters.reports = t.reports;
    counters.uncovered_flush_entries = t.flush_entries;
    counters.uncovered_worker_duplicates = t.worker_duplicates;
    let uncovered_set = imp.merged.stats();
    counters.uncovered_merge_duplicates = uncovered_set.duplicates;
    counters.uncovered_distinct = uncovered_set.entries;
    counters.uncovered_set = uncovered_set;
    if let Some(seen) = imp.seen.as_ref() {
        let st = seen.stats();
        counters.impl_distinct_summaries = Some(st.entries);
        counters.impl_seen_flush_entries = t.seen_flush_entries;
        counters.impl_seen_worker_duplicates = t.seen_worker_duplicates;
        counters.impl_set = Some(st);
    }
    counters.wall_ms_at_first_report = imp.first.wall_ms;
    counters.vmhwm_kb_at_first_report = imp.first.vmhwm_kb;
    counters.max_paper_events = cc.paper_events.then_some(imp.max_paper);
    counters.stopped_early = imp.stopped;
    counters.uncovered_at_stop = if imp.stopped {
        uncovered_set.entries
    } else {
        0
    };
    counters.spawned_at_stop = imp.first.spawned_at_stop.unwrap_or(0);
    let impl_end = if imp.stopped {
        SearchEnd::StoppedAtFirstReport
    } else {
        SearchEnd::StateSpaceExhausted
    };

    let uncovered: Vec<(Sig, OrdCounts, usize)> = imp
        .merged
        .entries_counted()
        .map(|(_h, _id, sig, _seq, ord, count)| (sig.clone(), ord.clone(), count as usize))
        .collect();
    counters.uncovered_multiplicity = uncovered.iter().map(|(_, _, m)| *m).sum();
    debug_assert_eq!(
        counters.uncovered_multiplicity, counters.reports,
        "conformance: sverify-p's uncovered multiplicities sum to its reports"
    );
    counters.uncovered = uncovered
        .iter()
        .map(|(sig, ord, multiplicity)| UncoveredSummary {
            signature: format!("{sig:?}"),
            counts: format!("{ord:?}"),
            multiplicity: *multiplicity,
        })
        .collect();

    SverifyPOutcome {
        counters,
        uncovered,
        spec_end: SearchEnd::StateSpaceExhausted,
        impl_end,
        spec_errors,
        impl_notes: imp.diagnostics,
        executions: imp.graphs,
        max_paper_events: cc.paper_events.then_some(imp.max_paper),
    }
}

/// The public entry (I3-7): the refusals as `KnobConflict`s in the F5 shape,
/// then `run_with`, then the verdict as SVerify-S builds it — with `reports`
/// empty, `report_count` the uncovered completions, and the uncovered
/// summaries in the engine's record (`ConfCounters::sverify_p`).
pub(crate) fn run(
    cc: ConfConfig,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
) -> Result<ConfVerdict, ConfError> {
    let started = Instant::now();
    if cc.threads == 0 {
        return Err(ConfError::KnobConflict {
            knob: "threads(0)",
            conflicts_with: "engine(SverifyP)",
        });
    }
    if cc.flush_entries == 0 {
        return Err(ConfError::KnobConflict {
            knob: "flush_entries(0)",
            conflicts_with: "engine(SverifyP)",
        });
    }
    if cc.config.max_iterations.is_some() {
        return Err(ConfError::KnobConflict {
            knob: "max_iterations(Some(_))",
            conflicts_with: "engine(SverifyP)",
        });
    }
    if cc.config.parallel {
        return Err(ConfError::KnobConflict {
            knob: "parallel(true)",
            conflicts_with: "engine(SverifyP)",
        });
    }
    let out = run_with(&cc, &implementation, &specification);

    if let Some((thread, pos, visible)) = out.spec_errors.first() {
        // The same text as the stateful engine's (stateful.rs, `run`), so the
        // two engines' refusals compare equal on a single-error fixture.
        let detail = if *visible {
            format!(
                "The visible thread `{thread}` failed an assertion at {pos} during the \
                 stateful engine's enumeration of the specification (its index run, which \
                 replaces the \u{a7}5.4 precheck)."
            )
        } else {
            format!(
                "The invisible thread `{thread}` failed an assertion at {pos} during the \
                 stateful engine's enumeration of the specification (its index run, which \
                 replaces the \u{a7}5.4 precheck). It is not a declared visible thread, which \
                 changes what a *report* would mean but not whether the specification is \
                 error-free."
            )
        };
        return Err(ConfError::SpecNotErrorFree { detail });
    }

    let notes = out
        .impl_notes
        .iter()
        .map(|d| ConfNote::of(d.reason, d.thread.clone(), d.pos.to_string()))
        .collect();
    let report_count = out.counters.uncovered_multiplicity;
    let counters = ConfCounters {
        executions: out.executions,
        max_paper_events_per_execution: out.max_paper_events.unwrap_or(0),
        wall_time_ms: started.elapsed().as_millis(),
        sverify_p: Some(out.counters),
        ..ConfCounters::default()
    };

    Ok(ConfVerdict::of(ConfOutcome {
        report_count,
        reports: Vec::new(),
        exhaustions: Vec::new(),
        notes,
        end: out.impl_end,
        spec_errfree: SpecErrFreedom::Checked,
        budget: cc.search_budget,
        triage_enabled: cc.triage,
        seed: cc.config.seed,
        counters,
        engine: Engine::SverifyP,
        stateful_counters: None,
        cfirst_counters: None,
        gated_counters: None,
        flat_counters: None,
        flat_eligibility: None,
    }))
}
