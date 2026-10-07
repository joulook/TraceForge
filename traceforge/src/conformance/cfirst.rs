//! `CVerify`, the complete-first checker (`alg.tex` §8.5; `P4-CFIRST`).
//!
//! > **CVerify(Impl, Spec).** `W ← ∅`; CVisit(`G_∅`).
//! > **CVisit(G).** Must's exploration of Impl, unchanged, with error events
//! > installed and continued (`lem:inert`); at `e = ⊥` (`ln:cfinal`): if
//! > ¬Covered(G) then report G.
//! > **Covered(G).** (`ln:ccache`) for `M ∈ W` if `cov(G,M)` return true;
//! > (`ln:csweep`) for `M ∈ Graphs(Spec)` — Must on Spec, unpruned —
//! > (`ln:cfound`) if `cov(G,M)` then `W ← W ∪ {M}`; return true; return
//! > false.
//!
//! > **thm:cfirst.** `alg:cfirst` reports exactly the uncovered members of
//! > `Graphs(Impl)`.
//!
//! **Shape (C1–C3).** The outer run is one enumerating run of Impl
//! ([`ConfMode::CFirstOuter`], the stateful checker's driver under its own
//! label) whose completion sink is `Covered`: the witness cache `W`
//! ([`WitnessCache`], Part 1) is probed first, and on a miss the specification
//! is swept — a nested enumerating run of Spec ([`ConfMode::CFirstSweep`]) on
//! its own OS thread, unpruned, stopped by its sink at the first covering
//! graph, which is then admitted to `W`. A failing sweep must end
//! `StateSpaceExhausted`, which the engine asserts: a sweep that ended any
//! other way would make "uncovered" unsound.
//!
//! **Why a thread per sweep (C2).** Isolation, not necessity: the sink runs
//! after the outer execution has returned, so no continuation is live and the
//! continuation pool would merely be shadowed, but `explore` installs the
//! running `Must` in `CURRENT_MUST` and never clears it, and the sweep's own
//! panics are cleanest to catch at a join. The handle is joined explicitly and
//! a panic payload is re-raised on the outer thread (`resume_unwind`), so §9
//! rejections and invalid-input panics arrive as themselves.
//!
//! **§5.4 (C4).** The sweeps are partial, so they do not replace the
//! precheck: [`run`] calls it first, **unbounded** (this engine's Spec side is
//! never bounded), unless skipped. A sweep that meets a specification
//! assertion failure aborts the run with [`ConfError::SpecNotErrorFree`]
//! whatever the flag says.
//!
//! **The early-error cut (C5, A27).** Off by default. When on, the outer run
//! prunes and reports a visible thread's failed assertion as a prefix, and
//! the engine *decides* but does not enumerate: a backward revisit from
//! inside the skipped subtree can reach an uncovered complete graph that is
//! neither listed nor certified. The rendering says so (C7).
//!
//! **Bounds.** `max_iterations` bounds the outer run only; the precheck and
//! every sweep run with `None`. `search_budget`, `inner_order`, `memo` and
//! `triage` do not apply.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

use crate::conformance::config::{CompletionCover, ConfConfig, Engine};
use crate::conformance::flat;
use crate::conformance::report::FlatCounters;
use crate::conformance::ctx::{
    CompletionSink, ConfMode, Diagnostic, DiagnosticReason, Gate, Report, ReportKind, SinkVerdict,
};
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{wobs, Wobs};
use crate::conformance::precheck;
use crate::conformance::report::{
    build_report_for, replay_snapshot, CFirstCounters, ConfCounters, ConfError, ConfNote,
    ConfOutcome, ConfReport, ConfVerdict, Diagnostics, ReplaySnapshot, SearchEnd, SpecErrFreedom,
};
use crate::conformance::sig::{cone_from, covered, Summary, VisOrder};
use crate::conformance::stateful::{enumerate, summarise, EnumRun, Enumerated};
use crate::conformance::witness::WitnessCache;
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;
use crate::must::MustState;
use crate::Config;

/// How one sweep ended (C3's decision table; criterion 11).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SweepEnd {
    /// Stopped at a covering graph, which was admitted to `W`.
    Witness,
    /// Enumerated all of `Graphs(Spec)` and found none: a report.
    Exhausted,
    /// Met a specification assertion failure: the run aborts.
    Aborted,
    /// `P4-GATED` G4: stopped by a `Budget(B)` limit with graphs left,
    /// having tested `B` and found none — no certificate, no report. Only a
    /// sweep given a limit can end this way.
    Budgeted,
}

/// `P4-GATED` G4: what a sweep tests each complete specification graph
/// against — Part 4's completion test, or the gate's `cone_from` on a
/// partial outer graph.
#[derive(Clone)]
pub(crate) enum SweepTest {
    Covered(Summary),
    Cone { wobs: Wobs, ord: VisOrder },
}

impl SweepTest {
    fn passes(&self, m: &Summary, m_wobs: &Wobs, visible: &[String]) -> bool {
        match self {
            SweepTest::Covered(outer) => covered(outer, m),
            SweepTest::Cone { wobs, ord } => {
                let _ = m_wobs;
                cone_from(wobs, ord, m, visible)
            }
        }
    }
}

/// C3's decision table, shared with the gated checker (`P4-GATED` G4):
/// errors first, whatever the end; a stored graph with a stop is a witness;
/// no graph and exhaustion is a failing sweep; under a limit, no graph and a
/// stop is `Budgeted`; anything else panics.
pub(crate) fn classify(swept: &Swept, limited: bool) -> SweepEnd {
    if !swept.run.visible_errors.is_empty()
        || swept
            .run
            .diagnostics
            .iter()
            .any(|d| d.reason == DiagnosticReason::InvisibleThread)
    {
        return SweepEnd::Aborted;
    }
    match (swept.witness.is_some(), swept.run.end, swept.budgeted) {
        (true, SearchEnd::StoppedAtFirstReport, false) => SweepEnd::Witness,
        (false, SearchEnd::StateSpaceExhausted, false) => SweepEnd::Exhausted,
        (false, SearchEnd::StoppedAtFirstReport, true) if limited => SweepEnd::Budgeted,
        (stored, end, _) => panic!(
            "conformance: a sweep of the specification ended {end:?} with{} a stored \
             witness; a failing sweep must end StateSpaceExhausted and a successful one \
             StoppedAtFirstReport",
            if stored { "" } else { "out" }
        ),
    }
}

/// The engine-only result (criterion 11).
pub(crate) struct CFirstOutcome {
    /// Completion reports, in completion order, each with the snapshot taken
    /// at the sink.
    pub(crate) reports: Vec<(ExecutionGraph, ReplaySnapshot)>,
    /// The outer context's own reports — the cut's `VisibleError` prefixes,
    /// in the order raised; empty with the cut off.
    pub(crate) cut_reports: Vec<Report>,
    pub(crate) counters: CFirstCounters,
    pub(crate) witnesses: WitnessCache,
    /// Every outer completion, in completion order; empty unless asked for.
    pub(crate) kept_impl_graphs: Vec<ExecutionGraph>,
    /// One `Vec` per sweep, in sweep order, each in completion order; empty
    /// unless asked for.
    pub(crate) kept_spec_graphs: Vec<Vec<ExecutionGraph>>,
    pub(crate) sweep_ends: Vec<SweepEnd>,
    /// A sweep aborted the run (C4).
    pub(crate) aborted: bool,
    /// The outer run's end. On an abort it is what the stop mechanism
    /// recorded: `StoppedAtFirstReport`, or `MaxIterations(n)` when the bound
    /// coincided on that completion (first writer wins).
    pub(crate) impl_end: SearchEnd,
    /// The aborting sweep's assertion failures, visible first; the `bool` is
    /// "visible".
    pub(crate) spec_errors: Vec<(String, Event, bool)>,
    /// Impl invisible-thread failures, which `run` turns into `ConfNote`s.
    pub(crate) impl_notes: Vec<Diagnostic>,
    /// Every outer execution, pruned ones included.
    pub(crate) executions: usize,
    pub(crate) max_paper_events: usize,
}

/// What the outer sink accumulates, shared with [`run_with`] through an
/// `Rc<RefCell<_>>` and drained with `std::mem::take` once the run is over
/// (`Rc::try_unwrap` would fail while `CURRENT_MUST` still holds the `Must`).
struct SinkState {
    witnesses: WitnessCache,
    counters: CFirstCounters,
    /// Summed as a `Duration` and converted once (truncating per sweep would
    /// undercount sub-millisecond sweeps).
    sweep_time: std::time::Duration,
    reports: Vec<(ExecutionGraph, ReplaySnapshot)>,
    kept_impl: Vec<ExecutionGraph>,
    kept_spec: Vec<Vec<ExecutionGraph>>,
    sweep_ends: Vec<SweepEnd>,
    spec_errors: Vec<(String, Event, bool)>,
    aborted: bool,
}

/// What one sweep hands back across its thread.
pub(crate) struct Swept {
    pub(crate) run: Enumerated,
    /// The covering graph, if the sink stopped on one.
    pub(crate) witness: Option<ExecutionGraph>,
    /// Complete Spec graphs tested.
    pub(crate) tested: usize,
    pub(crate) kept: Vec<ExecutionGraph>,
    /// `P4-GATED` G4: the sink stopped at completion `B + 1` without testing
    /// it (a limit was given and reached).
    pub(crate) budgeted: bool,
}

/// The public path: the (unbounded) precheck, then [`run_with`] with
/// `keep_graphs = false`, then the `ConfOutcome` (C4, C7).
pub(crate) fn run(
    cc: ConfConfig,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
) -> Result<ConfVerdict, ConfError> {
    let started = Instant::now();
    let flat = cc.completion_cover == CompletionCover::Flat;
    // `P4-FLAT` F5/D13: eligibility needs the precheck.
    if flat && cc.skip_spec_errfree_check {
        return Err(ConfError::KnobConflict {
            knob: "completion_cover(Flat)",
            conflicts_with: "skip_spec_errfree_check(true)",
        });
    }
    let mut eligibility = None;

    // -- §5.4, unbounded (C4) --------------------------------------------
    let (spec_errfree, precheck_ran, precheck_wall_time_ms) = if cc.skip_spec_errfree_check {
        (SpecErrFreedom::Assumed, false, 0)
    } else {
        let precheck_started = Instant::now();
        let mut unbounded = cc.clone();
        unbounded.config.max_iterations = None;
        eligibility = precheck::run(&unbounded, &specification)?;
        (
            SpecErrFreedom::Checked,
            true,
            precheck_started.elapsed().as_millis(),
        )
    };

    // `P4-FLAT` F5: an ineligible specification is refused, never swept.
    if let Some(e) = eligibility.as_ref() {
        if !e.communication_flat {
            let (thread, pos) = e.first_invisible.clone().unwrap_or_default();
            return Err(ConfError::SpecNotCommunicationFlat { thread, pos });
        }
    }
    let mut out = run_with(&cc, &implementation, &specification, false);
    out.counters.precheck_ran = precheck_ran;
    out.counters.precheck_wall_time_ms = precheck_wall_time_ms;

    // C4: a sweep met a specification assertion failure.
    if let Some((thread, pos, visible)) = out.spec_errors.first() {
        let nth = out.counters.impl_graphs;
        let detail = if *visible {
            format!(
                "The visible thread `{thread}` failed an assertion at {pos} during a \
                 complete-first sweep of the specification (the sweep for complete \
                 implementation graph number {nth})."
            )
        } else {
            format!(
                "The invisible thread `{thread}` failed an assertion at {pos} during a \
                 complete-first sweep of the specification (the sweep for complete \
                 implementation graph number {nth}). It is not a declared visible \
                 thread, which changes what a *report* would mean but not whether the \
                 specification is error-free."
            )
        };
        return Err(ConfError::SpecNotErrorFree { detail });
    }

    // C5: completion reports in completion order, then the cut's prefixes
    // in the order raised.
    let mut reports: Vec<ConfReport> = out
        .reports
        .into_iter()
        .map(|(graph, replay)| {
            let events = label_count(&graph);
            let mut r = build_report_for(
                Engine::CompleteFirst,
                &ReportKind::NoCover,
                Some(Gate::Completion),
                events,
                &graph,
                replay,
                Diagnostics::NotProduced {
                    by: Engine::CompleteFirst,
                },
            );
            // `P4-FLAT` criterion 8: every completion report of a `Flat` run.
            r.by_flat_cover = flat;
            r
        })
        .collect();
    reports.extend(out.cut_reports.into_iter().map(|r| {
        build_report_for(
            Engine::CompleteFirst,
            &r.kind,
            r.gate,
            r.events,
            &r.graph,
            r.replay,
            Diagnostics::NotApplicable,
        )
    }));
    let notes = out
        .impl_notes
        .iter()
        .map(|d| ConfNote::of(d.reason, d.thread.clone(), d.pos.to_string()))
        .collect();

    let counters = ConfCounters {
        executions: out.executions,
        max_paper_events_per_execution: out.max_paper_events,
        wall_time_ms: started.elapsed().as_millis(),
        invisible_ops_of_visible_threads: out.counters.invisible_ops_of_visible_threads,
        ..ConfCounters::default()
    };

    Ok(ConfVerdict::of(ConfOutcome {
        reports,
        exhaustions: Vec::new(),
        notes,
        end: out.impl_end,
        spec_errfree,
        budget: cc.search_budget,
        triage_enabled: cc.triage,
        seed: cc.config.seed,
        counters,
        engine: Engine::CompleteFirst,
        stateful_counters: None,
        flat_counters: out.counters.flat.clone(),
        flat_eligibility: eligibility,
        cfirst_counters: Some(out.counters),
        gated_counters: None,
    }))
}

/// `alg:cfirst` and nothing else (criterion 1): the outer run with `Covered`
/// at every completion. No precheck here — the engine-only path observes
/// sweep aborts directly (C4).
///
/// # Panics
///
/// On invalid input, as `verify` documents: a §9 scope rejection (naming
/// "complete-first" or "complete-first sweep"); a §8 violation (from
/// `summarise` or a witness admission, naming the program); if a sweep ends
/// in a way C3's decision table rules out; and if `W` refuses an admission as
/// already held, which the probe should have answered.
pub(crate) fn run_with(
    cc: &ConfConfig,
    implementation: &Arc<dyn Fn() + Send + Sync>,
    specification: &Arc<dyn Fn() + Send + Sync>,
    keep_graphs: bool,
) -> CFirstOutcome {
    // §9's config-time layer, before any engine exists.
    crate::conformance::assert_config_in_scope(&cc.config, "complete-first");
    let visible = cc.visible.clone();

    let state = Rc::new(RefCell::new(SinkState {
        witnesses: WitnessCache::new(visible.clone()),
        counters: CFirstCounters::default(),
        sweep_time: std::time::Duration::ZERO,
        reports: Vec::new(),
        kept_impl: Vec::new(),
        kept_spec: Vec::new(),
        sweep_ends: Vec::new(),
        spec_errors: Vec::new(),
        aborted: false,
    }));
    // `P4-FLAT` F6: `Some` whenever the knob is `Flat`, zero counts allowed.
    if cc.completion_cover == CompletionCover::Flat {
        state.borrow_mut().counters.flat = Some(FlatCounters::default());
    }

    let outer_started = Instant::now();
    let sink = {
        let state = Rc::clone(&state);
        let visible = visible.clone();
        let config = cc.config.clone();
        let specification = Arc::clone(specification);
        let stop_at_first_report = cc.stop_at_first_report;
        let flat_ctx = (cc.completion_cover == CompletionCover::Flat)
            .then(|| flat::FlatCtx::new(&config, &visible, &specification));
        Box::new(move |g: &ExecutionGraph, must_state: &MustState| {
            let summary = summarise(g, &visible, "implementation");
            {
                let mut st = state.borrow_mut();
                st.counters.impl_graphs += 1;
                // `P4-MIXED` M8, in the implementation completion sink.
                let inv = crate::conformance::ctx::invisible_ops_of_visible_threads(g, &visible);
                st.counters.invisible_ops_of_visible_threads =
                    st.counters.invisible_ops_of_visible_threads.max(inv);
                if keep_graphs {
                    st.kept_impl.push(g.clone());
                }
            }

            // ln:ccache — W first.
            let hit = {
                let mut st = state.borrow_mut();
                let (found, tests) = st.witnesses.probe_covered_counted(&summary);
                let hit = found.is_some();
                st.counters.cache_probes += 1;
                st.counters.cache_tests += tests;
                if hit {
                    st.counters.cache_hits += 1;
                }
                hit
            };
            if hit {
                return SinkVerdict::Continue;
            }
            if let Some(fctx) = flat_ctx.as_ref() {
                // `P4-FLAT` F4: the adapter — `FlatCover` in place of the
                // completion sweep, on its own thread; a witness is admitted
                // through `flat::admit`, which re-enters the cache's one mutating
                // method `admit_from_sweep` (`P4-APPARATUS` 15); ⊥ is the
                // uncovered completion.
                let flat_started = Instant::now();
                let (witness, delta) = flat::flat_cover(fctx, g).unwrap_or_else(|e| {
                    panic!("conformance: the specification program is not a valid input: {e}")
                });
                let mut st = state.borrow_mut();
                st.sweep_time += flat_started.elapsed();
                st.counters
                    .flat
                    .get_or_insert_with(FlatCounters::default)
                    .accumulate(&delta);
                return match witness {
                    Some(w) => {
                        debug_assert!(
                            covered(&summary, w.summary()),
                            "conformance: FlatCover returned a graph that does not cover its \
                             completion (thm:flat)"
                        );
                        let inserted = flat::admit(&mut st.witnesses, w).unwrap_or_else(|e| {
                            panic!("conformance: the specification program is not a valid input: {e}")
                        });
                        if !inserted {
                            st.counters.witness_duplicates += 1;
                        }
                        assert!(
                            inserted,
                            "conformance: the complete-first engine admitted a FlatCover witness W \
                             already holds; the cache probe should have hit"
                        );
                        st.counters.witnesses = st.witnesses.len();
                        SinkVerdict::Continue
                    }
                    None => {
                        st.counters.reports += 1;
                        let snapshot = replay_snapshot(g, must_state, &config, None);
                        st.reports.push((g.clone(), snapshot));
                        if stop_at_first_report {
                            SinkVerdict::Stop
                        } else {
                            SinkVerdict::Continue
                        }
                    }
                };
            }

            // ln:csweep — Must on Spec, unpruned, on its own thread (C2).
            let sweep_started = Instant::now();
            let swept = sweep(
                &config,
                &visible,
                &specification,
                SweepTest::Covered(summary.clone()),
                None,
                keep_graphs,
                ConfMode::CFirstSweep,
            );
            let mut st = state.borrow_mut();
            st.counters.sweeps += 1;
            st.counters.sweep_sizes.push(swept.tested);
            st.counters.sweep_graphs += swept.tested;
            st.counters.sweep_graphs_max = st.counters.sweep_graphs_max.max(swept.tested);
            st.sweep_time += sweep_started.elapsed();
            // C3's decision table: errors first, whatever the end.
            let end = classify(&swept, false);
            if keep_graphs {
                st.kept_spec.push(swept.kept.clone());
            }
            if end == SweepEnd::Aborted {
                st.counters.sweeps_aborted += 1;
                st.sweep_ends.push(SweepEnd::Aborted);
                st.spec_errors = spec_errors_of(&swept.run);
                st.aborted = true;
                return SinkVerdict::Stop;
            }
            match (swept.witness, end) {
                (Some(m), SweepEnd::Witness) => {
                    // ln:cfound — the stopping witness joins W. The graph is
                    // the sweep's completion-gate capture, one thread later,
                    // which is what `assume_finished_at_gate` asks for.
                    let exec = CompleteExecution::assume_finished_at_gate(&m);
                    let inserted = st.witnesses.admit_from_sweep(exec).unwrap_or_else(|e| {
                        panic!("conformance: the specification program is not a valid input: {e}")
                    });
                    if !inserted {
                        st.counters.witness_duplicates += 1;
                    }
                    assert!(
                        inserted,
                        "conformance: the complete-first engine admitted a witness W already \
                         holds; the cache probe should have hit"
                    );
                    st.counters.sweeps_successful += 1;
                    st.counters.witnesses = st.witnesses.len();
                    st.sweep_ends.push(SweepEnd::Witness);
                    SinkVerdict::Continue
                }
                (None, SweepEnd::Exhausted) => {
                    st.counters.sweeps_failing += 1;
                    st.sweep_ends.push(SweepEnd::Exhausted);
                    st.counters.reports += 1;
                    let snapshot = replay_snapshot(g, must_state, &config, None);
                    st.reports.push((g.clone(), snapshot));
                    if stop_at_first_report {
                        SinkVerdict::Stop
                    } else {
                        SinkVerdict::Continue
                    }
                }
                (stored, end) => unreachable!(
                    "conformance: `classify` returned {end:?} with{} a stored witness",
                    if stored.is_some() { "" } else { "out" }
                ),
            }
        }) as CompletionSink
    };

    let outer = enumerate(
        EnumRun {
            config: cc.config.clone(),
            visible,
            mode: ConfMode::CFirstOuter,
            sink,
            cut: cc.early_error_cut,
            stop_at_first_report: cc.stop_at_first_report,
            gate_sink: None,
        },
        implementation,
    );
    let mut st = std::mem::take(&mut *state.borrow_mut());
    // `outer_wall_time_ms` includes every sweep's time (the sweeps run inside
    // the outer run's completions).
    st.counters.outer_wall_time_ms = outer_started.elapsed().as_millis();
    st.counters.sweep_wall_time_ms = st.sweep_time.as_millis();
    st.counters.cut_reports = outer.reports.len();

    CFirstOutcome {
        reports: st.reports,
        cut_reports: outer.reports,
        counters: st.counters,
        witnesses: st.witnesses,
        kept_impl_graphs: st.kept_impl,
        kept_spec_graphs: st.kept_spec,
        sweep_ends: st.sweep_ends,
        aborted: st.aborted,
        impl_end: outer.end,
        spec_errors: st.spec_errors,
        // As the enumerator: every Impl diagnostic becomes a note (with the
        // cut on, `AfterPrune` entries arise and are kept).
        impl_notes: outer.diagnostics,
        executions: outer.executions,
        max_paper_events: outer.max_paper_events,
    }
}

impl Default for SinkState {
    fn default() -> Self {
        Self {
            witnesses: WitnessCache::new(Vec::new()),
            counters: CFirstCounters::default(),
            sweep_time: std::time::Duration::ZERO,
            reports: Vec::new(),
            kept_impl: Vec::new(),
            kept_spec: Vec::new(),
            sweep_ends: Vec::new(),
            spec_errors: Vec::new(),
            aborted: false,
        }
    }
}

/// One sweep (C2, C3): a nested enumerating run of Spec on a scoped thread
/// with `verify`'s stack size, unbounded, under the configured selector,
/// stopped by its sink at the first graph covering `outer`.
/// The errors an aborting sweep recorded, visible first (C4).
pub(crate) fn spec_errors_of(run: &Enumerated) -> Vec<(String, Event, bool)> {
    let mut errors: Vec<(String, Event, bool)> = run
        .visible_errors
        .iter()
        .map(|(t, p)| (t.clone(), *p, true))
        .collect();
    errors.extend(
        run.diagnostics
            .iter()
            .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
            .map(|d| (d.thread.clone(), d.pos, false)),
    );
    errors
}

/// One sweep (C2, C3; `P4-GATED` G4): a nested enumerating run of Spec on a
/// scoped thread with `verify`'s stack size, unbounded, under the configured
/// selector, stopped by its sink at the first graph passing `test` — or,
/// under `limit = Some(B)`, at completion `B + 1` without testing it ("test,
/// then limit").
pub(crate) fn sweep(
    config: &Config,
    visible: &[String],
    specification: &Arc<dyn Fn() + Send + Sync>,
    test: SweepTest,
    limit: Option<usize>,
    keep_graphs: bool,
    mode: ConfMode,
) -> Swept {
    let mut spec_config = config.clone();
    spec_config.max_iterations = None;
    // `P4-CFIRST-CODE` round 01 m4: a sweep is a whole exploration nested
    // inside one outer execution, so it gets no observers (a fresh, empty
    // `callbacks`) and no trace/dot outputs — the user's observers and files
    // see the precheck (when it runs) and the outer run, never a sweep.
    // Documented on `Engine::CompleteFirst`.
    spec_config.callbacks = Arc::new(std::sync::Mutex::new(Vec::new()));
    spec_config.dot_file = None;
    spec_config.trace_file = None;
    spec_config.error_trace_file = None;
    spec_config.turmoil_trace_file = None;
    let visible = visible.to_vec();
    let specification = Arc::clone(specification);

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!(
                "conformance-{}",
                mode.engine_label().replace(' ', "-")
            ))
            .stack_size(32 * 1024 * 1024)
            .spawn_scoped(s, move || {
                let found: Rc<RefCell<Option<ExecutionGraph>>> = Rc::new(RefCell::new(None));
                let tested = Rc::new(RefCell::new(0usize));
                let budgeted = Rc::new(RefCell::new(false));
                let kept: Rc<RefCell<Vec<ExecutionGraph>>> = Rc::new(RefCell::new(Vec::new()));
                let sink = {
                    let found = Rc::clone(&found);
                    let tested = Rc::clone(&tested);
                    let budgeted = Rc::clone(&budgeted);
                    let kept = Rc::clone(&kept);
                    let visible = visible.clone();
                    Box::new(move |m: &ExecutionGraph, _: &MustState| {
                        // Test, then limit: completion `B + 1` stops untested.
                        if limit.is_some_and(|b| *tested.borrow() >= b) {
                            *budgeted.borrow_mut() = true;
                            return SinkVerdict::Stop;
                        }
                        *tested.borrow_mut() += 1;
                        if keep_graphs {
                            kept.borrow_mut().push(m.clone());
                        }
                        let m_wobs = wobs(m, &visible).unwrap_or_else(|e| {
                            panic!(
                                "conformance: the specification program is not a valid input: {e}"
                            )
                        });
                        let spec = summarise(m, &visible, "specification");
                        if test.passes(&spec, &m_wobs, &visible) {
                            *found.borrow_mut() = Some(m.clone());
                            SinkVerdict::Stop
                        } else {
                            SinkVerdict::Continue
                        }
                    }) as CompletionSink
                };
                let run = enumerate(
                    EnumRun {
                        config: spec_config,
                        visible,
                        mode,
                        sink,
                        cut: false,
                        stop_at_first_report: false,
                        gate_sink: None,
                    },
                    &specification,
                );
                let witness = found.borrow_mut().take();
                let tested = *tested.borrow();
                let budgeted = *budgeted.borrow();
                let kept = std::mem::take(&mut *kept.borrow_mut());
                Swept {
                    run,
                    witness,
                    tested,
                    kept,
                    budgeted,
                }
            })
            .expect("conformance: the complete-first sweep thread could not be spawned");
        // Joined explicitly: an un-joined panicking scoped thread makes
        // `scope` panic with a generic message and loses the payload.
        match handle.join() {
            Ok(swept) => swept,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

/// The reported graph's label count, as the other engines count `events`.
fn label_count(graph: &ExecutionGraph) -> usize {
    graph
        .thread_ids()
        .into_iter()
        .map(|t| graph.thread_size(t))
        .sum()
}
