//! `SVerify`, the stateful checker (`alg.tex` §8.3; `P4-STATEFUL`).
//!
//! > **SVerify(Impl, Spec).** `I ← ∅`; for `G' ∈ Graphs(Spec)` add `ord(G')` to
//! > `I[sig(G')]`; for `G ∈ Graphs(Impl)`, if no `Q ∈ I[sig(G)]` has
//! > `Q ⊆ ord(G)` then report `G`.
//!
//! > **thm:stateful.** `alg:stateful` reports exactly the uncovered members of
//! > `Graphs(Impl)`.
//!
//! It *enumerates* (§8.1): both families are explored in full by Must, so its
//! silence **and** its report list are complete. It has no inner search, no
//! cache and no certificate — two [`ConfMode::Enumerate`] runs, Part 1's
//! [`Summary`] and `lem:sig`.
//!
//! **Shape (T1–T4).** Each family is enumerated by a production twin of the
//! oracle's `Collect` run (`oracle.rs` is test-only): a `Must` under
//! [`ConfMode::Enumerate`], which never prunes, with a **completion sink** (T3)
//! that summarises each complete graph on the spot and drops it. The Spec sink
//! builds the index; the Impl sink does the lookup and keeps only reported
//! graphs, each with its replay snapshot taken there. So the Impl family is
//! **streamed**, `stop_at_first_report` is honoured through the sink, and peak
//! memory is the index plus one graph.
//!
//! **The index run is the §5.4 check (T4).** The Spec enumeration records
//! every assertion failure (visible in `collect_errors`, invisible as an
//! `InvisibleThread` diagnostic); if any, [`run`] returns
//! [`ConfError::SpecNotErrorFree`] before the Impl run starts, whatever
//! `skip_spec_errfree_check` says — one Spec enumeration, as §8.3 counts it.
//!
//! **Bounds (T5).** `max_iterations` is honoured on the Impl run (the owner's
//! ruling B: recorded, never rejected) and forced to `None` on the Spec run,
//! because a truncated index would produce false reports. `search_budget`,
//! `inner_order`, `memo` and `triage` do not apply.
//!
//! **Divergence recorded (T4):** under [`Engine::Stateful`] the
//! `skip_spec_errfree_check` flag has no effect.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

use crate::conformance::config::{ConfConfig, Engine};
use crate::conformance::ctx::{
    CompletionSink, ConfCtx, ConfMode, Diagnostic, DiagnosticReason, Gate, GateSink, Report,
    ReportKind, SinkVerdict,
};
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::wobs;
use crate::conformance::report::{
    build_report_for, replay_snapshot, ConfCounters, ConfError, ConfNote, ConfOutcome, ConfVerdict,
    Diagnostics, ReplaySnapshot, SearchEnd, SpecErrFreedom, StatefulCounters,
};
use crate::conformance::selector::paper_events;
use crate::conformance::sig::{SigBuckets, Summary, VisOrder};
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;
use crate::must::{Must, MustState};
use crate::Config;

/// The engine-only result (`P4-STATEFUL` criterion 12): what the two loops
/// produced, with the index and the Spec family for Part 6's certification
/// oracle, and the graphs only when asked for.
pub(crate) struct StatefulOutcome {
    /// Each reported Impl graph with the replay snapshot taken at its
    /// completion.
    pub(crate) reports: Vec<(ExecutionGraph, ReplaySnapshot)>,
    pub(crate) counters: StatefulCounters,
    pub(crate) index: SigBuckets<BTreeSet<VisOrder>>,
    /// Every Impl graph, in completion order — empty unless `keep_graphs`.
    pub(crate) kept_impl_graphs: Vec<ExecutionGraph>,
    /// Every Spec graph, in completion order — empty unless `keep_graphs`.
    pub(crate) kept_spec_graphs: Vec<ExecutionGraph>,
    /// The Impl run's end; `Unknown` when the Impl run never started (T4).
    pub(crate) impl_end: SearchEnd,
    pub(crate) spec_end: SearchEnd,
    /// Spec assertion failures: `(thread, position, visible)`, visible first.
    pub(crate) spec_errors: Vec<(String, Event, bool)>,
    /// Impl invisible-thread assertion failures, which `run` renders as notes.
    pub(crate) impl_notes: Vec<Diagnostic>,
    /// Impl executions seen at `Completion` (the enumerator's `executions`).
    pub(crate) executions: usize,
    /// The paper's `L` over the Impl run.
    pub(crate) max_paper_events: usize,
}

/// What a completion sink accumulates (T3), shared with [`run_with`] through
/// an `Rc<RefCell<_>>` and drained with `std::mem::take` once the run is over
/// (`Rc::try_unwrap` would fail while `CURRENT_MUST` still holds the `Must`).
#[derive(Default)]
struct SinkState {
    index: SigBuckets<BTreeSet<VisOrder>>,
    counters: StatefulCounters,
    reports: Vec<(ExecutionGraph, ReplaySnapshot)>,
    kept: Vec<ExecutionGraph>,
    executions: usize,
    max_paper_events: usize,
}

/// The public path: [`run_with`] with `keep_graphs = false`, then the
/// `ConfOutcome` (T6).
pub(crate) fn run(
    cc: ConfConfig,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
) -> Result<ConfVerdict, ConfError> {
    let started = Instant::now();
    let out = run_with(&cc, &implementation, &specification, false);

    // T4: the index run was the §5.4 check.
    if let Some((thread, pos, visible)) = out.spec_errors.first() {
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

    let reports = out
        .reports
        .into_iter()
        .map(|(graph, replay)| {
            let events: usize = graph
                .thread_ids()
                .into_iter()
                .map(|t| graph.thread_size(t))
                .sum();
            build_report_for(
                Engine::Stateful,
                &ReportKind::NoCover,
                Some(Gate::Completion),
                events,
                &graph,
                replay,
                Diagnostics::NotProduced {
                    by: Engine::Stateful,
                },
            )
        })
        .collect();
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
        // The index run *is* the check, exhaustive whatever the flag says (T4).
        spec_errfree: SpecErrFreedom::Checked,
        budget: cc.search_budget,
        triage_enabled: cc.triage,
        seed: cc.config.seed,
        counters,
        engine: Engine::Stateful,
        stateful_counters: Some(out.counters),
        cfirst_counters: None,
        gated_counters: None,
        flat_counters: None,
        flat_eligibility: None,
    }))
}

/// The two loops and nothing else, with one early exit (criterion 1): if the
/// Spec enumeration recorded an assertion failure, the Impl run never starts.
///
/// # Panics
///
/// On invalid input, as `verify` documents: a §9 scope rejection; a §8
/// violation (a declared visible name spawned late, twice, or never — the
/// last surfaces from `Summary::of` here, naming the program); and if the
/// Spec run ends other than `StateSpaceExhausted`, which T5 rules out.
pub(crate) fn run_with(
    cc: &ConfConfig,
    implementation: &Arc<dyn Fn() + Send + Sync>,
    specification: &Arc<dyn Fn() + Send + Sync>,
    keep_graphs: bool,
) -> StatefulOutcome {
    // §9's config-time layer, before any engine exists.
    crate::conformance::assert_config_in_scope(&cc.config, "stateful");
    let visible = cc.visible.clone();

    // -- the index run (T4): Spec, unbounded (T5) ------------------------
    let mut spec_config = cc.config.clone();
    spec_config.max_iterations = None;
    let state = Rc::new(RefCell::new(SinkState::default()));
    let spec_started = Instant::now();
    let spec_sink = {
        let state = Rc::clone(&state);
        let visible = visible.clone();
        Box::new(move |g: &ExecutionGraph, _: &MustState| {
            let summary = summarise(g, &visible, "specification");
            let mut st = state.borrow_mut();
            let inserted = st
                .index
                .entry(summary.sig, BTreeSet::new)
                .insert(summary.ord);
            st.counters.spec_graphs += 1;
            if inserted {
                st.counters.orders_held += 1;
            }
            if keep_graphs {
                st.kept.push(g.clone());
            }
            SinkVerdict::Continue
        }) as CompletionSink
    };
    let spec_run = enumerate(
        EnumRun {
            config: spec_config,
            visible: visible.clone(),
            mode: ConfMode::Enumerate,
            sink: spec_sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
        },
        specification,
    );
    {
        let mut st = state.borrow_mut();
        st.counters.spec_wall_time_ms = spec_started.elapsed().as_millis();
        st.counters.sig_key_buckets = st.index.key_buckets();
        st.counters.signatures = st.index.len();
    }
    assert!(
        spec_run.end == SearchEnd::StateSpaceExhausted,
        "conformance: the stateful engine's enumeration of the specification ended {:?}, \
         not StateSpaceExhausted; the index would be incomplete",
        spec_run.end
    );
    let kept_spec_graphs = std::mem::take(&mut state.borrow_mut().kept);

    // Visible first, then invisible (T4).
    let mut spec_errors: Vec<(String, Event, bool)> = spec_run
        .visible_errors
        .into_iter()
        .map(|(t, p)| (t, p, true))
        .collect();
    spec_errors.extend(
        spec_run
            .diagnostics
            .iter()
            .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
            .map(|d| (d.thread.clone(), d.pos, false)),
    );
    if !spec_errors.is_empty() {
        let st = std::mem::take(&mut *state.borrow_mut());
        return StatefulOutcome {
            reports: Vec::new(),
            counters: st.counters,
            index: st.index,
            kept_impl_graphs: Vec::new(),
            kept_spec_graphs,
            impl_end: SearchEnd::Unknown,
            spec_end: spec_run.end,
            spec_errors,
            impl_notes: Vec::new(),
            executions: 0,
            max_paper_events: 0,
        };
    }

    // -- the stream (T3): Impl, bounded as configured (T5) ---------------
    let impl_started = Instant::now();
    let impl_sink = {
        let state = Rc::clone(&state);
        let visible = visible.clone();
        let config = cc.config.clone();
        let stop_at_first_report = cc.stop_at_first_report;
        Box::new(move |g: &ExecutionGraph, must_state: &MustState| {
            let summary = summarise(g, &visible, "implementation");
            let mut st = state.borrow_mut();
            st.executions += 1;
            let paper: usize = g.thread_ids().into_iter().map(|t| paper_events(g, t)).sum();
            st.max_paper_events = st.max_paper_events.max(paper);
            // `P4-MIXED` M8, in the implementation completion sink.
            let inv = crate::conformance::ctx::invisible_ops_of_visible_threads(g, &visible);
            st.counters.invisible_ops_of_visible_threads =
                st.counters.invisible_ops_of_visible_threads.max(inv);
            st.counters.impl_graphs += 1;
            st.counters.lookups += 1;
            if keep_graphs {
                st.kept.push(g.clone());
            }
            // The lookup (criterion 1): the full-`Sig` slot, scanned in
            // `BTreeSet` order, short-circuiting at the first containing `Q`.
            // Split the borrow: the index is read, the counters written.
            let SinkState {
                index, counters, ..
            } = &mut *st;
            let covered = match index.get(&summary.sig) {
                None => {
                    counters.lookups_signature_miss += 1;
                    false
                }
                Some(orders) => {
                    counters.lookups_containment_tested += 1;
                    let mut found = false;
                    let mut tests = 0;
                    for q in orders {
                        tests += 1;
                        if q.is_subset(&summary.ord) {
                            found = true;
                            break;
                        }
                    }
                    counters.containment_tests += tests;
                    if found {
                        counters.lookups_succeeded += 1;
                    } else {
                        counters.lookups_failed_after_tests += 1;
                    }
                    found
                }
            };
            if covered {
                return SinkVerdict::Continue;
            }
            st.counters.reports += 1;
            // T3: the snapshot is taken here, with the live state, so it is
            // `Serialized` like the enumerator's completion reports.
            let snapshot = replay_snapshot(g, must_state, &config, None);
            st.reports.push((g.clone(), snapshot));
            if stop_at_first_report {
                SinkVerdict::Stop
            } else {
                SinkVerdict::Continue
            }
        }) as CompletionSink
    };
    let impl_run = enumerate(
        EnumRun {
            config: cc.config.clone(),
            visible,
            mode: ConfMode::Enumerate,
            sink: impl_sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
        },
        implementation,
    );
    let mut st = std::mem::take(&mut *state.borrow_mut());
    st.counters.impl_wall_time_ms = impl_started.elapsed().as_millis();

    StatefulOutcome {
        reports: st.reports,
        counters: st.counters,
        index: st.index,
        kept_impl_graphs: st.kept,
        kept_spec_graphs,
        impl_end: impl_run.end,
        spec_end: spec_run.end,
        spec_errors: Vec::new(),
        impl_notes: impl_run.diagnostics,
        executions: st.executions,
        max_paper_events: st.max_paper_events,
    }
}

/// One program's `Summary` at a completion, or a panic naming the program on
/// a §8 violation (T6). Shared with the complete-first checker (`P4-CFIRST`
/// C1).
pub(crate) fn summarise(graph: &ExecutionGraph, visible: &[String], program: &str) -> Summary {
    let exec = CompleteExecution::assume_finished_at_gate(graph);
    let w = wobs(graph, visible)
        .unwrap_or_else(|e| panic!("conformance: the {program} program is not a valid input: {e}"));
    Summary::of(exec, &w, visible)
        .unwrap_or_else(|e| panic!("conformance: the {program} program is not a valid input: {e}"))
}

/// What an enumerating run leaves behind besides what its sink collected.
/// Shared with the complete-first checker (`P4-CFIRST` C1), which reads the
/// last three fields; the stateful engine ignores them.
pub(crate) struct Enumerated {
    pub(crate) end: SearchEnd,
    /// Visible assertion failures (`collect_errors`).
    pub(crate) visible_errors: Vec<(String, Event)>,
    /// Invisible-thread failures (`InvisibleThread`), and — only with the cut
    /// on (`P4-CFIRST` C5) — `AfterPrune` entries: the visible thread whose
    /// failure was cut keeps running until it yields (`traceforge::assert`
    /// installs without yielding), so a second failed `assert` on it is
    /// recorded after the prune. `ctx.rs`'s "believed unreachable" is about an
    /// *invisible* thread reaching that branch, not about `AfterPrune`
    /// (`P4-CFIRST-CODE` round 01 M1).
    pub(crate) diagnostics: Vec<Diagnostic>,
    /// The context's own reports — empty unless the cut is on (`P4-CFIRST`
    /// C5: `VisibleError` prefix reports).
    pub(crate) reports: Vec<Report>,
    /// Every execution the context saw, pruned ones included.
    pub(crate) executions: usize,
    /// The largest paper-event count of a completed graph seen by the gate.
    pub(crate) max_paper_events: usize,
    /// The context's F49 replay-skip count (`P4-GATED` criterion 9).
    pub(crate) gate_skipped_replay: usize,
}

/// How one enumerating run is set up (`P4-CFIRST` C1, round 02 m1 (b)).
pub(crate) struct EnumRun {
    pub(crate) config: Config,
    pub(crate) visible: Vec<String>,
    /// `Enumerate`, `CFirstOuter` or `CFirstSweep` — the label a §9
    /// rejection names.
    pub(crate) mode: ConfMode,
    pub(crate) sink: CompletionSink,
    /// `P4-CFIRST` C5; only honoured under `CFirstOuter`.
    pub(crate) cut: bool,
    /// Consulted only with the cut on (the sink stops completion reports).
    pub(crate) stop_at_first_report: bool,
    /// `P4-GATED` G1: the gate sink; `GatedOuter` only.
    pub(crate) gate_sink: Option<GateSink>,
}

/// One enumerating run of `program` (T1): the oracle's `Collect` mechanism in
/// production code, with `sink` at every completion.
pub(crate) fn enumerate(run: EnumRun, program: &Arc<dyn Fn() + Send + Sync>) -> Enumerated {
    let EnumRun {
        config,
        visible,
        mode,
        sink,
        cut,
        stop_at_first_report,
        gate_sink,
    } = run;
    assert!(
        mode.enumerates(),
        "conformance: `enumerate` runs an enumerating mode, not {mode:?}"
    );
    let program = Arc::clone(program);
    let program = Arc::new(move || program());
    let must = Rc::new(RefCell::new(Must::new(config.clone(), false)));
    let mut ctx = ConfCtx::gate_disabled(config, visible, mode);
    ctx.set_sink(sink);
    if mode == ConfMode::CFirstOuter {
        ctx.set_cut(cut, stop_at_first_report);
    }
    if let Some(gate_sink) = gate_sink {
        ctx.set_gate_sink(gate_sink);
    }
    must.borrow_mut().enable_conformance(ctx);

    crate::explore(&must, &program);

    // No worker to end, but the symmetric call keeps the run's shape.
    must.borrow_mut().conf_shutdown();
    let must = must.borrow();
    let ctx = must
        .conf_ctx()
        .expect("conformance: an enumerating run's context was taken and not put back");
    Enumerated {
        end: ctx.end(),
        visible_errors: ctx.collect_errors().to_vec(),
        diagnostics: ctx.diagnostics().to_vec(),
        reports: ctx.reports().to_vec(),
        executions: ctx.counters().executions,
        max_paper_events: ctx.counters().max_paper_events_per_execution,
        gate_skipped_replay: ctx.counters().gate_skipped_replay,
    }
}
