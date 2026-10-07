//! `GVerify`, the gated checker (`alg.tex` §8.6; `P4-GATED`).
//!
//! > **GVerify(Impl, Spec).** `W ← ∅`; GVisit(`G_∅`, ⊥, false).
//! > **GStep(e, G, M, c).** (`ln:ggate`) if `e` visible and ¬c then ⟨M, c⟩ ←
//! > Gate(G, M); GVisit(G, M, c).
//! > **Gate(G, M).** (`ln:gwit`) if M ≠ ⊥ and `cone(G, M)` return ⟨M, false⟩;
//! > (`ln:gskip`) if the policy declines return ⟨⊥, false⟩; (`ln:gsweep`) for
//! > M' ∈ W, then M' ∈ Graphs(Spec) — Must on Spec, unpruned — if `cone(G, M')`
//! > then W ← W ∪ {M'}; return ⟨M', false⟩; (`ln:gabsent`) in first-failure
//! > mode report G; return ⟨⊥, true⟩.
//! > **GVisit(G, M, c)** at `e = ⊥` (`ln:gfinal`): if `c` or ¬Covered(G) then
//! > report G.
//!
//! > **thm:gated.** For every gate policy, in exhaustive mode `alg:gated`
//! > reports exactly the uncovered members of `Graphs(Impl)`, and in
//! > first-failure mode it decides.
//!
//! **Shape (G1–G4).** Part 4's complete-first checker plus a **gate sink** at
//! the three growing gates of an enumerating run ([`ConfMode::GatedOuter`]).
//! The carried pair ⟨M, c⟩ lives on the engine's `MustState` ([`Carry`]), one
//! slot per state (D5 option 2): it moves with the state, a revisited
//! execution starts from a fresh default — the paper's `ln:greset` — and the
//! state's forward pops share it, soundly, because the certificate is
//! **validated at the point of use** by `def:ext` (`Certificate::valid_at`)
//! at every fired gate and at every completion. A gate re-tests the carried
//! witness by one `cone_from`, then by policy probes `W` and sweeps the
//! specification (Part 4's sweep, generalised to a `cone` test and a budget
//! limit) on its own thread; an exhaustive failing sweep sets the certificate
//! at that graph. The completion sink reports under a valid certificate
//! without testing, else runs Part 4's `Covered`.
//!
//! **Modes (G5).** Exhaustive: reports only at completions, the outer run
//! Must's and uncut. First-failure: a gate that certifies absence reports the
//! gated partial graph and prunes, with the stop reaching `try_revisit`'s head
//! (`must.rs`), so the whole search ends at its first report of either kind.
//!
//! **§5.4 (G5).** As Part 4: the unbounded precheck runs first unless skipped;
//! a sweep that meets a specification assertion failure aborts the run
//! (`GateVerdict::Stop` at a gate — a prune without a report — or the
//! completion sink's `Stop`).

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

use crate::conformance::cert::Certificate;
use crate::conformance::cfirst::{classify, spec_errors_of, sweep, SweepEnd, SweepTest};
use crate::conformance::config::{CompletionCover, ConfConfig, Engine, GatePolicy, GatedMode};
use crate::conformance::flat;
use crate::conformance::report::FlatCounters;
use crate::conformance::ctx::{
    CompletionSink, ConfMode, Diagnostic, Gate, GateAt, GateSink, GateVerdict, ReportKind,
    RevisitKind, SinkVerdict,
};
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{is_visible, wobs};
use crate::conformance::precheck;
use crate::conformance::report::{
    build_report_for, replay_snapshot, ConfCounters, ConfError, ConfNote, ConfOutcome, ConfReport,
    ConfVerdict, Diagnostics, GatedCounters, ReplaySnapshot, SearchEnd, SpecErrFreedom,
};
use crate::conformance::selector::paper_events;
use crate::conformance::sig::{cone_from, covered, ord};
use crate::conformance::stateful::{enumerate, summarise, EnumRun};
use crate::conformance::witness::WitnessCache;
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;
use crate::must::MustState;

/// The carried pair ⟨M, c⟩ of `alg:gated`, one per `MustState` (G2).
///
/// `witness` is an index into `W` — a hint only, re-tested by `cone` at
/// every gate, so a stale one is sound. `cert` carries its set point and is
/// validated by `def:ext` at the point of use.
#[derive(Clone, Debug, Default)]
pub(crate) struct Carry {
    pub(crate) witness: Option<usize>,
    pub(crate) cert: Certificate,
}

/// Where a report was raised (criterion 11).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReportSite {
    Completion,
    /// A first-failure report at a growing gate.
    Gate(Gate),
}

/// The engine-only result (criterion 11).
pub(crate) struct GatedOutcome {
    /// Reports in the order raised, each with the snapshot taken where it
    /// was raised.
    pub(crate) reports: Vec<(ExecutionGraph, ReplaySnapshot, ReportSite)>,
    pub(crate) counters: GatedCounters,
    pub(crate) witnesses: WitnessCache,
    /// Every outer completion, in completion order; empty unless asked for.
    pub(crate) kept_impl_graphs: Vec<ExecutionGraph>,
    /// One `Vec` per sweep (gate and completion sweeps, in sweep order), each
    /// in completion order; empty unless asked for.
    pub(crate) kept_spec_graphs: Vec<Vec<ExecutionGraph>>,
    /// How every sweep ended, in sweep order.
    pub(crate) sweep_ends: Vec<SweepEnd>,
    /// A sweep aborted the run.
    pub(crate) aborted: bool,
    /// The outer run's end. On an abort or a first-failure report it is what
    /// the stop mechanism recorded (`StoppedAtFirstReport`, or
    /// `MaxIterations(n)` when the bound coincided on that completion).
    pub(crate) impl_end: SearchEnd,
    /// The aborting sweep's assertion failures, visible first.
    pub(crate) spec_errors: Vec<(String, Event, bool)>,
    /// The implementation's visible event whose gate sweep aborted the run,
    /// if the abort was at a gate (criterion 8's wording).
    pub(crate) abort_gate_at: Option<Event>,
    /// Impl diagnostics, which `run` turns into `ConfNote`s.
    pub(crate) impl_notes: Vec<Diagnostic>,
    pub(crate) executions: usize,
    pub(crate) max_paper_events: usize,
}

/// What the two sinks accumulate, shared through an `Rc<RefCell<_>>` and
/// drained with `std::mem::take` once the run is over.
struct SinkState {
    witnesses: WitnessCache,
    counters: GatedCounters,
    sweep_time: std::time::Duration,
    reports: Vec<(ExecutionGraph, ReplaySnapshot, ReportSite)>,
    kept_impl: Vec<ExecutionGraph>,
    kept_spec: Vec<Vec<ExecutionGraph>>,
    sweep_ends: Vec<SweepEnd>,
    spec_errors: Vec<(String, Event, bool)>,
    aborted: bool,
    abort_gate_at: Option<Event>,
}

impl Default for SinkState {
    fn default() -> Self {
        Self {
            witnesses: WitnessCache::new(Vec::new()),
            counters: GatedCounters::default(),
            sweep_time: std::time::Duration::ZERO,
            reports: Vec::new(),
            kept_impl: Vec::new(),
            kept_spec: Vec::new(),
            sweep_ends: Vec::new(),
            spec_errors: Vec::new(),
            aborted: false,
            abort_gate_at: None,
        }
    }
}

impl SinkState {
    fn note_first_report(&mut self, g: &ExecutionGraph) {
        if self.counters.paper_events_at_first_report.is_none() {
            let paper: usize = g.thread_ids().into_iter().map(|t| paper_events(g, t)).sum();
            self.counters.paper_events_at_first_report = Some(paper);
        }
    }
}

/// The public path: the (unbounded) precheck, then [`run_with`] with
/// `keep_graphs = false`, then the `ConfOutcome` (G5, G6).
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

    // -- §5.4, unbounded (Part 4 C4) --------------------------------------
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

    if let Some((thread, pos, visible)) = out.spec_errors.first() {
        let site = match out.abort_gate_at {
            None => format!(
                "the sweep for complete implementation graph number {}",
                out.counters.impl_graphs
            ),
            Some(at) => format!("the gate after the implementation's visible event at {at}"),
        };
        let who = if *visible { "visible" } else { "invisible" };
        let tail = if *visible {
            String::new()
        } else {
            " It is not a declared visible thread, which changes what a *report* would \
             mean but not whether the specification is error-free."
                .to_owned()
        };
        return Err(ConfError::SpecNotErrorFree {
            detail: format!(
                "The {who} thread `{thread}` failed an assertion at {pos} during a gated \
                 sweep of the specification ({site}).{tail}"
            ),
        });
    }

    let first_failure = cc.gated_mode == GatedMode::FirstFailure;
    let reports: Vec<ConfReport> = out
        .reports
        .into_iter()
        .map(|(graph, replay, site)| {
            let events: usize = graph
                .thread_ids()
                .into_iter()
                .map(|t| graph.thread_size(t))
                .sum();
            let gate = match site {
                ReportSite::Completion => Gate::Completion,
                ReportSite::Gate(g) => g,
            };
            let mut r = build_report_for(
                Engine::Gated,
                &ReportKind::NoCover,
                Some(gate),
                events,
                &graph,
                replay,
                Diagnostics::NotProduced { by: Engine::Gated },
            );
            // `P4-FLAT` criterion 8: every completion report of a `Flat` run,
            // never a gate-site report.
            r.by_flat_cover = flat && matches!(site, ReportSite::Completion);
            r
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
        // `P4-GATED` round 01 m6: §8.8's headline figure, filled from the
        // engine's own counter.
        paper_events_at_first_report: out.counters.paper_events_at_first_report,
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
        engine: Engine::Gated,
        stateful_counters: None,
        cfirst_counters: None,
        flat_counters: out.counters.flat.clone(),
        flat_eligibility: eligibility,
        gated_counters: Some(GatedCounters {
            first_failure_mode: first_failure,
            ..out.counters
        }),
    }))
}

/// `alg:gated` and nothing else (criterion 1): the outer run with the gate
/// sink (`Gate`) and the completion sink (`ln:gfinal`). No precheck here.
///
/// # Panics
///
/// On invalid input, as `verify` documents: a §9 scope rejection (naming
/// "gated" or "gated sweep"); a §8 violation (from `summarise`, `wobs`, a
/// witness admission or `valid_at`, naming the program); if a sweep ends in a
/// way the decision table rules out; and if `W` refuses an admission as
/// already held, which the probe should have answered.
pub(crate) fn run_with(
    cc: &ConfConfig,
    implementation: &Arc<dyn Fn() + Send + Sync>,
    specification: &Arc<dyn Fn() + Send + Sync>,
    keep_graphs: bool,
) -> GatedOutcome {
    crate::conformance::assert_config_in_scope(&cc.config, "gated");
    let visible = cc.visible.clone();
    let first_failure = cc.gated_mode == GatedMode::FirstFailure;
    let stop_on_completion_report = first_failure || cc.stop_at_first_report;
    let policy = cc.gate_policy;

    let state = Rc::new(RefCell::new(SinkState {
        witnesses: WitnessCache::new(visible.clone()),
        ..SinkState::default()
    }));
    // `P4-FLAT` F6: `Some` whenever the knob is `Flat`, zero counts allowed.
    if cc.completion_cover == CompletionCover::Flat {
        state.borrow_mut().counters.flat = Some(FlatCounters::default());
    }

    let outer_started = Instant::now();

    // -- the gate sink (G1, G3) -------------------------------------------
    let gate_sink: GateSink = {
        let state = Rc::clone(&state);
        let visible = visible.clone();
        let config = cc.config.clone();
        let specification = Arc::clone(specification);
        Box::new(
            move |gate: Gate, site: &GateAt, g1: &ExecutionGraph, must_state: &MustState| {
                let mut st = state.borrow_mut();
                if st.aborted {
                    return GateVerdict::Continue;
                }
                // `states_pushed`, before the inertness test (criterion 9).
                if site.revisit == Some(RevisitKind::Backward) {
                    st.counters.states_pushed += 1;
                    if site
                        .outgoing_carry
                        .as_ref()
                        .is_some_and(|c| c.cert.is_set())
                    {
                        st.counters.certified_states_revisited += 1;
                    }
                }
                // `ln:ggate`'s "`e` visible", exactly, through `is_visible` (the
                // operation's annotation under `P4-MIXED`): the fresh send or
                // receive; a forward pop iff the popped receive is visible; a
                // backward revisit iff the revisiting send is.
                let fires = match site.revisit {
                    None | Some(RevisitKind::Forward) => is_visible(g1, site.at, &visible),
                    Some(RevisitKind::Backward) => site
                        .source
                        .is_some_and(|s| is_visible(g1, s, &visible)),
                };
                if !fires {
                    st.counters.gates_inert += 1;
                    return GateVerdict::Continue;
                }
                st.counters.gates += 1;

                let mut carry = must_state.conf_carry.borrow_mut();

                // The certificate step (G2): valid ⇒ skip; invalid ⇒ drop.
                if carry.cert.is_set() {
                    match carry.cert.valid_at(g1, &visible) {
                        Ok(true) => {
                            st.counters.gates_skipped_certified += 1;
                            return GateVerdict::Continue;
                        }
                        Ok(false) => {
                            carry.cert = Certificate::none();
                            st.counters.certificate_resets += 1;
                        }
                        Err(e) => panic!(
                            "conformance: the implementation program is not a valid input: {e}"
                        ),
                    }
                }

                let w1 = wobs(g1, &visible).unwrap_or_else(|e| {
                    panic!("conformance: the implementation program is not a valid input: {e}")
                });
                let ord1 = ord(g1, &w1, &visible);

                // `ln:gwit`: the carried witness, one `cone` test.
                if let Some(i) = carry.witness {
                    st.counters.c1_tests_carried += 1;
                    if cone_from(&w1, &ord1, st.witnesses.entries()[i].summary(), &visible) {
                        st.counters.carried_hits += 1;
                        return GateVerdict::Continue;
                    }
                    carry.witness = None;
                }

                // `ln:gskip`.
                let limit = match policy {
                    GatePolicy::Never => {
                        st.counters.gates_declined += 1;
                        return GateVerdict::Continue;
                    }
                    GatePolicy::Always => None,
                    GatePolicy::Budget(b) => Some(b),
                };

                // `ln:gsweep`: `W` first.
                let (hit, tests) = st.witnesses.probe_cone_counted(&w1, &ord1);
                st.counters.c1_tests_cache += tests;
                if let Some(i) = hit {
                    carry.witness = Some(i);
                    st.counters.gate_cache_hits += 1;
                    return GateVerdict::Continue;
                }

                // Then the specification, on its own thread (G4).
                let sweep_started = Instant::now();
                let swept = sweep(
                    &config,
                    &visible,
                    &specification,
                    SweepTest::Cone {
                        wobs: w1,
                        ord: ord1,
                    },
                    limit,
                    keep_graphs,
                    ConfMode::GatedSweep,
                );
                st.sweep_time += sweep_started.elapsed();
                st.counters.gate_sweeps += 1;
                st.counters.gate_sweep_sizes.push(swept.tested);
                st.counters.c1_tests_sweep += swept.tested;
                if keep_graphs {
                    st.kept_spec.push(swept.kept.clone());
                }
                let end = classify(&swept, limit.is_some());
                st.sweep_ends.push(end);
                match end {
                    SweepEnd::Aborted => {
                        st.counters.gate_sweeps_aborted += 1;
                        st.spec_errors = spec_errors_of(&swept.run);
                        st.aborted = true;
                        // The event the gate follows: the send for a backward
                        // revisit (`ln:greset`'s `e`), else the installed one.
                        st.abort_gate_at = Some(match site.revisit {
                            Some(RevisitKind::Backward) => site.source.unwrap_or(site.at),
                            _ => site.at,
                        });
                        GateVerdict::Stop
                    }
                    SweepEnd::Witness => {
                        let m = swept
                            .witness
                            .as_ref()
                            .expect("conformance: a successful sweep stores its witness");
                        // The sweep's completion-gate capture, one thread later.
                        let exec = CompleteExecution::assume_finished_at_gate(m);
                        let inserted = st.witnesses.admit_from_sweep(exec).unwrap_or_else(|e| {
                            panic!(
                                "conformance: the specification program is not a valid input: {e}"
                            )
                        });
                        if !inserted {
                            st.counters.witness_duplicates += 1;
                        }
                        assert!(
                            inserted,
                            "conformance: the gated engine admitted a witness W already holds; \
                         the cache probe should have hit"
                        );
                        st.counters.gate_sweeps_successful += 1;
                        st.counters.witnesses = st.witnesses.len();
                        carry.witness = Some(st.witnesses.len() - 1);
                        GateVerdict::Continue
                    }
                    SweepEnd::Budgeted => {
                        st.counters.gate_sweeps_budgeted += 1;
                        GateVerdict::Continue
                    }
                    SweepEnd::Exhausted => {
                        // `ln:gabsent`: the certificate, set at this graph.
                        st.counters.gate_sweeps_failing += 1;
                        st.counters.certificates_set += 1;
                        carry.witness = None;
                        carry.cert =
                            Certificate::absence_established(g1, &visible).unwrap_or_else(|e| {
                                panic!(
                                    "conformance: the implementation program is not a valid \
                                 input: {e}"
                                )
                            });
                        // T1 (gate 3): `replay_snapshot` clones the `MustState`,
                        // slot included, so the slot's borrow is released first.
                        drop(carry);
                        if first_failure {
                            st.counters.reports += 1;
                            st.note_first_report(g1);
                            // The context pushes the report and takes the snapshot
                            // before the prune; the engine-only outcome records the
                            // same graph here.
                            let snapshot = replay_snapshot(g1, must_state, &config, None);
                            st.reports
                                .push((g1.clone(), snapshot, ReportSite::Gate(gate)));
                            GateVerdict::Report
                        } else {
                            GateVerdict::Continue
                        }
                    }
                }
            },
        )
    };

    // -- the completion sink (`ln:gfinal`, G4) ---------------------------
    let sink: CompletionSink = {
        let state = Rc::clone(&state);
        let visible = visible.clone();
        let config = cc.config.clone();
        let specification = Arc::clone(specification);
        let flat_ctx = (cc.completion_cover == CompletionCover::Flat)
            .then(|| flat::FlatCtx::new(&config, &visible, &specification));
        Box::new(move |g: &ExecutionGraph, must_state: &MustState| {
            let mut st = state.borrow_mut();
            if st.aborted {
                return SinkVerdict::Stop;
            }
            let summary = summarise(g, &visible, "implementation");
            st.counters.impl_graphs += 1;
            // `P4-MIXED` M8, in the implementation completion sink.
            let inv = crate::conformance::ctx::invisible_ops_of_visible_threads(g, &visible);
            st.counters.invisible_ops_of_visible_threads =
                st.counters.invisible_ops_of_visible_threads.max(inv);
            if keep_graphs {
                st.kept_impl.push(g.clone());
            }

            // The certificate test first (G4). The slot's borrow is released
            // before any snapshot (T1, gate 3: `replay_snapshot` clones the
            // `MustState`, slot included).
            let certified = {
                let mut carry = must_state.conf_carry.borrow_mut();
                if carry.cert.is_set() {
                    match carry.cert.valid_at(g, &visible) {
                        Ok(true) => true,
                        Ok(false) => {
                            carry.cert = Certificate::none();
                            st.counters.certificate_resets += 1;
                            false
                        }
                        Err(e) => panic!(
                            "conformance: the implementation program is not a valid input: {e}"
                        ),
                    }
                } else {
                    false
                }
            };
            if certified {
                st.counters.reports_certified += 1;
                st.counters.reports += 1;
                st.note_first_report(g);
                let snapshot = replay_snapshot(g, must_state, &config, None);
                st.reports
                    .push((g.clone(), snapshot, ReportSite::Completion));
                return if stop_on_completion_report {
                    SinkVerdict::Stop
                } else {
                    SinkVerdict::Continue
                };
            }

            // Part 4's `Covered`: `W`, then a sweep.
            st.counters.completion_probes += 1;
            let (found, tests) = st.witnesses.probe_covered_counted(&summary);
            let hit = found.is_some();
            st.counters.completion_cache_tests += tests;
            if hit {
                st.counters.completion_cache_hits += 1;
                return SinkVerdict::Continue;
            }
            if let Some(fctx) = flat_ctx.as_ref() {
                // `P4-FLAT` F4: the adapter — `FlatCover` in place of the
                // completion sweep (gate sweeps are untouched); a witness is
                // admitted through `flat::admit`, which re-enters the cache's one
                // mutating method `admit_from_sweep` (`P4-APPARATUS` 15); ⊥ is
                // the uncovered completion.
                drop(st);
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
                            "conformance: the gated engine admitted a FlatCover witness W already \
                             holds; the cache probe should have hit"
                        );
                        st.counters.witnesses = st.witnesses.len();
                        SinkVerdict::Continue
                    }
                    None => {
                        st.counters.reports_by_completion_test += 1;
                        st.counters.reports += 1;
                        st.note_first_report(g);
                        let snapshot = replay_snapshot(g, must_state, &config, None);
                        st.reports
                            .push((g.clone(), snapshot, ReportSite::Completion));
                        if stop_on_completion_report {
                            SinkVerdict::Stop
                        } else {
                            SinkVerdict::Continue
                        }
                    }
                };
            }
            let sweep_started = Instant::now();
            let swept = sweep(
                &config,
                &visible,
                &specification,
                SweepTest::Covered(summary.clone()),
                None,
                keep_graphs,
                ConfMode::GatedSweep,
            );
            st.sweep_time += sweep_started.elapsed();
            st.counters.completion_sweeps += 1;
            st.counters.completion_sweep_sizes.push(swept.tested);
            if keep_graphs {
                st.kept_spec.push(swept.kept.clone());
            }
            let end = classify(&swept, false);
            st.sweep_ends.push(end);
            match end {
                SweepEnd::Aborted => {
                    st.counters.completion_sweeps_aborted += 1;
                    st.spec_errors = spec_errors_of(&swept.run);
                    st.aborted = true;
                    SinkVerdict::Stop
                }
                SweepEnd::Witness => {
                    let m = swept
                        .witness
                        .as_ref()
                        .expect("conformance: a successful sweep stores its witness");
                    let exec = CompleteExecution::assume_finished_at_gate(m);
                    let inserted = st.witnesses.admit_from_sweep(exec).unwrap_or_else(|e| {
                        panic!("conformance: the specification program is not a valid input: {e}")
                    });
                    if !inserted {
                        st.counters.witness_duplicates += 1;
                    }
                    assert!(
                        inserted,
                        "conformance: the gated engine admitted a witness W already holds; \
                         the cache probe should have hit"
                    );
                    st.counters.completion_sweeps_successful += 1;
                    st.counters.witnesses = st.witnesses.len();
                    SinkVerdict::Continue
                }
                SweepEnd::Exhausted => {
                    st.counters.completion_sweeps_failing += 1;
                    st.counters.reports_by_completion_test += 1;
                    st.counters.reports += 1;
                    st.note_first_report(g);
                    let snapshot = replay_snapshot(g, must_state, &config, None);
                    st.reports
                        .push((g.clone(), snapshot, ReportSite::Completion));
                    if stop_on_completion_report {
                        SinkVerdict::Stop
                    } else {
                        SinkVerdict::Continue
                    }
                }
                SweepEnd::Budgeted => {
                    unreachable!("conformance: a completion sweep is never given a limit")
                }
            }
        })
    };

    let outer = enumerate(
        EnumRun {
            config: cc.config.clone(),
            visible,
            mode: ConfMode::GatedOuter,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: Some(gate_sink),
        },
        implementation,
    );
    let mut st = std::mem::take(&mut *state.borrow_mut());
    st.counters.outer_wall_time_ms = outer_started.elapsed().as_millis();
    st.counters.sweep_wall_time_ms = st.sweep_time.as_millis();
    st.counters.gates_skipped_replay = outer.gate_skipped_replay;
    st.counters.first_failure_mode = first_failure;
    debug_assert!(
        outer.reports.len()
            == st
                .reports
                .iter()
                .filter(|r| matches!(r.2, ReportSite::Gate(_)))
                .count(),
        "conformance: the context's gate reports and the engine's disagree"
    );

    GatedOutcome {
        reports: st.reports,
        counters: st.counters,
        witnesses: st.witnesses,
        kept_impl_graphs: st.kept_impl,
        kept_spec_graphs: st.kept_spec,
        sweep_ends: st.sweep_ends,
        aborted: st.aborted,
        impl_end: outer.end,
        spec_errors: st.spec_errors,
        abort_gate_at: st.abort_gate_at,
        impl_notes: outer.diagnostics,
        executions: outer.executions,
        max_paper_events: outer.max_paper_events,
    }
}
