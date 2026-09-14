//! §7.3: run the engine a second time on a graph captured at report time, and
//! complete it into a trace a user can read.
//!
//! # Which branch of `traceforge::assert` a triage run takes, and why it had
//! to be decided
//!
//! Blocked item **F**. §7.3 says triage runs with the "conformance gate off",
//! and the obvious reading of that is `Must::new`'s `conf: None`. That reading
//! has no model. `traceforge::assert` (`traceforge::assert`) has exactly three
//! branches on a false condition:
//!
//! 1. `conf_active()` → `conf_assert_failure`. **Needs `conf.is_some()`.**
//! 2. `keep_going_after_error` → `handle_block`, then `persist_task_failure` —
//!    which latches `PANIC_HOOK` to `Persisted(msg)` on a thread `explore`
//!    shares with the outer run, silently disarming the outer run's panic
//!    reporting for the rest of the session.
//! 3. otherwise → `handle_block`, a printed graph, and a **panic**.
//!
//! `is_consistent()` guards neither (F38: it is vacuous in this fragment). And
//! the case is reachable: `conf_assert_failure` installs the `Block(Assert)`
//! *before* reporting, so a `VisibleError` report's captured graph carries it,
//! and triage replays that prefix and re-runs the user's `assert`.
//!
//! **The ruling is the gate-disabled `ConfCtx`**, and the reason is the
//! opposite of the one first given for it. `with_initial_graph` is `Must::new`
//! plus a graph assignment, so a `conf: None` triage runs with S4's
//! `store_replay_information` exemption (`store_replay_information`'s conformance early return) **inactive**: branch 3
//! calls it directly on the already-borrowed `must`, so triage would print
//! "Random schedule seed…" (`store_replay_information`'s seed line), call `top_sort` on a
//! conformance-captured partial graph, and **write a counterexample file per
//! report** whenever the outer `Config` carries `with_error_trace`. That is
//! the file spam §4.4 exists to replace, arriving through the criterion
//! rewritten to forbid it. Giving triage `conf: Some(..)` is what keeps the
//! exemption armed.
//!
//! The `reject_out_of_scope` arming that comes with it is **accepted, not
//! merely tolerated**: triage replays an implementation prefix the outer run
//! already admitted, so a guard firing here would mean the outer run let
//! something through — an internal invariant violation worth hearing about.
//!
//! Nothing here renders; `report.rs` does.

use std::cell::RefCell;
use std::panic::AssertUnwindSafe;
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::config::ConfConfig;
use crate::conformance::ctx::{ConfCtx, ConfMode};
use crate::conformance::diagnose;
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::report::{ConfReport, ReportCause, TriageFailure, TriageOutcome};
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;

/// `validate_replay_event`'s own message (`ExecutionGraph::panic_if_err`).
///
/// The classification is on **this string** rather than on "a panic escaped
/// triage", and that is criterion 4's whole point: in the branch the default
/// configuration takes, a replayed user assertion arrives preceded by a graph
/// dump and by a `top_sort` call `store_replay_information`'s rustdoc says can panic and
/// "*replace* the original one". A developer catching panics at the triage
/// boundary and labelling them all "nondeterministic Impl" reports a
/// legitimate replayed assertion as a defect in the user's program — F-C's
/// shape at the boundary the criteria call the dangerous one.
const NONDETERMINISM_MARKER: &str = "Incorrect TraceForge Program";

/// Triage one report.
///
/// **Runs on the caller's thread, which must not be inside an execution.**
/// `explore` installs a current-`Must` thread-local and a continuation pool;
/// calling this from inside the outer run would nest two runtimes in one
/// thread's scoped state. `mod.rs` runs all post-run work on a dedicated OS
/// thread for exactly that reason.
pub(crate) fn triage_one(
    cc: &ConfConfig,
    implementation: &Arc<dyn Fn() + Send + Sync>,
    report: &ConfReport,
    graph: ExecutionGraph,
) -> Result<TriageOutcome, TriageFailure> {
    // §7.3, item 1: a fresh engine state whose `current.graph` is the reported
    // graph — the in-memory clone captured at report time, no serialization,
    // so no predicate loss — with an empty rqueue and an empty state stack
    // (`Must::new`'s own initial values, which `with_initial_graph` does not
    // disturb) and `max_iterations = 1`.
    let mut config = cc.config.clone();
    // **Through the constant, not past it** (gate-4 round 1, M1). The first
    // version hard-coded `Some(1)` here and never read
    // `TRIAGE_MAX_ITERATIONS`, so the two tests asserting it were
    // `assert_eq!(1, 1)` and the `recvs`-staleness argument was pinned to
    // nothing: changing this line to `Some(2)` left them both green.
    config.max_iterations = Some(TRIAGE_MAX_ITERATIONS);

    let visible = cc.visible.clone();
    let config_for_ctx = config.clone();
    let implementation = Arc::clone(implementation);

    let outcome = std::panic::catch_unwind(AssertUnwindSafe(move || {
        let must = Rc::new(RefCell::new(Must::with_initial_graph(config, graph)));
        // The gate-disabled context: `conf.is_some()` so that
        // `traceforge::assert` takes branch 1 and
        // `store_replay_information` stays exempt, with no probe worker and
        // no `Cover` call behind it.
        must.borrow_mut()
            .enable_conformance(ConfCtx::gate_disabled(
                config_for_ctx,
                visible.clone(),
                ConfMode::Triage,
            ));

        // `explore` is generic over a *sized* closure; the trait object is
        // wrapped rather than passed through.
        let f = Arc::new(move || implementation());
        crate::explore(&must, &f);

        let stats = must.borrow().stats();
        let sink_reported = must
            .borrow()
            .conf_ctx()
            .map(|c| (c.reports().to_vec(), c.diagnostics().to_vec()))
            .unwrap_or_default();
        let final_graph = must.borrow_mut().take_graph();
        (stats, sink_reported, final_graph)
    }));

    let (stats, (sink_reports, sink_notes), final_graph) = match outcome {
        Ok(v) => v,
        Err(payload) => {
            let detail = payload_text(&payload);
            return Err(if detail.contains(NONDETERMINISM_MARKER) {
                TriageFailure::NondeterministicImpl { detail }
            } else {
                TriageFailure::Panicked { detail }
            });
        }
    };

    // The replayed assertion, ahead of everything else: it is the expected
    // outcome of triaging a §4.4 report, and it *also* produces a blocked
    // ending (the prune blocks every thread), so checking "blocked" first
    // would hide it behind "could not complete".
    //
    // **Only the assertion this report names is `ReplayedAssertion`** (gate-4
    // round 1, m7). An invisible thread's failure, or a post-prune one, or a
    // visible one on a *different* thread, is not "what this report says
    // should happen" — and the first version rendered that sentence over a
    // note the report never mentioned.
    let names = match report.cause() {
        ReportCause::VisibleError { thread, .. } => Some(thread.as_str()),
        ReportCause::NoCover => None,
    };
    if let Some(r) = sink_reports.first() {
        if let crate::conformance::ctx::ReportKind::VisibleError { thread, pos } = &r.kind {
            let (thread, pos) = (thread.clone(), pos.to_string());
            return Ok(if names == Some(thread.as_str()) {
                TriageOutcome::ReplayedAssertion { thread, pos }
            } else {
                TriageOutcome::OtherAssertion { thread, pos }
            });
        }
    }
    if let Some(n) = sink_notes.first() {
        // A note is by construction *not* the report's own failure: §4.4 sends
        // an invisible thread's assertion and a post-prune one here precisely
        // because neither is a report.
        return Ok(TriageOutcome::OtherAssertion {
            thread: n.thread.clone(),
            pos: n.pos.to_string(),
        });
    }

    // §7.3's cutoff is at `record_ending_telemetry`'s `max_iterations` test, **inside `record_ending_telemetry`**
    // — which `complete_execution` calls — and it compares `n <= num_total`
    // where `num_total = num_execs + num_blocked`, i.e. **all** endings
    // including blocked ones. (§7.3 says "consulted in `complete_execution`";
    // the criteria file is the accurate one and this comment follows it.)
    //
    // So "exactly one execution" is not the property worth asserting: triage
    // can end with one *blocked* execution and no complete graph, and §7.3's
    // conclusion — "the result is a *complete* uncovered graph … the concrete
    // trace a user can read" — is then false with nothing to signal it.
    debug_assert_eq!(
        stats.execs + stats.block,
        TRIAGE_MAX_ITERATIONS as usize,
        "conformance: triage ran more than one execution despite max_iterations = 1"
    );
    if stats.block > 0 || stats.execs == 0 {
        return Ok(TriageOutcome::Blocked {
            ending: if stats.block > 0 {
                "blocked".to_owned()
            } else {
                "with no counted execution at all".to_owned()
            },
        });
    }

    // A complete execution. `try_finished` checks the half of the
    // precondition a graph can carry; main never gets an `End` (A8), so the
    // other half is the ending we just read off the telemetry.
    let complete = CompleteExecution::try_finished(&final_graph);
    let vis = match diagnose::canonical_vis(&final_graph, &cc.visible, complete) {
        Ok(v) => v,
        Err(e) => {
            return Err(TriageFailure::Panicked {
                detail: format!(
                    "the completed graph's visible trace could not be extracted: {e}"
                ),
            })
        }
    };
    let spec_mismatch = diagnose::spec_side_first_mismatch(&report.diagnostics, &report.cause);
    Ok(TriageOutcome::Completed {
        vis,
        spec_mismatch,
        dump: final_graph.to_string(),
    })
}

fn payload_text(payload: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_owned()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "a panic payload that is neither `&str` nor `String`".to_owned()
    }
}

/// The staleness argument for the captured graph's `recvs` index, **pinned so
/// that it breaks if triage stops discarding revisits**.
///
/// The `FreshRecv` gate fires at **two** sites — `visit_rfs`' bottom gate site (the ⊥ case)
/// and `visit_rfs`' canonical-rf gate site (the canonical-rf case) — both inside `visit_rfs` and
/// both **before** `register_recv` (`register_recv`'s two call sites in `handle_recv`), which `handle_recv`
/// calls after `visit_rfs` returns. So a graph cloned at either is missing
/// that receive's entry in `ExecutionGraph::recvs`. The send gate does not
/// have this shape: it fires after `register_send`.
///
/// The harm is bounded today, and the argument is worth pinning rather than
/// re-deriving: `recvs` is read only by `rev_matching_recvs`, whose only
/// callers are the backward-revisit computation, and triage runs under
/// `max_iterations = 1`, so every revisit it queues is discarded with the
/// engine state rather than applied.
///
/// This constant is what a test asserts against. If triage ever stops
/// discarding revisits — a `max_iterations` other than 1, or a second
/// execution — the assumption lapses and the index must be normalised first.
pub(crate) const TRIAGE_MAX_ITERATIONS: u64 = 1;
