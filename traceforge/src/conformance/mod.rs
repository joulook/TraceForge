//! Conformance verification: does one program's visible behaviour refine
//! another's?
//!
//! The implementation and the specification are both ordinary TraceForge
//! programs. The implementation is explored by the stock Must engine; the
//! specification is consulted through [`probe`] executions, which report what
//! it could do next without committing to any of it. A search over
//! specification graphs then tries those options, looking for one that matches
//! what the implementation has done so far.
//!
//! This module is being built step by step; see
//! `plan/traceForge/conf-plan.md`. Present contents: probe mode (S1),
//! observations and the morphism (S2), the inner search (S3), and the engine
//! gate with its prune path and minimal sink (S4). Still to come: reports
//! (§7, S5), which is also where the public entry point lands — see
//! [`verify_conformance`].

// S4's gate now consumes the search, so most of this module is reachable from
// the engine rather than only from its own tests. What is still unused is the
// read side of the minimal sink — `Outcome`'s fields and the `ConfCtx`
// accessors behind them — which exists for S5 and for the tests S4's gate
// requires.
//
// **This should shrink again, not stay.** Two earlier versions of this comment
// outlived their reason; when S5 consumes the sink, this allow should go.
#![allow(dead_code)]

pub(crate) mod ctx;
pub(crate) mod morphism;
pub(crate) mod obs;
pub(crate) mod probe;
pub(crate) mod prober;
pub(crate) mod search;

/// The §9 config predicate, in one place.
///
/// `conf-plan.md` §9 calls the constructor-side check "the guarantee", and
/// gives the reason: a `Config` can reach a `Must` without ever passing
/// `check_valid` — `replay` deserializes one, and `estimate_execs_with_config`
/// silently overwrites `cons_type` *and* `schedule_policy`. Builder validation
/// is UX; this is the guarantee.
///
/// §9 applies it "to the outer conf run, the probe `Must`, and the err-freedom
/// precheck alike". It is a single function so those cannot drift apart: the
/// probe used to carry **four** of the seven exclusions and the gap went
/// unnoticed for three review rounds, because the four were written out by
/// hand at one call site and nothing compared them to §9's list.
///
/// The err-freedom precheck does not exist yet (§7, S5). When it lands it
/// calls this.
pub(crate) fn assert_config_in_scope(config: &crate::Config, engine: &str) {
    use crate::channel::cons_to_model;
    use crate::{CommunicationModel, ExplorationMode, SchedulePolicy};

    assert_ne!(
        cons_to_model(config.cons_type),
        CommunicationModel::TotalOrder,
        "{engine}: conformance is scoped to asyn/p2p/cd (conf-plan.md §1/§9); \
         mailbox is out of scope. Checked on the *model*, so the deprecated \
         `MO` spelling is caught as well as `Mailbox`."
    );
    assert_eq!(
        config.schedule_policy,
        SchedulePolicy::LTR,
        "{engine}: conformance requires the LTR schedule policy (conf-plan.md §9)"
    );
    assert_eq!(
        config.mode,
        ExplorationMode::Verification,
        "{engine}: conformance does not run in estimation mode (conf-plan.md §9)"
    );
    assert_eq!(
        config.lossy_budget, 0,
        "{engine}: conformance excludes lossy sends (conf-plan.md §9). \
         Obligation **O-skip** depends on this: S4's revisit-apply skip is \
         sound only because a gated forward revisit is always at a `RecvMsg`, \
         which holds only while lossy sends are excluded. See \
         `Must::conf_revisit_gate`'s derivation before relaxing it."
    );
    assert!(
        !config.parallel && !config.partitioned_parallelization,
        "{engine}: conformance excludes both parallel modes (conf-plan.md §9). \
         The exclusion is load-bearing beyond scope: in shared-queue mode \
         `backward_revisit` ships the graph and returns false, so a post-apply \
         gate would never fire for shipped revisits (§4.1)."
    );
    assert!(
        config.predetermined_choices.is_empty() && config.predetermined_global_choices.is_empty(),
        "{engine}: conformance excludes predetermined choices (conf-plan.md §9); \
         a predetermined choice is a decision the search never sees"
    );
    #[cfg(feature = "symbolic")]
    assert!(
        !config.symbolic,
        "{engine}: conformance excludes symbolic execution (conf-plan.md §9)"
    );
}

#[cfg(test)]
pub(crate) mod adversarial;
#[cfg(test)]
mod gate_tests;
#[cfg(test)]
pub(crate) mod testing;

/// What a conformance run found.
///
/// The minimal sink's read side (§4.2, owner ruling 2026-09-12). S5 turns this
/// into the reporting product; it deliberately renders nothing.
#[derive(Debug, Default)]
pub(crate) struct Outcome {
    pub(crate) reports: Vec<ctx::Report>,
    pub(crate) exhaustions: Vec<ctx::Exhaustion>,
    pub(crate) diagnostics: Vec<ctx::Diagnostic>,
    pub(crate) stats: Option<crate::Stats>,
}

/// Run `implementation` under conformance against `specification`.
///
/// **Deliberately `pub(crate)`.** §3 item 4 asks for a `pub mod conformance`
/// re-export; that is *deferred* and recorded as such (criterion 15). Every
/// item in this module is `pub(crate)`, so making the module public today
/// would export an empty namespace while committing an unstable surface to
/// semver. The public entry point belongs with reports (§7, S5), which is also
/// where the err-freedom precheck and the user-facing error types land.
///
/// `visible` is the list of declared visible thread names, `"main"` included if
/// the two programs' main threads are to be paired. `budget` is the inner
/// search's node ceiling per `Cover` attempt.
pub(crate) fn verify_conformance<I, S>(
    config: crate::Config,
    implementation: I,
    specification: S,
    visible: Vec<String>,
    budget: usize,
) -> Outcome
where
    I: Fn() + Send + Sync + 'static,
    S: Fn() + Send + Sync + 'static,
{
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    let ctx = ctx::ConfCtx::new(config.clone(), Arc::new(specification), visible, budget);
    let must = Rc::new(RefCell::new(crate::must::Must::new(config, false)));
    must.borrow_mut().enable_conformance(ctx);

    let implementation = Arc::new(implementation);
    crate::explore(&must, &implementation);

    // The run is over: end the probe worker here rather than leaving it to
    // `Drop`, which does not run at this point — `explore` leaves the outer
    // `Must` in the `CURRENT_MUST` thread-local, so the `Rc` below is not the
    // last one (gate-4 review, m1).
    must.borrow_mut().conf_shutdown();

    let must = must.borrow();
    let conf = must
        .conf_ctx()
        .expect("conformance: the context was taken and not put back");
    Outcome {
        reports: conf.reports().to_vec(),
        exhaustions: conf.exhaustions().to_vec(),
        diagnostics: conf.diagnostics().to_vec(),
        stats: Some(must.stats()),
    }
}
