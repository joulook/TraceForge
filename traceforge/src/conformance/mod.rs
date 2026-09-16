//! Conformance verification: does one program's visible behaviour refine
//! another's?
//!
//! The implementation and the specification are both ordinary TraceForge
//! programs. The implementation is explored by the stock Must engine; the
//! specification is consulted through *probe* executions, which report what
//! it could do next without committing to any of it. A search over
//! specification graphs then tries those options, looking for one that matches
//! what the implementation has done so far.
//!
//! # The front door
//!
//! ```no_run
//! use traceforge::conformance::{self, ConfBuilder};
//!
//! # fn impl_prog() {}
//! # fn spec_prog() {}
//! let verdict = conformance::verify(
//!     ConfBuilder::new()
//!         .visible_threads(["main", "server"])
//!         .build()?,
//!     impl_prog,
//!     spec_prog,
//! )?;
//! println!("{verdict}");
//! # Ok::<(), traceforge::conformance::ConfError>(())
//! ```
//!
//! # What a verdict means, in one paragraph
//!
//! **Only silence is a verdict.** [`ConfVerdict::Conforms`] is constructible
//! only when no candidate violation was reported, no inner search ran out of
//! budget, *and* the outer loop reached the end of its state space — the last
//! being a fact the engine records rather than one inferred from the first
//! two. Every other outcome names why it is not a certificate. A **report** is
//! a *candidate* violation: it certifies that no complete specification graph
//! covers any event-extension of the reported graph, modulo the draft's own
//! lemmas, and certifies nothing about whether the report list is complete.
//!
//! # `verify` panics on invalid input
//!
//! Blocked item C's ruling. [`ConfError`] carries the failures of a run that
//! started legitimately — §5.4's precheck and §7.3's triage. §8's
//! visible-thread violations and §9's scope rejections are "this program is
//! not a valid input", and they **panic**, with a message naming the event,
//! which is what §9 asks for in terms and what Rust's convention says for a
//! precondition a caller can check. The alternative needs a `catch_unwind`
//! boundary inside conformance's hot path, and S4 was bitten at that exact
//! boundary by a failure that became a different failure and lost its origin.
//!
//! # Map of the module
//!
//! `prober`/`probe` (S1) ask the specification what it could do next;
//! `obs`/`morphism` (S2) are the observation adapters and the morphism;
//! `search` (S3) is `Cover`/`SpecVisit`/`Done`/Φ; `ctx` (S4) is the gate's
//! state on the outer `Must`; and `config`, `report`, `precheck`, `triage`,
//! `diagnose` (S5) are the configuration, the reporting product and the two
//! extra engine runs. See `plan/traceForge/conf-plan.md`.

// **Still needed, and narrower than it was.** S4 carried a blanket
// `allow(dead_code)` for the sink's read side; S5 consumes that, and what
// remains is items whose only consumers are `#[cfg(test)]` modules — S1's
// `probe_once`/`recv_sources`/`probe_recv_sources`, S2's `Obs::type_name` and
// `Wobs::names`/`unspawned`, `Outcome::stats` and `verify_conformance` (the
// engine half, which `gate_tests` is written against), and
// `TRIAGE_MAX_ITERATIONS`. Every one of them is *used*, by a test; `dead_code`
// does not see test-only use from a non-test build. Removing the allow means
// either `#[cfg(test)]`-gating library items — which changes what the library
// compiles to depending on how it is built — or deleting an S1/S2 accessor,
// which is outside S5's write scope and would be a finding rather than an
// edit. Recorded in the S5 report as an open item rather than papered over.
#![allow(dead_code)]

pub(crate) mod config;
pub(crate) mod ctx;
pub(crate) mod diagnose;
pub(crate) mod morphism;
pub(crate) mod obs;
pub(crate) mod precheck;
pub(crate) mod probe;
pub(crate) mod prober;
pub(crate) mod report;
pub(crate) mod search;
pub(crate) mod triage;

// ---------------------------------------------------------------------------
// The public surface, and what it commits (criterion 11).
//
// §3 item 4 asks for a `pub mod conformance` re-export; S4 deferred it
// *because* every item in the module was `pub(crate)`, so publishing then
// would have exported an empty namespace while committing an unstable surface
// to semver. This is where it lands, and the set is chosen rather than
// inherited:
//
// - **the entry point and its configuration** — `verify`, `ConfBuilder`,
//   `ConfConfig`, `ConfigError`, `ScopeField`, `DEFAULT_SEARCH_BUDGET`. A
//   caller cannot use conformance without these.
// - **the verdict and everything needed to act on it** — `ConfVerdict`,
//   `Certificate`, `ConfOutcome`, `NotACertificate`, `SearchEnd`,
//   `SpecErrFreedom`, `ConfError`, `TriageFailure`. These are the difference
//   between a certificate and a run that merely produced no report, which is
//   the one distinction the theorem turns on; hiding it behind `Display` would
//   leave a programmatic caller with `to_string().contains(..)`.
// - **the report and its parts** — `ConfReport`, `ReportGate`, `ReportCause`,
//   `Diagnostics`, `UnavailableKind`, `Obligation`, `VisTrace`, `TriageOutcome`,
//   `ReplaySnapshot`, `ConfExhaustion`, `ConfNote`.
//
// What is **not** exported, deliberately: `Gate`, `ReportKind`, `Report`,
// `ConfCtx`, `Search`, `Cover`, `Wobs`, `Obs`, `Status`, `Offer` and every
// other engine-facing type. They are the internals the next steps will change.
// `ReportGate` is a *separate* five-variant type rather than
// `Option<ctx::Gate>` for that reason, and `Obligation`/`ReportCause` carry
// `String` positions rather than `Event`s so that no engine type crosses the
// boundary.
//
// Everything above is a semver commitment on a crate at 0.2.1. The
// enumerations are the risk: adding a `ReportGate` variant or a `ConfError`
// variant is a breaking change for a caller that matches exhaustively. They
// are left exhaustive rather than `#[non_exhaustive]` on purpose — the gate
// sites are §4.1's four plus "not a gate", and that list is a claim about the
// design rather than an implementation detail; if it grows, callers *should*
// be made to look.
// ---------------------------------------------------------------------------

pub use config::{ConfBuilder, ConfConfig, ConfigError, ScopeField, DEFAULT_SEARCH_BUDGET};
pub use report::{
    Certificate, ConfError, ConfExhaustion, ConfNote, ConfOutcome, ConfReport, ConfVerdict,
    Diagnostics, NotACertificate, Obligation, ReplaySnapshot,
    ReportCause, ReportGate, SearchEnd, SpecErrFreedom, TriageFailure, TriageOutcome,
    UnavailableKind, VisTrace,
};

use std::sync::Arc;

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
/// **It tests nine `Config` fields with seven assertion macros**, because two
/// of them cover two fields each (`!parallel && !partitioned_parallelization`,
/// and both predetermined maps). [`ConfBuilder::build`] enumerates the same
/// nine independently, and `s5_tests` diffs the two per *field* — a per-macro
/// diff would pass while `partitioned_parallelization` went unchecked at
/// config time, which is the failure criterion 7 names.
///
/// §5.4's precheck now calls this, with the engine name `"precheck"`.
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
/// §11.6's `vis(Impl) ⊆ vis(Spec)` oracle. **Test-only**: it is the ground
/// truth the differential harness measures the tool against, it is the naive
/// exponential algorithm the paper's algorithm exists to avoid, and nothing
/// in it is reachable from the public API (criterion 17).
#[cfg(test)]
pub(crate) mod oracle;
#[cfg(test)]
mod oracle_tests;
/// §11.6's differential harness: the tool against the oracle. **Test-only.**
#[cfg(test)]
pub(crate) mod differential;
/// §11.6's fragment program generator. **Test-only.**
#[cfg(test)]
pub(crate) mod generator;
#[cfg(test)]
mod differential_smoke;
#[cfg(test)]
mod paper_examples;
/// A guided demonstration of the draft's examples, one at a time. **Test-only.**
#[cfg(test)]
mod demo;
#[cfg(test)]
mod refinement_suite;
/// S7's benchmark: two-phase commit, and what conformance costs. **Test-only**;
/// the measurements are `#[ignore]`d because they are a table for a human.
#[cfg(test)]
mod bench;
#[cfg(test)]
mod gate_tests;
#[cfg(test)]
mod s5_harden;
#[cfg(test)]
mod s5_tests;
#[cfg(test)]
pub(crate) mod testing;

/// What a conformance run found, at the sink's level of detail.
///
/// The minimal sink's read side (§4.2, owner ruling 2026-09-12). [`verify`]
/// turns this into the reporting product; it deliberately renders nothing, and
/// S4's gate tests are written against it.
#[derive(Debug, Default)]
pub(crate) struct Outcome {
    pub(crate) reports: Vec<ctx::Report>,
    pub(crate) exhaustions: Vec<ctx::Exhaustion>,
    pub(crate) diagnostics: Vec<ctx::Diagnostic>,
    pub(crate) stats: Option<crate::Stats>,
    pub(crate) end: report::SearchEnd,
    /// How many gates F49's replay-frontier skip suppressed (review `P3-A16`).
    ///
    /// **A skipped gate is a check that did not happen.** A run with a non-zero
    /// count established "no gate *that ran* found a violation", which is
    /// weaker than refinement — so any figure derived from it must assert this
    /// is zero or state what it was. Same obligation F43 imposes for
    /// exhaustions.
    pub(crate) skipped_gates: usize,
    /// How many gates F42's inertness skip suppressed — a fresh event that
    /// changed nothing observable, so the gate's answer could not differ.
    pub(crate) inert_gates: usize,
}

/// Run `implementation` under conformance against `specification`, at the
/// sink's level of detail.
///
/// The engine half of [`verify`], kept separate because S4's gate tests are
/// written against it and because it is the piece with no post-processing: no
/// precheck, no diagnostics, no triage, no rendering.
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
    verify_conformance_with(
        config,
        Arc::new(implementation),
        Arc::new(specification),
        visible,
        budget,
        false,
    )
}

pub(crate) fn verify_conformance_with(
    config: crate::Config,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
    visible: Vec<String>,
    budget: usize,
    stop_at_first_report: bool,
) -> Outcome {
    use std::cell::RefCell;
    use std::rc::Rc;

    let ctx = ctx::ConfCtx::new(
        config.clone(),
        specification,
        visible,
        budget,
        stop_at_first_report,
    );
    let must = Rc::new(RefCell::new(crate::must::Must::new(config, false)));
    must.borrow_mut().enable_conformance(ctx);

    // `explore` is generic over a *sized* closure; the trait object is wrapped
    // rather than passed through.
    let f = Arc::new(move || implementation());
    crate::explore(&must, &f);

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
        end: conf.end(),
        skipped_gates: conf.skipped_gates(),
        inert_gates: conf.inert_gates(),
    }
}

/// **The public entry point** (§8).
///
/// Runs §5.4's specification err-freedom precheck (unless opted out), then the
/// outer conformance exploration, then — per report — the §7.1 diagnostics and
/// §7.3's triage if asked for. Returns a [`ConfVerdict`] whose "conforms" case is a certificate and
/// whose other cases say why they are not.
///
/// # Panics
///
/// On **invalid input**, deliberately and with a message naming the event:
///
/// - §8's visible-thread violations — a declared visible name spawned after
///   its program has communicated (`ctx.rs`), spawned twice, or (at a complete
///   execution) never spawned;
/// - §9's scope rejections, from either program — `inbox`, `sample`, a
///   `TotalOrder` send or receive, monitor registration, symmetric spawning, a
///   predetermined named choice, or symbolic evaluation.
///
/// A configuration outside §9's scope is refused earlier and more gently, by
/// [`ConfBuilder::build`], which returns a [`ConfigError`]. That layer is UX;
/// the panic is the guarantee.
///
/// # Threading
///
/// The whole run happens on a dedicated OS thread. Every engine conformance
/// uses installs a current-`Must` thread-local and a continuation pool, and
/// there are four of them — the outer run, the probe worker, the precheck and
/// each triage — so none of them may share a thread with a caller that is
/// itself inside an execution. A panic raised inside is re-raised on the
/// caller's thread with its original payload, so §8's and §9's messages arrive
/// as themselves rather than as a join error.
pub fn verify<I, S>(
    config: ConfConfig,
    implementation: I,
    specification: S,
) -> Result<ConfVerdict, ConfError>
where
    I: Fn() + Send + Sync + 'static,
    S: Fn() + Send + Sync + 'static,
{
    let implementation: Arc<dyn Fn() + Send + Sync> = Arc::new(implementation);
    let specification: Arc<dyn Fn() + Send + Sync> = Arc::new(specification);

    let handle = std::thread::Builder::new()
        .name("traceforge-conformance".to_owned())
        // The inner search recurses once per installed specification event and
        // the diagnostics recomputation does it again; the default 2 MiB is
        // enough for the fragment's scale but leaves no margin for a deep
        // `Budget`.
        .stack_size(32 * 1024 * 1024)
        .spawn(move || run(config, implementation, specification))
        .expect("conformance: could not spawn the conformance thread");

    match handle.join() {
        Ok(v) => v,
        // §8 and §9 raise *panics*, by ruling. Re-raise with the original
        // payload so the user reads the message naming the event rather than
        // "the conformance thread died".
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

fn run(
    cc: ConfConfig,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
) -> Result<ConfVerdict, ConfError> {
    use report::{Diagnostics, ReportGate, SpecErrFreedom};

    // -- §5.4 ------------------------------------------------------------
    let spec_errfree = if cc.skip_spec_errfree_check {
        SpecErrFreedom::Assumed
    } else {
        precheck::run(&cc, &specification)?;
        SpecErrFreedom::Checked
    };

    // -- the outer run ---------------------------------------------------
    let raw = verify_conformance_with(
        cc.config.clone(),
        Arc::clone(&implementation),
        Arc::clone(&specification),
        cc.visible.clone(),
        cc.search_budget,
        cc.stop_at_first_report,
    );

    // -- §7.1's diagnostics, §7.3's triage, §7.3's oracle ------------------
    let phi = diagnose::Recompute::new(
        cc.config.clone(),
        Arc::clone(&specification),
        cc.visible.clone(),
        cc.search_budget,
        true,
    );

    let mut reports = Vec::with_capacity(raw.reports.len());
    for (i, r) in raw.reports.iter().enumerate() {
        let gate = ReportGate::of(r.gate);
        let complete = diagnose::outer_complete(gate);
        // **One `match` on `r.kind`, producing both.** §7.1's diagnostics and
        // §7.3's oracle ask the same precondition — is there a `Cover` answer
        // here at all? — and at round 2 they asked it in two places, of which
        // the oracle's was missing (round 2, M1): on a §4.4 visible-error
        // report, where `Report.gate` is `None` and nothing was asked of the
        // specification, it printed "**disagreement** … Φ lost a cover" one
        // line below the tool's own "inner-search diagnostics do not apply".
        //
        // Round 2 fixed that and left a comment saying "one `match`" beside
        // two of them, which is the round-3 shape: a right fix with a wrong
        // sentence beside it. The real protection is now
        // `c10_a_visible_error_report_carries_no_inner_search_diagnostics`.
        //
        // **The `--naive-oracle` flag was deleted in S6** (night-run Poll 1,
        // criterion 17). F-17 established that `Recompute` and `Search::cover`
        // are two transcriptions of one algorithm, so their agreement carried
        // no information; and the outcome type it rendered would have become a
        // semver commitment the moment `pub mod conformance` shipped, on a
        // crate at 0.2.1. §11.6's `vis(Impl) ⊆ vis(Spec)` checker is this
        // project's first genuine oracle — it materialises word sets rather
        // than re-running the morphism — and it is test-only, in
        // `conformance::oracle`.
        //
        // The un-Φ traversal itself survives as `pub(crate)` test material,
        // which is what Poll 1 ruled: `diagnose::Recompute` is still what §7.1
        // uses, and only the *rendering* and the *flag* are gone.
        let diagnostics = match &r.kind {
            // A §4.4 report is a failed assertion, not a `Cover` answer.
            ctx::ReportKind::VisibleError { .. } => Diagnostics::NotApplicable,
            ctx::ReportKind::NoCover => phi.diagnose(&r.graph, complete),
        };

        // §7.1's serialized half was built at capture time, off the live
        // `Must` (round 1, M3): the sink carries the JSON, not a `MustState`.
        let mut out = report::build_report(
            &r.kind,
            r.gate,
            r.events,
            &r.graph,
            r.replay.clone(),
            diagnostics,
        );

        if cc.triage {
            match triage::triage_one(&cc, &implementation, &out, r.graph.clone()) {
                Ok(o) => out.triage = Some(o),
                // Not swallowed. A swallowed triage failure silently degrades
                // a report to its pre-triage form and nobody knows.
                Err(cause) => return Err(ConfError::TriageFailed { report: i, cause }),
            }
        }
        reports.push(out);
    }

    let exhaustions = raw
        .exhaustions
        .iter()
        .map(|e| ConfExhaustion {
            gate: ReportGate::of(Some(e.gate)),
            events: e.events,
            budget: cc.search_budget,
        })
        .collect();
    let notes = raw
        .diagnostics
        .iter()
        .map(|d| ConfNote::of(d.reason, d.thread.clone(), d.pos.to_string()))
        .collect();

    Ok(ConfVerdict::of(ConfOutcome {
        reports,
        exhaustions,
        notes,
        end: raw.end,
        spec_errfree,
        budget: cc.search_budget,
        triage_enabled: cc.triage,
    }))
}
