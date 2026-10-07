//! Conformance verification: does one program's visible behaviour refine
//! another's?
//!
//! The implementation and the specification are both ordinary TraceForge
//! programs. Two checkers are offered, chosen by [`Engine`]
//! (`ConfBuilder::engine`; the default is the enumerator):
//!
//! - **The directed enumerator** (`Engine::Enumerator`, paper §8.7). The
//!   implementation is explored by the stock Must engine; the specification is
//!   consulted through *probe* executions, which report what it could do next
//!   without committing to any of it. A search over specification graphs then
//!   tries those options, looking for one that matches what the implementation
//!   has done so far. It runs §5.4's precheck, the §7.1 diagnostics and §7.3's
//!   triage.
//! - **The stateful checker** (`Engine::Stateful`, paper §8.3, `P4-STATEFUL`).
//!   Both programs are enumerated in full by two gate-disabled runs: the
//!   specification's run builds an index of signatures and orders and *is* the
//!   §5.4 check (the opt-out has no effect), and the implementation's run looks
//!   each complete graph up in it. A report is an uncovered complete
//!   implementation graph, with no probe, no inner search, no diagnostics and
//!   no triage. `search_budget`, `inner_order` and `memo` are ignored.
//! - **The complete-first checker** (`Engine::CompleteFirst`, paper §8.5,
//!   `P4-CFIRST`). Must on the implementation, uncut, with §5.4's precheck
//!   run unbounded first (skippable); at each complete graph the witness cache
//!   `W` is probed and, on a miss, the specification is swept by Must on its
//!   own thread, unpruned, stopped at the first covering graph, which joins
//!   `W`. A report is an uncovered complete implementation graph (or, with
//!   `early_error_cut(true)`, a visible-error prefix — then the engine decides
//!   but does not enumerate, A27). No probe, no inner search, no diagnostics,
//!   no triage. `search_budget`, `inner_order` and `memo` are ignored.
//! - **The gated checker** (`Engine::Gated`, paper §8.6, `P4-GATED`). The
//!   complete-first checker plus a gate after every visible event of the
//!   implementation: the carried witness is re-tested by one `cone` test, and
//!   on a miss the policy (`GatePolicy`) decides whether to sweep the
//!   specification for a fresh witness or an absence certificate, which
//!   transfers to every extension and skips every gate and completion test
//!   below it. Exhaustive mode reports uncovered complete graphs
//!   (`thm:gated`); first-failure mode (`GatedMode`) reports the first gated
//!   partial graph with no match, or the first uncovered complete graph, and
//!   stops. `early_error_cut` is ignored.
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
//! # Writing a pair: both programs must be re-entrant
//!
//! **A program is re-executed from its entry point, many times, and must behave
//! the same way each time.** The engine explores by calling the program again and
//! replaying the prefix it has recorded — `lib.rs`'s
//! `loop { Execution::new(..); execution.run(|| f()) }` — and conformance does the
//! same to the *specification* once per inner-search node, which is far more
//! often: 372 246 probes in one `verify` run of the `ndk3` pair measured in F63.
//!
//! What replay restores is the **engine's** decisions: thread interleaving,
//! `nondet()`, and which send a receive reads from. All three live in the graph.
//! What it cannot restore is memory the program itself keeps — a captured atomic
//! or `static`, a clock, `rand`, a file — because those lines are ordinary Rust
//! and simply run again.
//!
//! So both programs must put **all** their nondeterminism through `nondet()` and
//! carry **no** state across executions.
//!
//! **Breaking it is detected sometimes and not others, which is the awkward part.**
//! The engine does validate replay — `ExecutionGraph::validate_replay_event` runs
//! `compare_for_replay`, and on a mismatch it panics with *"TraceForge programs
//! must be deterministic. Any nondeterminism should be under the control of
//! TraceForge via the nondet() function"*. But that comparison is partial:
//! `RecvMsg` returns `Ok` unconditionally, and a `SendMsg` value is compared only
//! when the recorded value is **not pending** (`event_label.rs:194`). So a
//! divergence can be caught loudly, and can also pass unnoticed — detection is not
//! something to rely on.
//!
//! `traceforge/tests/f72_stateful_program.rs` (on `fix/f72-contract`) exhibits the
//! silent side: a captured counter reads `0` then `1` across two executions, and a
//! program whose *pending* send value depends on it completes normally with no
//! diagnostic. Backlog **F72**; the same account belongs on [`crate::verify`],
//! which is an upstream change.
//!
//! # Writing a pair: do not send a `ThreadId` a visible thread will observe
//!
//! A `ThreadId` is an opaque number allocated **per program in spawn order**.
//! The implementation and the specification are different programs, and a
//! specification normally spawns fewer invisible threads — that is what the
//! abstraction is. So the same logical thread holds a different number on the
//! two sides:
//!
//! ```text
//! implementation            specification
//!   1  logger    (hidden)     1  coordinator (hidden)
//!   2  coordinator (hidden)   2  participant (visible)
//!   3  participant (visible)
//! ```
//!
//! §6.1 matches a visible thread's observations **by value**. If the
//! participant receives `Prepare(coordinator_id)`, the implementation observes
//! `2` and the specification `1`, so every such observation mismatches and the
//! run reports a candidate violation although the two programs agree.
//!
//! **Nothing detects this for you**, and the reason is in the message trait.
//! [`crate::Message`] is `Send + DynClone`, plus whichever formatting trait the
//! selected feature adds: `Debug` under the default `print_vals`, `Display`
//! under `print_vals_custom`, neither under `--no-default-features`. The blanket
//! implementation asks a user type for **more**, and for something different in
//! each of the three configurations: `Send + PartialEq + DynClone + 'static`
//! throughout, plus `Debug` with no feature (`msg.rs:129`) and under
//! `print_vals` (`:134`), but `Display` under `print_vals_custom` (`:147`).
//! `PartialEq` is the bound §6.1's by-value matching rests on and is demanded
//! everywhere; the formatting bound is not, so nothing here may assume `Debug`
//! without naming the feature. Note the feature-free arm asks for `Debug` while
//! its trait adds no formatting supertrait at all — part of why that build does
//! not compile. There is no `Serialize` and no
//! reflection, so what conformance holds — a `Val`, a `Box<dyn Message>` beside
//! a type name — can be inspected in exactly two ways: compared against another
//! value of a type the caller already names, by downcast; or rendered, and only
//! because a feature supplied a formatting trait. Neither lets it walk a
//! message's fields looking for an id.
//!
//! Two ways to write such a protocol so that it works:
//!
//! 1. **Send the name, not the id** — as an **owned** value.
//!    [`crate::thread::Thread::name`] gives the declared name, and a name —
//!    unlike an id — is chosen by the author rather than allocated by the
//!    runtime, so the same string can appear on both sides and a message
//!    carrying it compares equal by construction. It returns `Option<&str>`,
//!    which borrows the handle, and [`crate::send_msg`] takes
//!    `T: Message + 'static`, so the borrowed form **cannot be sent as it
//!    stands**: copy it out.
//!
//!    ```text
//!    // One literal, named by both programs, sent as an owned `String`.
//!    const COORD: &str = "coordinator";
//!
//!    let coord = traceforge::thread::Builder::new()
//!        .name(COORD.to_owned())
//!        .spawn(coordinator)?;
//!    traceforge::send_msg(participant, Prepare(COORD.to_owned()));
//!
//!    // Or read it back off the handle, remembering that it borrows:
//!    //   let who: Option<String> = coord.thread().name().map(str::to_owned);
//!    ``` For
//!    *visible* threads the sharing is automatic: one `visible_threads` list on
//!    [`ConfConfig`] names the visible threads of both programs, so a visible
//!    name is shared or the pair does not run at all.
//!
//!    **The thread whose id travels is usually not one of those** — in the
//!    table above it is the coordinator, hidden on both sides — and for it the
//!    sharing is a discipline, not a guarantee: `name` returns
//!    `Option<&str>`, and nothing requires an invisible thread to be named, or
//!    to be named the same on the two sides. **Still prefer this**, for a
//!    reason that is not strength but visibility: what it couples is two
//!    string literals in the spawn prologues, which a reader comparing the two
//!    programs can see, where option 2 couples their spawn *orders*, which
//!    nothing on the page shows.
//! 2. **Align the spawn order** of every thread whose id is observed, so that
//!    it occupies the same position on both sides and therefore has the same
//!    number. This is what `bench.rs`'s two-phase-commit pair does, by spawning
//!    the coordinator first on both sides.
//!
//!    **The discipline that makes it work: every spawn before the observed
//!    thread is unconditional.** That is *sufficient*, and it is the version
//!    worth holding, because it is the one a reader can check by eye. Within it
//!    the numbering is deterministic — measured identical across executions,
//!    across revisits and across separate runs — so equal positions give equal
//!    ids.
//!
//!    It is not *necessary*. An id is `max(existing)+1` within the **current**
//!    graph, so a thread spawned under a `nondet()` shifts the numbering of
//!    everything after it *between executions of one program*: one program then
//!    produces two different observed values for one behaviour. That is fatal
//!    only if the other program cannot produce both — a specification mirroring
//!    the same conditional structure admits a matching execution for each, and
//!    the pair can still verify. What fails is *positional* alignment across
//!    programs whose conditional spawn behaviour differs.
//!
//!    Prefer the unconditional form anyway. Aligned conditional structure is a
//!    property of two programs' branch behaviour that nothing checks and no
//!    error message names, where unconditional prologues are two lists a reader
//!    can compare — and this option is already the fragile one, since a single
//!    hidden thread added in the wrong place breaks it silently.
//!
//! Neither is needed for a thread's *own* identity: an observation's thread is
//! recorded by declared name, not by id (see `obs.rs`). This is only about ids
//! travelling **inside message values**.
//!
//! If it goes wrong anyway, the report says so: an `(M1)` mismatch either of
//! whose rendered values mentions `ThreadId` carries a note that restates the
//! per-program numbering and both remedies inline. It names no section — a
//! report is read without the source at hand — so this section and that note
//! have to be kept in agreement by whoever changes either.
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

pub(crate) mod canon;
pub(crate) mod cert;
pub(crate) mod cfirst;
pub(crate) mod config;
pub(crate) mod ctx;
pub(crate) mod diagnose;
pub(crate) mod flat;
pub(crate) mod gated;
pub(crate) mod morphism;
pub(crate) mod obs;
pub(crate) mod precheck;
pub(crate) mod probe;
pub(crate) mod prober;
pub(crate) mod report;
pub(crate) mod search;
pub(crate) mod selector;
pub(crate) mod sig;
pub(crate) mod stateful;
pub(crate) mod triage;
pub(crate) mod witness;

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
//   `ConfConfig`, `ConfigError`, `ScopeField`, `DEFAULT_SEARCH_BUDGET`, and
//   the two selector knobs `Selector` (knob A, the Must selector) and
//   `InnerOrder` (knob B, the inner offer order) of `P4-SELECTOR`. A caller
//   cannot use conformance without these.
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
// be made to look. `Selector` and `InnerOrder` follow the same policy: their
// variants are the plan's selector list and knob-B policy list (§3, §6), and a
// new one is a design change a matching caller should see. So do `ReportTag`
// (the three certificates of plan §6), the `SearchEnd::SpecNotAssertionSafe`
// and `ConfError::SpecNotAssertionSafe` variants (`P4-ENUMERATOR` criterion 9);
// `ConfCounters` and `CoverCounters` are plain public records (criterion 13),
// and `ReportTag::certifies` is the rendering text of criterion 6. `Engine`
// (`P4-STATEFUL` T6) is exhaustive, complete since Part 5 (CompleteFirst and
// Gated were its announced later additions); `Diagnostics::NotProduced` is its arm;
// `StatefulCounters` is a plain public record (criterion 8).
//
// **Counters' "explored complete graphs" (criterion 13).** The engine does
// not decide paper-completeness of a growing report graph (an implementation
// probe from it would: complete iff nothing parks), so `ConfCounters` exposes
// the completion-captured keys and the report keys **by gate** separately, and
// a consumer forms the union with the predicate stated in the criteria.
// ---------------------------------------------------------------------------

pub use config::{
    CompletionCover, ConfBuilder, ConfConfig, ConfigError, Engine, GatePolicy, GatedMode,
    ScopeField, DEFAULT_SEARCH_BUDGET,
};
pub use report::{
    CFirstCounters, Certificate, ConfCounters, ConfError, ConfExhaustion, ConfNote, ConfOutcome,
    ConfReport, ConfVerdict, CoverCounters, Diagnostics, FlatCounters, FlatEligibility,
    GatedCounters, NotACertificate,
    Obligation, ReplaySnapshot, ReportCause, ReportGate, ReportTag, SearchEnd, SpecErrFreedom,
    StatefulCounters, TriageFailure, TriageOutcome, UnavailableKind, VisTrace,
};
pub use selector::{InnerOrder, Selector};

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
#[cfg(test)]
mod apparatus_tests;
/// S7's benchmark: two-phase commit, and what conformance costs. **Test-only**;
/// the measurements are `#[ignore]`d because they are a table for a human.
#[cfg(test)]
mod bench;
#[cfg(test)]
mod cfirst_tests;
/// A guided demonstration of the draft's examples, one at a time. **Test-only.**
#[cfg(test)]
mod demo;
/// §11.6's differential harness: the tool against the oracle. **Test-only.**
#[cfg(test)]
pub(crate) mod differential;
#[cfg(test)]
mod differential_smoke;
#[cfg(test)]
mod enumerator_tests;
#[cfg(test)]
mod gate_tests;
#[cfg(test)]
mod gated_tests;
/// §11.6's fragment program generator. **Test-only.**
#[cfg(test)]
pub(crate) mod generator;
/// P4-DIFF's grid (plan §6): the fixture registry, the per-configuration
/// runner and the table writer (lead); the oracle and the tests are the
/// tester's `grid_oracle.rs`/`grid_tests.rs`. **Test-only.**
#[cfg(test)]
mod grid;
#[cfg(test)]
mod grid_oracle;
#[cfg(test)]
mod grid_tests;
#[cfg(test)]
mod mixed_tests;
#[cfg(test)]
mod flat_tests;
/// §11.6's `vis(Impl) ⊆ vis(Spec)` oracle. **Test-only**: it is the ground
/// truth the differential harness measures the tool against, it is the naive
/// exponential algorithm the paper's algorithm exists to avoid, and nothing
/// in it is reachable from the public API (criterion 17).
#[cfg(test)]
pub(crate) mod oracle;
#[cfg(test)]
mod oracle_tests;
#[cfg(test)]
mod paper_examples;
#[cfg(test)]
mod refinement_suite;
#[cfg(test)]
mod s5_harden;
#[cfg(test)]
mod s5_tests;
#[cfg(test)]
mod selector_tests;
#[cfg(test)]
mod stateful_baseline;
#[cfg(test)]
mod stateful_tests;
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
    /// The random seed the outer engine used (F61). Any figure derived from a
    /// program that calls `nondet()` depends on it; print it with the figure.
    pub(crate) seed: u64,
    /// How many gates F42's inertness skip suppressed — a fresh event that
    /// changed nothing observable, so the gate's answer could not differ.
    pub(crate) inert_gates: usize,
    /// `P4-ENUMERATOR` criterion 9: the inner search aborted on a
    /// specification assertion. **An engine-only consumer checks this first**,
    /// ahead of `reports` and `end`: the run was abandoned at that gate, and
    /// what it recorded before is not a verdict about anything.
    pub(crate) spec_error: Option<(String, crate::event::Event)>,
    /// Criterion 13.
    pub(crate) counters: report::ConfCounters,
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
    verify_conformance_with_order(
        config,
        implementation,
        specification,
        visible,
        budget,
        stop_at_first_report,
        InnerOrder::Recorded,
    )
}

/// [`verify_conformance_with`] carrying knob B (`P4-SELECTOR` S3, route (a));
/// the signature-stable function above delegates here with `Recorded`.
pub(crate) fn verify_conformance_with_order(
    config: crate::Config,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
    visible: Vec<String>,
    budget: usize,
    stop_at_first_report: bool,
    inner_order: InnerOrder,
) -> Outcome {
    verify_conformance_with_opts(
        config,
        implementation,
        specification,
        visible,
        budget,
        stop_at_first_report,
        search::SearchOpts {
            inner_order,
            ..search::SearchOpts::default()
        },
    )
}

/// [`verify_conformance_with_order`] carrying every inner-search option
/// (`P4-ENUMERATOR` criterion 4, route (a)); the signature-stable functions
/// above delegate here.
pub(crate) fn verify_conformance_with_opts(
    config: crate::Config,
    implementation: Arc<dyn Fn() + Send + Sync>,
    specification: Arc<dyn Fn() + Send + Sync>,
    visible: Vec<String>,
    budget: usize,
    stop_at_first_report: bool,
    opts: search::SearchOpts,
) -> Outcome {
    use std::cell::RefCell;
    use std::rc::Rc;

    let started = std::time::Instant::now();
    let seed = config.seed;
    let ctx = ctx::ConfCtx::new_with_opts(
        config.clone(),
        specification,
        visible,
        budget,
        stop_at_first_report,
        opts,
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
    let mut counters = conf.counters().clone();
    counters.wall_time_ms = started.elapsed().as_millis();
    Outcome {
        reports: conf.reports().to_vec(),
        exhaustions: conf.exhaustions().to_vec(),
        diagnostics: conf.diagnostics().to_vec(),
        stats: Some(must.stats()),
        end: conf.end(),
        skipped_gates: conf.skipped_gates(),
        inert_gates: conf.inert_gates(),
        seed,
        spec_error: conf.spec_error().cloned(),
        counters,
    }
}

/// **The public entry point** (§8).
///
/// Under the default [`Engine::Enumerator`]: runs §5.4's specification
/// err-freedom precheck (unless opted out), then the outer conformance
/// exploration, then — per report — the §7.1 diagnostics and §7.3's triage if
/// asked for. Under [`Engine::Stateful`]: two full enumerations, the
/// specification's doubling as the §5.4 check, with none of the per-report
/// steps. Under [`Engine::CompleteFirst`]: the unbounded precheck, then
/// Must on the implementation with a witness-cache probe and a sweep of the
/// specification at each complete graph, again with none of the per-report
/// steps. Under [`Engine::Gated`]: the same, plus a gate at every visible
/// event (see the module doc). Returns a [`ConfVerdict`] whose "conforms" case
/// is a certificate and whose other cases say why they are not.
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
/// there are four of them under the enumerator — the outer run, the probe
/// worker, the precheck and each triage — two under the stateful checker
/// — the specification's and the implementation's enumeration — and, under
/// the complete-first and gated checkers, the precheck, the outer run and one
/// scoped thread per sweep — so none of them may share a thread with a caller that is
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

    // `P4-FLAT` F5: `FlatCover` serves the complete-first and gated engines only.
    if cc.completion_cover == config::CompletionCover::Flat
        && matches!(cc.engine, Engine::Enumerator | Engine::Stateful)
    {
        return Err(ConfError::KnobConflict {
            knob: "completion_cover(Flat)",
            conflicts_with: "engine(Enumerator | Stateful)",
        });
    }

    // `P4-STATEFUL` T4/T6: the stateful engine is its own §5.4 check and has
    // no inner search, diagnostics or triage; it leaves here.
    if cc.engine == Engine::Stateful {
        return stateful::run(cc, implementation, specification);
    }
    // `P4-CFIRST` C4/C7: its own (unbounded) precheck, no inner search,
    // diagnostics or triage; it leaves here.
    if cc.engine == Engine::CompleteFirst {
        return cfirst::run(cc, implementation, specification);
    }
    // `P4-GATED` G5/G6: likewise.
    if cc.engine == Engine::Gated {
        return gated::run(cc, implementation, specification);
    }

    // -- §5.4 ------------------------------------------------------------
    let spec_errfree = if cc.skip_spec_errfree_check {
        SpecErrFreedom::Assumed
    } else {
        let _ = precheck::run(&cc, &specification)?;
        SpecErrFreedom::Checked
    };

    // -- the outer run ---------------------------------------------------
    let raw = verify_conformance_with_opts(
        cc.config.clone(),
        Arc::clone(&implementation),
        Arc::clone(&specification),
        cc.visible.clone(),
        cc.search_budget,
        cc.stop_at_first_report,
        search::SearchOpts {
            inner_order: cc.inner_order.clone(),
            memo: cc.memo,
            instrument: false,
        },
    );

    // `P4-ENUMERATOR` criterion 9: the inner search found the specification
    // not assertion-safe. The run was abandoned at that gate; nothing it
    // recorded is a verdict, so this leaves before the diagnostics loop and
    // before any `ConfOutcome` is built.
    if let Some((thread, pos)) = raw.spec_error {
        return Err(ConfError::SpecNotAssertionSafe {
            thread,
            pos: pos.to_string(),
        });
    }

    // -- §7.1's diagnostics, §7.3's triage, §7.3's oracle ------------------
    let phi = diagnose::Recompute::new(
        cc.config.clone(),
        Arc::clone(&specification),
        cc.visible.clone(),
        cc.search_budget,
        true,
    )
    .with_inner_order(cc.inner_order.clone())
    .with_memo(cc.memo);

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
        seed: cc.config.seed,
        counters: raw.counters,
        engine: Engine::Enumerator,
        stateful_counters: None,
        cfirst_counters: None,
        gated_counters: None,
        flat_counters: None,
        flat_eligibility: None,
    }))
}
