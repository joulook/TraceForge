//! What a conformance run says, and **the only place it says anything**.
//!
//! `conf-plan.md` §7.1–§7.2. Two jobs, deliberately in one file:
//!
//! 1. the result types — [`ConfVerdict`], [`ConfReport`], [`ConfExhaustion`],
//!    [`ConfNote`], [`ConfError`];
//! 2. every `Display` that turns one of them into text a user reads.
//!
//! **Criterion 1's rule, and why it is a rule rather than a preference.** The
//! criterion the step is judged on is that a report does not claim more than
//! §7.2 licenses — and §7.2's licence is narrow: `Cover(G₁,·) = ⊥` certifies
//! that no complete specification graph covers any *event-extension of the
//! reported graph*, modulo the draft's own lemmas, and certifies **nothing**
//! about whether the report list is complete. Those are two different claims
//! and CA §7's own text conflates them. A negative universal over every
//! string the tool can emit is not checkable, so the obligation is made
//! structural instead: **every user-facing string is produced here**, and the
//! check is a grep over `conformance/**` for emission outside this file
//! against a written allowlist — `c1_no_user_facing_emission_outside_the_rendering_module`
//! and `c1_every_panic_message_under_conformance_names_its_engine` in
//! `s5_tests`.
//!
//! That is why nothing else in this module tree has a `Display` impl or a
//! `println!` — and why the two that predate S5 are disposed of by name in
//! the test rather than left to a reader's judgement.

use std::fmt;

use crate::conformance::config::{Engine, ScopeField, DEFAULT_SEARCH_BUDGET};
use crate::conformance::ctx::{DiagnosticReason, Gate, ReportKind};
use crate::exec_graph::ExecutionGraph;

// ---------------------------------------------------------------------------
// The qualifying clauses, as constants.
//
// Criterion 1's snapshot tests pin these by name. A wording regression then
// fails a test instead of shipping, which is the whole point: the previous
// form of this criterion was "no output may say 'violation found'
// unqualified", a negative universal a developer cannot know they have
// satisfied.
// ---------------------------------------------------------------------------

/// What a report is called. Never "violation", never "bug".
pub(crate) const CANDIDATE_VIOLATION: &str = "candidate violation";

/// §7.2 / backlog A1. **Non-exhaustiveness**: about the *list*.
pub(crate) const NOT_A_COMPLETE_SET: &str =
    "This list is not a complete set of violations: a lost backward revisit can suppress \
     other reports, and how often is unmeasured (backlog A1).";

/// CA §7, Theorem alg.
pub(crate) const ONLY_SILENCE_IS_A_VERDICT: &str =
    "Only silence is a verdict: a run that produced no report, hit no search budget and \
     reached the end of its state space is the certificate, and nothing else is.";

/// §7.2's residual, both named sources.
pub(crate) const RESIDUAL_SOURCES: &str =
    "\"Candidate\" has two named sources: (i) single-cover is sufficient but not necessary \
     for trace inclusion, so a union of specification graphs may still cover these traces; \
     (ii) the lemmas this rests on carry the open A4 transport gap.";

/// §7.2's settled half. **About the reported graph's own event-extensions.**
pub(crate) const SETTLED_CLAIM: &str =
    "What this report establishes (Lemma gate, modulo the draft's own lemmas): no complete \
     specification graph covers any event-extension of the reported graph.";

/// §7.2's unsettled half, kept a separate sentence with a different subject.
///
/// CA §7 conflates the two; §7.2 records the conflation and corrects it. The
/// tool must not repeat the conflation its own design document corrects, and
/// with these two constants that is checkable by reading two fixed strings.
pub(crate) const UNSETTLED_CLAIM: &str =
    "What this report does not establish, which is a different claim about a different \
     thing: that the report list is complete.";

/// The knob an exhaustion must name (criterion 2).
pub(crate) const BUDGET_KNOB: &str = "ConfBuilder::search_budget";

/// `P4-STATEFUL` T6: true of every stateful report, on every run — it is
/// `alg:stateful`'s lookup (`I[sig(G)]`), which needs only a complete index.
pub(crate) const STATEFUL_EACH_UNCOVERED: &str =
    "Every graph in this list is an uncovered complete graph of the implementation: each \
     was looked up in an index of every specification graph, and either no specification \
     graph has its signature or no order stored under its signature is contained in its \
     own (lem:sig).";

/// `P4-STATEFUL` T6: `thm:stateful`'s "exactly", printed only when both
/// enumerations completed (`end == StateSpaceExhausted`).
pub(crate) const STATEFUL_EXACTLY_THE_SET: &str =
    "The list is exactly the set of such graphs (thm:stateful): both enumerations reached \
     the end of their state spaces.";

/// `P4-CFIRST` C7: true of every complete-first completion report, on every
/// run — it is `alg:cfirst`'s `Covered`, which needs only an exhaustive
/// failing sweep (asserted by the engine).
pub(crate) const CFIRST_EACH_UNCOVERED: &str =
    "Every complete graph in this list is an uncovered complete graph of the \
     implementation: at its completion no cached witness covered it, and an unpruned \
     sweep of the specification found no graph with its signature whose order is \
     contained in its own (lem:sig).";

/// `P4-CFIRST` C7: `thm:cfirst`'s "exactly", printed only when the outer run
/// completed and no early-error cut fired (A27: with a cut the engine decides,
/// it does not enumerate).
pub(crate) const CFIRST_EXACTLY_THE_SET: &str =
    "The list is exactly the set of such graphs (thm:cfirst): the outer exploration \
     reached the end of its state space, no early-error cut fired, and every failing \
     sweep reached the end of the specification's.";

/// `P4-GATED` G6: true of every exhaustive-mode gated report, on every run.
pub(crate) const GATED_EACH_UNCOVERED: &str =
    "Every graph in this list is an uncovered complete graph of the implementation: it \
     was reported under an absence certificate set at a gate above it (cor:absence), or \
     no cached witness covered it and an unpruned sweep of the specification found none \
     (lem:sig).";

/// `P4-GATED` G6: `thm:gated`'s "exactly", exhaustive mode, printed only when
/// the outer run completed.
pub(crate) const GATED_EXACTLY_THE_SET: &str =
    "The list is exactly the set of such graphs (thm:gated, exhaustive mode): the outer \
     exploration reached the end of its state space and every failing sweep reached the \
     end of the specification's.";

/// `P4-GATED` G6: the first-failure report's sentence.
pub(crate) const GATED_FIRST_FAILURE: &str =
    "This run was gated in first-failure mode and stopped at its first report (thm:gated): \
     the reported graph is either a partial implementation graph with a completion, every \
     completion of every extension of which is uncovered (cor:absence), or a complete \
     graph that no specification graph covers (lem:sig).";

// `P4-FLAT` criterion 8: the `Flat` variants, selected by
// `ConfOutcome::flat_counters.is_some()`; the `Sweep` texts above are
// byte-identical to Parts 4–5's.
pub(crate) const CFIRST_EACH_UNCOVERED_FLAT: &str =
    "Every complete graph in this list is an uncovered complete graph of the \
     implementation: at its completion no cached witness covered it, and `FlatCover` \
     found no covering graph (thm:flat).";

pub(crate) const CFIRST_EXACTLY_THE_SET_FLAT: &str =
    "The list is exactly the set of such graphs (thm:cfirst): the outer exploration \
     reached the end of its state space, no early-error cut fired, and `FlatCover` is \
     exact for this communication-flat specification (thm:flat, cor:mixedflat).";

pub(crate) const GATED_EACH_UNCOVERED_FLAT: &str =
    "Every graph in this list is an uncovered complete graph of the implementation: it \
     was reported under an absence certificate set at a gate above it (cor:absence), or \
     no cached witness covered it and `FlatCover` found no covering graph (thm:flat).";

pub(crate) const GATED_EXACTLY_THE_SET_FLAT: &str =
    "The list is exactly the set of such graphs (thm:gated, exhaustive mode): the outer \
     exploration reached the end of its state space, every failing gate sweep reached the \
     end of the specification's, and `FlatCover` is exact for this communication-flat \
     specification (thm:flat, cor:mixedflat).";

pub(crate) const GATED_FIRST_FAILURE_FLAT: &str =
    "This run was gated in first-failure mode and stopped at its first report (thm:gated): \
     the reported graph is either a partial implementation graph with a completion, every \
     completion of every extension of which is uncovered (cor:absence), or a complete \
     graph that no specification graph covers (thm:flat).";

/// `P4-CFIRST` C7: printed whenever a cut report is present.
pub(crate) const CFIRST_CUT_PREFIXES: &str =
    "Reports raised by the early-error cut are prefixes of the implementation: every \
     completion of every extension of each is uncovered (the certificate of \u{a7}8.1); \
     the cut skips the subtree below each, which may contain other uncovered graphs \
     that are not listed.";

// ---------------------------------------------------------------------------
// Report content (§7.1)
// ---------------------------------------------------------------------------

/// Where a report was raised — **five** rendering cases, not four.
///
/// §7.1's prose names four items, and that is not the source's enumeration
/// (round 3, M6). The discriminator is `Report.gate: Option<Gate>` paired with
/// `Report.kind`: `Gate` has four variants, so §7.1's "fresh add" is two of
/// them, and "visible error" is not a gate at all — `Report.gate` is `None`
/// there, and hard-coding it to `Completion` was S4's F-E defect.
///
/// A renderer built from §7.1's four names would print `FreshSend` and
/// `FreshRecv` identically — losing what `Report.gate`'s own rustdoc calls
/// "the first thing anyone debugging a conformance failure wants" — and would
/// have no branch at all for `NotAGate`, which is *every* §4.4 report.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReportGate {
    FreshSend,
    FreshRecv,
    RevisitApply,
    Completion,
    /// Not a gate firing. A visible thread's assertion failed (§4.4), which
    /// can happen at any point in an execution.
    NotAGate,
}

impl ReportGate {
    pub(crate) fn of(gate: Option<Gate>) -> Self {
        match gate {
            Some(Gate::FreshSend) => ReportGate::FreshSend,
            Some(Gate::FreshRecv) => ReportGate::FreshRecv,
            Some(Gate::RevisitApply) => ReportGate::RevisitApply,
            Some(Gate::Completion) => ReportGate::Completion,
            None => ReportGate::NotAGate,
        }
    }

    /// One sentence per case. Five arms; the compiler enforces that.
    fn site(self) -> &'static str {
        match self {
            ReportGate::FreshSend => {
                "the fresh-send gate — the tail of `handle_send`, after the send was \
                 installed and its revisits computed"
            }
            ReportGate::FreshRecv => {
                "the fresh-receive gate — `visit_rfs`, after the canonical rf (or \u{22a5}) \
                 was installed"
            }
            ReportGate::RevisitApply => {
                "the revisit-apply gate — `try_revisit`, after a popped alternative was \
                 applied"
            }
            ReportGate::Completion => {
                "the completion gate — the execution had ended, so the implementation \
                 graph was complete"
            }
            ReportGate::NotAGate => {
                "no gate: a declared visible thread's assertion failed (\u{a7}4.4), which is \
                 not a gate firing and can happen at any point in an execution"
            }
        }
    }
}

/// Why a report was raised.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReportCause {
    /// The draft's \u{22a5}: no specification graph covers this implementation
    /// graph. `Cover` established it; the search did not merely run out of
    /// room.
    NoCover,
    /// §4.4: a declared visible thread failed an assertion.
    VisibleError { thread: String, pos: String },
}

/// **The semantic tag**: which certificate this engine established for the
/// report (`P4-ENUMERATOR` criteria 5–6; plan §4.4, §5.2, §6). The call-site
/// tag is [`ReportGate`]; this one is a function of (cause, gate), stated once
/// in [`ReportTag::of`].
///
/// It records the certificate **this engine** established, not the paper's
/// line: a complete graph reported at a growing gate is tagged
/// `GrowingExhaustion`, because the positional `Done` flag made that gate check
/// matching and `cor:absence` certifies it; the paper's `ln:stepreport` would
/// certify the same graph through `lem:coverexact`(2). Both are correct, and
/// Part 6 certifies each report by **its tag's** certificate rather than
/// requiring tag equality across engines on complete graphs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReportTag {
    /// No partial graph of Spec matches the reported graph, so every
    /// completion of every extension of it is uncovered (`cor:absence`).
    GrowingExhaustion,
    /// No graph of Spec covers the reported complete graph
    /// (`lem:coverexact`(2)).
    CompleteCoverage,
    /// A visible thread errored, so (M3) fails against every graph of Spec
    /// (§8.1). Never checked by C1-absence: the empty graph matches.
    VisibleError,
}

impl ReportTag {
    /// The correspondence, stated once. Two combinations cannot occur: a
    /// `NoCover` is always a gate firing, and a `VisibleError` never is
    /// (`report_visible_error` carries `gate: None`).
    pub(crate) fn of(cause: &ReportCause, gate: ReportGate) -> Self {
        match (cause, gate) {
            (ReportCause::VisibleError { .. }, ReportGate::NotAGate) => ReportTag::VisibleError,
            (ReportCause::NoCover, ReportGate::Completion) => ReportTag::CompleteCoverage,
            (
                ReportCause::NoCover,
                ReportGate::FreshSend | ReportGate::FreshRecv | ReportGate::RevisitApply,
            ) => ReportTag::GrowingExhaustion,
            (ReportCause::NoCover, ReportGate::NotAGate) => {
                unreachable!("conformance: a NoCover report with no gate")
            }
            (ReportCause::VisibleError { .. }, _) => {
                unreachable!("conformance: a VisibleError report at a gate")
            }
        }
    }

    /// `P4-FLAT` criterion 8: the per-report text of a `CompleteCoverage`
    /// report whose completion decision was `FlatCover`'s — `certifies_under`'s
    /// text with its sweep clause substituted, the leading clause verbatim. On
    /// any other engine or tag it is `certifies_under`'s text.
    pub(crate) fn certifies_flat(self, engine: Engine) -> &'static str {
        match (engine, self) {
            (Engine::CompleteFirst, ReportTag::CompleteCoverage) => {
                "no graph of the specification covers the reported complete graph: no cached \
                 witness did, and `FlatCover` found no covering graph of this \
                 communication-flat specification (thm:flat, cor:mixedflat, thm:cfirst)"
            }
            (Engine::Gated, ReportTag::CompleteCoverage) => {
                "no graph of the specification covers the reported complete graph: it was \
                 reported under an absence certificate set at a gate above it (cor:absence), \
                 or no cached witness covered it and `FlatCover` found no covering graph of \
                 it (thm:flat, cor:mixedflat, thm:gated)"
            }
            _ => self.certifies_under(engine),
        }
    }

    /// What the tag certifies under a given engine (`P4-STATEFUL` T6).
    ///
    /// For [`Engine::Enumerator`] this is [`ReportTag::certifies`]. The
    /// stateful engine produces only `CompleteCoverage`, whose certificate it
    /// states in its own terms; for the two tags it never produces the
    /// enumerator's text is returned (a tag's certificate does not depend on
    /// which engine is asked). Never panics.
    pub fn certifies_under(self, engine: Engine) -> &'static str {
        match (engine, self) {
            (Engine::Stateful, ReportTag::CompleteCoverage) => {
                "no graph of the specification covers the reported complete graph: its \
                 signature has no slot in the index, or no order in the slot is contained in \
                 the graph's (lem:sig, thm:stateful)"
            }
            // `P4-CFIRST` C7; `VisibleError` (the cut) and `GrowingExhaustion`
            // (never produced) take the enumerator's text.
            (Engine::CompleteFirst, ReportTag::CompleteCoverage) => {
                "no graph of the specification covers the reported complete graph: no cached \
                 witness did, and an exhaustive unpruned sweep of the specification found \
                 none (lem:sig, thm:cfirst)"
            }
            // `P4-GATED` G6; `GrowingExhaustion` (a first-failure gate report)
            // and `VisibleError` (never produced) take the enumerator's text.
            (Engine::Gated, ReportTag::CompleteCoverage) => {
                "no graph of the specification covers the reported complete graph: it was \
                 reported under an absence certificate set at a gate above it (cor:absence), \
                 or no cached witness and no graph of an exhaustive unpruned sweep covered \
                 it (lem:sig, thm:gated)"
            }
            _ => self.certifies(),
        }
    }

    /// What the tag certifies, in the paper's terms (criterion 6), for the
    /// enumerator.
    pub fn certifies(self) -> &'static str {
        match self {
            ReportTag::GrowingExhaustion => {
                "no partial graph of the specification matches the reported graph, so every \
                 completion of every extension of it is uncovered (cor:absence)"
            }
            ReportTag::CompleteCoverage => {
                "no graph of the specification covers the reported complete graph \
                 (lem:coverexact (2))"
            }
            ReportTag::VisibleError => {
                "a visible thread errored, so the status vector fails against every graph of \
                 the specification (\u{a7}8.1); this is not a C1-absence claim"
            }
        }
    }
}

/// §7.1's inner-search diagnostics: which failed attempt got furthest, and
/// what stopped it.
///
/// **Recomputed outside the search** (blocked item D's ruling). §7.1 says the
/// diagnostics "do not influence the search"; recomputing makes that trivially
/// and permanently true, where an accumulator threaded through
/// `spec_visit`/`spec_step`/`phi` would have to be proved write-only across
/// backtracking and clone points. The cost is that a reconstruction can
/// disagree with what the search actually did, which is why [`Self::
/// Unavailable`] exists and why the recomputation refuses to guess.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Diagnostics {
    /// The recomputation reproduced the search's own verdict.
    Available {
        /// The per-visible-thread observation-count vector the canonically
        /// chosen failed attempt reached, in the declared order.
        prefix: Vec<(String, usize)>,
        obligation: Obligation,
    },
    /// No obligation is named. **Two unlike reasons**, kept apart because
    /// the rendering used to assert the first of them unconditionally and was
    /// therefore false for the second — B1's own shape, one layer up
    /// (developer's B1-fix pass, F-B1b).
    ///
    /// `Diverged` is the original: the recomputation did not reproduce the
    /// search's verdict, so it refuses to guess. `blame_for` cost S4 two
    /// rounds to learn that.
    ///
    /// `NoValueForIt` is the case §7.1 cannot express — the morphism holds on
    /// the furthest-following attempt and no extension of it covers. The
    /// recomputation agreed with the search perfectly; the *enumeration* is
    /// what falls short, which is **A14**.
    Unavailable {
        because: String,
        kind: UnavailableKind,
    },
    /// There is no inner-search attempt to describe: a §4.4 visible-error
    /// report is not a `Cover` answer at all.
    NotApplicable,
    /// `P4-STATEFUL` T6: an engine that computes no inner-search diagnostics
    /// at all. Only the stateful engine produces this today.
    NotProduced { by: Engine },
}

/// Why no obligation was named. See [`Diagnostics::Unavailable`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnavailableKind {
    /// The recomputation did not reproduce the search's verdict.
    Diverged,
    /// It did, and §7.1's four values have no name for what it found (A14).
    NoValueForIt,
}

/// The first failing obligation — §7.1's four values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Obligation {
    /// (M1): the observation sequences differ.
    ObservationMismatch {
        thread: String,
        position: usize,
        spec: String,
        imp: String,
    },
    /// (M2): a `vo` edge on the specification side does not pull back.
    MissingPullBack {
        spec_from: String,
        spec_to: String,
        imp_from: String,
        imp_to: String,
    },
    /// (M3): the two sides disagree on a visible thread's status.
    StatusMismatch {
        thread: String,
        spec: String,
        imp: String,
    },
    /// Nothing the specification could offer passed \u{3a6}.
    NoOfferablePassedPhi,
}

/// §7.3's product: a ⟨word, status vector⟩ **pair**.
///
/// **Not a word.** The draft's Def. (Visible trace) is
/// `vis(σ) ≝ ⟨w, status_σ|_Tvis⟩`; the word-alone display is a convention the
/// draft licenses only for its two examples, "because their status components
/// all agree". §11.3 and §11.4 both name **Ex. blocking** as the status-only
/// difference that must report, and `statuses_agree` is a `BTreeMap` equality
/// on status vectors — so for a report whose only discriminator is (M3), a
/// word-only rendering shows the user two identical words and nothing wrong in
/// them. Filed as A13 and amended in §7.3.
///
/// And `vis(G)` is a **set** — the linear extensions of `vo(G)` — so a test
/// pinning "the word" pins whichever linearisation the implementation
/// happened to emit. [`VisTrace::word`] is therefore one **named canonical**
/// linearisation with a deterministic tie-break; see
/// `conformance::diagnose::canonical_vis`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VisTrace {
    pub(crate) word: Vec<String>,
    pub(crate) statuses: Vec<(String, String)>,
}

impl VisTrace {
    /// The canonically chosen linearisation of `obsposet(G)`.
    pub fn word(&self) -> &[String] {
        &self.word
    }
    /// The status component, one entry per declared visible thread.
    pub fn statuses(&self) -> &[(String, String)] {
        &self.statuses
    }
}

/// What §7.3's triage produced for one report.
///
/// A **nondeterministic** implementation is *not* here: that is a run-level
/// failure and leaves through [`ConfError`] (blocked item C's ruling). The
/// distinction criterion 4 asks for is between that and
/// [`Self::ReplayedAssertion`], which is the ordinary outcome of triaging a
/// §4.4 report and must never be labelled "nondeterministic Impl".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TriageOutcome {
    /// §7.3's stated result: a *complete* uncovered graph.
    Completed {
        vis: VisTrace,
        /// The specification-side first mismatch the pair is presented next
        /// to (§7.3's final paragraph).
        spec_mismatch: String,
        dump: String,
    },
    /// The completion **blocked** instead of finishing.
    ///
    /// §7.3's conclusion — "the result is a *complete* uncovered graph" — is
    /// false here and nothing else would signal it. `max_iterations = 1` is
    /// consulted at `record_ending_telemetry`'s `max_iterations` test inside `record_ending_telemetry`, and it
    /// compares `n <= num_total` where `num_total = num_execs + num_blocked`
    /// — i.e. **all** endings, blocked ones included. So triage can end with
    /// one blocked execution and no complete graph, and the reported graph
    /// was cut out of a doomed subtree: completing it under LTR can deadlock
    /// on a suffix receive, which is the ordinary case.
    ///
    /// "Triage could not complete this graph" is not a conformance claim.
    Blocked { ending: String },
    /// **The assertion this report names** fired again on the replay.
    ///
    /// Expected when the report was a §4.4 visible error: triage replays the
    /// prefix that contains the `Block(Assert)` and re-runs the statement. It
    /// is **not** nondeterminism, and rendering it as such is the failure
    /// criterion 4 was written to catch.
    ReplayedAssertion { thread: String, pos: String },
    /// A **different** assertion fired during the replay.
    ///
    /// An invisible thread's, or one arriving after the replay's own prune, or
    /// a visible one on a thread this report does not name. It is still not
    /// nondeterminism — but it is not "what this report says should happen"
    /// either, and rendering it with that sentence attributed a *note* to a
    /// report that never mentioned it (gate-4 round 1, m7).
    OtherAssertion { thread: String, pos: String },
}

/// One recorded candidate violation, with everything §7.1 asks a report to
/// carry.
#[derive(Clone)]
pub struct ConfReport {
    /// Which engine raised it (`P4-STATEFUL` T6); decides the certificate text.
    pub(crate) engine: Engine,
    pub(crate) gate: ReportGate,
    pub(crate) cause: ReportCause,
    /// The semantic tag, a function of `(cause, gate)` — [`ReportTag::of`].
    pub(crate) tag: ReportTag,
    pub(crate) events: usize,
    /// §7.1's outer graph snapshot, dump half.
    pub(crate) dump: String,
    /// §7.1's outer graph snapshot, serialized half. See
    /// [`ReplaySnapshot`].
    pub(crate) replay: ReplaySnapshot,
    pub(crate) diagnostics: Diagnostics,
    pub(crate) triage: Option<TriageOutcome>,
    /// `P4-FLAT` criterion 8: the completion decision behind this report was
    /// `FlatCover`'s (set by `cfirst::run`/`gated::run` on every completion
    /// report of a `Flat` run; never on a cut or gate-site report).
    pub(crate) by_flat_cover: bool,
}

/// §7.1's "serialized replay information — the existing `ReplayInformation`
/// machinery, T7".
///
/// **`store_replay_information`'s conformance early return is not deleted.**
/// `store_replay_information`'s conformance early return returns on `probe_active() || conf.is_some()` and that is
/// S4's fix for F-C: both modes stop threads at positions whose labels were
/// never installed, so `top_sort(pos)` on such a position indexes past the end
/// of a thread's row and the resulting index panic *replaces* the original
/// one. Deleting the guard reopens F-C on the exact path S4 spent a gate round
/// fixing.
///
/// So this is criterion 13's route (a): `ReplayInformation::create` is called
/// directly, off the live outer `Must`, on a graph and a `MustState` cloned at
/// report time. `top_sort`'s precondition is **established** rather than
/// assumed, and the argument has to be per report kind because the position
/// differs:
///
/// - **`NoCover`** — `pos` is `None`. `top_sort(None)` takes each thread's
///   *last installed label* as a maximal element and walks backwards through
///   `po` and `rf`; it never names a position, so there is no position to
///   index past. The gate fires with every thread's row installed up to its
///   own frontier, by construction: gates run at the tail of a handler, after
///   `add_to_graph`.
/// - **`VisibleError`** — `pos` is the assertion's position, and
///   `conf_assert_failure` calls `handle_block(Block::new(pos,
///   BlockType::Assert))` **before** `report_visible_error`, so the label at
///   `pos` is installed when the snapshot is taken. That ordering is
///   load-bearing here and is asserted in `s5_tests`.
///
/// **What it costs, measured** (gate-4 round 2, M3). The figure has been stated
/// wrongly twice — once as the criteria's `O(reports × |G₁|)` while a
/// `MustState` was also retained, and once as "one `ExecutionGraph` and one
/// `String`", which is true of the shapes and false about the size: the
/// `String` is a sorted graph *plus* a `MustState` *plus* the `Config`, as
/// text. Compact rather than pretty-printed, and **affine rather than
/// proportional** — a per-event figure alone understates a small report badly,
/// and F-18's regime is the many-small-reports one. Least-squares over 21
/// reports from 6 to 26 events:
///
/// ```text
///     bytes  ≈  440  +  570 × events          (4.1 KB at 6 events,
///                                              6.2 KB at 10, 10.7 KB at 18)
///
///     run    ≈  reports × (440 + 570 × |G₁|)  of JSON, held for the whole run
///             + reports × one ExecutionGraph  of structure
/// ```
///
/// and on a run that reports often it is the text that dominates. §7.1 asks
/// every report to carry this and says nothing about the bound; whether that
/// wants a knob, a file sink, or a cap is a design question and is routed to
/// the owner rather than settled here. `c13_the_serialized_snapshot_size_is_measured_not_described`
/// pins the per-event figure.
///
/// What is **not** claimed: that feeding this back to `traceforge::replay`
/// reproduces the run. That path deserializes its own `Config` (`traceforge::replay`)
/// and is not in conformance's configuration scope; nobody has run the
/// round-trip and this file does not say it works. The artefact delivered is
/// the linearisation and the serialized state, which is what "re-run a
/// counterexample outside the tool" needs as its input — not a demonstration
/// that the tool on the other end accepts it. See the S5 report's findings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplaySnapshot {
    /// The serialized `ReplayInformation`, as JSON.
    Serialized(String),
    /// Serialization itself failed (a payload that is not `Serialize`-able
    /// through `serde_json`). Recorded rather than swallowed.
    Unavailable { because: String },
}

impl ConfReport {
    pub fn gate(&self) -> ReportGate {
        self.gate
    }
    pub fn cause(&self) -> &ReportCause {
        &self.cause
    }
    /// The semantic tag: which certificate this report carries.
    pub fn tag(&self) -> ReportTag {
        self.tag
    }
    /// The implementation graph's size when the report was raised.
    pub fn events(&self) -> usize {
        self.events
    }
    pub fn diagnostics(&self) -> &Diagnostics {
        &self.diagnostics
    }
    pub fn triage(&self) -> Option<&TriageOutcome> {
        self.triage.as_ref()
    }
    pub fn graph_dump(&self) -> &str {
        &self.dump
    }
    pub fn replay_snapshot(&self) -> &ReplaySnapshot {
        &self.replay
    }
}

impl fmt::Debug for ConfReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ConfReport")
            .field("gate", &self.gate)
            .field("cause", &self.cause)
            .field("events", &self.events)
            .field("diagnostics", &self.diagnostics)
            .field("triage", &self.triage)
            .finish_non_exhaustive()
    }
}

/// The inner search ran out of room. **Not a report**, and not silence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfExhaustion {
    pub(crate) gate: ReportGate,
    pub(crate) events: usize,
    /// The budget that was hit — criterion 2 requires an exhaustion to name
    /// it, because the stated failure mode is "a user set the budget too low
    /// and got a clean-looking result".
    pub(crate) budget: usize,
}

impl ConfExhaustion {
    pub fn gate(&self) -> ReportGate {
        self.gate
    }
    pub fn budget(&self) -> usize {
        self.budget
    }
}

/// An assertion failure that is **not** a conformance report (§4.4).
///
/// **The two cases are separate variants, and the position field is named
/// differently in each, because it means something different in each.** S4's
/// `Diagnostic` carried one `pos: Event` whose meaning depended on `reason`:
/// for an invisible thread it is an installed `Block(Assert)`, a real event in
/// the graph; for a post-prune failure **nothing was installed**, so it is the
/// position the failing statement *would* have occupied — which may hold
/// conformance's own `Block(ConfPrune)` or lie past the end of the row.
/// Resolving one as the other is a defect S4's own rustdoc warned about and
/// could not prevent. The reviewer's recommendation for S5, recorded at gate 4,
/// was to make the divergence structural when S5 replaced the type. This is
/// that.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfNote {
    /// An **invisible** thread failed an assertion.
    ///
    /// The theorem does not speak about it, so reporting it would claim a
    /// violation of something never promised. `at` is a real event: the
    /// `Block(Assert)` that was installed.
    InvisibleThread { thread: String, at: String },
    /// A thread failed one *after* this execution was already pruned.
    ///
    /// **This does not imply the thread was visible.** The classification is
    /// positional — `conf_assert_failure` tests the prune latch before it
    /// tests visibility — and `AfterPrune ⟹ visible` is *unproven* and
    /// believed unreachable. `thread` is the declared visible name where the
    /// thread has one and the **runtime task name** otherwise, so the
    /// rendering is one adjective away from making the unproven claim by
    /// accident. It does not make it; see this type's `Display`.
    ///
    /// `would_be` is **not** an event: nothing was installed at that position.
    AfterPrune { thread: String, would_be: String },
}

impl ConfNote {
    pub(crate) fn of(reason: DiagnosticReason, thread: String, pos: String) -> Self {
        match reason {
            DiagnosticReason::InvisibleThread => ConfNote::InvisibleThread { thread, at: pos },
            DiagnosticReason::AfterPrune => ConfNote::AfterPrune {
                thread,
                would_be: pos,
            },
        }
    }

    /// The declared visible name where the thread has one, the runtime task
    /// name otherwise — the same key a [`ConfReport`] uses, so the two can be
    /// joined.
    pub fn thread(&self) -> &str {
        match self {
            ConfNote::InvisibleThread { thread, .. } | ConfNote::AfterPrune { thread, .. } => {
                thread
            }
        }
    }
}

// ---------------------------------------------------------------------------
// How the run ended, and what that does to the verdict (§7.4, blocked B + G)
// ---------------------------------------------------------------------------

/// Why the outer loop stopped. **A carried fact, never an inference.**
///
/// Blocked item B's ruling: "the search completed" is a distinct carried fact,
/// not something derived from an empty report list. The engine records this at
/// each site where `complete_execution` decides the run is over, so the three
/// are told apart by construction rather than reconstructed afterwards — which
/// is exactly what item G refused to do by draining `rqueue` (a drained queue
/// is indistinguishable from an exhausted one) or by setting
/// `config.max_iterations` from the gate (which would destroy the distinction
/// between a bound the *user* set and one the *gate* set).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SearchEnd {
    /// `try_revisit` found nothing left. **This, and only this, is "the
    /// search completed".**
    StateSpaceExhausted,
    /// `Config::max_iterations` stopped it — a bound the *user* set.
    MaxIterations(u64),
    /// `stop_at_first_report` stopped it — a bound the *gate* set.
    StoppedAtFirstReport,
    /// The inner search found the specification not assertion-safe and
    /// aborted the run (`P4-ENUMERATOR` criterion 9). Written **first**
    /// through `record_end`, so no later ending can overwrite it. It is the
    /// engine-only `Outcome`'s end on that path; [`crate::conformance::verify`]
    /// returns [`ConfError::SpecNotAssertionSafe`] before any [`ConfOutcome`]
    /// is built, so no `ConfOutcome` ever carries it.
    SpecNotAssertionSafe,
    /// Nothing recorded an ending. Silence must not be inferred from this.
    ///
    /// The **default**, deliberately: the fact has to be written down by
    /// something that observed it, and the absence of an observation is not
    /// evidence that the search completed.
    #[default]
    Unknown,
}

/// A named reason this run's silence is not a certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NotACertificate {
    /// The inner search hit its node budget somewhere, so \u{22a5} was never
    /// established there.
    SearchExhausted { occurrences: usize, budget: usize },
    /// The outer loop terminated by configuration, not by exhausting the
    /// state space.
    StoppedAtFirstReport,
    /// The outer loop terminated on a user-set iteration bound.
    BoundedRun { max_iterations: u64 },
    /// Nothing recorded how the run ended.
    EndUnknown,
    /// There is at least one report, so this is not silence at all.
    Reported { count: usize },
}

/// What the run assumed rather than checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecErrFreedom {
    /// The specification was found error-free: by §5.4's precheck under
    /// [`Engine::Enumerator`], or by the stateful engine's index run, which
    /// enumerates the specification in full and *is* that check
    /// (`P4-STATEFUL` T4).
    Checked,
    /// The enumerator's record of `ConfBuilder::skip_spec_errfree_check(true)`.
    /// The verdict records the assumption, because an opt-out that leaves no
    /// trace is a silent change of what the verdict means. Never recorded by
    /// [`Engine::Stateful`], whose index run checks regardless of the flag.
    Assumed,
}

/// `FlatCover`'s counters (`P4-FLAT` F6), each at a named program point of
/// `flat.rs`: `calls` completions handed to `flat_cover`; `visits` the paper's
/// FlatVisit invocations (`flat::visit`), the root included; `nd_branches` values tried at `ln:fnd`;
/// `source_branches` options tried at `ln:fsrc` (an `install_recv` followed by
/// a `follows` test, `⊥` included) and `source_recursions` those that passed
/// and recursed; `send_kills` `follows` failures at `ln:fsend`; `slot_kills`
/// the slot's thread not standing at an **offered** receive — the prober
/// offers a blocking receive only when a source exists, so a slot thread at a
/// blocking receive with nothing deliverable (`alg:flat`'s `ln:fsrc` with no
/// option, counted in `source_kills` there) counts here (round 01 n1; the ⊥ answer is
/// the same); `source_kills` no option passing; `done_kills` `ln:fdone` failures; `witnesses` non-⊥ returns;
/// `max_depth` the recursion depth; `wall_time_ms` the flat threads' time.
/// Tests compare fields, never whole structs (`wall_time_ms` is inside).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FlatCounters {
    pub calls: usize,
    pub visits: usize,
    pub nd_branches: usize,
    pub source_branches: usize,
    pub source_recursions: usize,
    pub send_kills: usize,
    pub slot_kills: usize,
    pub source_kills: usize,
    pub done_kills: usize,
    pub witnesses: usize,
    pub max_depth: usize,
    pub wall_time_ms: u128,
}

impl FlatCounters {
    /// Fold one `flat_cover` call's counters into the run's (sums; `max` for
    /// the depth).
    pub(crate) fn accumulate(&mut self, d: &FlatCounters) {
        self.calls += d.calls;
        self.visits += d.visits;
        self.nd_branches += d.nd_branches;
        self.source_branches += d.source_branches;
        self.source_recursions += d.source_recursions;
        self.send_kills += d.send_kills;
        self.slot_kills += d.slot_kills;
        self.source_kills += d.source_kills;
        self.done_kills += d.done_kills;
        self.witnesses += d.witnesses;
        self.max_depth = self.max_depth.max(d.max_depth);
        self.wall_time_ms += d.wall_time_ms;
    }
}

/// The communication-flat eligibility record (`P4-FLAT` F1), decided on the
/// precheck's enumeration of `Graphs(Spec)`: `communication_flat` iff every
/// send and receive of every collected graph is visible (`is_visible`);
/// `thread_flat` is `flat.tex`'s class — every spawned thread declared, `main`
/// declared or communicating not at all — recorded, not used; `first_invisible`
/// the first invisible send or receive in scan order (graphs in completion
/// order, threads by `ThreadId`, events by index), as a thread name or id and a
/// position.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FlatEligibility {
    pub communication_flat: bool,
    pub thread_flat: bool,
    pub spec_graphs_scanned: usize,
    pub first_invisible: Option<(String, String)>,
}

/// Everything one conformance run produced.
#[derive(Clone)]
pub struct ConfOutcome {
    pub(crate) reports: Vec<ConfReport>,
    pub(crate) exhaustions: Vec<ConfExhaustion>,
    pub(crate) notes: Vec<ConfNote>,
    pub(crate) end: SearchEnd,
    pub(crate) spec_errfree: SpecErrFreedom,
    pub(crate) budget: usize,
    pub(crate) triage_enabled: bool,
    /// The random seed this run's engines used (F61).
    pub(crate) seed: u64,
    /// `P4-ENUMERATOR` criterion 13.
    pub(crate) counters: ConfCounters,
    /// `P4-STATEFUL` T6: which engine produced this outcome.
    pub(crate) engine: Engine,
    /// `P4-STATEFUL` criterion 8: the stateful engine's own counters; `None`
    /// on the enumerator.
    pub(crate) stateful_counters: Option<StatefulCounters>,
    /// `P4-CFIRST` criterion 9: the complete-first engine's own counters;
    /// `None` on the other engines.
    pub(crate) cfirst_counters: Option<CFirstCounters>,
    /// `P4-GATED` criterion 9: the gated engine's own counters; `None` on the
    /// other engines.
    pub(crate) gated_counters: Option<GatedCounters>,
    /// `P4-FLAT` F6: `Some` whenever `completion_cover = Flat` ran.
    pub(crate) flat_counters: Option<FlatCounters>,
    /// `P4-FLAT` F1: `Some` whenever the precheck ran under `Flat`.
    pub(crate) flat_eligibility: Option<FlatEligibility>,
}

/// The stateful engine's counters (`P4-STATEFUL` criterion 8), each defined
/// there. Identities: `lookups = lookups_signature_miss + lookups_containment_tested`;
/// `lookups_containment_tested = lookups_succeeded + lookups_failed_after_tests`;
/// `reports = lookups_signature_miss + lookups_failed_after_tests`; `containment_tests ≥ lookups_containment_tested`.
/// A `SigKey` hit followed by a full-`Sig` miss is a signature miss.
/// `orders_held` counts after `BTreeSet` deduplication. The index size the plan
/// calls the point of comparison is `signatures + orders_held`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StatefulCounters {
    pub spec_graphs: usize,
    pub impl_graphs: usize,
    /// `SigKey` hash buckets of the index — coarser than `signatures`.
    pub sig_key_buckets: usize,
    /// Full-`Sig` slots of the index.
    pub signatures: usize,
    pub orders_held: usize,
    pub lookups: usize,
    pub lookups_signature_miss: usize,
    pub lookups_containment_tested: usize,
    pub lookups_succeeded: usize,
    pub lookups_failed_after_tests: usize,
    pub containment_tests: usize,
    pub reports: usize,
    pub spec_wall_time_ms: u128,
    pub impl_wall_time_ms: u128,
    /// `P4-MIXED` M8: see [`ConfCounters::invisible_ops_of_visible_threads`];
    /// computed in this engine's implementation completion sink.
    pub invisible_ops_of_visible_threads: usize,
}

/// The counters of one conformance run (`P4-ENUMERATOR` criterion 13; plan
/// §6). A plain record: every field is public and the struct is `Default`.
///
/// **Engine definitions**, since several names are the paper's:
///
/// - `gate_*`: invocations of `ConfCtx::gate` (the engine's own measure, not
///   the paper's per-event Visit), partitioned by return path. `cover_calls`
///   is the `Cover`-calling bucket.
/// - `rebuilds_*`: `ln:rebuild` taken (seed attempt `NoCover`, seed not
///   initial), skipped because the seed was initial, skipped because the seed
///   attempt was exhausted.
/// - `spec_visit_*`: `SpecVisit` calls, total and per attempt; a memo hit
///   counts as a call (it spent its budget unit and probed).
/// - `distinct_*` and `per_attempt_distinct`: **instrumentation only**
///   (`SearchOpts::instrument`), zero otherwise — with memo off they would
///   canonicalise every node and taint the memo-off performance arm. A key is
///   *met* in an attempt when a probe output with that key is encountered in
///   it, hits included. `f63_per_attempt_distinct` is F63's own definition: the
///   `Display` of the graph handed to `probe` (the input), per attempt.
/// - `explored_complete_keys`: canonical keys of graphs captured at
///   `Completion` of **unpruned** executions, instrumentation only.
///   `report_keys` (instrumentation only) are the keys of report graphs, by
///   gate, so that a consumer can form "explored complete graphs" with the
///   paper-completeness predicate the engine does not decide for a growing
///   graph (an implementation probe from it would; criterion 13's caveat). A
///   `RevisitApply` report graph is keyed as cut by `revisit_view`.
/// - `max_paper_events_per_execution` is the paper's `L`: the largest number of
///   paper events (sends, receives, tosses, choices, assertion failures) any
///   execution installed. `paper_events_at_first_report` counts them in the
///   first reported graph, not `Report.events`, which counts bookkeeping.
/// - `wall_time_ms` is the outer run's wall time; peak memory is Part 6's.
///
/// **On a result of [`crate::conformance::verify`] every instrumentation field
/// is zero or empty** — `distinct_keys_run_wide`, `f63_distinct_run_wide`,
/// `explored_complete_keys`, `report_keys`, and the `distinct_*`/`f63_*` fields
/// of each [`CoverCounters`]: `run` does not instrument (the flag is
/// crate-internal, for the differential harness and the tests). The other
/// counters are always filled on the enumerator; the stateful engine fills only
/// `executions`, `max_paper_events_per_execution`, `wall_time_ms` and
/// `invisible_ops_of_visible_threads` (`P4-STATEFUL` T6; `P4-MIXED` M8), the
/// sweeping engines those and `paper_events_at_first_report` (gated).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ConfCounters {
    pub gate_invocations: usize,
    pub gate_skipped_inert: usize,
    pub gate_skipped_replay: usize,
    pub gate_skipped_pruned: usize,
    pub gate_skipped_disabled: usize,
    pub gate_skipped_aborted: usize,
    pub cover_calls: usize,
    pub cover_exhaustions: usize,
    pub rebuilds_taken: usize,
    pub rebuilds_skipped_initial_seed: usize,
    pub rebuilds_skipped_exhausted_seed: usize,
    pub spec_visit_calls: usize,
    pub spec_visit_calls_extend: usize,
    pub spec_visit_calls_rebuild: usize,
    pub memo_hits: usize,
    /// Per `Cover` call, in call order.
    pub per_cover: Vec<CoverCounters>,
    pub distinct_keys_run_wide: usize,
    /// F63's run-wide `Display`-keyed count (criterion 14 (i)).
    pub f63_distinct_run_wide: usize,
    pub explored_complete_keys: Vec<String>,
    pub report_keys: Vec<(ReportGate, String)>,
    pub max_paper_events_per_execution: usize,
    pub paper_events_at_first_report: Option<usize>,
    pub executions: usize,
    pub wall_time_ms: u128,
    /// `P4-MIXED` M8: the number of sends and receives of declared threads that
    /// are invisible (an `Invisible` annotation), per unpruned complete graph,
    /// maximum over the run — 0 on every unannotated program. Filled by all four
    /// engines (the enumerator at its completion gate; the other three in their
    /// implementation completion sinks). A receive that blocks is no event and
    /// is not counted.
    pub invisible_ops_of_visible_threads: usize,
}

/// One `Cover` call's counters (`P4-ENUMERATOR` criterion 13).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CoverCounters {
    pub spec_visit_calls: usize,
    pub spec_visit_calls_extend: usize,
    pub spec_visit_calls_rebuild: usize,
    pub memo_hits: usize,
    pub rebuild_taken: bool,
    pub rebuild_skipped_initial_seed: bool,
    pub rebuild_skipped_exhausted_seed: bool,
    /// Instrumentation only.
    pub distinct_keys: usize,
    pub per_attempt_distinct: [usize; 2],
    pub f63_per_attempt_distinct: [usize; 2],
    /// Instrumentation only: the run-wide distinct count after this call.
    pub run_wide_distinct_so_far: usize,
    /// Instrumentation only: F63's run-wide `Display`-keyed count after this
    /// call (criterion 14 (i), the across-attempt factor).
    pub f63_run_wide_distinct_so_far: usize,
}

impl ConfOutcome {
    /// **The random seed this run used** (F61).
    ///
    /// `nondet()` draws its first value from this seed, and that draw sets the
    /// order in which the checker explores a program. The verdict did not
    /// change with the seed in anything measured (`P3-F61`), but the *set* of
    /// reports, the concrete graph inside a report, the triage trace and some
    /// internal counts do. Under a bounded `Config` (`max_iterations`), which
    /// branch is explored first can also decide the precheck's result.
    ///
    /// **What this seed reproduces, and what it does not.** Every engine a
    /// conformance run builds (the outer run, the precheck, triage and the
    /// diagnostics) is built from the same `Config` and so draws from this
    /// seed. Rebuilding the **same** `Config` (every other setting unchanged)
    /// with `.with_seed(seed)` added therefore reproduces **the choices
    /// TraceForge makes**. It reproduces the whole run only when, in
    /// addition, the program under test is deterministic apart from
    /// TraceForge's own `nondet()`: it does not read time, OS randomness,
    /// atomics or other state outside the checker. The run must also use the
    /// same TraceForge version, and any callbacks registered with
    /// `Config::with_callback` must not carry state that changes execution.
    /// Callbacks are shared between *clones* of a `Config`, so a stateful one
    /// is **not** reset by cloning it. A `Config` rebuilt through
    /// `Config::builder()` holds only the observers registered on it, so
    /// rebuild it with freshly constructed observers rather than clone it. An
    /// observer that keeps its state behind its own shared handle (an `Arc`
    /// field, say) carries that state into the rebuilt `Config` too. Within
    /// those limits, exact
    /// reproduction is tested, including triage's own `nondet()` rolls
    /// (`P3-F61-fix`).
    ///
    /// `Config`'s default seed is fresh randomness on every call, so without
    /// this value an unseeded run generally cannot be repeated.
    pub fn seed(&self) -> u64 {
        self.seed
    }
    pub fn reports(&self) -> &[ConfReport] {
        &self.reports
    }
    pub fn exhaustions(&self) -> &[ConfExhaustion] {
        &self.exhaustions
    }
    pub fn notes(&self) -> &[ConfNote] {
        &self.notes
    }
    pub fn end(&self) -> SearchEnd {
        self.end
    }
    pub fn spec_err_freedom(&self) -> SpecErrFreedom {
        self.spec_errfree
    }

    /// Every named reason this run is not a certificate. **Empty is the only
    /// thing that makes [`ConfVerdict::Conforms`] constructible.**
    pub fn not_a_certificate(&self) -> Vec<NotACertificate> {
        let mut out = Vec::new();
        if !self.reports.is_empty() {
            out.push(NotACertificate::Reported {
                count: self.reports.len(),
            });
        }
        if !self.exhaustions.is_empty() {
            out.push(NotACertificate::SearchExhausted {
                occurrences: self.exhaustions.len(),
                budget: self.budget,
            });
        }
        match self.end {
            SearchEnd::StateSpaceExhausted => {}
            SearchEnd::MaxIterations(n) => {
                out.push(NotACertificate::BoundedRun { max_iterations: n })
            }
            SearchEnd::StoppedAtFirstReport => out.push(NotACertificate::StoppedAtFirstReport),
            SearchEnd::Unknown => out.push(NotACertificate::EndUnknown),
            // `run` returns `Err(ConfError::SpecNotAssertionSafe)` before it
            // builds a `ConfOutcome`, so this end never reaches one (gate-1
            // round 04, m1). An arm rather than a `NotACertificate` variant:
            // a variant would be a public addition no caller could observe.
            SearchEnd::SpecNotAssertionSafe => unreachable!(
                "conformance: a ConfOutcome was built from a run the inner search aborted; \
                 `run` returns Err(SpecNotAssertionSafe) before building one"
            ),
        }
        out
    }

    /// `P4-ENUMERATOR` criterion 7: **inconclusive iff some `Cover` ran out of
    /// budget**. Independent of [`ConfVerdict::Inconclusive`], which also
    /// covers `MaxIterations` and `StoppedAtFirstReport` runs with no
    /// exhaustion; a `Reported` run with exhaustions is inconclusive too, in
    /// this sense, about the graphs its exhausted gates did not settle.
    pub fn inconclusive(&self) -> bool {
        !self.exhaustions.is_empty()
    }

    /// The run's counters (`P4-ENUMERATOR` criterion 13).
    pub fn counters(&self) -> &ConfCounters {
        &self.counters
    }

    /// Which engine produced this outcome (`P4-STATEFUL` T6).
    pub fn engine(&self) -> Engine {
        self.engine
    }

    /// The stateful engine's counters; `None` on the enumerator
    /// (`P4-STATEFUL` criterion 8).
    pub fn stateful_counters(&self) -> Option<&StatefulCounters> {
        self.stateful_counters.as_ref()
    }

    /// The complete-first engine's counters; `None` on the other engines
    /// (`P4-CFIRST` criterion 9).
    pub fn cfirst_counters(&self) -> Option<&CFirstCounters> {
        self.cfirst_counters.as_ref()
    }

    /// The gated engine's counters; `None` on the other engines
    /// (`P4-GATED` criterion 9).
    pub fn gated_counters(&self) -> Option<&GatedCounters> {
        self.gated_counters.as_ref()
    }

    /// `FlatCover`'s counters (`P4-FLAT` F6); `Some` whenever the run's
    /// `completion_cover` was `Flat`, zero counts allowed.
    pub fn flat_counters(&self) -> Option<&FlatCounters> {
        self.flat_counters.as_ref()
    }

    /// The communication-flat eligibility record (`P4-FLAT` F1); `Some`
    /// whenever the precheck ran under `completion_cover = Flat`.
    pub fn flat_eligibility(&self) -> Option<&FlatEligibility> {
        self.flat_eligibility.as_ref()
    }
}

/// `P4-GATED` criterion 9: the gated engine's counters, two families, each
/// field defined by what it counts. Identities on every run:
///
/// - `gates` is the sum of `gates_skipped_certified`, `gates_declined`,
///   `carried_hits`, `gate_cache_hits` and `gate_sweeps`;
/// - `gate_sweeps` is the sum of its `successful`, `failing`, `budgeted` and
///   `aborted` parts;
/// - `certificates_set` equals `gate_sweeps_failing`;
/// - `reports` is the sum of `reports_certified` and
///   `reports_by_completion_test` (exhaustive), and is at most 1 (first-failure);
/// - `impl_graphs` is the sum of `completion_cache_hits`, `completion_sweeps`
///   and `reports_certified`;
/// - `witness_duplicates` is asserted zero by the engine.
///
/// **Under `CompletionCover::Flat`** (`P4-FLAT` F6) no completion sweep runs
/// (`completion_sweeps = 0`), `flat` is `Some`, and: `impl_graphs =
/// completion_cache_hits + reports_certified + flat.calls` exactly;
/// `reports_by_completion_test = flat.calls − flat.witnesses`; `reports =
/// reports_certified + reports_by_completion_test` (exhaustive) unchanged; `flat.calls =
/// completion_probes − completion_cache_hits`. Gate sweeps are unchanged.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GatedCounters {
    /// The reporting contract the run used (`GatedMode::FirstFailure`).
    pub first_failure_mode: bool,
    // ---- the gate family ------------------------------------------------
    /// Gate-sink calls that fired: a visible fresh send or receive, a forward
    /// pop of a visible receive, a backward revisit by a visible send.
    pub gates: usize,
    /// Gate-sink calls on an invisible event: no gate.
    pub gates_inert: usize,
    /// Growing gates the context skipped because the previous execution was
    /// still being replayed (F49); they never reach the sink.
    pub gates_skipped_replay: usize,
    /// Fired gates skipped under a valid certificate.
    pub gates_skipped_certified: usize,
    /// Fired gates the policy declined (`Never`).
    pub gates_declined: usize,
    /// `cone` tests of the carried witness (`ln:gwit`).
    pub c1_tests_carried: usize,
    /// … of which passed.
    pub carried_hits: usize,
    /// `cone_from` calls made by `W` probes at gates.
    pub c1_tests_cache: usize,
    /// Gates answered by `W`.
    pub gate_cache_hits: usize,
    /// Complete specification graphs tested by gate sweeps.
    pub c1_tests_sweep: usize,
    pub gate_sweeps: usize,
    pub gate_sweeps_successful: usize,
    /// Exhaustive sweeps that found no witness: a certificate.
    pub gate_sweeps_failing: usize,
    /// Sweeps stopped by `Budget(B)` with graphs left.
    pub gate_sweeps_budgeted: usize,
    /// Sweeps that met a specification assertion failure (the run aborts).
    pub gate_sweeps_aborted: usize,
    /// Per gate sweep, in sweep order.
    pub gate_sweep_sizes: Vec<usize>,
    /// `= gate_sweeps_failing`.
    pub certificates_set: usize,
    /// Certificates dropped at the point of use (`valid_at` false).
    pub certificate_resets: usize,
    /// Backward revisits taken (every backward `RevisitApply` call, inert or
    /// not).
    pub states_pushed: usize,
    /// Backward revisits whose **outgoing** state's slot held a certificate —
    /// an engine fact, not the paper's `ln:greset` reset.
    pub certified_states_revisited: usize,
    /// Completions reported under a valid certificate, without a test.
    pub reports_certified: usize,
    /// Completions reported by a failed `Covered`.
    pub reports_by_completion_test: usize,
    /// Paper events of the first report's graph, if any.
    pub paper_events_at_first_report: Option<usize>,
    // ---- the completion family (Part 4's) --------------------------------
    pub impl_graphs: usize,
    pub completion_probes: usize,
    pub completion_cache_hits: usize,
    pub completion_cache_tests: usize,
    pub completion_sweeps: usize,
    pub completion_sweeps_successful: usize,
    pub completion_sweeps_failing: usize,
    pub completion_sweeps_aborted: usize,
    pub completion_sweep_sizes: Vec<usize>,
    /// `|W|` at the end.
    pub witnesses: usize,
    /// Admissions `W` refused as already held — asserted zero by the engine.
    pub witness_duplicates: usize,
    /// Every report, of either kind.
    pub reports: usize,
    pub precheck_ran: bool,
    pub precheck_wall_time_ms: u128,
    /// Includes every sweep's time; excludes the precheck's.
    pub outer_wall_time_ms: u128,
    pub sweep_wall_time_ms: u128,
    /// `P4-MIXED` M8: see [`ConfCounters::invisible_ops_of_visible_threads`];
    /// computed in this engine's implementation completion sink.
    pub invisible_ops_of_visible_threads: usize,
    /// `P4-FLAT` F6: `FlatCover`'s counters, `Some` iff `completion_cover = Flat`.
    pub(crate) flat: Option<FlatCounters>,
}

/// `P4-CFIRST` criterion 9: the complete-first engine's counters, each field
/// defined by what it counts. Identities, on every run: `sweeps =
/// sweeps_successful + sweeps_failing + sweeps_aborted`; `impl_graphs =
/// cache_hits + sweeps`; `cache_probes = impl_graphs`; `sweep_graphs =
/// Σ sweep_sizes`; `witnesses + witness_duplicates = sweeps_successful`, with
/// `witness_duplicates = 0` asserted by the engine; with the cut off
/// `reports = sweeps_failing`.
///
/// **Under `CompletionCover::Flat`** (`P4-FLAT` F6) no completion sweep runs
/// (`sweeps = 0`), `flat` is `Some`, and the identities read: `impl_graphs =
/// cache_hits + flat.calls`; `witnesses + witness_duplicates = flat.witnesses`;
/// with the cut off `reports = flat.calls − flat.witnesses`; `flat.calls =
/// cache_probes − cache_hits`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CFirstCounters {
    /// Outer completions that reached the sink (pruned executions excluded).
    pub impl_graphs: usize,
    /// `W` probes — one per completion.
    pub cache_probes: usize,
    /// Probes answered by `W`.
    pub cache_hits: usize,
    /// `covered` calls made by probes (`covered` short-circuits on a signature
    /// mismatch, so these are calls, not containment tests).
    pub cache_tests: usize,
    pub sweeps: usize,
    /// Sweeps stopped at a covering witness.
    pub sweeps_successful: usize,
    /// Sweeps that exhausted the specification without a witness (a report).
    pub sweeps_failing: usize,
    /// Sweeps that met a specification assertion failure (the run aborts).
    pub sweeps_aborted: usize,
    /// Complete specification graphs tested, per sweep, in sweep order.
    pub sweep_sizes: Vec<usize>,
    /// `Σ sweep_sizes`.
    pub sweep_graphs: usize,
    /// `max sweep_sizes`, 0 with no sweep.
    pub sweep_graphs_max: usize,
    /// `|W|` at the end.
    pub witnesses: usize,
    /// Admissions `W` refused as already held — asserted zero by the engine.
    pub witness_duplicates: usize,
    /// Completion reports.
    pub reports: usize,
    /// Prefix reports raised by the early-error cut.
    pub cut_reports: usize,
    /// Whether the (unbounded) §5.4 precheck ran before the outer run.
    pub precheck_ran: bool,
    /// The precheck's wall time; 0 when skipped.
    pub precheck_wall_time_ms: u128,
    /// The outer run's wall time, which includes every sweep's
    /// (`⊇ sweep_wall_time_ms`) and excludes the precheck's.
    pub outer_wall_time_ms: u128,
    /// Summed over every sweep (the sweep threads' own time).
    pub sweep_wall_time_ms: u128,
    /// `P4-MIXED` M8: see [`ConfCounters::invisible_ops_of_visible_threads`];
    /// computed in this engine's implementation completion sink.
    pub invisible_ops_of_visible_threads: usize,
    /// `P4-FLAT` F6: `FlatCover`'s counters, `Some` iff `completion_cover = Flat`.
    pub(crate) flat: Option<FlatCounters>,
}

/// A conformance certificate: the "conforms" case, and the **only** one.
///
/// It is constructible through `ConfVerdict::of` alone, and only when
/// [`ConfOutcome::not_a_certificate`] is empty — reports and exhaustions both
/// empty *and* the search completed, the last being the carried
/// [`SearchEnd::StateSpaceExhausted`] rather than an inference from the first
/// two.
#[derive(Clone)]
pub struct Certificate {
    pub(crate) outcome: ConfOutcome,
}

impl Certificate {
    /// What the run assumed rather than established.
    pub fn assumptions(&self) -> Vec<&'static str> {
        let mut out = Vec::new();
        if self.outcome.spec_errfree == SpecErrFreedom::Assumed {
            out.push(
                "specification err-freedom was assumed, not checked \
                 (`ConfBuilder::skip_spec_errfree_check(true)`)",
            );
        }
        if self.outcome.flat_counters.is_some() {
            out.push(
                "eligibility decided from the precheck's enumeration of `Graphs(Spec)` (D12)",
            );
            out.push("saturation order-independent under F79's premise");
        }
        out.push("the draft's own lemmas, including the open A4 transport gap");
        out
    }
    pub fn outcome(&self) -> &ConfOutcome {
        &self.outcome
    }
}

/// What `verify` concluded.
///
/// **There is no `is_silent()`** (blocked item B's ruling). `is_silent()` as
/// `reports.is_empty()` is true of a run that exhausted its budget at every
/// gate and checked nothing, true of a run that stopped at its first report
/// and found none, and true of a run bounded by `max_iterations`. So the type
/// is shaped to make the mistake unavailable: the certificate case is a
/// distinct variant that cannot be built without all three facts, and every
/// other case names why it is not one.
#[derive(Clone)]
pub enum ConfVerdict {
    /// Reports and exhaustions empty **and** the search completed.
    Conforms(Certificate),
    /// At least one candidate violation.
    Reported(ConfOutcome),
    /// No report — and no certificate either. `not_a_certificate` says why.
    Inconclusive(ConfOutcome),
}

impl ConfVerdict {
    /// The single construction point. Three facts, checked here and nowhere
    /// else.
    pub(crate) fn of(outcome: ConfOutcome) -> Self {
        if !outcome.reports.is_empty() {
            return ConfVerdict::Reported(outcome);
        }
        if outcome.not_a_certificate().is_empty() {
            ConfVerdict::Conforms(Certificate { outcome })
        } else {
            ConfVerdict::Inconclusive(outcome)
        }
    }

    pub fn outcome(&self) -> &ConfOutcome {
        match self {
            ConfVerdict::Conforms(c) => &c.outcome,
            ConfVerdict::Reported(o) | ConfVerdict::Inconclusive(o) => o,
        }
    }

    /// The certificate, if this run produced one.
    pub fn certificate(&self) -> Option<&Certificate> {
        match self {
            ConfVerdict::Conforms(c) => Some(c),
            _ => None,
        }
    }
}

impl fmt::Debug for ConfVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConfVerdict::Conforms(_) => write!(f, "ConfVerdict::Conforms"),
            ConfVerdict::Reported(o) => write!(f, "ConfVerdict::Reported({})", o.reports.len()),
            ConfVerdict::Inconclusive(o) => {
                write!(f, "ConfVerdict::Inconclusive({:?})", o.not_a_certificate())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The error channel (blocked item C's ruling, option (ii))
// ---------------------------------------------------------------------------

/// A conformance run that started legitimately and then failed.
///
/// **Run-level only.** §5.4's precheck failure and §7.3's triage failure are
/// outcomes of a run; §8's visible-thread violations and §9's scope rejections
/// are "this program is not a valid input", and Rust's convention for that is
/// a panic with a message naming the event — which is what §9 asks for in
/// terms. [`crate::conformance::verify`] is documented as panicking on invalid
/// input, and criterion 1's grep domain therefore includes panic text.
///
/// The reason for the split rather than a `catch_unwind`: three of the four
/// in-engine panics are raised from inside an outer-execution continuation on
/// a thread the outer scheduler owns, with `init_panic_hook` armed. S4 was
/// bitten at this exact boundary by a failure that became a different failure
/// and lost its origin (F-C).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfError {
    /// §5.4: the specification is not error-free, so the problem statement's
    /// assumption does not hold and no conformance verdict means anything.
    SpecNotErrorFree { detail: String },
    /// §7.3: triage failed. Not swallowed — a swallowed triage failure would
    /// silently degrade a report to its pre-triage form and nobody would
    /// know.
    TriageFailed {
        /// Which report, by index into the outcome's report list.
        report: usize,
        cause: TriageFailure,
    },
    /// `ConfBuilder::build` refused the configuration. `verify` never returns
    /// this — `build` does — but it is the same error channel as far as a
    /// caller using `?` is concerned.
    Config { field: ScopeField },
    /// `P4-ENUMERATOR` criterion 9: a probe of the specification inside the
    /// inner search installed a `Block(Assert)`, so the specification is not
    /// assertion-safe (plan §1) and no verdict means anything. The run is
    /// aborted at that gate, with no report; `pos` is the event's `Display`,
    /// per this module's boundary policy.
    SpecNotAssertionSafe { thread: String, pos: String },
    /// `P4-FLAT` F5: `completion_cover = Flat` with a knob it cannot run with —
    /// `skip_spec_errfree_check(true)` (eligibility needs the precheck, D13) or
    /// `Engine::{Enumerator, Stateful}` — refused before any engine runs.
    KnobConflict {
        knob: &'static str,
        conflicts_with: &'static str,
    },
    /// `P4-FLAT` F5: the precheck found a send or receive of the specification
    /// that is not visible, so `FlatCover` is not exact for it; the first such
    /// operation in scan order, as a thread name (or id) and a position.
    SpecNotCommunicationFlat { thread: String, pos: String },
}

/// How triage failed. **Two origins, and they must not render alike**
/// (criterion 4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TriageFailure {
    /// `validate_replay_event` refused the replay: the implementation did not
    /// reproduce its own prefix.
    NondeterministicImpl { detail: String },
    /// Something else panicked inside the triage engine.
    ///
    /// A developer catching panics at the triage boundary will otherwise
    /// label a legitimate replayed assertion "nondeterministic Impl" — and in
    /// the branch criterion 3 identifies as the default, the user's assertion
    /// panic arrives preceded by a graph dump and by a `top_sort` call whose
    /// own rustdoc says it can panic and *replace* the original one. So the
    /// classification is on `validate_replay_event`'s own message, and
    /// everything else lands here with its payload rather than being assigned
    /// a cause it may not have.
    Panicked { detail: String },
}

impl From<crate::conformance::config::ConfigError> for ConfError {
    fn from(e: crate::conformance::config::ConfigError) -> Self {
        ConfError::Config { field: e.field }
    }
}

impl std::error::Error for ConfError {}

// ---------------------------------------------------------------------------
// Rendering. Everything below this line is the only user-facing text S5
// produces.
// ---------------------------------------------------------------------------

impl fmt::Display for ConfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConfError::SpecNotErrorFree { detail } => write!(
                f,
                "conformance: the specification is not error-free, so the conformance \
                 question is not well posed (conf-plan.md \u{a7}5.4; CA \u{a7}7's A-candidate 5 \
                 assumes no specification graph contains `err`). No verdict was produced. \
                 {detail}\nEither fix the specification, or — on the enumerator — accept \
                 the assumption with `ConfBuilder::skip_spec_errfree_check(true)`, which \
                 records it in the verdict. Under `Engine::CompleteFirst` that flag skips \
                 only the precheck: a sweep that meets a specification assertion failure \
                 still aborts the run. Under `Engine::Gated`, as under `CompleteFirst`. \
                 Under `Engine::Stateful` it has no effect and the only remedy is fixing \
                 the specification."
            ),
            // **It does not "keep its pre-triage form", because the caller has
            // no reports at all**: a triage failure is a run-level failure and
            // leaves through `Err`, so there is no verdict and no report list
            // on this path (gate-4 round 1, m7). The index is a position in the
            // list the run *would* have produced, and saying so is the honest
            // version.
            ConfError::TriageFailed { report, cause } => write!(
                f,
                "conformance: triage failed while completing the candidate violation that \
                 would have been report #{report}. **No verdict was produced and no report \
                 list is returned** — a triage failure is a failure of the run, not a \
                 conformance claim about the program, and the run is not resumed from here. \
                 Re-run with `ConfBuilder::triage(false)` to get the reports without their \
                 concrete traces. {cause}"
            ),
            ConfError::Config { field } => write!(
                f,
                "conformance: `Config::{}` is outside conformance scope (conf-plan.md \
                 \u{a7}9): {}. This check is UX; the same predicate is re-asserted when the \
                 engine is constructed, which is the guarantee.",
                field.field_name(),
                field.reason()
            ),
            ConfError::SpecNotAssertionSafe { thread, pos } => write!(
                f,
                "conformance: the specification failed an assertion on thread `{thread}` at \
                 {pos} inside the inner search, so it is not assertion-safe and the \
                 conformance question is not well posed (IMPL-PLAN-algorithms.md \u{a7}1). \
                 No verdict was produced and no report list is returned. Fix the \
                 specification; the \u{a7}5.4 precheck would have found this too unless it \
                 was skipped (`skip_spec_errfree_check(true)`) or bounded by \
                 `Config::max_iterations`."
            ),
            ConfError::KnobConflict { knob, conflicts_with } => write!(
                f,
                "conformance: `ConfBuilder::{knob}` cannot be combined with \
                 `{conflicts_with}` (P4-FLAT F5): `FlatCover` decides its eligibility on the \
                 precheck's enumeration of the specification and serves only the \
                 complete-first and gated engines. No verdict was produced."
            ),
            ConfError::SpecNotCommunicationFlat { thread, pos } => write!(
                f,
                "conformance: the specification is not communication-flat: thread `{thread}` \
                 performs a send or receive at {pos} that is not visible, so `FlatCover` \
                 (thm:flat, cor:mixedflat) is not exact for it and the run was refused \
                 rather than silently swept. Declare the thread visible, annotate the \
                 operation, or use `CompletionCover::Sweep`. No verdict was produced."
            ),
        }
    }
}

impl fmt::Display for TriageFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TriageFailure::NondeterministicImpl { detail } => write!(
                f,
                "The implementation did not reproduce its own recorded prefix: \
                 `validate_replay_event` refused the replay. Triage re-runs the \
                 implementation against the reported graph, and that requires the \
                 implementation to be deterministic except where TraceForge controls the \
                 choice (`nondet()`). Origin: replay divergence, **not** a failed \
                 assertion. {detail}"
            ),
            TriageFailure::Panicked { detail } => write!(
                f,
                "The triage engine panicked, and the payload is reproduced rather than \
                 classified — labelling an unidentified panic \"nondeterministic Impl\" is \
                 how a legitimate replayed assertion gets reported as a defect in the \
                 user's program. Payload: {detail}"
            ),
        }
    }
}

impl fmt::Display for ReportGate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.site())
    }
}

impl fmt::Display for ReportCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReportCause::NoCover => write!(
                f,
                "no specification graph covers the implementation graph below"
            ),
            ReportCause::VisibleError { thread, pos } => write!(
                f,
                "the declared visible thread `{thread}` failed an assertion at {pos}. The \
                 theorem speaks about visible behaviour, so this is a conformance report; \
                 an invisible thread's failed assertion is a note and never becomes one"
            ),
        }
    }
}

impl fmt::Display for Obligation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Obligation::ObservationMismatch {
                thread,
                position,
                spec,
                imp,
            } => {
                write!(
                    f,
                    "(M1) observation mismatch on `{thread}` at position {position}: the \
                     specification has {spec}, the implementation has {imp}"
                )?;
                if let Some(hint) = thread_id_hint(spec, imp) {
                    write!(f, "{hint}")?;
                }
                Ok(())
            }
            Obligation::MissingPullBack {
                spec_from,
                spec_to,
                imp_from,
                imp_to,
            } => write!(
                f,
                "(M2) missing pull-back edge: the specification orders {spec_from} before \
                 {spec_to}, and the matched implementation events {imp_from} and {imp_to} \
                 are unordered"
            ),
            Obligation::StatusMismatch { thread, spec, imp } => write!(
                f,
                "(M3) status mismatch on `{thread}`: the specification is {spec}, the \
                 implementation is {imp}"
            ),
            Obligation::NoOfferablePassedPhi => write!(
                f,
                "no offerable specification event passed \u{3a6}, so the search had nowhere \
                 left to go from this attempt"
            ),
        }
    }
}

impl fmt::Display for Diagnostics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Diagnostics::Available { prefix, obligation } => {
                let p = prefix
                    .iter()
                    .map(|(n, k)| format!("{n}: {k}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    f,
                    "inner-search diagnostics (recomputed after the run, so they did not \
                     influence it):\n    furthest-following attempt, by visible-thread \
                     observation count: [{p}]\n    first failing obligation: {obligation}"
                )
            }
            Diagnostics::Unavailable { because, kind } => match kind {
                UnavailableKind::Diverged => write!(
                    f,
                    "inner-search diagnostics unavailable: {because}. The diagnostics are \
                     recomputed outside the search, and a recomputation that does not \
                     reproduce the search's own verdict is not evidence about this report — \
                     saying so beats guessing"
                ),
                // Deliberately *not* the sentence above: here the recomputation
                // agreed with the search exactly, and claiming otherwise would
                // assert a condition the code did not check — which is the
                // defect this whole path exists to have fixed.
                UnavailableKind::NoValueForIt => write!(
                    f,
                    "inner-search diagnostics unavailable: {because}. The recomputation \
                     agreed with the search here; it is §7.1's list of obligations that \
                     has no name for what it found"
                ),
            },
            Diagnostics::NotApplicable => write!(
                f,
                "inner-search diagnostics do not apply: this report is a failed assertion, \
                 not a `Cover` answer"
            ),
            Diagnostics::NotProduced {
                by: Engine::CompleteFirst,
            } => write!(
                f,
                "the complete-first engine computes no inner-search diagnostics; this report \
                 is a failed coverage test at completion (lem:sig)"
            ),
            Diagnostics::NotProduced { by: Engine::Gated } => write!(
                f,
                "the gated engine computes no inner-search diagnostics; this report is an \
                 absence certificate set at a gate (cor:absence) or a failed coverage test \
                 at completion (lem:sig)"
            ),
            Diagnostics::NotProduced { .. } => write!(
                f,
                "the stateful engine computes no inner-search diagnostics; this report is a \
                 failed signature or containment lookup (lem:sig)"
            ),
        }
    }
}

impl fmt::Display for VisTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let word = if self.word.is_empty() {
            "\u{3b5} (no visible events)".to_owned()
        } else {
            self.word.join(" \u{2192} ")
        };
        let statuses = self
            .statuses
            .iter()
            .map(|(n, s)| format!("{n}: {s}"))
            .collect::<Vec<_>>()
            .join(", ");
        // The pair, never the word alone: `vis(σ)` is ⟨word, status vector⟩,
        // and a report whose only discriminator is (M3) shows two identical
        // words with nothing wrong in them if the status half is dropped.
        write!(
            f,
            "\u{27e8}word, status vector\u{27e9} = \u{27e8} {word} , [{statuses}] \u{27e9}"
        )
    }
}

impl fmt::Display for TriageOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TriageOutcome::Completed {
                vis,
                spec_mismatch,
                dump,
            } => write!(
                f,
                "triage completed this graph. The visible trace, canonically linearised:\n \
                 \u{a0}   {vis}\n    specification-side first mismatch: {spec_mismatch}\n\
                 {dump}"
            ),
            TriageOutcome::Blocked { ending } => write!(
                f,
                "triage could not complete this graph: the completion ended {ending} \
                 instead of finishing. That is not a conformance claim and there is no \
                 concrete complete trace to show \u{2014} the reported graph was cut out of a \
                 subtree the gate had already condemned, and completing it under the \
                 left-to-right schedule can deadlock on a suffix receive"
            ),
            TriageOutcome::ReplayedAssertion { thread, pos } => write!(
                f,
                "triage replayed the prefix and `{thread}`'s assertion failed again at \
                 {pos}, which is what this report says should happen. This is a replayed \
                 assertion and **not** a nondeterministic implementation"
            ),
            TriageOutcome::OtherAssertion { thread, pos } => write!(
                f,
                "triage replayed the prefix and an assertion failed on `{thread}` at \
                 {pos} — a *different* one from the failure this report names, so it is \
                 not the trace this report was asking for. It is still a replayed \
                 assertion and **not** a nondeterministic implementation"
            ),
        }
    }
}

impl fmt::Display for ConfExhaustion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "search budget exhausted at {} ({} implementation events). The inner search \
             spent all {} of its nodes without deciding, so it established **nothing** \
             here \u{2014} neither a cover nor its absence. This is not a report and it is not \
             silence. Raise the budget with `{}(n)` (the default is {}) and run again.",
            self.gate, self.events, self.budget, BUDGET_KNOB, DEFAULT_SEARCH_BUDGET
        )
    }
}

impl fmt::Display for ConfNote {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConfNote::InvisibleThread { thread, at } => write!(
                f,
                "note: `{thread}` failed an assertion at {at}, and it is not a declared \
                 visible thread. The theorem does not speak about it, so this is not a \
                 conformance report and nothing was pruned on its account."
            ),
            // **No adjective.** `AfterPrune ⟹ visible` is unproven and
            // believed unreachable, and `thread` is the runtime task name when
            // the thread is not declared visible — so calling it "a visible
            // thread" here would make the unproven claim by accident. The
            // position is named as one the statement *would* have occupied,
            // because nothing was installed there.
            ConfNote::AfterPrune { thread, would_be } => write!(
                f,
                "note: a further assertion failed after this execution was pruned, on \
                 `{thread}` at the position {would_be} its statement would have occupied. \
                 The execution was already condemned and the report that pruned it names \
                 the occasion, so this is not a second report. Whether this case is \
                 reachable at all is unproven."
            ),
        }
    }
}

impl fmt::Display for NotACertificate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NotACertificate::SearchExhausted {
                occurrences,
                budget,
            } => write!(
                f,
                "the inner search ran out of room {occurrences} time(s) on a budget of \
                 {budget} nodes, so \u{22a5} was never established there \u{2014} raise it with \
                 `{BUDGET_KNOB}(n)`"
            ),
            NotACertificate::StoppedAtFirstReport => write!(
                f,
                "`stop_at_first_report` was set, so the outer loop terminated by \
                 configuration rather than by exhausting the state space"
            ),
            NotACertificate::BoundedRun { max_iterations } => write!(
                f,
                "`Config::max_iterations` was set to {max_iterations}, so this was a \
                 bounded run: it stopped when it had counted enough endings, not when it \
                 had seen them all"
            ),
            NotACertificate::EndUnknown => write!(
                f,
                "nothing recorded how the outer loop ended, so \"the search completed\" is \
                 not established \u{2014} and it is a fact this tool carries rather than infers"
            ),
            NotACertificate::Reported { count } => write!(
                f,
                "{count} {} {} reported",
                CANDIDATE_VIOLATION,
                if *count == 1 { "was" } else { "were" }
            ),
        }
    }
}

impl fmt::Display for ConfReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "  {CANDIDATE_VIOLATION}: {}", self.cause)?;
        writeln!(f, "  raised at: {}", self.gate)?;
        writeln!(
            f,
            "  certifies ({:?}): {}",
            self.tag,
            if self.by_flat_cover {
                self.tag.certifies_flat(self.engine)
            } else {
                self.tag.certifies_under(self.engine)
            }
        )?;
        writeln!(f, "  implementation graph size: {} events", self.events)?;
        writeln!(f, "  {}", self.diagnostics)?;
        if let Some(t) = &self.triage {
            writeln!(f, "  {t}")?;
        }
        writeln!(f, "  implementation graph:\n{}", indent(&self.dump))?;
        match &self.replay {
            ReplaySnapshot::Serialized(s) => writeln!(
                f,
                "  serialized replay information ({} bytes of JSON) is attached to this \
                 report; see `ConfReport::replay_snapshot`",
                s.len()
            ),
            ReplaySnapshot::Unavailable { because } => {
                writeln!(f, "  serialized replay information unavailable: {because}")
            }
        }
    }
}

fn indent(s: &str) -> String {
    s.lines()
        .map(|l| format!("    {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

impl fmt::Display for ConfVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // F61: the seed goes first, so no rendering of a verdict omits it.
        let seed = self.outcome().seed;
        writeln!(
            f,
            "conformance: run seed {seed} (reproduce with the same `Config` plus `.with_seed({seed})`)"
        )?;
        match self {
            // ---- the certificate -------------------------------------------
            ConfVerdict::Conforms(c) => {
                match c.outcome.engine {
                    Engine::Enumerator => writeln!(
                        f,
                        "conformance: silence. No candidate violation, no exhausted search \
                         budget, and the outer loop reached the end of its state space."
                    )?,
                    // `P4-STATEFUL` T6, line (1).
                    Engine::Stateful => writeln!(
                        f,
                        "conformance: silence. Every complete graph of the implementation is \
                         covered by one of the specification (thm:stateful), and both \
                         enumerations reached the end of their state spaces."
                    )?,
                    // `P4-CFIRST` C7, line (1).
                    Engine::CompleteFirst if c.outcome().flat_counters.is_some() => writeln!(
                        f,
                        "conformance: silence. Every complete graph of the implementation is \
                         covered by one of the specification \u{2014} by a cached witness or by \
                         `FlatCover` (thm:cfirst with thm:flat, cor:mixedflat) \u{2014} and the \
                         outer exploration reached the end of its state space."
                    )?,
                    Engine::CompleteFirst => writeln!(
                        f,
                        "conformance: silence. Every complete graph of the implementation is \
                         covered by one of the specification \u{2014} by a cached witness or by \
                         a sweep (thm:cfirst) \u{2014} and the outer exploration reached the \
                         end of its state space."
                    )?,
                    // `P4-GATED` G6, line (1): both modes (a silent first-failure
                    // run coincides with the exhaustive run).
                    Engine::Gated if c.outcome().flat_counters.is_some() => writeln!(
                        f,
                        "conformance: silence. Every complete graph of the implementation is \
                         covered by one of the specification \u{2014} by a cached witness or by \
                         `FlatCover` (thm:gated with thm:flat, cor:mixedflat) \u{2014} and the \
                         outer exploration reached the end of its state space."
                    )?,
                    Engine::Gated => writeln!(
                        f,
                        "conformance: silence. Every complete graph of the implementation is \
                         covered by one of the specification \u{2014} by a cached witness or by \
                         a sweep (thm:gated) \u{2014} and the outer exploration reached the \
                         end of its state space."
                    )?,
                }
                render_flat(f, c.outcome())?;
                writeln!(f, "{ONLY_SILENCE_IS_A_VERDICT}")?;
                writeln!(f, "This run therefore certifies visible-trace refinement of the specification by the implementation, resting on:")?;
                for a in c.assumptions() {
                    writeln!(f, "  - {a}")?;
                }
                render_notes(f, &c.outcome)
            }

            // ---- reports ----------------------------------------------------
            ConfVerdict::Reported(o) => {
                writeln!(
                    f,
                    "conformance: {} {}(s).",
                    o.reports.len(),
                    CANDIDATE_VIOLATION
                )?;
                match o.engine {
                    Engine::Enumerator => {
                        writeln!(f, "{SETTLED_CLAIM}")?;
                        writeln!(f, "{UNSETTLED_CLAIM}")?;
                        writeln!(f, "{NOT_A_COMPLETE_SET}")?;
                    }
                    // `P4-STATEFUL` T6: the always-true lookup sentence, then
                    // `thm:stateful`'s "exactly" only when its premise holds.
                    Engine::Stateful => {
                        writeln!(f, "{STATEFUL_EACH_UNCOVERED}")?;
                        if o.end == SearchEnd::StateSpaceExhausted {
                            writeln!(f, "{STATEFUL_EXACTLY_THE_SET}")?;
                        }
                    }
                    // `P4-CFIRST` C7: the always-true sentence (scoped to
                    // complete graphs), `thm:cfirst`'s "exactly" only when
                    // the outer run completed *and* no cut fired (A27), and
                    // the prefix line whenever a cut report is present.
                    Engine::CompleteFirst => {
                        let cut_fired = o.reports.iter().any(|r| r.tag == ReportTag::VisibleError);
                        if o.flat_counters.is_some() {
                            writeln!(f, "{CFIRST_EACH_UNCOVERED_FLAT}")?;
                        } else {
                            writeln!(f, "{CFIRST_EACH_UNCOVERED}")?;
                        }
                        if o.end == SearchEnd::StateSpaceExhausted && !cut_fired {
                            if o.flat_counters.is_some() {
                                writeln!(f, "{CFIRST_EXACTLY_THE_SET_FLAT}")?;
                            } else {
                                writeln!(f, "{CFIRST_EXACTLY_THE_SET}")?;
                            }
                        }
                        if cut_fired {
                            writeln!(f, "{CFIRST_CUT_PREFIXES}")?;
                        }
                    }
                    // `P4-GATED` G6: first-failure's one sentence, or the
                    // always-true sentence and `thm:gated`'s "exactly" when the
                    // outer run completed.
                    Engine::Gated => {
                        let first_failure = o
                            .gated_counters
                            .as_ref()
                            .is_some_and(|c| c.first_failure_mode);
                        let flat = o.flat_counters.is_some();
                        if first_failure {
                            writeln!(f, "{}", if flat { GATED_FIRST_FAILURE_FLAT } else { GATED_FIRST_FAILURE })?;
                        } else {
                            writeln!(f, "{}", if flat { GATED_EACH_UNCOVERED_FLAT } else { GATED_EACH_UNCOVERED })?;
                            if o.end == SearchEnd::StateSpaceExhausted {
                                writeln!(f, "{}", if flat { GATED_EXACTLY_THE_SET_FLAT } else { GATED_EXACTLY_THE_SET })?;
                            }
                        }
                    }
                }
                render_flat(f, o)?;
                writeln!(f, "{RESIDUAL_SOURCES}")?;
                writeln!(f, "{ONLY_SILENCE_IS_A_VERDICT}")?;
                render_truncation(f, o)?;
                for (i, r) in o.reports.iter().enumerate() {
                    writeln!(f, "\n#{i}")?;
                    write!(f, "{r}")?;
                }
                render_exhaustions(f, o)?;
                render_notes(f, o)?;
                render_caveats(f, o)
            }

            // ---- neither -----------------------------------------------------
            ConfVerdict::Inconclusive(o) => {
                writeln!(
                    f,
                    "conformance: **no verdict**. This run produced no {CANDIDATE_VIOLATION}, \
                     and that is not the same thing as silence."
                )?;
                writeln!(f, "{ONLY_SILENCE_IS_A_VERDICT}")?;
                if o.inconclusive() {
                    writeln!(
                        f,
                        "inconclusive: the inner search ran out of budget {} time(s), so the \
                         gates it exhausted established nothing (ruling 1: an exhaustion is \
                         never a report).",
                        o.exhaustions.len()
                    )?;
                }
                writeln!(f, "This run is not a certificate, for these reasons:")?;
                for r in o.not_a_certificate() {
                    writeln!(f, "  - {r}")?;
                }
                render_flat(f, o)?;
                render_exhaustions(f, o)?;
                render_notes(f, o)?;
                render_caveats(f, o)
            }
        }
    }
}

/// `P4-FLAT` criterion 8: the `Flat` block — nothing at all under `Sweep`, so
/// every pinned `Sweep` rendering is byte-identical.
fn render_flat(f: &mut fmt::Formatter<'_>, o: &ConfOutcome) -> fmt::Result {
    let Some(fc) = o.flat_counters.as_ref() else {
        return Ok(());
    };
    if let Some(e) = o.flat_eligibility.as_ref() {
        writeln!(
            f,
            "the specification is communication-flat: {} graphs scanned",
            e.spec_graphs_scanned
        )?;
    }
    if !o.reports.is_empty() {
        writeln!(
            f,
            "completion reports not raised under an absence certificate are `FlatCover`'s \
             \u{22a5} (thm:flat)"
        )?;
    }
    writeln!(
        f,
        "FlatCover: {} calls, {} visits, {} witnesses, {} value branches, {} source options \
         tried ({} recursed), kills send/slot/source/done {}/{}/{}/{}, max depth {}, {} ms",
        fc.calls,
        fc.visits,
        fc.witnesses,
        fc.nd_branches,
        fc.source_branches,
        fc.source_recursions,
        fc.send_kills,
        fc.slot_kills,
        fc.source_kills,
        fc.done_kills,
        fc.max_depth,
        fc.wall_time_ms
    )
}

/// **A report list the run stopped early is a shorter list, and nothing said
/// so** (gate-4 round 1, m6).
///
/// The `Inconclusive` arm enumerates `not_a_certificate()` because silence is
/// what those reasons destroy. But `stop_at_first_report` and
/// `max_iterations` truncate a *report list* just as surely, and a user
/// reading three reports off a bounded run had no way to know a fourth was
/// never looked for. §7.2's "the report list is not a complete set of
/// violations" covers the A1 direction, which is about revisits the search
/// lost — not about a loop the user or the gate stopped.
fn render_truncation(f: &mut fmt::Formatter<'_>, o: &ConfOutcome) -> fmt::Result {
    match o.end {
        SearchEnd::StateSpaceExhausted => Ok(()),
        // `P4-GATED` G5/G6 (gate-4 round 01 m5): first-failure mode implies the
        // stop, so the sentence must not claim the user set the knob.
        SearchEnd::StoppedAtFirstReport
            if o.engine == Engine::Gated
                && o.gated_counters
                    .as_ref()
                    .is_some_and(|c| c.first_failure_mode) =>
        {
            writeln!(
                f,
                "**This list is truncated by configuration.** `GatedMode::FirstFailure` \
                 implies `stop_at_first_report`, so the search stopped at the report below \
                 and looked for no others. There may be more; this run did not ask."
            )
        }
        SearchEnd::StoppedAtFirstReport => writeln!(
            f,
            "**This list is truncated by configuration.** `stop_at_first_report` was set, \
             so the outer loop stopped at the report below and looked for no others. There \
             may be more; this run did not ask."
        ),
        SearchEnd::MaxIterations(n) => writeln!(
            f,
            "**This list is truncated by a bound you set.** `Config::max_iterations` was \
             {n}, so the outer loop stopped after counting that many endings rather than \
             after seeing them all. There may be more reports; this run did not look."
        ),
        SearchEnd::Unknown => writeln!(
            f,
            "**This list may be truncated.** Nothing recorded how the outer loop ended, so \
             whether the state space was exhausted is not established."
        ),
        // Never rendered: see `not_a_certificate`'s arm.
        SearchEnd::SpecNotAssertionSafe => {
            unreachable!("conformance: rendering a ConfOutcome from a run the inner search aborted")
        }
    }
}

fn render_exhaustions(f: &mut fmt::Formatter<'_>, o: &ConfOutcome) -> fmt::Result {
    if o.exhaustions.is_empty() {
        return Ok(());
    }
    writeln!(f, "\nexhausted searches ({}):", o.exhaustions.len())?;
    for e in &o.exhaustions {
        writeln!(f, "  {e}")?;
    }
    Ok(())
}

fn render_notes(f: &mut fmt::Formatter<'_>, o: &ConfOutcome) -> fmt::Result {
    if o.notes.is_empty() {
        return Ok(());
    }
    writeln!(
        f,
        "\nnotes ({}) \u{2014} none of these is a report:",
        o.notes.len()
    )?;
    for n in &o.notes {
        writeln!(f, "  {n}")?;
    }
    Ok(())
}

fn render_caveats(f: &mut fmt::Formatter<'_>, o: &ConfOutcome) -> fmt::Result {
    if o.spec_errfree == SpecErrFreedom::Assumed {
        writeln!(
            f,
            "\nassumption recorded: specification err-freedom was **assumed**, not checked \
             (`ConfBuilder::skip_spec_errfree_check(true)`). If a specification execution \
             can fail an assertion, the problem statement this tool answers does not hold."
        )?;
    }
    // `P4-STATEFUL` T6: triage is ignored by the stateful engine, so the
    // caveat would advertise a knob that does nothing there.
    if !o.triage_enabled && !o.reports.is_empty() && o.engine == Engine::Enumerator {
        writeln!(
            f,
            "\ntriage is off (the default). `ConfBuilder::triage(true)` completes each \
             reported graph into a concrete trace, at the cost of one extra engine run per \
             report."
        )?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The rendering vocabulary.
//
// These four turn engine values into the words a user reads. They live here,
// not at their call sites, for criterion 1's reason: the rendering module is
// the module that decides what the tool *says*, and a `format!` that builds a
// user-facing phrase somewhere else is the same leak as a `println!` there.
// `diagnose.rs` and `triage.rs` call these; they compose no phrases of their
// own.
// ---------------------------------------------------------------------------

/// One observation, as a user reads it.
pub(crate) fn obs_text(obs: &crate::conformance::obs::Obs) -> String {
    use crate::conformance::obs::Obs;
    match obs {
        Obs::Send(v) => format!("send {:?}", v.val),
        Obs::Recv(None) => "receive \u{22a5} (read nothing)".to_owned(),
        Obs::Recv(Some(v)) => format!("receive {:?}", v.val),
    }
}

/// **The commonest cause of a value mismatch, named when it is visible.**
///
/// A `ThreadId` is an opaque number allocated per program in spawn order, so
/// the same logical thread carries a different number on the two sides whenever
/// they spawn a different count of *invisible* threads before it — which is what
/// an abstraction does. A protocol that tells one thread about another by
/// sending its id therefore mismatches on every such observation while both
/// programs behave identically. It is the trap a first-time user falls into,
/// because passing ids in messages is the natural way to write an actor
/// protocol.
///
/// Detection is by the **rendered** value, so it also catches an id inside a
/// user type (`Prepare(ThreadId { .. })`), which no type-level check could see:
/// a `Val` is a `Box<dyn Message>`, and `Message` is `Send + DynClone` plus
/// `Debug` under `print_vals`, with no reflection and no serialization to look
/// inside a user type with.
///
/// So it detects through `Debug`, and the text says `ThreadId` because the
/// derived `Debug` prints the struct's name. Under `print_vals_custom` values
/// would render through `Display` instead, where a hand-written impl need not
/// print the name and the note would not fire — the cause it names would be
/// unaffected, only the detection. That is stated as a conditional on purpose:
/// **that configuration does not compile today**, and
/// [`nothing_text_with_examples`] carries the measurement.
///
/// A false positive costs a sentence and is harmless; a message whose own text
/// happens to contain the word would earn one undeservedly.
fn thread_id_hint(spec: &str, imp: &str) -> Option<&'static str> {
    if !spec.contains("ThreadId") && !imp.contains("ThreadId") {
        return None;
    }
    Some(
        ".\n  Note: a `ThreadId` is numbered per program in spawn order, so the same \
         thread has a different number on the two sides whenever they spawn a different \
         number of invisible threads before it. If an id travels inside a message, either \
         give the threads whose ids are observed the same spawn position on both sides, or \
         send `Thread::name()` instead of the id.",
    )
}

/// Where a row has no observation at all at a position.
pub(crate) fn nothing_text() -> String {
    "nothing (the row ends here)".to_owned()
}

/// The same, naming what the specification **was** seen to observe there.
///
/// A mismatch at a thread's first observation is reported against an attempt in
/// which that thread has not acted, so the bare wording above says the row ends
/// — which a reader takes to mean the specification is *missing* an event. It
/// may not be: other attempts of the same specification were seen to observe
/// something at that position, and those are what this names
/// (`diagnose::SeenAt`).
///
/// **It names them and stops**, in four deliberate respects.
///
/// - *No cause is asserted.* An earlier draft ended "so the difference is in
///   the value, not a missing event". That is sometimes true — on F41's own
///   shape the example is `send ThreadId { opaque_id: 1 }` against an
///   implementation's `2`, and the difference is exactly in the value — and
///   sometimes false: where the two attempts are `follows`-incomparable the
///   example is byte-identical to the implementation's own observation, so the
///   disagreement is in the order or the coverage and the row really does end.
///   Both shapes reach this function and it cannot tell them apart, because
///   `SeenAt` records a following row and a rejected one alike. So it asserts
///   no cause: the examples are evidence for the reader, not a diagnosis.
/// - *They are examples, not requirements.* A specification generally has many
///   executions and different ones may observe different things here, so this
///   must never read as "the specification requires".
/// - *It stays a noun phrase*, because §7.1 substitutes it into "the
///   specification has _, the implementation has _". A clause here does not
///   parse in that slot, which is how the earlier draft read.
/// - *It says "attempt", not "execution".* What the search saw is a partial
///   specification graph. Such a graph is a genuine prefix of specification
///   behaviour — every offer installed in it came from probing the
///   specification — but nothing shows it extends to a *complete* execution,
///   and elsewhere in this module "a specification execution" means a complete
///   one. **Measured, not hypothetical**: an example has been observed coming
///   from a branch entered six times that got past its blocking receive zero
///   times (`P3-F41-round2` §5). With "execution" the sentence would be false
///   there; with "attempt" it is true, and it is the strongest true thing this
///   function knows.
///
/// Two things it does **not** disclose, both recorded rather than papered over:
/// that an example may come from an attempt which never completes, as above;
/// and that `diagnose::SEEN_EXAMPLES` may have truncated the list. Note which
/// wording is exposed: the singular "another attempt" fires exactly when one
/// value was kept, and truncation needs a *fourth* distinct value, which always
/// renders in the plural — so the undisclosed case is a plural list of three
/// that is three **of more**, never a singular claim that understates.
/// Whether either deserves words in a user-facing
/// report is an owner question — more hedging in a sentence read during a
/// failure is not obviously an improvement.
///
/// **The `Debug` dependency is not a configuration a user can be in.** Both
/// items this function belongs to need values to render, so the obvious question
/// is what happens without `print_vals`. Measured (2026-09-28,
/// `cargo check -p traceforge --lib`): `--no-default-features` fails with **7**
/// errors and `--features print_vals_custom` with **85**. The two builds fail in
/// different places and the distinction is worth keeping straight. Of the seven,
/// two are [`obs_text`] itself, which formats a `Val` with `{:?}`, and the other
/// five are upstream: `exec_graph.rs` (three), `msg.rs`, and `sync/mpsc.rs`,
/// which does `format!("{:?}", msg).contains("mpscClose")` on an unbounded `T`.
/// The 85 are elsewhere again — `sync/rwlock.rs`, `msg.rs`, `future/mod.rs`,
/// `lib.rs`, `sync/mutex.rs` — and conformance is a rounding error in that
/// total. So there is no build of this crate in
/// which a message does not implement `Debug`, and the dependency cannot be
/// exercised. It is recorded rather than defended: if those configurations are
/// ever repaired, this function and [`thread_id_hint`] both need a look, and
/// `obs_text` needs a rendering that does not assume `Debug`.
pub(crate) fn nothing_text_with_examples(examples: &[String]) -> String {
    if examples.is_empty() {
        return nothing_text();
    }
    let listed = examples.join(", ");
    let attempts = if examples.len() == 1 {
        "another attempt of the specification observed"
    } else {
        "other attempts of the specification observed"
    };
    format!(
        "nothing here (this attempt's row ends, though {attempts} {listed} at \
         this position)"
    )
}

/// One event position.
pub(crate) fn event_text(e: crate::event::Event) -> String {
    format!("{e}")
}

/// One visible thread's status (CA §3).
pub(crate) fn status_text(s: crate::conformance::morphism::Status) -> &'static str {
    use crate::conformance::morphism::Status;
    match s {
        Status::Errored => "errored",
        Status::Done => "done",
        Status::Blocked => "blocked",
    }
}

// ---------------------------------------------------------------------------
// Construction helpers used by `mod.rs`. No rendering here.
// ---------------------------------------------------------------------------

/// §7.1's serialized half, built **at capture time and off the live `Must`**.
///
/// See [`ReplaySnapshot`] for why `store_replay_information`'s conformance
/// early return is not deleted and why `top_sort`'s precondition holds for
/// each report kind. The `catch_unwind` is a **backstop, not the argument**:
/// if the precondition ever stops holding, this turns an index panic that
/// would destroy the whole run into one report whose serialized half is marked
/// unavailable and says why.
///
/// The `MustState` is borrowed and cloned only for
/// `ReplayInformation::create`'s by-value argument; the clone is dropped as
/// soon as the JSON exists, so nothing retains it (gate-4 round 1, M3).
pub(crate) fn replay_snapshot(
    graph: &ExecutionGraph,
    state: &crate::must::MustState,
    config: &crate::Config,
    pos: Option<crate::event::Event>,
) -> ReplaySnapshot {
    let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let sorted = graph.top_sort(pos);
        let info = crate::replay::ReplayInformation::create(sorted, state.clone(), config.clone());
        // `to_string`, not `to_string_pretty`: the artefact is an input to
        // `traceforge::replay`, not something a human reads, and the
        // indentation is a large fraction of a figure that is already the
        // dominant per-report cost (gate-4 round 2, M3).
        serde_json::to_string(&info)
    }));
    match attempt {
        Ok(Ok(s)) => ReplaySnapshot::Serialized(s),
        Ok(Err(e)) => ReplaySnapshot::Unavailable {
            because: format!("the replay information did not serialize: {e}"),
        },
        Err(_) => ReplaySnapshot::Unavailable {
            because: "linearising the reported graph panicked, which means `top_sort`'s \
                      precondition did not hold on it after all — see `ReplaySnapshot`'s \
                      argument, which is now wrong"
                .to_owned(),
        },
    }
}

/// No gate-disabled mode renders the snapshot its `ConfCtx` would take, so
/// none of them pays for a linearisation here. Only the precheck and triage
/// can reach this: their sinks are read for their contents and discarded.
/// `Collect` and `Enumerate` never take a context snapshot at all — their
/// `report_visible_error` returns before the reporting branch — and the
/// stateful engine's rendered reports carry snapshots taken at its completion
/// sink through [`replay_snapshot`] directly (`P4-STATEFUL` T3). See
/// `ConfCtx::snapshot`.
pub(crate) fn replay_not_produced() -> ReplaySnapshot {
    ReplaySnapshot::Unavailable {
        because: "this report was raised on the specification err-freedom precheck or on a \
                  triage run, whose sink is read for its contents and discarded rather \
                  than rendered; a rendered stateful report takes its snapshot at the \
                  completion sink instead"
            .to_owned(),
    }
}

/// Build the public report from S4's sink entry plus S5's additions.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_report(
    kind: &ReportKind,
    gate: Option<Gate>,
    events: usize,
    graph: &ExecutionGraph,
    replay: ReplaySnapshot,
    diagnostics: Diagnostics,
) -> ConfReport {
    build_report_for(
        Engine::Enumerator,
        kind,
        gate,
        events,
        graph,
        replay,
        diagnostics,
    )
}

/// [`build_report`] for a named engine (`P4-STATEFUL` T6).
pub(crate) fn build_report_for(
    engine: Engine,
    kind: &ReportKind,
    gate: Option<Gate>,
    events: usize,
    graph: &ExecutionGraph,
    replay: ReplaySnapshot,
    diagnostics: Diagnostics,
) -> ConfReport {
    let cause = match kind {
        ReportKind::NoCover => ReportCause::NoCover,
        ReportKind::VisibleError { thread, pos } => ReportCause::VisibleError {
            thread: thread.clone(),
            pos: pos.to_string(),
        },
    };
    let gate = ReportGate::of(gate);
    let tag = ReportTag::of(&cause, gate);
    ConfReport {
        engine,
        gate,
        cause,
        tag,
        events,
        dump: graph.to_string(),
        replay,
        diagnostics,
        triage: None,
        by_flat_cover: false,
    }
}
