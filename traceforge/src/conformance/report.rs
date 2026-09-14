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

use crate::conformance::config::{ScopeField, DEFAULT_SEARCH_BUDGET};
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
    /// It did **not** reproduce the search's verdict, so it says so rather
    /// than guessing. `blame_for` cost S4 two rounds to learn this.
    Unavailable { because: String },
    /// There is no inner-search attempt to describe: a §4.4 visible-error
    /// report is not a `Cover` answer at all.
    NotApplicable,
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

/// The `--naive-oracle` cross-check for one report (§7.3, criterion 10).
///
/// **What it compares, stated correctly at the third attempt** (gate-4 round
/// 2, M2). Not Φ against un-Φ: those are the same traversal. Φ filters
/// `SpecVisit`'s loop *range*, and every offer it would reject is refused a
/// step later by `spec_step`'s own `follows` conjunct, which this module keeps
/// in both modes — while the one offer kind that bypasses `spec_step`, a
/// nondet, has an extension that follows exactly when its parent does, so Φ
/// never rejects one. The `use_phi` flag changes no answer and visits no
/// different graph.
///
/// What it does compare is `conformance::diagnose::Recompute` against
/// S3's `Search::cover` — **two implementations of one algorithm**. That is
/// real content and it is what a disagreement means: one of the two is wrong.
/// It is also less than criterion 10 asked for, since neither is independent
/// of the other's premises. See the S5 report's finding F-17.
///
/// **Three-valued, and it has to be** (gate-4 round 1, M2). The first version
/// asked `matches!(answer, Ok(Answer::Found))` and reported "agrees" for
/// everything else — so a traversal that ran out of budget, having established
/// nothing whatever, rendered as a second opinion confirming the report. That
/// is `search.rs`'s own recurring defect, the one its comments record removing
/// six times: **a failure turned into an answer**. It is worse here than
/// anywhere, because this artefact exists for no other purpose than to be an
/// independent check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OracleOutcome {
    /// The independent traversal found no cover either. The report is
    /// confirmed, by an implementation that is not the one that produced it.
    Agrees,
    /// The independent traversal **found a cover** where `Search::cover`
    /// reported none. The two implementations disagree, and one of them is
    /// wrong.
    Disagrees,
    /// The independent traversal ran out of budget. It established
    /// **nothing**: this is neither agreement nor disagreement.
    ///
    /// Unreachable on the `NoCover` path as things stand — a report *means*
    /// `Search::cover`'s rebuild-from-empty completed inside one budget, and
    /// this is the same traversal from the same start with the same budget.
    /// The variant exists because that is a property of two implementations
    /// agreeing, not an invariant, and the alternative is to fold exhaustion
    /// into one of the other two.
    Inconclusive { budget: usize },
    /// The traversal raised a usage error (§8/§9) rather than answering.
    Failed { detail: String },
}

/// One recorded candidate violation, with everything §7.1 asks a report to
/// carry.
#[derive(Clone)]
pub struct ConfReport {
    pub(crate) gate: ReportGate,
    pub(crate) cause: ReportCause,
    pub(crate) events: usize,
    /// §7.1's outer graph snapshot, dump half.
    pub(crate) dump: String,
    /// §7.1's outer graph snapshot, serialized half. See
    /// [`ReplaySnapshot`].
    pub(crate) replay: ReplaySnapshot,
    pub(crate) diagnostics: Diagnostics,
    pub(crate) triage: Option<TriageOutcome>,
    pub(crate) oracle: Option<OracleOutcome>,
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
    /// The `--naive-oracle` cross-check, when it was asked for.
    pub fn oracle(&self) -> Option<&OracleOutcome> {
        self.oracle.as_ref()
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
            ConfNote::InvisibleThread { thread, .. } | ConfNote::AfterPrune { thread, .. } => thread,
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
    /// §5.4's precheck ran and the specification was error-free.
    Checked,
    /// `ConfBuilder::skip_spec_errfree_check(true)`. The verdict records the
    /// assumption, because an opt-out that leaves no trace is a silent change
    /// of what the verdict means.
    Assumed,
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
}

impl ConfOutcome {
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
        }
        out
    }
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
                 {detail}\nEither fix the specification, or accept the assumption with \
                 `ConfBuilder::skip_spec_errfree_check(true)`, which records it in the \
                 verdict."
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
            } => write!(
                f,
                "(M1) observation mismatch on `{thread}` at position {position}: the \
                 specification has {spec}, the implementation has {imp}"
            ),
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
            Diagnostics::Unavailable { because } => write!(
                f,
                "inner-search diagnostics unavailable: {because}. The diagnostics are \
                 recomputed outside the search, and a recomputation that does not \
                 reproduce the search's own verdict is not evidence about this report — \
                 saying so beats guessing"
            ),
            Diagnostics::NotApplicable => write!(
                f,
                "inner-search diagnostics do not apply: this report is a failed assertion, \
                 not a `Cover` answer"
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

impl fmt::Display for OracleOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OracleOutcome::Agrees => write!(
                f,
                "naive oracle: a second, independently written traversal of the same \
                 algorithm agrees \u{2014} it found no cover either"
            ),
            // **Not "\u{3a6} lost a cover"** (gate-4 round 2, M2). The comparison is
            // between two implementations, not between two filters; the un-\u{3a6}
            // traversal visits the same graphs in the same order as the \u{3a6}'d one,
            // so a difference in answer cannot be attributed to \u{3a6}.
            OracleOutcome::Disagrees => write!(
                f,
                "naive oracle: **disagreement**. A second, independently written traversal \
                 of the same algorithm found a cover where the search that produced this \
                 report found none. One of the two is wrong, and this report is only as \
                 good as whichever it is \u{2014} treat it as unreliable until the two are \
                 reconciled"
            ),
            OracleOutcome::Inconclusive { budget } => write!(
                f,
                "naive oracle: **established nothing**. The second traversal spent all \
                 {budget} of its nodes without deciding, so it neither confirms nor \
                 contradicts this report. Raise the budget with `{BUDGET_KNOB}(n)` if you \
                 want the cross-check to mean something"
            ),
            OracleOutcome::Failed { detail } => write!(
                f,
                "naive oracle: **could not run**. The second traversal raised a usage error \
                 rather than answering, so it established nothing: {detail}"
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
            self.gate,
            self.events,
            self.budget,
            BUDGET_KNOB,
            DEFAULT_SEARCH_BUDGET
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
        writeln!(f, "  implementation graph size: {} events", self.events)?;
        writeln!(f, "  {}", self.diagnostics)?;
        if let Some(t) = &self.triage {
            writeln!(f, "  {t}")?;
        }
        if let Some(o) = &self.oracle {
            writeln!(f, "  {o}")?;
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
        match self {
            // ---- the certificate -------------------------------------------
            ConfVerdict::Conforms(c) => {
                writeln!(
                    f,
                    "conformance: silence. No candidate violation, no exhausted search \
                     budget, and the outer loop reached the end of its state space."
                )?;
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
                writeln!(f, "{SETTLED_CLAIM}")?;
                writeln!(f, "{UNSETTLED_CLAIM}")?;
                writeln!(f, "{NOT_A_COMPLETE_SET}")?;
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
                writeln!(f, "This run is not a certificate, for these reasons:")?;
                for r in o.not_a_certificate() {
                    writeln!(f, "  - {r}")?;
                }
                render_exhaustions(f, o)?;
                render_notes(f, o)?;
                render_caveats(f, o)
            }
        }
    }
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
    writeln!(f, "\nnotes ({}) \u{2014} none of these is a report:", o.notes.len())?;
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
    if !o.triage_enabled && !o.reports.is_empty() {
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

/// Where a row has no observation at all at a position.
pub(crate) fn nothing_text() -> String {
    "nothing (the row ends here)".to_owned()
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

/// The two gate-disabled engines do not produce reports anyone reads, so they
/// do not pay for a linearisation. See `ConfCtx::snapshot`.
pub(crate) fn replay_not_produced() -> ReplaySnapshot {
    ReplaySnapshot::Unavailable {
        because: "this report was raised on the specification err-freedom precheck or on a \
                  triage run, whose sink is read for its contents and discarded; only the \
                  outer run's reports are rendered"
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
    let cause = match kind {
        ReportKind::NoCover => ReportCause::NoCover,
        ReportKind::VisibleError { thread, pos } => ReportCause::VisibleError {
            thread: thread.clone(),
            pos: pos.to_string(),
        },
    };
    ConfReport {
        gate: ReportGate::of(gate),
        cause,
        events,
        dump: graph.to_string(),
        replay,
        diagnostics,
        triage: None,
        oracle: None,
    }
}
