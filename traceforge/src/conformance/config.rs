//! `ConfConfig`, `ConfBuilder`, and §9's **config-time** layer.
//!
//! `conf-plan.md` §3's module table lists this file; §12 listed it in no step
//! until the owner's ruling of 2026-09-14 (blocked item **A** of P3-S5) gave
//! it to S5 along with the rest of the public entry.
//!
//! §9 is explicit about the division of labour and it is worth repeating here,
//! because the shape of this file only makes sense with it: **this layer is
//! UX; the `Must::new`-time assertion is the guarantee.** A `Config` can reach
//! a `Must` without ever passing through [`ConfBuilder::build`] — `replay`
//! deserializes one, `estimate_execs_with_config` overwrites two of its fields
//! — so nothing here may be the only thing standing between an out-of-scope
//! configuration and a conformance run. What it buys is a `Result` at the call
//! site instead of a panic three frames into the engine.
//!
//! **No user-facing string is produced in this file** (criterion 1). The
//! rejection is data; [`crate::conformance::report`] renders it.

use crate::conformance::selector::{InnerOrder, Selector};

use crate::{ConsType, ExplorationMode, SchedulePolicy};

/// Which checker a conformance run uses (`P4-STATEFUL` T6; plan §1).
///
/// Exhaustive on purpose, per `conformance/mod.rs`'s policy: the variants are
/// the paper's four checkers; CompleteFirst (Part 4) and Gated (Part 5) were
/// the later additions a caller matching on this enum was told to expect.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Engine {
    /// The directed enumerator (paper §8.7): decides, with an inner search.
    #[default]
    Enumerator,
    /// SVerify (paper §8.3): enumerates both families, indexes the
    /// specification's signatures and orders, streams the implementation.
    /// Under it `triage`, `search_budget`, `inner_order` and `memo` are
    /// ignored, and `skip_spec_errfree_check` has no effect (the index run
    /// *is* the §5.4 check).
    Stateful,
    /// CVerify (paper §8.5, `P4-CFIRST`): Must on the implementation,
    /// uncut; at each complete graph the witness cache `W` is probed, then
    /// the specification is swept (Must, unpruned, stopped at the first
    /// covering graph). Under it `triage`, `search_budget`, `inner_order` and
    /// `memo` are ignored; `skip_spec_errfree_check` skips only the (unbounded)
    /// precheck — a sweep that meets a specification assertion failure still
    /// aborts the run; `early_error_cut` is honoured (this engine only);
    /// `max_iterations` bounds the outer run only. **Sweeps are isolated
    /// explorations**: each runs on its own thread with no
    /// `ExecutionObserver` and no trace/dot output (a sweep runs nested inside
    /// one outer execution, which an observer with per-exploration state
    /// could not tell apart). The configured observers and files therefore
    /// see the precheck's exploration (when it runs; here unbounded, on the
    /// specification — the other engines likewise show their observers a
    /// specification exploration first) and the outer run, never a sweep. A
    /// sweep still prints to stdout — progress lines by default
    /// (`progress_report = 0` is the 1, 2, …, 9, 10, 20, … schedule) and
    /// graphs under `verbose` — with counters that restart per sweep.
    CompleteFirst,
    /// GVerify (paper §8.6, `P4-GATED`): complete-first plus a gate after
    /// every visible event — the carried witness re-tested by `cone`, then by
    /// policy a sweep that returns a fresh witness or certifies absence; a
    /// certificate skips every gate and completion test below it. Two modes
    /// (`GatedMode`) and three policies (`GatePolicy`). Under it `triage`,
    /// `search_budget`, `inner_order`, `memo` **and `early_error_cut`** are
    /// ignored; `skip_spec_errfree_check` as under `CompleteFirst`;
    /// `max_iterations` bounds the outer run only. Sweeps are isolated as
    /// under `CompleteFirst`.
    Gated,
}

/// `P4-GATED` G5: the gated checker's reporting contract.
/// Which engine answers the **completion question** in the complete-first and
/// gated checkers (`P4-FLAT` F4; `flat.tex` §9's drop-in paragraph): the
/// directed sweep of Parts 4–5, or `FlatCover`, exact for a communication-flat
/// specification and refused for any other (eligibility is decided on the
/// §5.4 precheck's enumeration, so the knob requires the precheck — D12, D13).
/// Gate sweeps are unchanged; the enumerator and the stateful engine do not
/// read it (a `ConfError::KnobConflict` at `run`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum CompletionCover {
    #[default]
    Sweep,
    Flat,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum GatedMode {
    /// Reports only at complete graphs; the outer run is Must's, uncut
    /// (`thm:gated`: exactly the uncovered members of `Graphs(Impl)`).
    #[default]
    Exhaustive,
    /// A gate that certifies absence reports the gated partial graph and the
    /// whole search stops; so does the first completion report (`thm:gated`:
    /// decides).
    FirstFailure,
}

/// `P4-GATED` G5: when a gate pays for a sweep of the specification.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum GatePolicy {
    /// Decline every sweep: complete-first plus the gates' bookkeeping.
    Never,
    /// Sweep at every gate whose carried witness fails.
    #[default]
    Always,
    /// Sweep, but stop after `B` complete specification graphs tested in that
    /// sweep (`W` probes do not count); on the limit the gate carries nothing
    /// and certifies nothing.
    Budget(usize),
}

/// The inner search's node ceiling per `Cover` attempt, when the user does not
/// set one.
///
/// It had no knob at all before S5 — `verify_conformance` took `budget:
/// usize` positionally and §8's sketch had nothing for it — which is half of
/// why criterion 2 requires an exhaustion to *name* this number and the knob
/// that raises it. A budget a user cannot see is a budget a user cannot
/// raise.
///
/// The value is a working default rather than a measured one, and is said to
/// be: the draft's examples settle in tens of nodes, the fragment-scale pairs
/// S6 will generate in hundreds, and 10 000 leaves room for both while still
/// failing loudly rather than hanging (`search.rs`'s `Budget` exists for
/// backlog **F34**, the non-monotone probe graph).
pub const DEFAULT_SEARCH_BUDGET: usize = 10_000;

/// One `Config` field that §9 puts outside conformance scope.
///
/// **Nine variants, eight of them reachable without `--features symbolic`.**
/// The enumeration is per *field*, not per assertion: `assert_config_in_scope`
/// covers nine fields with seven assertion macros, because two of them test
/// two fields each. A per-macro enumeration would let a `build()` that
/// rejects `parallel` and forgets `partitioned_parallelization` tick the
/// "parallel" box and be caught only at `Must::new` — "loudly and later",
/// which is what criterion 7 exists to prevent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ScopeField {
    /// `Config::cons_type` — conformance is scoped to asyn/p2p/cd; mailbox is
    /// out. Tested on the *communication model*, so the deprecated `MO`
    /// spelling is caught as well as `Mailbox`.
    ConsType,
    /// `Config::schedule_policy` — LTR only.
    SchedulePolicy,
    /// `Config::mode` — verification only, not estimation.
    Mode,
    /// `Config::lossy_budget` — lossy sends are excluded (obligation
    /// **O-skip** depends on it).
    LossyBudget,
    /// `Config::parallel` — the shared-queue parallel mode.
    Parallel,
    /// `Config::partitioned_parallelization` — the *other* parallel mode, and
    /// its own field.
    PartitionedParallelization,
    /// `Config::predetermined_choices`.
    PredeterminedChoices,
    /// `Config::predetermined_global_choices` — a second map, a second field.
    PredeterminedGlobalChoices,
    /// `Config::symbolic`. Only exists under `--features symbolic`; the
    /// variant exists unconditionally so that the count is the same number
    /// wherever it is written down, and [`ScopeField::checked`] says which
    /// build is being talked about.
    Symbolic,
}

impl ScopeField {
    /// Every field §9 excludes, in a fixed order. Nine.
    pub const ALL: [ScopeField; 9] = [
        ScopeField::ConsType,
        ScopeField::SchedulePolicy,
        ScopeField::Mode,
        ScopeField::LossyBudget,
        ScopeField::Parallel,
        ScopeField::PartitionedParallelization,
        ScopeField::PredeterminedChoices,
        ScopeField::PredeterminedGlobalChoices,
        ScopeField::Symbolic,
    ];

    /// The fields this build actually checks — [`Self::ALL`] without
    /// [`ScopeField::Symbolic`] unless the `symbolic` feature is on.
    ///
    /// Criterion 17 asks for "nine cells — eight under default features", and
    /// a count that is a `const` in one build and a different `const` in
    /// another is how that sentence stops being checkable. This is the
    /// function both the builder and its test ask.
    pub fn checked() -> Vec<ScopeField> {
        ScopeField::ALL
            .into_iter()
            .filter(|f| !matches!(f, ScopeField::Symbolic) || cfg!(feature = "symbolic"))
            .collect()
    }

    /// The `Config` field's name, for a message. Data, not a rendering: the
    /// sentence around it is built in `report.rs`.
    pub fn field_name(self) -> &'static str {
        match self {
            ScopeField::ConsType => "cons_type",
            ScopeField::SchedulePolicy => "schedule_policy",
            ScopeField::Mode => "mode",
            ScopeField::LossyBudget => "lossy_budget",
            ScopeField::Parallel => "parallel",
            ScopeField::PartitionedParallelization => "partitioned_parallelization",
            ScopeField::PredeterminedChoices => "predetermined_choices",
            ScopeField::PredeterminedGlobalChoices => "predetermined_global_choices",
            ScopeField::Symbolic => "symbolic",
        }
    }

    /// Why §9 excludes it — the one-line reason, as data.
    pub fn reason(self) -> &'static str {
        match self {
            ScopeField::ConsType => "conformance is scoped to asyn/p2p/cd; mailbox is out of scope",
            ScopeField::SchedulePolicy => "conformance requires the LTR schedule policy",
            ScopeField::Mode => "conformance does not run in estimation mode",
            ScopeField::LossyBudget => {
                "conformance excludes lossy sends; obligation O-skip depends on it"
            }
            ScopeField::Parallel => {
                "conformance excludes the shared-queue parallel mode: `backward_revisit` \
                 ships the graph and returns false, so a post-apply gate would never fire"
            }
            ScopeField::PartitionedParallelization => {
                "conformance excludes partitioned parallelization, the second parallel mode"
            }
            ScopeField::PredeterminedChoices => {
                "a predetermined choice is a decision the inner search never sees"
            }
            ScopeField::PredeterminedGlobalChoices => {
                "a predetermined global choice is a decision the inner search never sees"
            }
            ScopeField::Symbolic => "conformance excludes symbolic execution",
        }
    }
}

/// [`ConfBuilder::build`] refused the configuration.
///
/// Carries the offending field so a caller can act on it; the sentence a user
/// reads is built in `report.rs`, which is the only module that renders.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigError {
    pub(crate) field: ScopeField,
}

impl ConfigError {
    /// Which `Config` field was out of scope.
    pub fn field(&self) -> ScopeField {
        self.field
    }
}

/// A validated conformance configuration.
///
/// Only [`ConfBuilder::build`] constructs one, and only after §9's
/// config-time layer has run — which is *not* the same as saying the engine
/// trusts it. `Must::new`-time re-assertion still happens; see the module
/// doc.
#[derive(Clone)]
pub struct ConfConfig {
    pub(crate) config: crate::Config,
    pub(crate) visible: Vec<String>,
    pub(crate) search_budget: usize,
    pub(crate) stop_at_first_report: bool,
    pub(crate) triage: bool,
    pub(crate) skip_spec_errfree_check: bool,
    /// Knob B (`P4-SELECTOR`): the inner search's offer order. Knob A lives on
    /// `config.selector`, copied in by [`ConfBuilder::build`].
    pub(crate) inner_order: InnerOrder,
    /// `P4-ENUMERATOR` criterion 4: per-`Cover` memoisation. Off by default in
    /// this part (`P4-DISCUSS.md` D7 decides the shipping default).
    pub(crate) memo: bool,
    /// `P4-STATEFUL` T6: which checker runs.
    pub(crate) engine: Engine,
    /// `P4-CFIRST` C5: the early-error cut; complete-first only.
    pub(crate) early_error_cut: bool,
    /// `P4-GATED` G5; gated only.
    pub(crate) gated_mode: GatedMode,
    /// `P4-GATED` G5; gated only.
    pub(crate) gate_policy: GatePolicy,
    /// `P4-FLAT` F4.
    pub(crate) completion_cover: CompletionCover,
}

impl ConfConfig {
    /// The declared visible thread names, the shared vocabulary of the two
    /// programs (§8).
    pub fn visible_threads(&self) -> &[String] {
        &self.visible
    }

    /// The inner search's node ceiling per `Cover` attempt.
    pub fn search_budget(&self) -> usize {
        self.search_budget
    }

    /// `Config::max_iterations`, which conformance **records** rather than
    /// rejects (blocked item B's ruling): a bounded run is a legitimate thing
    /// to ask for, and §9's list is about fragment scope rather than about
    /// thoroughness. What it may never do is pass as silence, which is why
    /// the verdict carries it.
    pub fn max_iterations(&self) -> Option<u64> {
        self.config.max_iterations
    }

    /// **The random seed every engine of a run built from this configuration
    /// will use** (F61): the outer run, the precheck, triage, the
    /// specification search and the diagnostics.
    ///
    /// The same value appears in the result as `ConfOutcome::seed`, but
    /// `verify` returns no outcome when it fails with an error. The
    /// specification's err-freedom precheck is one such case, and under a
    /// bounded `Config` whether it fails can depend on this seed. `verify`
    /// takes the configuration by value, so read this before calling it (or
    /// from a clone kept for the purpose). That is how such a failure is
    /// reproduced:
    /// rebuild the same `Config` with `.with_seed(seed)` added. See
    /// `ConfOutcome::seed` for what that does and does not reproduce.
    pub fn seed(&self) -> u64 {
        self.config.seed
    }
}

/// Builds a [`ConfConfig`]. §8's entry point.
pub struct ConfBuilder {
    config: crate::Config,
    visible: Vec<String>,
    search_budget: usize,
    stop_at_first_report: bool,
    triage: bool,
    skip_spec_errfree_check: bool,
    selector: Selector,
    inner_order: InnerOrder,
    memo: bool,
    engine: Engine,
    early_error_cut: bool,
    gated_mode: GatedMode,
    gate_policy: GatePolicy,
    completion_cover: CompletionCover,
}

impl Default for ConfBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ConfBuilder {
    pub fn new() -> Self {
        Self {
            config: crate::Config::default(),
            visible: Vec::new(),
            search_budget: DEFAULT_SEARCH_BUDGET,
            // §7.4: the draft's report-and-continue.
            stop_at_first_report: false,
            // Criterion 15. §7.3 says "optional" and §8's sketch passes
            // `.triage(true)`, which demonstrates the knob rather than setting
            // the default. The cost is one extra engine run *per report*; a
            // user who wants concrete traces asks for them.
            triage: false,
            // §5.4's precheck is default-*on*, so the opt-out is default-off.
            skip_spec_errfree_check: false,
            // `P4-SELECTOR`: today's orders.
            selector: Selector::Ltr,
            inner_order: InnerOrder::Recorded,
            // `P4-CFIRST` C5: plan §6 runs the cut off; A27 (the cut decides,
            // it does not enumerate) is the reason it stays off by default.
            early_error_cut: false,
            gated_mode: GatedMode::Exhaustive,
            gate_policy: GatePolicy::Always,
            // `P4-FLAT` F4: the sweep, as Parts 4–5 landed it.
            completion_cover: CompletionCover::Sweep,
            // `P4-ENUMERATOR` criterion 4: memo off until D7 is decided.
            memo: false,
            engine: Engine::Enumerator,
        }
    }

    /// `P4-STATEFUL` T6: which checker runs. See [`Engine`] for what each
    /// honours and ignores.
    pub fn engine(mut self, e: Engine) -> Self {
        self.engine = e;
        self
    }

    /// `P4-CFIRST` C5: the early-error cut of paper §8.5 — **complete-first
    /// only; the other engines ignore it**. When on, a visible thread's
    /// failed assertion is reported at once as a prefix (`ReportTag::VisibleError`)
    /// and the subtree below it is skipped. The engine then *decides* but
    /// does not enumerate (A27): each prefix report certifies every completion
    /// of every extension of it, but a backward revisit from inside the
    /// skipped subtree can reach an uncovered complete graph that is neither
    /// listed nor certified. The report list is the completion reports in
    /// completion order, followed by the cut reports in the order raised.
    /// Off by default.
    pub fn early_error_cut(mut self, on: bool) -> Self {
        self.early_error_cut = on;
        self
    }

    /// `P4-GATED` G5: exhaustive or first-failure reporting — **gated only**;
    /// the other engines ignore it. First-failure implies
    /// `stop_at_first_report`.
    pub fn gated_mode(mut self, m: GatedMode) -> Self {
        self.gated_mode = m;
        self
    }

    /// `P4-GATED` G5: the gate policy — **gated only**; the other engines
    /// ignore it. Default `Always`.
    /// `P4-FLAT` F4: the completion-question engine of the complete-first and
    /// gated checkers. `Flat` requires the precheck and those two engines
    /// (`ConfError::KnobConflict` otherwise, at `run`).
    pub fn completion_cover(mut self, c: CompletionCover) -> Self {
        self.completion_cover = c;
        self
    }

    pub fn gate_policy(mut self, p: GatePolicy) -> Self {
        self.gate_policy = p;
        self
    }

    /// `P4-ENUMERATOR` criterion 4: memoise the inner search per `Cover`
    /// call on the canonical probe output (`lem:memo`). The answer is
    /// unchanged at unlimited budget; at a finite budget memo on can turn an
    /// exhaustion into an established answer. Off by default in this part.
    pub fn memo(mut self, on: bool) -> Self {
        self.memo = on;
        self
    }

    /// `P4-ENUMERATOR` criterion 8: no inner-search budget — the paper's own
    /// `Cover`, which `lem:coverexact` and `lem:memo` speak about. Equivalent
    /// to `search_budget(usize::MAX)`.
    pub fn unlimited(self) -> Self {
        self.search_budget(usize::MAX)
    }

    /// Knob A: the Must selector of every run this configuration starts (the
    /// outer run, the precheck, triage, and under the stateful and
    /// complete-first checkers their enumerations and sweeps; probes are
    /// forced to `Ltr`). Copied
    /// into the engine `Config` by [`ConfBuilder::build`], after `.config()`,
    /// so `.config()` cannot overwrite it.
    pub fn selector(mut self, s: Selector) -> Self {
        self.selector = s;
        self
    }

    /// Knob B: the order in which the inner search tries a probe's offers, a
    /// nondet's values and a receive's sources. Orders, never discards.
    pub fn inner_order(mut self, o: InnerOrder) -> Self {
        self.inner_order = o;
        self
    }

    /// Start from an existing [`crate::Config`] — the way to set
    /// `max_iterations`, `with_error_trace`, the seed, and everything else
    /// conformance does not have its own knob for.
    pub fn config(mut self, config: crate::Config) -> Self {
        self.config = config;
        self
    }

    /// The shared `Tvis`. `"main"` is the reserved name for each closure's own
    /// thread.
    pub fn visible_threads<I, S>(mut self, names: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.visible = names.into_iter().map(Into::into).collect();
        self
    }

    pub fn cons_type(mut self, t: ConsType) -> Self {
        self.config.cons_type = t;
        self
    }

    /// §7.4. Default `false`.
    ///
    /// It does not change what a report means; it changes what *silence*
    /// means, so the verdict records it.
    pub fn stop_at_first_report(mut self, b: bool) -> Self {
        self.stop_at_first_report = b;
        self
    }

    /// §7.3's triage. Default `false` (criterion 15).
    pub fn triage(mut self, b: bool) -> Self {
        self.triage = b;
        self
    }

    /// Skip §5.4's err-freedom precheck, accepting the assumption instead.
    ///
    /// The verdict then **records the assumption**: an opt-out that leaves no
    /// trace is a silent change of what the verdict means.
    ///
    /// **Under [`Engine::Stateful`] this flag has no effect** (`P4-STATEFUL`
    /// T4). That engine enumerates the specification in full to build its
    /// index, and that run *is* the §5.4 check: a specification assertion
    /// failure returns `ConfError::SpecNotErrorFree` whatever this flag says,
    /// and a clean index run records `SpecErrFreedom::Checked`, never
    /// `Assumed`.
    ///
    /// **Under [`Engine::CompleteFirst`] it skips only the precheck**
    /// (`P4-CFIRST` C4), which that engine runs unbounded; a sweep that meets a
    /// specification assertion failure still aborts the run with
    /// `ConfError::SpecNotErrorFree`.
    pub fn skip_spec_errfree_check(mut self, b: bool) -> Self {
        self.skip_spec_errfree_check = b;
        self
    }

    /// The inner search's node ceiling per `Cover` attempt.
    /// Default [`DEFAULT_SEARCH_BUDGET`].
    pub fn search_budget(mut self, n: usize) -> Self {
        self.search_budget = n;
        self
    }

    /// §9's config-time layer, then the configuration.
    ///
    /// The nine checks below were written from §9's prose and the `Config`
    /// struct's fields, **not** from `assert_config_in_scope` — criterion 7
    /// requires the two lists derived independently and then diffed, because
    /// a list copied from the other cannot disagree with it and so proves
    /// nothing. The diff is `c7_config_rejections_match_the_constructor_predicate_field_by_field`.
    pub fn build(self) -> Result<ConfConfig, ConfigError> {
        for field in ScopeField::checked() {
            if out_of_scope(&self.config, field) {
                return Err(ConfigError { field });
            }
        }
        let mut config = self.config;
        // Knob A travels on the engine `Config` (`P4-SELECTOR` S4); set here,
        // after `.config()` has been applied, so it cannot be overwritten.
        config.selector = self.selector;
        Ok(ConfConfig {
            config,
            visible: self.visible,
            search_budget: self.search_budget,
            stop_at_first_report: self.stop_at_first_report,
            triage: self.triage,
            skip_spec_errfree_check: self.skip_spec_errfree_check,
            inner_order: self.inner_order,
            memo: self.memo,
            engine: self.engine,
            early_error_cut: self.early_error_cut,
            gated_mode: self.gated_mode,
            gate_policy: self.gate_policy,
            completion_cover: self.completion_cover,
        })
    }
}

/// Is this one field out of §9's scope?
///
/// One predicate per field, so that the enumeration in [`ScopeField`] and the
/// checking are the same list by construction. Adding a variant without an arm
/// here is a compile error.
pub(crate) fn out_of_scope(config: &crate::Config, field: ScopeField) -> bool {
    match field {
        // On the *model*, not the spelling: `MO` and `Mailbox` are the same
        // thing and a name-based test catches one of them.
        ScopeField::ConsType => {
            crate::channel::cons_to_model(config.cons_type) == crate::CommunicationModel::TotalOrder
        }
        ScopeField::SchedulePolicy => config.schedule_policy != SchedulePolicy::LTR,
        ScopeField::Mode => config.mode != ExplorationMode::Verification,
        ScopeField::LossyBudget => config.lossy_budget > 0,
        ScopeField::Parallel => config.parallel,
        ScopeField::PartitionedParallelization => config.partitioned_parallelization,
        ScopeField::PredeterminedChoices => !config.predetermined_choices.is_empty(),
        ScopeField::PredeterminedGlobalChoices => !config.predetermined_global_choices.is_empty(),
        #[cfg(feature = "symbolic")]
        ScopeField::Symbolic => config.symbolic,
        #[cfg(not(feature = "symbolic"))]
        ScopeField::Symbolic => false,
    }
}
