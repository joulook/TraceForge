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

use crate::{ConsType, ExplorationMode, SchedulePolicy};

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
            ScopeField::ConsType => {
                "conformance is scoped to asyn/p2p/cd; mailbox is out of scope"
            }
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
            // §7.3: debug only.
        }
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
        Ok(ConfConfig {
            config: self.config,
            visible: self.visible,
            search_budget: self.search_budget,
            stop_at_first_report: self.stop_at_first_report,
            triage: self.triage,
            skip_spec_errfree_check: self.skip_spec_errfree_check,
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
