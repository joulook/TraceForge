//! §11.6's differential harness: the tool against the oracle, on one pair.
//!
//! The tool answers "does some *single* specification graph cover each
//! implementation graph?" (`cor:sound`'s premise). The oracle answers
//! "`vis(Impl) ⊆ vis(Spec)`" (`Impl ⊑ Spec` itself, by Thm. morph). Those are
//! **not** the same question, and the gap between them is the quantity §11.6
//! asks this module to measure.
//!
//! # The four outcomes, and which one is the measurement
//!
//! | tool | oracle | meaning |
//! |---|---|---|
//! | certificate | holds | agreement. The floor. |
//! | reported | fails | agreement — a **correct** report. |
//! | reported | holds | **false alarm.** Single cover is sufficient but not necessary; this is the method's cost and the number §11.6 wants. |
//! | certificate | fails | **unsound.** The tool was silent on a pair that does not refine. This must never happen and is a defect in the tool, not a measurement. |
//!
//! # Silence is not the antecedent
//!
//! Thm. alg's antecedent is an **exhaustive** run. The crate ships
//! `DEFAULT_SEARCH_BUDGET = 10_000`, so a run can be silent because the inner
//! search ran out of nodes rather than because it found nothing — and
//! `mod.rs` states the point outright: the certificate types "are the
//! difference between a certificate and a run that merely produced no report,
//! which is the one distinction the theorem turns on". So [`Agreement`]
//! distinguishes `Inconclusive` from `Certificate`, and a harness must **gate**
//! the inconclusive count rather than report it (S6 criterion 6).
//!
//! # F43
//!
//! `Cover::BudgetExhausted` neither reports nor prunes — it records a
//! `ConfExhaustion` and the run continues — so a run that exhausted its budget
//! looks clean to anyone reading the report list alone. Every figure derived
//! from this module must therefore account for `exhaustions()`.
//!
//! **The certificate test alone does not do this, and an earlier version of
//! this paragraph claimed it did.** A run that reported at one gate *and*
//! exhausted its inner budget at another is `Reported`, lands in
//! `BothFail`/`FalseAlarm` — inside the false-alarm **denominator** — with no
//! exhaustion check on the path. The routing that sentence described holds for
//! the `Conforms` arm only.
//!
//! **And the cause is not the order of the two tests.** `ConfVerdict::of` does
//! test `reports` before `not_a_certificate()` (`report.rs:679-688`), but a
//! reporting run is `Reported` *whichever* runs first, because
//! `not_a_certificate()` pushes `NotACertificate::Reported` itself — so
//! `not_a_certificate().is_empty()` is false on exactly the runs the reports
//! test catches. Swapping the two is observationally identical, and was
//! measured to be: the mutation changes no test (developer,
//! `P3-S6-gate4-fixes`, finding 3). **What the `Reported` arm loses is not the
//! certificate test but the outcome** — it is dropped before anything reads
//! `exhaustions()`. A reader who "fixed" the ordering would change nothing.
//!
//! So the check is made explicit instead of inferred: [`Agreement::of`] reads
//! `exhaustions()` on the reporting arms before the outcome is dropped,
//! [`Tally::reported_but_not_exhaustive`] counts them, and
//! [`Tally::violations`] gates the count. On the shipped corpus it is zero —
//! which is precisely why the false sentence was dangerous: it would have been
//! read as a control by whoever first ran the harness on a corpus that can
//! exhaust. Criterion 6's first "Required alongside it" bullet is discharged
//! by the counter, not by this prose.

use crate::conformance::config::ConfBuilder;
use crate::conformance::oracle::{includes_capped, Inclusion, OracleError, VisWord};
use crate::conformance::report::ConfVerdict;
use crate::conformance::ConfError;
use crate::Config;

/// What the tool and the oracle jointly said about one pair.
#[derive(Debug)]
pub(crate) enum Agreement {
    /// Tool certified, oracle agrees inclusion holds.
    BothClean,
    /// Tool reported, oracle agrees inclusion fails. The report was correct.
    ///
    /// `exhausted` records whether the reporting run *also* ran out of inner
    /// budget at some other gate. See the module's `# F43` section: this arm
    /// is reached without the certificate test, so the flag is the only place
    /// the fact survives — the outcome is dropped here.
    BothFail { witness: VisWord, exhausted: bool },
    /// **The measurement.** The tool reported; the oracle says inclusion
    /// holds. Not a bug — single cover is sufficient, not necessary — but it
    /// is not free either, and the pair is retained so the reading is
    /// checkable case by case rather than assumed.
    ///
    /// `exhausted` as for [`Agreement::BothFail`]. A pair in the false-alarm
    /// **numerator** whose run was not exhaustive is not a measured false
    /// alarm at all, which is why the flag is carried rather than inferred.
    FalseAlarm { reports: usize, exhausted: bool },
    /// **Unsoundness.** The tool produced a certificate for a pair the oracle
    /// says does not refine. There is no benign reading of this.
    Unsound { witness: VisWord },
    /// The tool neither certified nor reported — a bounded run, an exhausted
    /// inner budget, or a stop-at-first. Carries why. Excluded from every
    /// ratio, and **gated**, not merely reported: a suite where most pairs
    /// land here is green and proves nothing.
    Inconclusive { why: String },
}

impl Agreement {
    /// Score one pair from the two engines' answers.
    ///
    /// **`pub(crate)` for one reason only: F59's second half.** The
    /// `FalseAlarm` arm's `exhausted:` read cannot be reached through
    /// [`compare_with_budget`], because that needs a pair the tool reports on
    /// while the oracle says inclusion holds — a false alarm — and **A15**
    /// records that no generator mode here builds one. Calling this directly
    /// with a *real* `Reported` verdict and `Inclusion::Holds` is therefore the
    /// only way that read is exercised at all. The `BothFail` arm, by contrast,
    /// is tested end to end through the harness; prefer that route wherever it
    /// exists. Owner ruling, 2026-09-16.
    pub(crate) fn of(verdict: ConfVerdict, oracle: Inclusion) -> Self {
        match (verdict, oracle) {
            (ConfVerdict::Conforms(_), Inclusion::Holds) => Agreement::BothClean,
            (ConfVerdict::Conforms(_), Inclusion::Fails { witness }) => {
                Agreement::Unsound { witness }
            }
            // **Read `exhaustions()` before dropping the outcome.** Both arms
            // below are reached without the certificate test, so this is the
            // last point at which the fact exists (gate-4 review, M2).
            (ConfVerdict::Reported(o), Inclusion::Fails { witness }) => Agreement::BothFail {
                witness,
                exhausted: !o.exhaustions().is_empty(),
            },
            (ConfVerdict::Reported(o), Inclusion::Holds) => Agreement::FalseAlarm {
                reports: o.reports().len(),
                exhausted: !o.exhaustions().is_empty(),
            },
            (ConfVerdict::Inconclusive(o), _) => Agreement::Inconclusive {
                why: o
                    .not_a_certificate()
                    .iter()
                    .map(|n| format!("{n}"))
                    .collect::<Vec<_>>()
                    .join("; "),
            },
        }
    }

    pub(crate) fn is_false_alarm(&self) -> bool {
        matches!(self, Agreement::FalseAlarm { .. })
    }

    pub(crate) fn is_unsound(&self) -> bool {
        matches!(self, Agreement::Unsound { .. })
    }

    pub(crate) fn is_inconclusive(&self) -> bool {
        matches!(self, Agreement::Inconclusive { .. })
    }

    /// Did the tool report? The denominator of the false-alarm rate is "pairs
    /// on which the tool produced at least one report" — fixed by the criteria
    /// rather than left to the caller, because "all generated pairs" and this
    /// give wildly different numbers from the same run and one of them
    /// flatters.
    pub(crate) fn tool_reported(&self) -> bool {
        matches!(
            self,
            Agreement::BothFail { .. } | Agreement::FalseAlarm { .. }
        )
    }

    pub(crate) fn oracle_holds(&self) -> bool {
        matches!(
            self,
            Agreement::BothClean | Agreement::FalseAlarm { .. }
        )
    }
}

/// Why a pair could not be compared at all.
#[derive(Debug)]
pub(crate) enum DiffError {
    Tool(ConfError),
    Oracle(OracleError),
    /// The pair's own configuration was refused — §9 scope, or an empty
    /// visible list. A generator bug, not a measurement.
    Config(String),
}

/// Run one pair through both, and say what they jointly establish.
///
/// The two engines see the **same** `Config`: the oracle runs the program
/// through `Must::enable_conformance` exactly as the tool does, so §9's guards
/// are armed, `keep_going_after_error` is forced and §8's `check_spawn_order`
/// runs on both. That is what makes "the executions of `P`" one set rather
/// than two, and it is why the enumeration mismatch is closed by construction
/// on runs with no report — which is precisely the runs §11.6's headline
/// property is about.
pub(crate) fn compare<I, S>(
    config: Config,
    visible: &[String],
    implementation: I,
    specification: S,
) -> Result<Agreement, DiffError>
where
    I: Fn() + Send + Sync + Clone + 'static,
    S: Fn() + Send + Sync + Clone + 'static,
{
    compare_with_budget(config, visible, implementation, specification, None)
}

/// [`compare`], with the tool's inner-search budget under the caller's control
/// (**F59**).
///
/// `None` is exactly [`compare`] — the tool runs at `DEFAULT_SEARCH_BUDGET`, and
/// [`compare`] is a one-line delegation here, so the two cannot drift.
/// `Some(n)` sets `ConfBuilder::search_budget(n)` on the tool side only.
///
/// **Why this exists.** Gate 4's M2 added a gate for pairs that *report at one
/// gate and exhaust the inner budget at another* — such a pair sits in the
/// false-alarm denominator without `thm:alg`'s antecedent. The developer
/// established that such a pair is constructible, deterministically across all
/// three models, but that nothing the harness could run reached it: [`compare`]
/// hard-wired the default budget, which is above every gate in any program the
/// generator emits or the oracle can afford to enumerate. So the two
/// `exhausted:` reads in [`Agreement::of`] were exercised only in the `false`
/// direction. This is the knob that lets the *harness* — not a test calling
/// `Agreement::of` directly — be driven into that state end to end, which is
/// what criterion 6's bullet is about.
///
/// **The oracle ignores the budget, deliberately.** It is the reference: it
/// enumerates `vis(P)` completely or not at all, and has no inner search to
/// bound. Only the tool's answer is made partial, which is exactly the
/// asymmetry the gate is meant to catch.
pub(crate) fn compare_with_budget<I, S>(
    config: Config,
    visible: &[String],
    implementation: I,
    specification: S,
    search_budget: Option<usize>,
) -> Result<Agreement, DiffError>
where
    I: Fn() + Send + Sync + Clone + 'static,
    S: Fn() + Send + Sync + Clone + 'static,
{
    compare_capped(
        config,
        visible,
        implementation,
        specification,
        search_budget,
        None,
    )
}

/// The harness's single implementation: [`compare_with_budget`], plus a
/// per-thread cap on the **oracle's** visible observations.
///
/// `event_cap` is passed to `oracle::includes_capped`, which refuses (with
/// `OracleError::OverCap`, surfaced here as `DiffError::Oracle`) any graph
/// whose visible thread exceeds it, **before** that graph's linear-extension
/// enumeration starts. The check is per graph: graphs scored before an
/// over-cap one have already been enumerated, and so has the whole
/// implementation if only the specification goes over. It does not touch the tool, whose cost is bounded by
/// `search_budget` instead.
///
/// [`compare`] and [`compare_with_budget`] pass `None` and are unchanged in
/// behaviour. Generated pairs are run through `generator::Pair::compare`,
/// which passes `Some(generator::MAX_VISIBLE_EVENTS_PER_THREAD)` — that is what
/// makes criterion 13's event bound a checked runtime bound rather than a
/// property of today's corpus (`P3-gate4-fixes` round 1, M1).
pub(crate) fn compare_capped<I, S>(
    config: Config,
    visible: &[String],
    implementation: I,
    specification: S,
    search_budget: Option<usize>,
    event_cap: Option<usize>,
) -> Result<Agreement, DiffError>
where
    I: Fn() + Send + Sync + Clone + 'static,
    S: Fn() + Send + Sync + Clone + 'static,
{
    let oracle = includes_capped(
        config.clone(),
        visible,
        implementation.clone(),
        specification.clone(),
        event_cap,
    )
    .map_err(DiffError::Oracle)?;

    let mut builder = ConfBuilder::new()
        .visible_threads(visible.iter().map(|s| s.as_str()))
        .config(config);
    if let Some(n) = search_budget {
        builder = builder.search_budget(n);
    }
    let cc = builder
        .build()
        .map_err(|e| DiffError::Config(format!("{e:?}")))?;

    let verdict =
        crate::conformance::verify(cc, implementation, specification).map_err(DiffError::Tool)?;

    Ok(Agreement::of(verdict, oracle))
}

/// How a false-alarm zero must be read.
///
/// **The owner ruled on 2026-09-17 (A15, route 2)**: where the population
/// cannot produce a false alarm, the figure is published as *"0 by
/// construction under this generator, not measured"* — a different and much
/// weaker claim than a measured zero, and the only true one.
///
/// This is an enum rather than a sentence in a report because prose candour is
/// not a control. A caller cannot obtain [`FalseAlarmFigure::Measured`] from a
/// population containing no pair capable of producing a false alarm, and that
/// is enforced here rather than remembered.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum FalseAlarmFigure {
    /// A genuine measurement: at least one pair in the population *could* have
    /// produced a false alarm, and this is how often one did.
    Measured {
        numerator: usize,
        denominator: usize,
    },
    /// **Zero by construction, not measured.** No pair in the population came
    /// from a mode capable of producing a false alarm, so the zero is
    /// arithmetic rather than evidence. A false alarm requires an
    /// implementation graph covered by the *union* of specification graphs and
    /// by no single one (`cor:sound` plus the remark at `ref2.tex:455-461`);
    /// see **A15** for why no mode here builds one.
    ZeroByConstruction { denominator: usize },
    /// Nothing reported, so there is no denominator. `0/0` is not a rate.
    NoReportingPairs,
}

/// **The caveats that travel with the figure** (criterion 7's last bullet and
/// criterion 14's last "Required").
///
/// A15's caveat travels because it was made structural — it is the difference
/// between two `FalseAlarmFigure` variants. These three could not be made
/// structural, so they are appended to the rendered figure instead. They were
/// previously stated in `generator.rs`'s and `oracle.rs`'s module docs: both
/// correct, and both in places a reader of the *number* never sees. The figure
/// is the artefact that leaves the project, and criterion 14's rule is that an
/// unstated blind spot in the evidence reads as covered ground.
pub(crate) const FIGURE_CAVEATS: &str = "\
     \n  caveats that travel with this figure:\
     \n  - F-6: no shape spawns a visible thread conditionally, so the rate is measured \
over a strictly smaller fragment than §9 admits and must be re-run when F-6's route (i) \
lands.\
     \n  - F41: a `ThreadId` in an observed value makes an observation a function of \
invisible spawn count, and the oracle inherits `msg_equals` and so agrees with the tool. \
Such a pair scores as a correct report and can never enter the numerator. This is a class \
the method **cannot measure**, not one it under-samples.\
     \n  - shared with the tool, so no disagreement can expose a fault in them: \
`obs::wobs`, `ExecutionGraph::in_porf`, `msg::Val::eq`.";

impl std::fmt::Display for FalseAlarmFigure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FalseAlarmFigure::Measured {
                numerator,
                denominator,
            } => write!(
                f,
                "single-cover false-alarm rate: {numerator}/{denominator} (measured)\
                 {FIGURE_CAVEATS}"
            ),
            FalseAlarmFigure::ZeroByConstruction { denominator } => write!(
                f,
                "single-cover false-alarm rate: 0/{denominator} — **0 by construction \
                 under this generator, not measured**. No pairing mode in this population \
                 can produce a false alarm, so the zero is arithmetic and not evidence \
                 that false alarms are rare (A15).{FIGURE_CAVEATS}"
            ),
            FalseAlarmFigure::NoReportingPairs => write!(
                f,
                "single-cover false-alarm rate: not computed — no pair reported, \
                 so there is no denominator"
            ),
        }
    }
}

/// Counts over a population of pairs, and the obligations that make them a
/// measurement rather than an anecdote.
#[derive(Debug, Default)]
pub(crate) struct Tally {
    pub(crate) both_clean: usize,
    pub(crate) both_fail: usize,
    pub(crate) false_alarm: usize,
    pub(crate) unsound: usize,
    pub(crate) inconclusive: usize,
    /// How many pairs came from a mode that **can** produce a false alarm.
    ///
    /// The discriminator between a measured rate and a zero by construction,
    /// and the reason [`Tally::false_alarm_figure`] cannot be talked into the
    /// wrong one.
    pub(crate) capable: usize,
    /// **Pairs that reported *and* exhausted their inner budget** (criterion
    /// 6's first "Required alongside it" bullet, gate-4 review M2).
    ///
    /// Such a pair sits in [`Tally::reporting`] — the false-alarm denominator
    /// — on the strength of a run that was not exhaustive, which is the one
    /// antecedent `thm:alg` turns on. The certificate test never sees it; it is
    /// counted here instead.
    ///
    /// **Which branch of criterion 6's bullet this discharges, stated because
    /// the counter's existence does not say it** (developer,
    /// `P3-S6-gate4-fixes`, finding 4). The bullet offers two: the count is
    /// **zero**, *or* it is reported beside every other number **and those
    /// pairs are excluded explicitly**. This implementation claims **the
    /// first**: the count is zero on the shipped corpus, and
    /// [`Tally::violations`] is the guard that keeps it so. It does **not**
    /// implement the second — a counted pair stays in [`Tally::reporting`] and
    /// in `both_fail`/`false_alarm`, and is not excluded from anything.
    ///
    /// That is deliberate. For a corpus that should not be producing these
    /// pairs at all, a gate is stronger than an exclusion: excluding them
    /// quietly would let the population drift while every published number
    /// stayed clean. A close-out quoting this must say "branch 1, gated",
    /// never "exhausted pairs are excluded".
    pub(crate) reported_but_not_exhaustive: usize,
}

impl Tally {
    /// `capable` says whether this pair's mode can produce a false alarm at
    /// all. It is a **parameter**, not a guess: a tally that inferred it from
    /// the outcome would conclude "no false alarms seen, therefore none
    /// possible", which is exactly A15's circularity.
    ///
    /// **The predicate is the _conjunction_ `is_constructed() &&
    /// can_false_alarm()`, and neither half alone will do** (gate 3). An
    /// earlier version of this comment named `Mode::is_constructed` on its own:
    /// that is true for five of six modes, so a caller following it would pass
    /// `capable = 5` and publish `Measured { 0, k }` — the precise claim the
    /// owner's A15 ruling forbids. `can_false_alarm` alone is equally wrong in
    /// the other direction: it is true for exactly the one mode that is **not
    /// built**. The call site had the conjunction right while this comment said
    /// otherwise, which is the defect shape this project keeps finding — a
    /// sentence asserting something the code does not do.
    pub(crate) fn add_capable(&mut self, a: &Agreement, capable: bool) {
        if capable {
            self.capable += 1;
        }
        self.add(a);
    }

    pub(crate) fn add(&mut self, a: &Agreement) {
        match a {
            Agreement::BothClean => self.both_clean += 1,
            Agreement::BothFail { exhausted, .. } => {
                self.both_fail += 1;
                if *exhausted {
                    self.reported_but_not_exhaustive += 1;
                }
            }
            Agreement::FalseAlarm { exhausted, .. } => {
                self.false_alarm += 1;
                if *exhausted {
                    self.reported_but_not_exhaustive += 1;
                }
            }
            Agreement::Unsound { .. } => self.unsound += 1,
            Agreement::Inconclusive { .. } => self.inconclusive += 1,
        }
    }

    pub(crate) fn total(&self) -> usize {
        self.both_clean + self.both_fail + self.false_alarm + self.unsound + self.inconclusive
    }

    /// The denominator: pairs on which the tool produced at least one report.
    pub(crate) fn reporting(&self) -> usize {
        self.both_fail + self.false_alarm
    }

    /// `false alarms / reporting pairs`, as a ratio with its denominator —
    /// `None` when nothing reported, because `0/0` is not a rate and
    /// publishing it as one is the failure this returns `None` to prevent.
    ///
    /// **Raw, and not publishable on its own** — use
    /// [`Tally::false_alarm_figure`], which says how the number must be read.
    pub(crate) fn false_alarm_rate(&self) -> Option<(usize, usize)> {
        if self.reporting() == 0 {
            None
        } else {
            Some((self.false_alarm, self.reporting()))
        }
    }

    /// The figure, with its reading attached.
    ///
    /// A zero from a population that could never have produced a false alarm
    /// is **not** a measurement, and this is where that is decided rather than
    /// left to whoever writes the report.
    pub(crate) fn false_alarm_figure(&self) -> FalseAlarmFigure {
        let denominator = self.reporting();
        if denominator == 0 {
            return FalseAlarmFigure::NoReportingPairs;
        }
        if self.capable == 0 {
            // Necessarily `false_alarm == 0` — no capable pair, no numerator.
            return FalseAlarmFigure::ZeroByConstruction { denominator };
        }
        FalseAlarmFigure::Measured {
            numerator: self.false_alarm,
            denominator,
        }
    }

    /// The four non-emptiness gates of criterion 6, plus soundness and the
    /// inconclusive bound.
    ///
    /// Returns every failure rather than the first: a caller that fixed one
    /// gate at a time would re-run the whole corpus per gate.
    pub(crate) fn violations(&self, max_inconclusive_ratio: usize) -> Vec<String> {
        let mut v = Vec::new();
        if self.unsound > 0 {
            v.push(format!(
                "{} pair(s) where the tool certified and the oracle says inclusion fails — \
                 unsoundness, not a measurement",
                self.unsound
            ));
        }
        if self.total() == 0 {
            v.push("no pairs were generated; every other assertion passes vacuously".to_owned());
        }
        // Criterion 6's four classes, each non-empty.
        if self.both_clean + self.false_alarm == 0 {
            v.push("no pair on which the oracle says inclusion holds".to_owned());
        }
        if self.both_fail == 0 {
            v.push("no pair on which the oracle says inclusion fails".to_owned());
        }
        if self.reporting() == 0 {
            v.push("no pair on which the tool reported".to_owned());
        }
        if self.both_clean == 0 {
            v.push("no pair on which the tool certified".to_owned());
        }
        // A15, the owner's ruling of 2026-09-17. Not an error — route 2 is an
        // accepted outcome — but it must be *stated*, because a reader who
        // sees a zero and no caveat will read it as a measurement.
        if self.capable == 0 && self.reporting() > 0 {
            v.push(
                "no pair in this population came from a mode capable of producing a false \
                 alarm, so the rate is 0 by construction and not measured (A15)"
                    .to_owned(),
            );
        }
        // Criterion 6's first "Required alongside it" bullet (gate-4 M2). The
        // bullet allows a non-zero count only if it "is reported next to every
        // other number the harness produces and those pairs are excluded
        // explicitly" — neither of which this struct can do on the caller's
        // behalf, so a non-zero count is a violation and the caller must
        // decide what to do about it in the open.
        if self.reported_but_not_exhaustive > 0 {
            v.push(format!(
                "{} of {} reporting pair(s) also exhausted an inner budget — those runs \
                 are not exhaustive, so they sit in the false-alarm denominator without \
                 thm:alg's antecedent. A reporting run is `Reported` whatever it \
                 exhausted, and its outcome is dropped once scored, so nothing else on \
                 the path catches this",
                self.reported_but_not_exhaustive,
                self.reporting()
            ));
        }
        // Gated, not reported (criterion 6).
        if self.inconclusive * max_inconclusive_ratio > self.total() {
            v.push(format!(
                "{} of {} pairs were inconclusive — over 1/{} of the population; the \
                 property was asserted on too few genuine certificates to mean anything",
                self.inconclusive,
                self.total(),
                max_inconclusive_ratio
            ));
        }
        v
    }
}
