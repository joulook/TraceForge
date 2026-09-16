//! The differential layer's acceptance suite (S6 criteria 6, 7, 19).
//!
//! **Rewritten by the developer at gate 3.** The previous contents were the
//! lead's own provisional smoke tests. Two of them survive here with their
//! mutation lines corrected; one of the three named a mutation that fails
//! nothing, which is the defect this project keeps re-shipping and which
//! criterion 19 exists to catch.
//!
//! Every `Mutation:` line below was **applied to the tree and observed to fail
//! the test it is attached to**, and then reverted. Where a line says
//! `REFUTED`, it records a mutation that was applied and did *not* fail, kept
//! because criterion 19 asks for what was attempted and not only for what was
//! concluded.
//!
//! # What this file does and does not establish
//!
//! It establishes that the four-outcome table is computed correctly, that
//! criterion 6's four classes are non-empty on the generated corpus, and that
//! [`FalseAlarmFigure`] cannot be talked into publishing a measured zero from a
//! population that cannot produce a false alarm.
//!
//! It does **not** establish a false-alarm rate. No generator mode can produce
//! one — `Mode::UnionCovered` is declared and unbuilt (A15) — and
//! [`no_generator_mode_is_capable_so_the_rate_is_never_measured`] pins exactly
//! that, so the absence is a tested fact rather than an unstated gap.

use std::collections::BTreeMap;

use crate::conformance::differential::{
    compare, compare_with_budget, Agreement, FalseAlarmFigure, Tally,
};
use crate::conformance::generator::{corpus, pair, Mode, Pair};
use crate::conformance::oracle::VisWord;

/// A throwaway `VisWord` for the tally tests, which never inspect it.
fn witness() -> VisWord {
    VisWord {
        word: Vec::new(),
        statuses: BTreeMap::new(),
    }
}

/// `capable` in criterion 7's sense: this pair's mode is **built** *and* its
/// construction can produce a false alarm.
///
/// Written here, once, because neither `Mode` helper is it on its own and the
/// rustdoc on `Tally::add_capable` names the wrong one — see
/// [`neither_single_mode_predicate_is_the_capability_a_caller_must_pass`].
fn capable(m: Mode) -> bool {
    m.is_constructed() && m.can_false_alarm()
}

/// A generated pair, through the harness **with criterion 13's event cap**.
///
/// This goes through `Pair::compare`, the generator's own entry point, not
/// through the uncapped `compare`, so that every corpus test also runs every
/// shipped shape against `MAX_VISIBLE_EVENTS_PER_THREAD`. Before
/// `P3-gate4-fixes` round 1 this called `compare`, which bypasses the cap.
fn run(p: &Pair) -> Result<Agreement, crate::conformance::differential::DiffError> {
    p.compare(None)
}

// ---------------------------------------------------------------------------
// The generator's pinned answers
// ---------------------------------------------------------------------------

/// Each mode's *oracle* answer is fixed by its construction, and this checks
/// the construction rather than trusting it.
///
/// This is the one obligation that makes the acceptance suite evidence rather
/// than a transcript: if `expect_inclusion` is derived but wrong, every pinned
/// outcome downstream is pinned to the wrong value.
///
/// **Mutation, MEASURED**: swap `DecoupleImpl` and `DecoupleSpec`'s arms in
/// `Mode::expect_inclusion`. Applied at gate 3 —
/// `every_generator_mode_matches_its_predicted_oracle_answer ... FAILED`,
/// 351 passed / 1 failed. The (M2) direction is one-way
/// (`morphism.rs:648-651`), so exactly one of the two must fail inclusion.
#[test]
fn every_generator_mode_matches_its_predicted_oracle_answer() {
    for m in Mode::all() {
        let p = pair(*m, 0xC0FFEE);
        let impl_ = {
            let a = p.implementation.clone();
            move || a()
        };
        let spec = {
            let a = p.specification.clone();
            move || a()
        };
        // Capped, like every other run of a generated pair.
        let got = crate::conformance::oracle::includes_capped(
            p.config.clone(),
            &p.visible,
            impl_,
            spec,
            Some(crate::conformance::generator::MAX_VISIBLE_EVENTS_PER_THREAD),
        )
        .unwrap_or_else(|e| panic!("oracle refused {:?}: {e:?}", m));
        let holds = matches!(got, crate::conformance::oracle::Inclusion::Holds);
        assert_eq!(
            holds, p.expect_inclusion,
            "{m:?}: the mode's construction predicts inclusion = {}, oracle said {holds}",
            p.expect_inclusion
        );
    }
}

// ---------------------------------------------------------------------------
// A15: the capability discriminator
// ---------------------------------------------------------------------------

/// **No generator mode is capable of producing a false alarm**, so the rate
/// this harness publishes is *never* a measurement.
///
/// This is A15 asserted rather than described. `Mode::UnionCovered` is the only
/// mode whose *construction* could produce one, and it is `decoupled` against
/// itself — an `Identity` pair. So the capability predicate is false on every
/// mode, and a reader who sees `0/k` is told by the type that the zero is
/// arithmetic.
///
/// The absence is pinned deliberately: an unstated gap reads as a tested
/// region, and if someone later *builds* the hub shape this test is what tells
/// them the caveat may now come off.
///
/// **Mutation, MEASURED**: make `Mode::is_constructed` return `true` for
/// `UnionCovered` — i.e. declare the unbuilt mode built. Applied at gate 3;
/// this test fails with `UnionCovered is declared but not constructed`.
#[test]
fn no_generator_mode_is_capable_so_the_rate_is_never_measured() {
    for m in Mode::all() {
        assert!(
            !capable(*m),
            "{m:?} claims to be a built mode that can produce a false alarm; no such mode \
             exists in this generator (A15), so either the hub shape was built and this \
             test should be updated, or a predicate is lying"
        );
    }
    assert!(
        Mode::all().iter().any(|m| m.can_false_alarm()),
        "the mode that *would* measure the rate has been deleted rather than left declared \
         and labelled; A15's record of what was attempted is then gone"
    );
    assert!(
        !Mode::UnionCovered.is_constructed(),
        "UnionCovered is declared but not constructed"
    );

    // And end to end: the real corpus carries no capable pair.
    let n = corpus(0x5EED, 1)
        .iter()
        .filter(|p| capable(p.mode))
        .count();
    assert_eq!(n, 0, "the corpus contains {n} capable pair(s)");
}

/// **Neither `Mode` predicate is, on its own, the thing `Tally::add_capable`
/// must be given** — and its own rustdoc names one of the two wrong ones.
///
/// `add_capable` says: "`capable` says whether this pair's mode can produce a
/// false alarm at all — `Mode::is_constructed` for the generator's modes." A
/// caller who follows that sentence passes `true` for five of six modes and
/// publishes `FalseAlarmFigure::Measured { 0, k }` — a *measured* zero from a
/// population that cannot produce a false alarm, which is precisely the claim
/// the owner's A15 ruling forbids. Passing `can_false_alarm` alone is no better:
/// it is `true` exactly for the one mode that is **not built**.
///
/// Only the conjunction is right. This test pins all three, so the hazard is a
/// tested fact rather than a comment, and the report files the rustdoc as the
/// lead's to fix.
///
/// **Mutation, MEASURED**: make `Mode::can_false_alarm` return `true` for every
/// mode. Applied at gate 3; the conjunction assertion below fails
/// (`Measured` where `ZeroByConstruction` is required).
#[test]
fn neither_single_mode_predicate_is_the_capability_a_caller_must_pass() {
    let figure_under = |pred: &dyn Fn(Mode) -> bool| {
        let mut t = Tally::default();
        for m in Mode::all() {
            // One reporting pair per mode, so the denominator is non-zero and
            // the discriminator is `capable` alone.
            t.add_capable(&Agreement::BothFail { witness: witness(), exhausted: false }, pred(*m));
        }
        t.false_alarm_figure()
    };

    assert!(
        matches!(
            figure_under(&|m: Mode| m.is_constructed()),
            FalseAlarmFigure::Measured { .. }
        ),
        "`is_constructed` alone — the predicate `add_capable`'s rustdoc names — publishes a \
         measured zero"
    );
    assert!(
        matches!(
            figure_under(&|m: Mode| m.can_false_alarm()),
            FalseAlarmFigure::Measured { .. }
        ),
        "`can_false_alarm` alone is true exactly for the unbuilt mode, and also publishes a \
         measured zero"
    );
    assert!(
        matches!(
            figure_under(&|m: Mode| capable(m)),
            FalseAlarmFigure::ZeroByConstruction { .. }
        ),
        "only `is_constructed() && can_false_alarm()` yields the honest figure"
    );
}

/// **A15, the owner's ruling of 2026-09-17.** The figure this harness publishes
/// must say *how* it is to be read, and a zero from a population that could
/// never have produced a false alarm is **not** a measurement.
///
/// **Mutation, MEASURED**: replace `false_alarm_figure`'s `if self.capable == 0`
/// guard by `if false`. Applied at gate 3 —
/// `a_population_with_no_capable_mode_publishes_zero_by_construction ... FAILED`,
/// 351 passed / 1 failed. The corpus then publishes `0/2` with no caveat, which
/// reads as evidence that false alarms are rare.
#[test]
fn a_population_with_no_capable_mode_publishes_zero_by_construction() {
    let mut t = Tally::default();
    for _ in 0..2 {
        t.add_capable(&Agreement::BothClean, false);
    }
    t.add_capable(&Agreement::FalseAlarm { reports: 1, exhausted: false }, false);
    assert!(
        matches!(
            t.false_alarm_figure(),
            FalseAlarmFigure::ZeroByConstruction { .. }
        ),
        "no capable pair, so the figure is not a measurement whatever the counts say"
    );
    assert!(
        t.violations(2)
            .iter()
            .any(|v| v.contains("0 by construction")),
        "and the caveat is stated, not left to the reader"
    );

    let mut t2 = Tally::default();
    t2.add_capable(&Agreement::BothFail { witness: witness(), exhausted: false }, true);
    assert!(
        matches!(t2.false_alarm_figure(), FalseAlarmFigure::Measured { .. }),
        "a capable population yields a measured figure"
    );
}

/// `0/0` is not a rate, and the figure says so rather than rounding it to zero.
///
/// **Mutation, MEASURED**: delete `false_alarm_figure`'s
/// `if denominator == 0 { return NoReportingPairs }` early return, so a silent
/// population publishes `ZeroByConstruction { denominator: 0 }` — a caveated
/// zero over nothing, which still reads as a rate.
#[test]
fn a_population_that_never_reported_has_no_rate_at_all() {
    let mut t = Tally::default();
    t.add_capable(&Agreement::BothClean, true);
    assert_eq!(t.reporting(), 0);
    assert_eq!(t.false_alarm_rate(), None, "0/0 is not a rate");
    assert!(matches!(
        t.false_alarm_figure(),
        FalseAlarmFigure::NoReportingPairs
    ));
    assert!(
        format!("{}", t.false_alarm_figure()).contains("no denominator"),
        "and the rendering says why"
    );
}

// ---------------------------------------------------------------------------
// Criterion 6's gates
// ---------------------------------------------------------------------------

/// **`Tally::violations` names every empty class**, one message each.
///
/// Criterion 6 requires all four classes non-empty *and* the counts stated.
/// Before this test only the A15 branch of `violations` was reached by any
/// assertion — the corpus test printed the rest — so six of its seven gates
/// were dead code as far as the suite was concerned.
///
/// **Mutation, MEASURED**: delete the `if self.both_fail == 0` gate from
/// `violations`. Applied at gate 3; this test fails on the missing
/// "no pair on which the oracle says inclusion fails" message.
#[test]
fn violations_names_every_empty_class_and_the_unsound_one() {
    let empty = Tally::default().violations(2);
    assert!(
        empty
            .iter()
            .any(|v| v.contains("no pairs were generated")),
        "an empty population must be named, not pass vacuously: {empty:?}"
    );

    // Oracle-holds empty: only correct reports.
    let mut t = Tally::default();
    t.add_capable(&Agreement::BothFail { witness: witness(), exhausted: false }, false);
    let v = t.violations(2);
    assert!(
        v.iter()
            .any(|m| m.contains("no pair on which the oracle says inclusion holds")),
        "{v:?}"
    );
    assert!(
        v.iter()
            .any(|m| m.contains("no pair on which the tool certified")),
        "{v:?}"
    );

    // Oracle-fails empty, and nothing reported.
    let mut t = Tally::default();
    t.add_capable(&Agreement::BothClean, false);
    let v = t.violations(2);
    assert!(
        v.iter()
            .any(|m| m.contains("no pair on which the oracle says inclusion fails")),
        "{v:?}"
    );
    assert!(
        v.iter()
            .any(|m| m.contains("no pair on which the tool reported")),
        "{v:?}"
    );

    // Unsoundness is named first and is not a measurement.
    let mut t = Tally::default();
    t.add_capable(&Agreement::Unsound { witness: witness() }, false);
    let v = t.violations(2);
    assert!(v[0].contains("unsoundness"), "{v:?}");
}

/// **The inconclusive bound is a number asserted in code, and it fires.**
///
/// Criterion 6: "the inconclusive count is *gated* at zero for the pairs the
/// property is asserted on — or, if a bound is accepted instead, the bound is a
/// number asserted in code, never a sentence." A run where 190 of 200 pairs end
/// in `SearchExhausted` must not pass on the surviving ten.
///
/// The boundary is exercised on both sides, because a gate that is never tested
/// at its own edge is a gate nobody has read: at `ratio = 2`, one inconclusive
/// in two is *not* over the bound and one in one is.
///
/// **Mutation, MEASURED**: delete the inconclusive gate from `violations`
/// (the final `if` block). Applied at gate 3; this test fails on the missing
/// "over 1/2 of the population" message.
#[test]
fn the_inconclusive_bound_is_a_number_and_it_fires() {
    let inconclusive = || Agreement::Inconclusive {
        why: "search budget exhausted".to_owned(),
    };

    // 1 of 2 — exactly at the bound, not over it.
    let mut t = Tally::default();
    t.add_capable(&Agreement::BothClean, false);
    t.add_capable(&inconclusive(), false);
    assert!(
        !t.violations(2)
            .iter()
            .any(|v| v.contains("were inconclusive")),
        "1/2 is at the 1/2 bound, not over it: {:?}",
        t.violations(2)
    );

    // 2 of 3 — over it.
    let mut t = Tally::default();
    t.add_capable(&Agreement::BothClean, false);
    t.add_capable(&inconclusive(), false);
    t.add_capable(&inconclusive(), false);
    let v = t.violations(2);
    assert!(
        v.iter()
            .any(|m| m.contains("2 of 3 pairs were inconclusive")),
        "{v:?}"
    );

    // And the inconclusive pairs are outside every ratio.
    assert_eq!(t.reporting(), 0, "an inconclusive pair is not a reporting pair");
    assert_eq!(t.total(), 3, "but it is counted in the total");
}

/// An `Inconclusive` verdict is **not** a certificate, end to end.
///
/// Criterion 6's antecedent is an exhaustive run, and the crate ships a finite
/// default inner budget, so a run can be silent because it ran out of nodes.
/// This drives a real pair through `compare` with `search_budget(1)` and
/// asserts the harness scores it `Inconclusive` rather than `BothClean` —
/// the one distinction the theorem turns on.
///
/// **Reachability.** `Agreement::of`'s `Inconclusive` arm is still **not
/// reachable through `compare`** on any pair this generator emits: `compare`
/// runs the tool at `DEFAULT_SEARCH_BUDGET = 10_000`, which the generator's
/// micro-programs cannot exhaust. This test therefore drives it at the
/// `verify` level. Since F59 the arm **is** reachable through the harness, by
/// `compare_with_budget(.., Some(1))` — see
/// [`a_reported_and_exhausted_pair_is_scored_exhausted_through_the_harness`],
/// which asserts it end to end under all three models.
///
/// **Mutation, MEASURED**: make `ConfVerdict::of` return
/// `Conforms(Certificate { outcome })` whenever `outcome.reports` is empty,
/// dropping the `not_a_certificate()` test. Applied at gate 3; this test fails
/// with `a one-node inner budget must not yield a certificate`.
///
/// **Mutation, REFUTED at gate 3, MEASURED since F59**: "in `Agreement::of`,
/// map `ConfVerdict::Inconclusive` to `BothClean`". At gate 3 the full lib
/// suite stayed green at **359 passed / 0 failed**, the arm being unreachable
/// through `compare`. Re-applied at `P3-F59`: the full lib suite gives
/// **396 passed / 1 failed** — this test still passes (it never calls
/// `Agreement::of`), and
/// [`a_reported_and_exhausted_pair_is_scored_exhausted_through_the_harness`]
/// fails on `FIFO: a one-node budget neither reports nor certifies; got
/// BothClean`.
#[test]
fn a_bounded_inner_search_is_inconclusive_and_never_a_certificate() {
    use crate::conformance::config::ConfBuilder;
    use crate::conformance::report::ConfVerdict;

    let p = pair(Mode::Identity, 7);
    let impl_ = {
        let a = p.implementation.clone();
        move || a()
    };
    let spec = {
        let a = p.specification.clone();
        move || a()
    };
    let cc = ConfBuilder::new()
        .visible_threads(p.visible.iter().map(|s| s.as_str()))
        .config(p.config.clone())
        .search_budget(1)
        .build()
        .expect("in-scope");
    let verdict = crate::conformance::verify(cc, impl_, spec).expect("run");
    let ConfVerdict::Inconclusive(o) = &verdict else {
        panic!("a one-node inner budget must not yield a certificate; got {verdict:?}");
    };
    assert!(
        !o.not_a_certificate().is_empty(),
        "an Inconclusive verdict whose not_a_certificate() is empty is a contradiction"
    );

    // And the harness scores it out of every ratio.
    let a = Agreement::Inconclusive {
        why: "x".to_owned(),
    };
    assert!(a.is_inconclusive());
    assert!(!a.tool_reported(), "not in the denominator");
    assert!(!a.oracle_holds(), "not in the numerator either");
}

// ---------------------------------------------------------------------------
// The corpus
// ---------------------------------------------------------------------------

/// The whole harness on a small corpus: every mode, through both engines,
/// **with criterion 6's four classes asserted rather than printed**.
///
/// The previous version of this test asserted only `unsound == 0` and
/// `total > 0`, and its `To break it:` line named a mutation that fails
/// nothing — see the `REFUTED` note below. A generator emitting only refining
/// pairs would have passed it in full.
///
/// **Mutation, MEASURED**: drop `order_is_reflected` from **both**
/// `morphism::follows` and `morphism::matches`. Applied at gate 3 —
/// `a_small_corpus_runs_through_both_engines ... FAILED` (with
/// `ex_morph_m2_variation_...`, `phi_holds_the_receive_back...` and
/// `ex_sched_holds`), because the `DecoupleImpl` pair then certifies while the
/// oracle says inclusion fails: `unsound == 1`.
///
/// **Mutation, REFUTED**: the line this test used to carry — "make
/// `Agreement::of` map `(Reported, Holds)` to `BothFail`, and the false-alarm
/// count silently becomes zero". Applied at gate 3: the full lib suite stayed
/// green at **352 passed / 0 failed**. The count it changes was never asserted,
/// and it is already zero on this corpus, so nothing could observe it. Recorded
/// rather than deleted, per criterion 19's what-was-attempted rule.
#[test]
fn a_small_corpus_runs_through_both_engines() {
    let mut tally = Tally::default();
    let mut notes: Vec<String> = Vec::new();

    for p in corpus(0x5EED, 1) {
        match run(&p) {
            Ok(a) => {
                notes.push(format!("{:?} seed={:#x} -> {:?}", p.mode, p.seed, a));
                // The discriminator is the mode's construction, never the
                // outcome: a tally that inferred capability from "no false
                // alarm seen" would conclude none was possible, which is
                // A15's circularity.
                tally.add_capable(&a, capable(p.mode));
            }
            Err(e) => panic!("{:?} seed={:#x} -> ERROR {e:?}", p.mode, p.seed),
        }
    }

    println!("--- differential tally ---");
    for n in &notes {
        println!("{n}");
    }
    println!("{tally:?}");
    println!("{}", tally.false_alarm_figure());

    assert_eq!(
        tally.unsound, 0,
        "the tool certified a pair the oracle says does not refine — unsoundness. {notes:?}"
    );
    assert_eq!(
        tally.inconclusive, 0,
        "criterion 6 gates the inconclusive count at zero for the pairs the property is \
         asserted on. {notes:?}"
    );

    // Criterion 6's four classes, each non-empty — asserted, not described.
    // A generator emitting only refining pairs satisfies every other clause of
    // this test, and this is the clause it fails.
    let v = tally.violations(2);
    let unexpected: Vec<_> = v
        .iter()
        .filter(|m| !m.contains("0 by construction"))
        .collect();
    assert!(
        unexpected.is_empty(),
        "criterion 6 gate(s) failed on the generated corpus: {unexpected:?}\n{notes:?}"
    );

    // The one violation that *is* expected, and is the owner's accepted
    // outcome rather than a defect (A15, route 2).
    assert_eq!(
        v.len(),
        1,
        "exactly the A15 caveat is expected on this corpus; got {v:?}"
    );
    assert!(v[0].contains("0 by construction and not measured (A15)"), "{v:?}");

    // The published figure, with its reading attached.
    assert!(matches!(
        tally.false_alarm_figure(),
        FalseAlarmFigure::ZeroByConstruction { .. }
    ));
}

/// **Criterion 6's four classes are non-empty because of *which* modes exist**,
/// and the mapping from mode to outcome class is pinned here.
///
/// The corpus test above asserts the classes are non-empty; this says which
/// mode supplies each, so that deleting a mode fails with a message naming it
/// rather than with "some class is empty".
///
/// **Second mutation, DEMONSTRATED IN THE WILD rather than synthetically**: add
/// a mode to `Mode::all()` without pinning it here. This happened for real
/// between the two halves of gate 3 — the lead landed `Mode::SpecBlocks`, the
/// (M3) mode criterion 6 requires, and the completeness check below fired
/// immediately with `these modes are emitted by the generator but pinned by no
/// assertion here: [SpecBlocks]`. Without it the new mode would have entered
/// the corpus, and the published figure, unasserted — which is the *same*
/// blindness one level up from the one this test exists to fix.
///
/// **Mutation, MEASURED**: remove `Mode::VisibleMutation` from `Mode::all()`.
/// Applied at gate 3 — `each_outcome_class_is_supplied_by_a_named_mode ...
/// FAILED`, 358 passed / 1 failed, on `VisibleMutation is absent from the
/// corpus`. **`a_small_corpus_runs_through_both_engines` stays green**, which
/// is exactly why this test exists: `DecoupleImpl` keeps the `BothFail` and
/// reporting classes non-empty, so criterion 6's gates cannot see a lost mode.
/// Non-emptiness is a weaker property than coverage, and the corpus test checks
/// only the weaker one.
#[test]
fn each_outcome_class_is_supplied_by_a_named_mode() {
    let mut by_mode: Vec<(Mode, String)> = Vec::new();
    for p in corpus(0x5EED, 1) {
        let a = run(&p).unwrap_or_else(|e| panic!("{:?}: {e:?}", p.mode));
        by_mode.push((p.mode, format!("{a:?}").split(' ').next().unwrap().to_owned()));
    }
    let mut pinned: Vec<Mode> = Vec::new();
    let mut class_of = |m: Mode| -> String {
        pinned.push(m);
        by_mode
            .iter()
            .find(|(x, _)| *x == m)
            .unwrap_or_else(|| panic!("{m:?} is absent from the corpus"))
            .1
            .clone()
    };
    assert_eq!(class_of(Mode::Identity), "BothClean");
    assert_eq!(class_of(Mode::InvisibleRefactor), "BothClean");
    assert_eq!(class_of(Mode::VisibleMutation), "BothFail");
    assert_eq!(class_of(Mode::DecoupleImpl), "BothFail");
    assert_eq!(class_of(Mode::DecoupleSpec), "BothClean");
    // (M3). Derived, not read off a run: the implementation's `c` receives once
    // and is `Done`; the specification's `c` receives twice and the second
    // cannot be satisfied, so it is `Blocked`. The *words* agree — `main` sends
    // `v` and `c` observes `v` on both sides — and only `status|_Tvis` differs,
    // so `VisWord`'s status component is the sole discriminator and inclusion
    // fails. The tool fails `statuses_agree` and reports. Hence `BothFail`, by
    // the same conjunct `paper_examples`' two (M3) tests turn on.
    assert_eq!(class_of(Mode::SpecBlocks), "BothFail");
    // The unbuilt mode is `decoupled` against itself, i.e. an `Identity` pair.
    // Pinned so that building the hub shape shows up here as a change.
    assert_eq!(class_of(Mode::UnionCovered), "BothClean");

    // **Every mode must be pinned above.** Without this a mode added later —
    // the (M3) mode criterion 6 requires and the generator does not yet have —
    // would simply not be looked up, and would land unasserted. That is the
    // same failure this test exists to prevent, one level up: criterion 6's
    // non-emptiness gates cannot see a *lost* mode, and a per-mode table that
    // does not check its own completeness cannot see a *new* one.
    let missing: Vec<Mode> = Mode::all()
        .iter()
        .copied()
        .filter(|m| !pinned.contains(m))
        .collect();
    assert!(
        missing.is_empty(),
        "these modes are emitted by the generator but pinned by no assertion here: \
         {missing:?}. Add an `assert_eq!(class_of(..), ..)` for each, derived from the \
         mode's construction rather than from a run."
    );
}

// ---------------------------------------------------------------------------
// Gate 4, M2: the exhaustion counter and the gate it feeds
// ---------------------------------------------------------------------------

/// **A reporting pair that also exhausted is counted — and it is still in the
/// false-alarm denominator.**
///
/// Criterion 6's first "Required alongside it" bullet. `ConfVerdict::of` tests
/// `reports` first, so such a run is `Reported`, never reaches
/// `not_a_certificate()`, and lands in `BothFail`/`FalseAlarm` — inside
/// `Tally::reporting()`, which is the denominator — on the strength of a run
/// that was not exhaustive. `Agreement::of` reads `exhaustions()` before the
/// outcome is dropped and the flag is the only place the fact survives.
///
/// **Both reporting arms are pinned, separately.** A counter wired into
/// `BothFail` alone would pass a test that only exercised that arm, and the
/// arm it would miss is the false-alarm **numerator** — the number that leaves
/// this project.
///
/// The denominator assertion is deliberate rather than incidental: the bullet's
/// second branch asks for such pairs to be "excluded explicitly", and this
/// implementation does **not** exclude them — it gates instead. The reading is
/// therefore pinned here so that "excluded" is not later read off the counter's
/// existence. See the report for the two branches of that bullet.
///
/// **Mutation, MEASURED**: delete `if *exhausted { .. }` from `Tally::add`'s
/// `FalseAlarm` arm. Applied — this test fails on
/// `the FalseAlarm arm must count it too`.
#[test]
fn a_reporting_pair_that_exhausted_is_counted_and_stays_in_the_denominator() {
    let mut t = Tally::default();
    t.add(&Agreement::BothFail {
        witness: witness(),
        exhausted: true,
    });
    assert_eq!(
        t.reported_but_not_exhaustive, 1,
        "a BothFail whose run exhausted an inner budget is not an exhaustive run"
    );
    assert_eq!(t.both_fail, 1, "and it is still a reporting pair");
    assert_eq!(
        t.reporting(),
        1,
        "it is *not* removed from the denominator; the implementation gates rather than \
         excludes, and that reading is pinned here"
    );

    let mut t = Tally::default();
    t.add(&Agreement::FalseAlarm {
        reports: 1,
        exhausted: true,
    });
    assert_eq!(
        t.reported_but_not_exhaustive, 1,
        "the FalseAlarm arm must count it too — that arm is the false-alarm numerator"
    );
    assert_eq!(t.false_alarm, 1);
    assert_eq!(t.reporting(), 1);

    // The arithmetic invariant the count only makes sense under.
    let mut t = Tally::default();
    t.add(&Agreement::BothFail {
        witness: witness(),
        exhausted: true,
    });
    t.add(&Agreement::FalseAlarm {
        reports: 2,
        exhausted: true,
    });
    t.add(&Agreement::BothClean);
    assert_eq!(t.reported_but_not_exhaustive, 2);
    assert!(
        t.reported_but_not_exhaustive <= t.reporting(),
        "the count is a subset of the reporting pairs, or it is counting something else"
    );
    assert_eq!(t.total(), 3);
}

/// **The gate fires on exactly the reporting-and-exhausted pairs, and on
/// nothing else.**
///
/// The half that discriminates is the negative one: a `violations` that pushed
/// the message unconditionally, or a counter that incremented on every
/// `add`, passes the positive assertion above and fails here.
///
/// `Inconclusive` is the case that most looks like it should count and must
/// not: an exhausted run *with no report* is already routed to `Inconclusive`
/// by the certificate test, is excluded from every ratio, and is gated by the
/// inconclusive bound. Counting it here would double-gate one class and leave
/// the class M2 is about indistinguishable from it.
///
/// **Mutation, MEASURED**: delete the `if self.reported_but_not_exhaustive > 0`
/// block from `Tally::violations`. Applied — this test fails on
/// `the gate must name the exhausted reporting pairs`.
#[test]
fn the_exhaustion_gate_fires_only_on_reporting_pairs_that_exhausted() {
    // A population that satisfies every *other* gate, so the message under
    // test is the only thing that can differ between the two halves.
    let populate = |exhausted: bool| {
        let mut t = Tally::default();
        t.add_capable(&Agreement::BothClean, true);
        t.add_capable(
            &Agreement::BothFail {
                witness: witness(),
                exhausted,
            },
            true,
        );
        t.add_capable(
            &Agreement::FalseAlarm {
                reports: 1,
                exhausted,
            },
            true,
        );
        t
    };

    let fired = populate(true);
    assert_eq!(fired.reported_but_not_exhaustive, 2);
    let v = fired.violations(2);
    assert!(
        v.iter()
            .any(|m| m.contains("2 of 2 reporting pair(s) also exhausted an inner budget")),
        "the gate must name the exhausted reporting pairs: {v:?}"
    );
    assert!(
        v.iter().any(|m| m.contains("thm:alg's antecedent")),
        "and say why it matters — the antecedent, not merely the count: {v:?}"
    );

    let quiet = populate(false);
    assert_eq!(quiet.reported_but_not_exhaustive, 0);
    assert!(
        !quiet
            .violations(2)
            .iter()
            .any(|m| m.contains("exhausted an inner budget")),
        "the same population without the flag must not trip the gate: {:?}",
        quiet.violations(2)
    );

    // Every non-reporting class leaves the counter alone.
    for a in [
        Agreement::BothClean,
        Agreement::Unsound { witness: witness() },
        Agreement::Inconclusive {
            why: "search budget exhausted".to_owned(),
        },
    ] {
        let mut t = Tally::default();
        t.add(&a);
        assert_eq!(
            t.reported_but_not_exhaustive, 0,
            "{a:?} is not a reporting pair, so it cannot be a reporting pair that exhausted"
        );
    }
}

/// **The state M2 is about is real, and it is `Reported`.**
///
/// Everything else in this section is a fixture. This is the run: an
/// implementation whose gates have *unequal* cost against a budget that sits
/// between them, so one gate finds no cover and reports while another runs out
/// of nodes. `ConfVerdict::of` tests `reports` first, so the verdict is
/// `Reported` — the certificate test that would have caught `SearchExhausted`
/// is never reached, which is exactly M2's claim, established by a run rather
/// than by reading `report.rs`.
///
/// The shape, derived rather than searched for: `c` receives twice and two
/// invisible senders offer `1` and `2`, so the implementation has graphs in
/// which `c` observes `2` first and graphs in which it observes `1` first. The
/// specification offers `1` twice, so no specification graph covers *any* of
/// them — but the gate after `c`'s **first** observation has a smaller search
/// than the gate after its second. At `search_budget(5)` the shallow gate
/// completes and reports; the deeper ones exhaust. Measured across `FIFO`,
/// `Bag` and `Causal`: `Reported`, `reports = 1`, `exhaustions = 2` at every
/// budget in `5..=12` (below 5 nothing reports, from 13 nothing exhausts).
///
/// **Mutation, MEASURED**: in `ConfVerdict::of`, move the
/// `not_a_certificate().is_empty()` test above the `reports.is_empty()` test —
/// i.e. make the certificate test run first, which is what the deleted
/// `differential.rs` sentence claimed happened. Applied — the verdict becomes
/// `Inconclusive` and this test fails on
/// `a run that reported is Reported, whatever else it did`.
#[test]
fn a_run_that_reports_at_one_gate_and_exhausts_at_another_is_reported_not_inconclusive() {
    use crate::conformance::config::ConfBuilder;
    use crate::conformance::report::{ConfVerdict, NotACertificate};

    let (verdict, _) = uneven_gate_run(5);
    let ConfVerdict::Reported(o) = &verdict else {
        panic!("a run that reported is Reported, whatever else it did; got {verdict:?}");
    };
    assert!(!o.reports().is_empty(), "the shape must actually report");
    assert!(
        !o.exhaustions().is_empty(),
        "and it must actually exhaust, or this test is about a different run"
    );

    // The certificate test *would* have named the exhaustion — it is simply
    // never consulted on this path. That is the whole of M2.
    let nac = o.not_a_certificate();
    assert!(
        nac.iter()
            .any(|n| matches!(n, NotACertificate::SearchExhausted { .. })),
        "not_a_certificate() knows about the exhaustion: {nac:?}"
    );
    assert!(
        nac.iter()
            .any(|n| matches!(n, NotACertificate::Reported { .. })),
        "{nac:?}"
    );
    assert!(
        verdict.certificate().is_none(),
        "a reporting run is never a certificate"
    );

    // And the budget is the only thing separating this from an ordinary
    // report: at a budget above every gate's cost the same pair reports with
    // nothing exhausted, so the flag is not an artefact of the shape.
    let (clean, _) = uneven_gate_run(13);
    let ConfVerdict::Reported(o2) = &clean else {
        panic!("at budget 13 the same pair still reports; got {clean:?}");
    };
    assert!(
        o2.exhaustions().is_empty(),
        "at a budget above every gate there is nothing to exhaust"
    );

    let _ = ConfBuilder::new();
}

/// The `Reported`-and-exhausted run of
/// [`a_run_that_reports_at_one_gate_and_exhausts_at_another_is_reported_not_inconclusive`],
/// at a caller-chosen inner budget.
///
/// Returns the verdict and the visible list, so a caller can also ask the
/// oracle about the same pair.
fn uneven_gate_run(budget: usize) -> (crate::conformance::report::ConfVerdict, Vec<String>) {
    uneven_gate_run_under(crate::ConsType::Bag, budget)
}

/// [`uneven_gate_run`] under a caller-chosen model.
fn uneven_gate_run_under(
    model: crate::ConsType,
    budget: usize,
) -> (crate::conformance::report::ConfVerdict, Vec<String>) {
    use crate::conformance::config::ConfBuilder;
    use crate::Config;

    let visible = vec!["c".to_string()];
    let cc = ConfBuilder::new()
        .visible_threads(visible.iter().map(|s| s.as_str()))
        .config(Config::builder().with_cons_type(model).build())
        .search_budget(budget)
        .build()
        .expect("in-scope");
    let verdict = crate::conformance::verify(cc, uneven_gate_impl, uneven_gate_spec).expect("run");
    (verdict, visible)
}

/// Spawn a named thread — the visible list matches on the name.
fn named_thread<F: FnOnce() + Send + 'static>(n: &str, f: F) -> crate::thread::JoinHandle<()> {
    crate::thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

/// The uneven-gate implementation: visible `c` receives twice; invisible `a`
/// and `b` offer `1` and `2`.
///
/// A plain `fn` rather than a closure so every test driving this shape — at
/// the `verify` level or through the harness — runs the same program.
fn uneven_gate_impl() {
    use crate::{recv_msg_block, send_msg};
    let c = named_thread("c", || {
        let _x: i32 = recv_msg_block();
        let _y: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named_thread("a", move || send_msg(cid, 1i32));
    let _b = named_thread("b", move || send_msg(cid, 2i32));
}

/// The uneven-gate specification: as [`uneven_gate_impl`], but both senders
/// offer `1`, so no specification graph covers an implementation graph in
/// which `c` observes `2`.
fn uneven_gate_spec() {
    use crate::{recv_msg_block, send_msg};
    let c = named_thread("c", || {
        let _x: i32 = recv_msg_block();
        let _y: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named_thread("a", move || send_msg(cid, 1i32));
    let _b = named_thread("b", move || send_msg(cid, 1i32));
}

/// The three models §9 admits — the ones the uneven-gate shape was measured
/// under.
fn section9_models() -> [crate::ConsType; 3] {
    use crate::ConsType;
    [ConsType::FIFO, ConsType::Bag, ConsType::Causal]
}

/// **M2's gate, driven end to end through the harness (F59).**
///
/// Criterion 6's first "Required alongside it" bullet is about the pairs the
/// *harness* scores, so the obligation is discharged only when the harness
/// itself carries a reporting-and-exhausting run to the counter and the gate:
/// `compare_with_budget` → `verify` → `Agreement::of`'s `exhausted:` read →
/// `Tally::reported_but_not_exhaustive` → `Tally::violations`. The two halves
/// were each tested before; the join was not, in the `true` direction, because
/// `compare` could only run at `DEFAULT_SEARCH_BUDGET`.
///
/// The pair is the uneven-gate shape of
/// [`a_run_that_reports_at_one_gate_and_exhausts_at_another_is_reported_not_inconclusive`],
/// at every budget in `5..=12` and under each of §9's three models. The oracle
/// says inclusion fails, so the arm is `BothFail`.
///
/// **Two bounds on the same pair show the flag follows the budget and not the
/// shape**: at `Some(DEFAULT_SEARCH_BUDGET)` it reports with nothing exhausted,
/// and at `Some(1)` it neither reports nor certifies and is `Inconclusive` —
/// which is also the first end-to-end reach of that arm through the harness.
///
/// **Only the `BothFail` read is reached.** `FalseAlarm`'s `exhausted:` read
/// needs a false-alarm pair, and no such pair is constructible here (A15), so
/// that read is still exercised by no end-to-end run in either direction.
///
/// **Mutations, all MEASURED at `P3-F59`** (applied to `differential.rs`,
/// filtered suite run, file restored and md5-verified):
///
/// - drop `builder = builder.search_budget(n)` (`Some(n)` ignored) — fails on
///   `FIFO budget 5: the harness scored a run that exhausted its inner budget
///   as exhaustive`;
/// - revert the `BothFail` arm's read to `exhausted: false` — fails on the same
///   message. **This is the join F59 is about, and it now fails something**;
/// - budget the oracle as well (`config.max_iterations = Some(n)` before
///   `includes`, the only budget the oracle has) — fails on `FIFO Some(5): the
///   pair is in scope: Oracle(Truncated { .. })`;
/// - delete `if *exhausted { .. }` from `Tally::add`'s `BothFail` arm — fails
///   here, with the two `Tally`-level tests;
/// - map `ConfVerdict::Inconclusive` to `BothClean` — fails on `FIFO: a
///   one-node budget neither reports nor certifies; got BothClean`.
///
/// **Not observed here**: revert the `FalseAlarm` arm's read to
/// `exhausted: false`. At `P3-F59` the full lib suite stayed at **397 passed /
/// 0 failed / 5 ignored**, as predicted by the paragraph above. That half of
/// F59 is closed by route 2 (owner ruling), in
/// [`a_real_reported_and_exhausted_verdict_scored_as_a_false_alarm_is_counted_and_gated`],
/// which the same mutation now fails.
#[test]
fn a_reported_and_exhausted_pair_is_scored_exhausted_through_the_harness() {
    use crate::conformance::config::DEFAULT_SEARCH_BUDGET;
    use crate::{Config, ConsType};

    let visible = ["c".to_string()];
    let run = |model: ConsType, budget: Option<usize>| {
        compare_with_budget(
            Config::builder().with_cons_type(model).build(),
            &visible,
            uneven_gate_impl,
            uneven_gate_spec,
            budget,
        )
        .unwrap_or_else(|e| panic!("{model:?} {budget:?}: the pair is in scope: {e:?}"))
    };

    for model in section9_models() {
        for b in 5..=12 {
            let got = run(model, Some(b));
            let Agreement::BothFail { exhausted, .. } = &got else {
                panic!(
                    "{model:?} budget {b}: the tool reports and the oracle says inclusion \
                     fails; got {got:?}"
                );
            };
            assert!(
                *exhausted,
                "{model:?} budget {b}: the harness scored a run that exhausted its inner \
                 budget as exhaustive"
            );

            let mut t = Tally::default();
            t.add(&got);
            assert_eq!(
                t.reported_but_not_exhaustive, 1,
                "{model:?} budget {b}: the counter must go off zero"
            );
            assert_eq!(
                t.reporting(),
                1,
                "{model:?} budget {b}: gated, not excluded — the pair stays in the denominator"
            );
            let v = t.violations(2);
            assert!(
                v.iter()
                    .any(|m| m.contains("1 of 1 reporting pair(s) also exhausted an inner budget")),
                "{model:?} budget {b}: the gate must name the pair: {v:?}"
            );
        }

        let high = run(model, Some(DEFAULT_SEARCH_BUDGET));
        let Agreement::BothFail { exhausted, .. } = &high else {
            panic!("{model:?} at the default budget: expected BothFail; got {high:?}");
        };
        assert!(
            !exhausted,
            "{model:?}: at the default budget nothing exhausts, so the flag is the budget's \
             doing and not the shape's"
        );

        let low = run(model, Some(1));
        assert!(
            low.is_inconclusive(),
            "{model:?}: a one-node budget neither reports nor certifies; got {low:?}"
        );
        let mut t = Tally::default();
        t.add(&low);
        assert_eq!(
            (t.inconclusive, t.reported_but_not_exhaustive, t.reporting()),
            (1, 0, 0),
            "{model:?}: an exhausted run with no report is Inconclusive and nothing else"
        );
    }
}

/// **F59's second half: the `FalseAlarm` arm's `exhausted:` read, in the
/// `true` direction, on a real verdict.**
///
/// That arm cannot be reached through the harness: it needs a pair the tool
/// reports on while the oracle says inclusion holds, and no such pair is
/// constructible here (A15). The owner ruled route 2, so this calls
/// `Agreement::of` directly. The `ConfVerdict` is **not fabricated**: it is
/// the uneven-gate pair run through `verify` at `search_budget(5)`, which is
/// `Reported` with a non-empty `exhaustions()`.
///
/// **`Inclusion::Holds` is counterfactual for this pair**; the oracle says
/// `Fails` (see
/// [`a_reported_and_exhausted_pair_is_scored_exhausted_through_the_harness`]).
/// So this establishes what `Agreement::of` and `Tally` do with a
/// reporting-and-exhausting false alarm, not that one exists. It tests the
/// function, not the harness, and it is the only test of this read.
///
/// **The complement is the same program at `DEFAULT_SEARCH_BUDGET`**, which
/// is `Reported` with empty `exhaustions()`. It scores
/// `FalseAlarm { exhausted: false }`, leaves the counter at zero and trips no
/// gate, so the budget is the only difference between the two halves. Run
/// under FIFO, Bag and Causal.
///
/// **Mutations, MEASURED at `P3-F59` continuation** (on `differential.rs` at
/// md5 `fb7a0937…`, filtered suite, restored and md5-verified):
///
/// - revert the `FalseAlarm` arm's read to `exhausted: false` — fails on
///   `FIFO: the FalseAlarm arm dropped the outcome's exhaustions`, and **only
///   this test** (filtered 21/1; full lib 397 passed / 1 failed / 5 ignored).
///   Before this test existed, the same mutation failed nothing;
/// - `FalseAlarm`'s `reports: 0` — fails on `` FIFO: `reports` is the
///   outcome's own count ``, only this test;
/// - delete `if *exhausted { .. }` from `Tally::add`'s `FalseAlarm` arm —
///   fails on `FIFO: counted, and kept in the denominator (gated, not
///   excluded)`, with the two `Tally`-level tests;
/// - revert the `BothFail` arm's read — does **not** fail this test (it
///   never reaches that arm), and still fails the two harness tests.
#[test]
fn a_real_reported_and_exhausted_verdict_scored_as_a_false_alarm_is_counted_and_gated() {
    use crate::conformance::config::DEFAULT_SEARCH_BUDGET;
    use crate::conformance::oracle::Inclusion;
    use crate::conformance::report::ConfVerdict;

    // Returns the scored agreement and the verdict's real report count.
    let score = |model: crate::ConsType, budget: usize, want_exhausted: bool| {
        let (verdict, _) = uneven_gate_run_under(model, budget);
        let ConfVerdict::Reported(o) = &verdict else {
            panic!("{model:?} budget {budget}: expected a real Reported verdict; got {verdict:?}");
        };
        assert_eq!(
            !o.exhaustions().is_empty(),
            want_exhausted,
            "{model:?} budget {budget}: precondition on the real outcome's exhaustions() \
             does not hold, so this half tests nothing"
        );
        let reports = o.reports().len();
        (Agreement::of(verdict, Inclusion::Holds), reports)
    };

    for model in section9_models() {
        // The true direction.
        let (got, reports) = score(model, 5, true);
        let Agreement::FalseAlarm {
            reports: r,
            exhausted,
        } = &got
        else {
            panic!("{model:?}: Reported + Holds is a false alarm; got {got:?}");
        };
        assert!(
            *exhausted,
            "{model:?}: the FalseAlarm arm dropped the outcome's exhaustions"
        );
        assert_eq!(
            *r, reports,
            "{model:?}: `reports` is the outcome's own count"
        );

        let mut t = Tally::default();
        t.add(&got);
        assert_eq!(
            (t.false_alarm, t.reported_but_not_exhaustive, t.reporting()),
            (1, 1, 1),
            "{model:?}: counted, and kept in the denominator (gated, not excluded)"
        );
        let v = t.violations(2);
        assert!(
            v.iter()
                .any(|m| m.contains("1 of 1 reporting pair(s) also exhausted an inner budget")),
            "{model:?}: the gate must name the pair: {v:?}"
        );

        // The complement: same program, default budget.
        let (quiet, _) = score(model, DEFAULT_SEARCH_BUDGET, false);
        assert!(
            matches!(
                quiet,
                Agreement::FalseAlarm {
                    exhausted: false,
                    ..
                }
            ),
            "{model:?}: at the default budget nothing exhausts; got {quiet:?}"
        );
        let mut t = Tally::default();
        t.add(&quiet);
        assert_eq!(
            (t.false_alarm, t.reported_but_not_exhaustive),
            (1, 0),
            "{model:?}"
        );
        assert!(
            !t.violations(2)
                .iter()
                .any(|m| m.contains("also exhausted an inner budget")),
            "{model:?}: the complement must not trip the gate: {:?}",
            t.violations(2)
        );
    }
}

/// **`compare` is the default-budget path, and at the default budget this pair
/// does not exhaust.**
///
/// Before F59 this test was a tripwire on `compare` having no budget knob. The
/// knob landed as a sibling, `compare_with_budget`, and `compare` is now
/// `compare_with_budget(.., None)`, so the tripwire framing no longer applies:
/// the reporting-and-exhausting state **is** reachable through the harness, by
/// [`a_reported_and_exhausted_pair_is_scored_exhausted_through_the_harness`].
///
/// What stays true, and is pinned here: `compare` runs the tool at
/// `DEFAULT_SEARCH_BUDGET`, which is above every gate in this pair, so every
/// caller of `compare` sees `exhausted: false` on it. The corpus tests now go
/// through `Pair::compare(None)`, which passes the same `None` budget. The same pair at `Some(12)` exhausts, in the same test, so this
/// assertion is about the budget `compare` passes and not about the pair.
///
/// Whether `compare` and `compare_with_budget(.., None)` can drift is
/// structural, not tested: the first is a call to the second. What *is* tested
/// is that the path `compare` takes runs at the default budget.
///
/// **Mutations, MEASURED at `P3-F59`** (on `differential.rs`, restored and
/// md5-verified):
///
/// - `compare` passes `Some(5)` instead of `None` — fails on `` `compare` must
///   run at the default budget, which is above every gate in this pair ``, and
///   fails **only** this test in the filtered suite;
/// - `compare_with_budget`'s `None` path sets `search_budget(5)` — fails on the
///   same message, and only this test;
/// - drop `builder = builder.search_budget(n)`, or revert the `BothFail`
///   read to `false` — fails on `the same pair at budget 12 exhausts, so the
///   assertion above discriminates; got BothFail { .., exhausted: false }`.
#[test]
fn compare_runs_at_the_default_budget_and_this_pair_does_not_exhaust_there() {
    use crate::{Config, ConsType};

    let config = || Config::builder().with_cons_type(ConsType::Bag).build();
    let visible = ["c".to_string()];

    let got = compare(config(), &visible, uneven_gate_impl, uneven_gate_spec)
        .expect("the pair is in scope on both engines");
    let Agreement::BothFail { exhausted, .. } = &got else {
        panic!("the tool reports and the oracle agrees inclusion fails; got {got:?}");
    };
    assert!(
        !exhausted,
        "`compare` must run at the default budget, which is above every gate in this pair"
    );
    let mut t = Tally::default();
    t.add(&got);
    assert_eq!(t.reported_but_not_exhaustive, 0);

    let bounded = compare_with_budget(
        config(),
        &visible,
        uneven_gate_impl,
        uneven_gate_spec,
        Some(12),
    )
    .expect("the pair is in scope on both engines");
    assert!(
        matches!(
            bounded,
            Agreement::BothFail {
                exhausted: true,
                ..
            }
        ),
        "the same pair at budget 12 exhausts, so the assertion above discriminates; \
         got {bounded:?}"
    );
}

// ---------------------------------------------------------------------------
// Gate 4, M3: criterion 13's two grammar bounds
// ---------------------------------------------------------------------------

/// The per-visible-thread event counts of one emitted pair, as the oracle's
/// enumerated words show them — implementation and specification.
///
/// A `vis` word is the visible events of one complete execution, so the number
/// of elements carrying a given declared name **is** that thread's visible
/// event count on that execution — the same quantity the oracle's cap reads
/// off `wobs` before enumerating.
///
/// **Deliberately uncapped.** This is a measurement, and the tests built on it
/// must not depend on the mechanism they are a second guard for.
fn events_per_visible_thread(p: &Pair) -> Vec<(String, usize)> {
    use crate::conformance::oracle::vis_of_program;
    let mut worst: BTreeMap<String, usize> = BTreeMap::new();
    for side in [p.implementation.clone(), p.specification.clone()] {
        let g = move || side();
        let set = vis_of_program(p.config.clone(), &p.visible, g)
            .unwrap_or_else(|e| panic!("{:?}: the oracle refused to enumerate: {e:?}", p.mode));
        for w in set.iter() {
            for name in &p.visible {
                let c = w.word.iter().filter(|e| &e.thread == name).count();
                let slot = worst.entry(name.clone()).or_insert(0);
                *slot = (*slot).max(c);
            }
        }
    }
    worst.into_iter().collect()
}

/// **Criterion 13's first bound, on every emitted pair** — and the bound is
/// tight, so the assertion in `pair()` is not slack.
///
/// `MAX_VISIBLE_THREADS` is asserted inside `pair()`, which is the single
/// construction point; that assertion's own failing direction is not
/// exercisable from here, because every shape is a literal in that module and
/// none declares three. What *is* exercisable, and what this test buys, is that
/// the corpus calls `pair()` for every mode — so a later shape declaring a
/// third visible thread trips the assertion inside this test rather than in
/// whatever run first happens to touch it.
///
/// The equality is asserted, not just the inequality: at `<=` alone a generator
/// that emitted one visible thread per pair would satisfy criterion 13 while
/// making `vo` total on every graph and the differential trivial.
///
/// The model pick is pinned in the same place because it is the other half of
/// the generator's "refused by §9" list: mailbox/`TotalOrder` is absent by
/// construction, and `models()` is the construction.
///
/// **Mutation, MEASURED**: change `MAX_VISIBLE_THREADS` to 1. Applied — the
/// assertion inside `pair()` fires first, so this test fails with
/// `generator: Identity declares 2 visible threads, over MAX_VISIBLE_THREADS (1)`.
#[test]
fn every_emitted_pair_declares_exactly_max_visible_threads() {
    use crate::conformance::generator::MAX_VISIBLE_THREADS;
    use crate::ConsType;

    assert_eq!(
        MAX_VISIBLE_THREADS, 2,
        "the bound this suite's cost figures were derived against"
    );
    for p in corpus(0x5EED, 1) {
        assert!(
            p.visible.len() <= MAX_VISIBLE_THREADS,
            "{:?} declares {} visible threads",
            p.mode,
            p.visible.len()
        );
        assert_eq!(
            p.visible.len(),
            MAX_VISIBLE_THREADS,
            "{:?} declares fewer than the bound; with one visible thread `vo` is total on \
             every graph and the linear-extension enumeration the oracle exists for is \
             vacuous",
            p.mode
        );
        assert!(
            matches!(
                p.config.cons_type,
                ConsType::FIFO | ConsType::Bag | ConsType::Causal
            ),
            "{:?} picked {:?}, which is outside §9's three models",
            p.mode,
            p.config.cons_type
        );
    }
}

/// **Criterion 13's second bound, on every emitted shape — a regression guard,
/// not the bound.**
///
/// Gate 4 wrote this as *the* check on `MAX_VISIBLE_EVENTS_PER_THREAD`.
/// `P3-gate4-fixes` rejected that twice: round 1 because it checks only today's
/// corpus, round 2 because a runtime cap alone runs after exploration. The
/// bound is now each shape's **declaration**, asserted in `pair()`, and
/// [`every_shapes_declared_observations_equal_the_measured_counts`] checks the
/// declarations are true.
///
/// Kept as a guard that depends on **neither** the declaration nor the
/// runtime cap. It compares the uncapped measured count with the constant
/// directly. It still catches a shape that really is over the bound in one
/// case the other layers miss together: an honest over-bound declaration
/// (so the equality test passes) with `pair()`'s bound assertion removed and
/// the pair run uncapped.
///
/// **Mutation, MEASURED** (gate 4): `MAX_VISIBLE_EVENTS_PER_THREAD = 0` failed
/// this test with `over MAX_VISIBLE_EVENTS_PER_THREAD (0)`. Re-measured at the
/// `P3-gate4-fixes` round-2 response: it still fails, now earlier, on `pair()`'s
/// assertion (`generator: Identity declares 1 visible observations for \`main\`
/// …`), because the bound is enforced at construction.
#[test]
fn no_emitted_pair_exceeds_max_visible_events_per_thread() {
    use crate::conformance::generator::MAX_VISIBLE_EVENTS_PER_THREAD;

    for p in corpus(0x5EED, 1) {
        for (name, n) in events_per_visible_thread(&p) {
            assert!(
                n <= MAX_VISIBLE_EVENTS_PER_THREAD,
                "{:?} seed={:#x}: visible thread {name:?} performs {n} visible events, over \
                 MAX_VISIBLE_EVENTS_PER_THREAD ({MAX_VISIBLE_EVENTS_PER_THREAD}). `vis` \
                 enumeration grows exponentially in this parameter across two visible \
                 threads",
                p.mode,
                p.seed
            );
        }
    }
}

/// **The second bound is slack, and the constant's rustdoc says otherwise.**
///
/// `MAX_VISIBLE_EVENTS_PER_THREAD`'s own rustdoc claims "`Mode::SpecBlocks` is
/// the shape that reaches it: its specification has `c` receive twice." Under
/// the definition that same rustdoc prescribes — the oracle's enumerated words
/// — it does not. The specification's second `recv_msg_block` can never be
/// satisfied, so it contributes no observation: `c` has **one** element in every
/// word and carries `Status::Blocked`, which is precisely what makes
/// `SpecBlocks` an (M3) test rather than an (M1) one. Measured: every mode,
/// both sides, worst = 1 against a bound of 2.
///
/// So the bound above is real but is never approached, and
/// [`no_emitted_pair_exceeds_max_visible_events_per_thread`] would pass on a
/// generator that had silently lost half its events. This test is the one that
/// notices. It is *not* asserting that the bound must be attained — criterion
/// 13 does not ask for tightness — it pins the measured value so that a change
/// on either side shows up as a change here.
///
/// Recorded as a finding rather than corrected: the rustdoc is production prose
/// and not the developer's to edit.
///
/// **Mutation, MEASURED**: give `Mode::Identity`'s `c` a second
/// `recv_msg_block()` fed by a second send. The measured maximum becomes 2 and
/// this test fails on `worst observed count`.
#[test]
fn the_events_per_thread_bound_is_not_attained_by_any_shape() {
    use crate::conformance::generator::MAX_VISIBLE_EVENTS_PER_THREAD;

    let mut worst = 0usize;
    let mut per_mode: Vec<(Mode, usize)> = Vec::new();
    for p in corpus(0x5EED, 1) {
        let m = events_per_visible_thread(&p)
            .into_iter()
            .map(|(_, n)| n)
            .max()
            .unwrap_or(0);
        per_mode.push((p.mode, m));
        worst = worst.max(m);
    }
    assert_eq!(
        worst, 1,
        "worst observed count over the whole corpus, against a declared bound of \
         {MAX_VISIBLE_EVENTS_PER_THREAD}: {per_mode:?}"
    );
    assert_eq!(
        per_mode
            .iter()
            .find(|(m, _)| *m == Mode::SpecBlocks)
            .map(|(_, n)| *n),
        Some(1),
        "MAX_VISIBLE_EVENTS_PER_THREAD's rustdoc names SpecBlocks as the shape that reaches \
         the bound; its blocked second receive contributes no observation, so it does not. \
         {per_mode:?}"
    );
}

// ---------------------------------------------------------------------------
// Gate 4, M4: the generator's two lists, made falsifiable
// ---------------------------------------------------------------------------

/// **No emitted pair is a visible-error pair**, which is what the generator's
/// "not reached by this generator" list now claims.
///
/// M4's fix added the entry; prose cannot fail. This makes the claim
/// falsifiable from the only side that can be checked — the emitted
/// population's own behaviour — so a shape added later whose visible thread
/// asserts fires here instead of quietly turning a declared gap into an
/// undeclared coverage claim.
///
/// The status component is the right probe: `vis(σ) ≝ ⟨w, status|_Tvis⟩`, and a
/// visible thread that fails an assertion is exactly `Status::Errored` in that
/// component. `a_visible_error_pair_is_enumerated_and_scores_rather_than_refusing`
/// shows the oracle *can* answer on such a pair, so an absence here is a
/// generator gap and nothing else — which is the sentence M4's fix put in the
/// list.
///
/// **Mutation, MEASURED**: change `Mode::Identity`'s implementation to
/// `named("c", || crate::assert(false))`. Applied — this test fails with
/// `Identity ... carries Status::Errored`.
#[test]
fn no_emitted_pair_is_a_visible_error_pair() {
    use crate::conformance::morphism::Status;
    use crate::conformance::oracle::vis_of_program;

    for p in corpus(0x5EED, 1) {
        for (side, f) in [
            ("implementation", p.implementation.clone()),
            ("specification", p.specification.clone()),
        ] {
            let g = move || f();
            let set = vis_of_program(p.config.clone(), &p.visible, g)
                .unwrap_or_else(|e| panic!("{:?} {side}: oracle refused: {e:?}", p.mode));
            for w in set.iter() {
                for (name, st) in &w.statuses {
                    assert_ne!(
                        *st,
                        Status::Errored,
                        "{:?} seed={:#x}: the {side}'s visible thread {name:?} carries \
                         Status::Errored, so this generator *does* emit §11.5's \
                         visible-error shape — the module doc lists it as never emitted",
                        p.mode,
                        p.seed
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Gate 4, M6: the caveats travel with the figure
// ---------------------------------------------------------------------------

/// **Both figure arms carry all three caveats**, itemised rather than checked
/// as one blob.
///
/// Criterion 7's last bullet asks for **two** caveats beside the figure (F-6
/// and F41) and criterion 14's last "Required" adds the three shared items, all
/// carried "by any figure derived from the harness". The figure is the artefact
/// that leaves the project, and before M6's fix it carried A15 alone — the
/// other three were in `generator.rs`'s and `oracle.rs`'s module docs, where a
/// reader of the *number* never looks.
///
/// Each caveat is asserted by name and on each arm separately: a single
/// `contains(FIGURE_CAVEATS)` would pass on a constant that had lost two of its
/// three bullets, and appending the block to one arm only is the likelier
/// regression of the two.
///
/// `NoReportingPairs` is deliberately excluded and the reason is pinned below:
/// it publishes no number, and criterion 7's bullet is about what travels with
/// a figure. That it says so — rather than rendering a caveated zero — is the
/// property asserted for it.
///
/// **Mutation, MEASURED**: delete `{FIGURE_CAVEATS}` from the
/// `ZeroByConstruction` arm of `Display`. Applied — this test fails on
/// `ZeroByConstruction is missing the F-6 caveat`; the `Measured` half stays
/// green, which is the point of splitting them.
#[test]
fn both_figure_arms_carry_all_three_caveats() {
    use crate::conformance::differential::FIGURE_CAVEATS;

    let arms = [
        (
            "Measured",
            FalseAlarmFigure::Measured {
                numerator: 1,
                denominator: 4,
            },
        ),
        (
            "ZeroByConstruction",
            FalseAlarmFigure::ZeroByConstruction { denominator: 4 },
        ),
    ];
    for (name, figure) in arms {
        let rendered = format!("{figure}");
        for caveat in [
            "F-6",
            "F41",
            "obs::wobs",
            "ExecutionGraph::in_porf",
            "msg::Val::eq",
        ] {
            assert!(
                rendered.contains(caveat),
                "{name} is missing the {caveat} caveat; the figure is the artefact that \
                 leaves the project and an unstated blind spot reads as covered ground \
                 (criteria 7 and 14). Rendered:\n{rendered}"
            );
        }
        assert!(
            rendered.contains("cannot measure"),
            "{name}: F41 must be worded as a limit on what the figure *can* measure, not as \
             a sampling gap (criterion 7). Rendered:\n{rendered}"
        );
    }

    // A15 still travels, and it travels structurally rather than as text.
    assert!(
        format!(
            "{}",
            FalseAlarmFigure::ZeroByConstruction { denominator: 4 }
        )
        .contains("not measured"),
        "the A15 reading must not have been displaced by the new block"
    );
    assert!(
        format!(
            "{}",
            FalseAlarmFigure::Measured {
                numerator: 1,
                denominator: 4
            }
        )
        .contains("1/4 (measured)"),
        "and the number itself must still be rendered"
    );

    // The non-figure arm: no number, so nothing to caveat — but it must say
    // that rather than round to zero.
    let none = format!("{}", FalseAlarmFigure::NoReportingPairs);
    assert!(none.contains("not computed"), "{none}");
    assert!(
        !none.contains("0/"),
        "`0/0` must not be rendered as a rate: {none}"
    );
    assert!(
        !none.contains(FIGURE_CAVEATS),
        "recorded, not accidental: the caveats are attached to the two arms that publish a \
         number. If criterion 14's \"any figure\" is read to include this arm, this is the \
         assertion that must change."
    );
}

/// **Gate 4's M1: the `Collect` branch is load-bearing, and a visible-error
/// pair scores instead of collapsing.**
///
/// Before this, `vis_of_program` returned `Err(OracleError::VisibleError)` on
/// `collect_errors().first()` *before* reading `collected()` — throwing away
/// the graphs `ConfMode::Collect` exists to keep untruncated. The branch
/// therefore changed no oracle answer, and the reviewer's dissenting route
/// (no edit to a sealed file) would have been observationally identical.
///
/// Three things this asserts, and the third is the one that was impossible:
///
/// 1. the oracle **answers** on a pair whose implementation's visible thread
///    fails an assertion, rather than refusing;
/// 2. it answers `Fails` — the implementation has `vis` words carrying
///    `Status::Errored`, and the specification, being err-free, has none;
/// 3. the pair therefore scores `BothFail` through `compare()`. Gate 4's M4
///    recorded §11.5's visible-error shape as un-emittable by the generator
///    *because the oracle refused to answer on it*; that is now false.
///
/// **Mutation, MEASURED**: restore the early
/// `return Err(OracleError::VisibleError { .. })` above the enumeration loop
/// in `vis_of_program` — `compare` then yields `DiffError::Oracle` and this
/// test fails on its first assertion.
#[test]
fn a_visible_error_pair_is_enumerated_and_scores_rather_than_refusing() {
    use crate::conformance::differential::{compare, Agreement};
    use crate::{thread, ConsType, Config};

    fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
        thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
    }

    let cfg = Config::builder().with_cons_type(ConsType::FIFO).build();
    let vis = vec!["w".to_string()];
    let imp = || {
        let _w = named("w", || crate::assert(false));
    };
    let spec = || {
        let _w = named("w", || {});
    };

    let got = compare(cfg, &vis, imp, spec)
        .expect("the oracle must answer on a visible-error pair, not refuse it");
    assert!(
        matches!(got, Agreement::BothFail { .. }),
        "an implementation whose visible thread errors does not refine an err-free \
         specification, and the tool reports it; got {got:?}"
    );
}

// ---------------------------------------------------------------------------
// P3-gate4-fixes round 1, M1: the event cap as a runtime bound
// ---------------------------------------------------------------------------

/// **A pair over the event cap is refused through `Pair::compare`, and the
/// refusal names the thread and the counts.**
///
/// Criterion 13 asks for a hard bound. The owner's route is a runtime cap:
/// `Pair::compare` passes `MAX_VISIBLE_EVENTS_PER_THREAD` to the oracle, which
/// refuses any graph whose visible thread exceeds it. No shipped shape exceeds
/// it, so the pairs here are built by hand (`Pair`'s fields are `pub(crate)`).
///
/// Three placements, one per way the check could be too narrow:
/// - over the cap on the **second** visible thread only, so a check that
///   looked at one thread would pass it;
/// - over the cap on the **first** thread, by exactly one;
/// - over the cap in the **specification only**, so a cap applied to the
///   implementation's enumeration alone would pass it.
#[test]
fn a_pair_over_the_event_cap_is_refused_through_pair_compare_naming_the_thread() {
    use crate::conformance::differential::DiffError;
    use crate::conformance::generator::MAX_VISIBLE_EVENTS_PER_THREAD as CAP;
    use crate::conformance::oracle::OracleError;
    use std::sync::Arc;

    let expect = |p: &Pair, what: &str, thread: &str, observations: usize| match p.compare(None) {
        Err(DiffError::Oracle(OracleError::OverCap {
            thread: t,
            observations: o,
            cap,
        })) => {
            assert_eq!(
                (t.as_str(), o, cap),
                (thread, observations, CAP),
                "{what}: the refusal must name the thread, its count and the cap"
            );
        }
        other => panic!("{what}: expected OverCap on {thread:?}; got {other:?}"),
    };

    expect(
        &two_chain_pair(1, CAP + 1),
        "second thread over",
        "d",
        CAP + 1,
    );
    expect(
        &two_chain_pair(CAP + 1, 1),
        "first thread over",
        "c",
        CAP + 1,
    );

    let mut p = two_chain_pair(1, 1);
    p.specification = Arc::new(|| {
        receive_chain("c", "s", 1);
        receive_chain("d", "t", CAP + 2);
    });
    expect(&p, "specification only", "d", CAP + 2);
}

/// **The cap does not fire at the bound, and it is the cap that refuses.**
///
/// - Exactly `MAX_VISIBLE_EVENTS_PER_THREAD` observations on both visible
///   threads is **accepted** by `Pair::compare` and scores as usual (`BothClean`:
///   implementation and specification are the same program). This separates
///   `>` from `>=`.
/// - The over-cap pair of
///   [`a_pair_over_the_event_cap_is_refused_through_pair_compare_naming_the_thread`],
///   run through the **uncapped** `compare`, is **not** refused. So the refusal
///   there comes from the cap and not from the program. This also pins the
///   bypass the generator's module doc states: the cap binds only pairs run
///   through `Pair::compare`.
#[test]
fn the_event_cap_accepts_the_bound_and_uncapped_compare_bypasses_it() {
    use crate::conformance::generator::MAX_VISIBLE_EVENTS_PER_THREAD as CAP;

    let at = two_chain_pair(CAP, CAP);
    let got = at.compare(None).unwrap_or_else(|e| {
        panic!("exactly {CAP} observations per thread is within the bound: {e:?}")
    });
    assert!(
        matches!(got, Agreement::BothClean),
        "an identical pair at the bound scores as usual; got {got:?}"
    );

    let over = two_chain_pair(1, CAP + 1);
    let (i, s) = (over.implementation.clone(), over.specification.clone());
    let got = compare(over.config.clone(), &over.visible, move || i(), move || s())
        .unwrap_or_else(|e| panic!("uncapped `compare` must not refuse an over-cap pair: {e:?}"));
    assert!(
        matches!(got, Agreement::BothClean),
        "uncapped, the same pair is enumerated and scored; got {got:?}"
    );
}

/// **An over-cap graph is refused before its enumeration starts.** This is
/// shown with the oracle's test-only counter, not with a clock.
///
/// `oracle::take_enumerations_started()` counts, per OS thread, the times
/// `vis_of_graph` reached `extend`. The oracle scores graphs on the calling
/// thread, and the tool never calls `vis_of_graph`, so every count here comes
/// from `Pair::compare`'s oracle calls. The test measures its own reference
/// numbers rather than assuming them: each side's graph count is the counter
/// after an **uncapped** `vis_of_program` of that side alone.
///
/// Three runs, one per way the counts can come out:
/// - **At the bound** (`(2,2)`): `Pair::compare` enumerates exactly
///   `graphs(impl) + graphs(spec)`. This also shows the counter is live and the
///   tool adds nothing to it.
/// - **Implementation over** (`(1,3)`): every graph of that program has `d` at
///   3, so the first graph scored is over the cap. The result is `OverCap` with
///   the counter at **0**, although the same program uncapped enumerates at
///   least one graph.
/// - **Specification only over**: the implementation is scored first and
///   fully enumerated, then the specification's first graph is refused. So
///   the count is **exactly** `graphs(impl)`: graphs scored before the refusal
///   are counted, and the refused graph is not.
///
/// This replaces a 30-second wall-clock test (`P3-gate4-fixes` round 2, m1).
/// That test depended on an unrun, extrapolated cost, and it left a worker
/// running when it failed. It added nothing this test does not show
/// deterministically, so it was removed rather than kept.
///
/// **Mutations, MEASURED at the round-2 response** (production file restored
/// and md5-verified after each):
/// - cap check moved after `extend` (round 1's N2) — fails on `the over-cap
///   graph was refused before its enumeration started`. This is the only
///   test that catches it;
/// - counter increment moved before the cap check — fails on the same message;
/// - counter increment deleted — fails on `each side enumerates at least one
///   graph uncapped; got 0, 0`;
/// - cap check removed, `Pair::compare` passing `None`, the cap checking only
///   the first thread, or `compare_capped` dropping the cap — each fails on
///   `expected OverCap; got Ok(BothClean)`;
/// - specification enumerated uncapped — fails on `expected OverCap; got
///   Ok(BothFail { .. })`;
/// - `>=` for `>` — fails on `at the bound the pair is scored; got
///   Err(Oracle(OverCap { .. }))`.
///
/// **Not distinguishable, and why**: moving the increment from just before
/// `extend` to just after it changes no count. `extend` always returns, and a
/// refused graph reaches neither point. What the test can observe is where the
/// increment sits relative to the **cap check**, and that is pinned by the
/// "moved before the cap check" mutation above.
#[test]
fn an_over_cap_graph_is_refused_before_its_enumeration_starts() {
    use crate::conformance::differential::DiffError;
    use crate::conformance::generator::MAX_VISIBLE_EVENTS_PER_THREAD as CAP;
    use crate::conformance::oracle::{take_enumerations_started, vis_of_program, OracleError};
    use std::sync::Arc;

    // Graphs of one side, as the uncapped oracle enumerates them.
    let graphs_of = |p: &Pair, side: &Arc<dyn Fn() + Send + Sync>| {
        let f = side.clone();
        let _ = take_enumerations_started();
        vis_of_program(p.config.clone(), &p.visible, move || f())
            .unwrap_or_else(|e| panic!("the uncapped oracle enumerates this side: {e:?}"));
        take_enumerations_started()
    };
    let is_over_cap = |r: &Result<Agreement, DiffError>| {
        matches!(r, Err(DiffError::Oracle(OracleError::OverCap { .. })))
    };

    // At the bound.
    let at = two_chain_pair(CAP, CAP);
    let (gi, gs) = (
        graphs_of(&at, &at.implementation),
        graphs_of(&at, &at.specification),
    );
    assert!(
        gi >= 1 && gs >= 1,
        "each side enumerates at least one graph uncapped; got {gi}, {gs}"
    );
    let _ = take_enumerations_started();
    let r = at.compare(None);
    assert!(r.is_ok(), "at the bound the pair is scored; got {r:?}");
    assert_eq!(
        take_enumerations_started(),
        gi + gs,
        "at the bound, Pair::compare enumerates every graph of both sides, once each"
    );

    // The implementation over the cap.
    let over = two_chain_pair(1, CAP + 1);
    let g_over = graphs_of(&over, &over.implementation);
    assert!(
        g_over >= 1,
        "uncapped, this program's graphs are enumerated, so the counter is live on it"
    );
    let _ = take_enumerations_started();
    let r = over.compare(None);
    assert!(is_over_cap(&r), "expected OverCap; got {r:?}");
    assert_eq!(
        take_enumerations_started(),
        0,
        "the over-cap graph was refused before its enumeration started"
    );

    // Only the specification over the cap.
    let mut spec_over = two_chain_pair(1, 1);
    spec_over.specification = Arc::new(|| {
        receive_chain("c", "s", 1);
        receive_chain("d", "t", CAP + 2);
    });
    let gi = graphs_of(&spec_over, &spec_over.implementation);
    let _ = take_enumerations_started();
    let r = spec_over.compare(None);
    assert!(is_over_cap(&r), "expected OverCap; got {r:?}");
    assert_eq!(
        take_enumerations_started(),
        gi,
        "exactly the implementation's {gi} graph(s) were enumerated before the \
         specification's first graph was refused"
    );
}

/// **`check_declaration` refuses a bad declaration on either side, and
/// accepts a correct one and one exactly at the bound.**
///
/// `pair()` calls `generator::check_declaration` on every shape's declaration.
/// Before the round-2 follow-up those checks were inline in `pair()`, and no
/// test could feed them a bad declaration. Here each refusal is driven
/// directly, and the panic **message** is asserted, not just that something
/// panicked:
/// - an entry over `MAX_VISIBLE_EVENTS_PER_THREAD`;
/// - a declaration missing a visible thread;
/// - a declaration naming a thread that is not visible.
///
/// Each is placed on the implementation side and, separately, on the
/// specification side. The other side is always correct, so a check that
/// looked at one side only would pass half the cases. Acceptance is asserted
/// for the correct declaration and for one where **every** entry equals the
/// bound, which separates `<=` from `<`.
///
/// **Mutations, MEASURED at the round-2 follow-up** (`generator.rs`, restored
/// and md5-verified after each; each fails **only this test**):
/// - bound assertion deleted — `over, implementation: check_declaration
///   accepted it`;
/// - name assertion deleted — `missing, implementation: check_declaration
///   accepted it`;
/// - `<=` changed to `<` — `every entry exactly at the bound is accepted`;
/// - only the implementation side checked — `over, specification:
///   check_declaration accepted it`.
///
/// **Not caught here: `pair()` no longer calling `check_declaration`.** With
/// every shipped declaration correct, the call has no observable effect. A bad
/// declaration would still be caught by
/// [`every_shapes_declared_observations_equal_the_measured_counts`], as it was
/// with the assertions deleted in the round-2 response.
#[test]
fn check_declaration_refuses_bad_declarations_on_either_side_and_accepts_the_bound() {
    use crate::conformance::generator::{
        check_declaration, DeclaredObservations, MAX_VISIBLE_EVENTS_PER_THREAD as CAP,
    };
    use std::panic::{catch_unwind, AssertUnwindSafe};

    const OK: &[(&str, usize)] = &[("p", 1), ("c", 1)];
    const AT_BOUND: &[(&str, usize)] = &[("p", CAP), ("c", CAP)];
    const OVER: &[(&str, usize)] = &[("p", 1), ("c", CAP + 1)];
    const MISSING: &[(&str, usize)] = &[("p", 1)];
    const EXTRA: &[(&str, usize)] = &[("p", 1), ("c", 1), ("x", 1)];

    let visible = vec!["p".to_string(), "c".to_string()];
    let run = |implementation, specification| {
        catch_unwind(AssertUnwindSafe(|| {
            check_declaration(
                Mode::DecoupleImpl,
                &visible,
                DeclaredObservations {
                    implementation,
                    specification,
                },
            )
        }))
        .err()
        .map(|e| {
            e.downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "<non-string panic payload>".to_owned())
        })
    };

    // Accepted.
    assert_eq!(run(OK, OK), None, "a correct declaration is accepted");
    assert_eq!(
        run(AT_BOUND, AT_BOUND),
        None,
        "every entry exactly at the bound is accepted"
    );

    let over = |side: &str| {
        format!(
            "declares {} visible observations for `c` in its {side}, over \
             MAX_VISIBLE_EVENTS_PER_THREAD ({CAP})",
            CAP + 1
        )
    };
    let names = |side: &str, got: &str| {
        format!(
            "DecoupleImpl's {side} declaration names {got} but the pair's visible threads \
             are [\"c\", \"p\"]"
        )
    };
    let cases = [
        (
            "over, implementation",
            run(OVER, OK),
            over("implementation"),
        ),
        ("over, specification", run(OK, OVER), over("specification")),
        (
            "missing, implementation",
            run(MISSING, OK),
            names("implementation", "[\"p\"]"),
        ),
        (
            "missing, specification",
            run(OK, MISSING),
            names("specification", "[\"p\"]"),
        ),
        (
            "extra, implementation",
            run(EXTRA, OK),
            names("implementation", "[\"c\", \"p\", \"x\"]"),
        ),
        (
            "extra, specification",
            run(OK, EXTRA),
            names("specification", "[\"c\", \"p\", \"x\"]"),
        ),
    ];
    for (what, got, want) in cases {
        let msg = got.unwrap_or_else(|| panic!("{what}: check_declaration accepted it"));
        assert!(
            msg.contains(&want),
            "{what}: refused, but with the wrong message.\n  want substring: {want}\n  got: {msg}"
        );
    }
}

/// **Every shape's declared observation counts equal the measured ones, per
/// side, under every model.**
///
/// `Mode::declared_observations` is the construction-time bound
/// (`P3-gate4-fixes` round 2, M1). `pair()` asserts it is within
/// `MAX_VISIBLE_EVENTS_PER_THREAD`, but a declaration is written by hand and
/// nothing in `pair()` can check that it is **true**. This test does, and it
/// requires **equality**:
/// - an under-declaration would defeat the bound;
/// - an over-declaration would hide slack and let a shape drift silently.
///
/// "Measured" means: for each side, the most elements carrying each visible
/// name in any word of the **uncapped** oracle's `vis`. The test does not use
/// the cap it backs.
///
/// **Seeds.** One seed per mode is not enough: `pair()`'s seed picks the
/// **model** (`rng.pick(models())`) as well as the value (`rng.val()`, 1 to 5),
/// and those two draws are all the seed decides. So a mode has exactly 15
/// distinct pairs, and this test checks **all 15**. It scans seeds `0..512`,
/// keeps one seed per new (model, implementation word set) combination, and
/// asserts it found 5 distinct word sets under each of the 3 models. The word
/// set stands in for the value, which `Pair` does not expose. If some shape's
/// words did not carry the value, coverage would come up short and the
/// assertion would fail loudly, rather than the test quietly checking less.
///
/// **Mutations, MEASURED at the round-2 response** (`generator.rs`, restored
/// and md5-verified after each):
/// - `DecoupleImpl` and its siblings declare `c` as **2** (still within the
///   bound, so `pair()` accepts it) — fails **only this test**, on
///   `DecoupleImpl seed=0x0 (Bag): the implementation's measured per-thread
///   observation maxima differ from its declaration`;
/// - `pair()`'s bound assertion deleted **and** `c` declared as 3 — fails only
///   this test, with the same message. Without the deletion, the same
///   declaration panics in `pair()` (9 tests fail on `declares 3 visible
///   observations for \`c\` … over MAX_VISIBLE_EVENTS_PER_THREAD`);
/// - `pair()`'s name-equality assertion deleted **and** `c` left undeclared —
///   fails only this test, with the same message. Without the deletion,
///   `pair()` panics (9 tests fail on `declaration names ["p"] but the pair's
///   visible threads are ["c", "p"]`).
///
/// So each construction check has a measured failing direction, and the test
/// catches the same bad declaration when that check is removed. Deleting
/// either check while **every** declaration is correct fails nothing
/// (26/0). That is expected: the checks only fire on a bad declaration, and
/// `Mode::declared_observations` is a fixed `match` that a test cannot feed
/// one. See the round-2 response in `log/dev/P3-F59.report.md` for the hook
/// that would allow it.
#[test]
fn every_shapes_declared_observations_equal_the_measured_counts() {
    use crate::conformance::oracle::vis_of_program;
    use std::collections::BTreeSet;

    let measure = |p: &Pair, side: &std::sync::Arc<dyn Fn() + Send + Sync>| {
        let f = side.clone();
        let set = vis_of_program(p.config.clone(), &p.visible, move || f())
            .unwrap_or_else(|e| panic!("{:?} seed={:#x}: {e:?}", p.mode, p.seed));
        let mut worst: BTreeMap<String, usize> = p.visible.iter().map(|n| (n.clone(), 0)).collect();
        for w in set.iter() {
            for name in &p.visible {
                let c = w.word.iter().filter(|e| &e.thread == name).count();
                let slot = worst.get_mut(name).expect("a visible name");
                *slot = (*slot).max(c);
            }
        }
        worst
    };
    let as_map = |entries: &[(&str, usize)]| -> BTreeMap<String, usize> {
        entries.iter().map(|(n, c)| (n.to_string(), *c)).collect()
    };

    for m in Mode::all() {
        let declared = m.declared_observations();
        // (model, value) pairs seen so far, and per model the distinct values.
        let mut seen: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut used = 0;
        for seed in 0..512u64 {
            let covered = seen.len() == 3 && seen.values().all(|v| v.len() == 5);
            if covered {
                break;
            }
            let p = pair(*m, seed);
            let model = format!("{:?}", p.config.cons_type);
            // The value is not exposed on `Pair`; the implementation's words
            // carry it, so the word set's rendering stands in for it.
            let words = {
                let f = p.implementation.clone();
                let set = vis_of_program(p.config.clone(), &p.visible, move || f())
                    .unwrap_or_else(|e| panic!("{m:?} seed={seed:#x}: {e:?}"));
                format!("{:?}", set.iter().collect::<Vec<_>>())
            };
            if seen.get(&model).is_some_and(|v| v.contains(&words)) {
                continue;
            }
            seen.entry(model.clone()).or_default().insert(words);
            used += 1;

            for (side, program, entries) in [
                ("implementation", &p.implementation, declared.implementation),
                ("specification", &p.specification, declared.specification),
            ] {
                assert_eq!(
                    measure(&p, program),
                    as_map(entries),
                    "{m:?} seed={seed:#x} ({model}): the {side}'s measured per-thread \
                     observation maxima differ from its declaration"
                );
            }
        }
        assert!(
            seen.len() == 3 && seen.values().all(|v| v.len() == 5),
            "{m:?}: seeds 0..512 did not cover all 15 (model, value) pairs ({used} used): \
             {seen:?}"
        );
        assert_eq!(used, 15, "{m:?}: one seed per distinct pair");
    }
}

/// A visible thread `name` that receives `k` messages, all from its own
/// invisible sender `sender`, which sends `1..=k` in order.
fn receive_chain(name: &'static str, sender: &'static str, k: usize) {
    use crate::{recv_msg_block, send_msg};
    let r = named_thread(name, move || {
        for _ in 0..k {
            let _v: i32 = recv_msg_block();
        }
    });
    let rid = r.thread().id();
    let _s = named_thread(sender, move || {
        for v in 1..=k {
            send_msg(rid, v as i32);
        }
    });
}

/// A hand-built `Pair`: visible `c` and `d` receive `kc` and `kd` messages
/// from independent invisible senders, so no `vo` edge joins `c`'s
/// observations to `d`'s. Implementation and specification are the same
/// program. Under FIFO.
fn two_chain_pair(kc: usize, kd: usize) -> Pair {
    use std::sync::Arc;
    let prog = Arc::new(move || {
        receive_chain("c", "s", kc);
        receive_chain("d", "t", kd);
    }) as Arc<dyn Fn() + Send + Sync>;
    Pair {
        mode: Mode::Identity,
        seed: 0,
        visible: vec!["c".to_string(), "d".to_string()],
        config: crate::Config::builder()
            .with_cons_type(crate::ConsType::FIFO)
            .build(),
        implementation: prog.clone(),
        specification: prog,
        expect_inclusion: true,
    }
}
