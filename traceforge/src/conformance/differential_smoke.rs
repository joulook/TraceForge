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

use crate::conformance::differential::{compare, Agreement, FalseAlarmFigure, Tally};
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

fn run(p: &Pair) -> Result<Agreement, crate::conformance::differential::DiffError> {
    let impl_ = {
        let a = p.implementation.clone();
        move || a()
    };
    let spec = {
        let a = p.specification.clone();
        move || a()
    };
    compare(p.config.clone(), &p.visible, impl_, spec)
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
        let got = crate::conformance::oracle::includes(p.config.clone(), &p.visible, impl_, spec)
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
            t.add_capable(&Agreement::BothFail { witness: witness() }, pred(*m));
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
    t.add_capable(&Agreement::FalseAlarm { reports: 1 }, false);
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
    t2.add_capable(&Agreement::BothFail { witness: witness() }, true);
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
    t.add_capable(&Agreement::BothFail { witness: witness() }, false);
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
/// **Reachability, measured and recorded**: `Agreement::of`'s `Inconclusive`
/// arm is **not reachable through `compare`** on any pair this generator emits.
/// `compare` builds its own `ConfBuilder` with the default
/// `DEFAULT_SEARCH_BUDGET = 10_000` and exposes no budget knob, and the
/// generator's micro-programs cannot exhaust that. So the arm is exercised
/// here only at the `verify` level and at `Tally` level, never end to end.
/// Recorded rather than worked around: the harness's own type is what would
/// have to change.
///
/// **Mutation, MEASURED**: make `ConfVerdict::of` return
/// `Conforms(Certificate { outcome })` whenever `outcome.reports` is empty,
/// dropping the `not_a_certificate()` test. Applied at gate 3; this test fails
/// with `a one-node inner budget must not yield a certificate`.
///
/// **Mutation, REFUTED**: "in `Agreement::of`, map `ConfVerdict::Inconclusive`
/// to `BothClean`". Applied at gate 3: the full lib suite stayed green at
/// **359 passed / 0 failed** — the arm is unreachable, per the paragraph above,
/// so nothing in the tree observes it.
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
