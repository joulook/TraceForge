//! Adversarial hardening pass over S5.
//!
//! **S5's production code and its tests were written by the same agent.** §12
//! assigned the step that way, which collapsed gates 2 and 3 of the owner's
//! four-gate rule and left the reviewer as the only independent look. The
//! owner ruled on 2026-09-16 that the rule wins, and that the separation is
//! symmetric: *whoever did not write the code writes the tests*.
//!
//! Method, for every test in this file: **the mutation comes first**. Each
//! test's "what would break it" clause names a change to the production code;
//! that change was applied to this tree, the test was run, the failing list was
//! recorded, and the tree was restored. A clause nothing demonstrates is a
//! clause that is wrong. The exact mutations and their verbatim results are in
//! `plan/traceForge/log/dev/P3-S5-harden-dev.report.md`.
//!
//! **Where the first two attempts went blind, and why, is worth keeping in
//! view.** Two of the three blind tests had one cause: a fixture whose report
//! is raised at a *mid-search* gate can only ever exhibit (M1). At such a gate
//! `outer.complete` is false, so `Recompute::done` is just `matches`; the
//! recomputation is reached only after the traversal answered `NoCover`, so no
//! visited attempt matched; `best.graph` satisfies `follows` by construction,
//! hence satisfies (M2); so it fails `observations_match`, and `obligation()`'s
//! (M1) block — which is exactly `!observations_match` — returns before (M2)
//! or (M3) is read. Every fixture in the first two versions of this file
//! reported at a mid-search gate, so neither the (M2) loop nor the second half
//! of `Recompute::done` was ever executed. Reaching them requires a
//! **completion-gate** report, which is why the fixtures below are built to
//! produce one.
//!
//! The third cause was a fixture too thin to be wrong about: one visible
//! thread with one visible event gives a single matched pair, the diagonal is
//! excluded, and (M2) is vacuous. Two visible threads with an order between
//! them on one side only is the smallest fixture (M2) can fail on.

#![cfg(test)]

use crate::conformance::diagnose::{self, Recompute};
use crate::conformance::obs::wobs;
use crate::conformance::report::{
    ConfVerdict, Diagnostics, Obligation, ReportCause, UnavailableKind,
};
use crate::conformance::testing::{names, run_once};
use crate::conformance::{verify, ConfBuilder};
use crate::thread::{self, main_thread_id, ThreadId};
use crate::{ConsType, Config};

fn base(visible: &[&str]) -> ConfBuilder {
    ConfBuilder::new()
        .visible_threads(visible.to_vec())
        .cons_type(ConsType::FIFO)
}

fn named<F>(name: &str, f: F) -> ThreadId
where
    F: FnOnce() + Send + 'static,
{
    thread::Builder::new()
        .name(name.to_owned())
        .spawn(f)
        .unwrap()
        .thread()
        .id()
}

/// The one report of a pair that must report exactly once.
fn sole_report(name: &str, imp: fn(), spec: fn(), visible: &[&str]) -> Diagnostics {
    let out = verify(
        base(visible).search_budget(4096).build().expect("in-scope config"),
        imp,
        spec,
    )
    .unwrap_or_else(|e| panic!("{name}: the run itself must not fail: {e}"));

    let ConfVerdict::Reported(o) = out else {
        panic!("{name}: this pair must report, or the test proves nothing");
    };
    assert_eq!(
        o.reports().len(),
        1,
        "{name}: expected exactly one report, got {:?}",
        o.reports().iter().map(|r| r.gate()).collect::<Vec<_>>()
    );
    o.reports()[0].diagnostics().clone()
}

/// The same pair's **rendered report** — what the user actually reads.
///
/// `sole_report` hands back the `Diagnostics` value; this hands back
/// `ConfReport`'s own `Display`, which embeds it. A claim about a *sentence*
/// has to be checked here: a negative assertion over the whole rendering is
/// what rules out the false sentence appearing somewhere else in the report.
fn sole_report_text(name: &str, imp: fn(), spec: fn(), visible: &[&str]) -> String {
    let out = verify(
        base(visible).search_budget(4096).build().expect("in-scope config"),
        imp,
        spec,
    )
    .unwrap_or_else(|e| panic!("{name}: the run itself must not fail: {e}"));

    let ConfVerdict::Reported(o) = out else {
        panic!("{name}: this pair must report, or the test proves nothing");
    };
    assert_eq!(o.reports().len(), 1, "{name}: expected exactly one report");
    o.reports()[0].to_string()
}

// ---------------------------------------------------------------------------
// H1 — `Obligation::MissingPullBack` is unreachable, not merely untested
// ---------------------------------------------------------------------------

/// **Finding H-1.** S5's report marks P9.5b **open** — "(M2) missing pull-back
/// edge: the variant exists and renders, and no test in this step produces
/// one". The reason is that **no such pair exists**; the variant is dead code.
///
/// Two steps, both in the source:
///
/// 1. `Recompute::visit` calls `best.offer(..)` **only inside**
///    `if follows(probed.graph(), outer.graph, ..)`, and `obligation()`'s only
///    caller feeds it `best.graph`. So every graph reaching `obligation()`
///    satisfied `follows` against the same `outer`.
/// 2. `follows` is `observations_follow && order_is_reflected`, and
///    `order_is_reflected` rejects exactly the pairs `obligation()`'s (M2)
///    loop searches for — same pair set, same predicate, same diagonal
///    exclusion.
///
/// **What this test has to do to be able to see (M2) at all.** The two earlier
/// versions could not: every fixture they used reported at a *mid-search*
/// gate, where (M1) always fires first (see this module's header), so the (M2)
/// loop was never executed and both mutations of it left the test green. This
/// fixture is built backwards from that constraint:
///
/// - it reports at a **completion** gate, so (M3) — and therefore (M2) before
///   it — is reached;
/// - its best attempt **clears (M1)**, pinned below by asserting the exact
///   obligation, which `obligation()` can only return after the (M2) loop has
///   run to completion and found nothing;
/// - it has **two** matched pairs, not one, so the loop's off-diagonal is
///   non-empty;
/// - the implementation orders `a`'s send before `b`'s receive (`b` reads it)
///   while the specification leaves them concurrent (`b` reads `main`'s send
///   instead, and a send does not observe its destination). That is the one
///   shape a (M2) check can be wrong about: `order_is_reflected` permits the
///   implementation to be *more* ordered than the specification, and a
///   predicate written the other way round accepts everything easy and rejects
///   this.
///
/// The premise is asserted on the graphs themselves rather than assumed, so a
/// later edit to either program that flattens the difference fails here instead
/// of silently emptying the test. (`adversarial::
/// m2_is_directional_on_an_executed_witness` pins the same two program shapes
/// against `morphism::order_is_reflected` directly; what is new here is driving
/// them through `verify` into `obligation()`'s own (M2) loop, which that test
/// cannot reach.)
///
/// What would break it: reversing `obligation()`'s (M2) predicate to
/// `imp_ordered && !spec_ordered`, or dropping its `se1 != se2` diagonal
/// exclusion. **Both demonstrated.** The reversal fails this test and **nothing
/// else in the crate** — it is the mutation two earlier versions of this file
/// left green. The dropped diagonal fails this test and H-2.
#[test]
fn h1_no_report_ever_carries_the_missing_pull_back_obligation() {
    // The premise, on the graphs: the implementation orders two visible events
    // the specification leaves concurrent.
    let vis = names(&["a", "b"]);
    let ordered = run_once(Config::builder().build(), imp_a_feeds_b);
    let concurrent = run_once(Config::builder().build(), spec_a_and_b_unrelated_and_b_blocks);
    for (what, g) in [("implementation", &ordered), ("specification", &concurrent)] {
        let w = wobs(g, &vis).unwrap();
        assert_eq!(w.of("a").len(), 1, "{what}: `a` must observe one send");
        assert_eq!(w.of("b").len(), 1, "{what}: `b` must observe one receive");
    }
    let edge = |g: &crate::exec_graph::ExecutionGraph| {
        let w = wobs(g, &vis).unwrap();
        g.in_porf(w.of("a")[0].0, w.of("b")[0].0)
    };
    assert!(
        edge(&ordered),
        "the implementation must order a's send before b's receive, or the (M2) \
         loop has nothing to be wrong about"
    );
    assert!(
        !edge(&concurrent),
        "the specification must leave them concurrent, or the difference this \
         test turns on does not exist"
    );

    // The consequence, end to end. `StatusMismatch` is returned only after the
    // (M2) loop has run over both matched pairs and found nothing: the (M1)
    // block precedes it and did not fire, and the (M3) block follows it.
    let d = sole_report(
        "m2-reached",
        imp_a_feeds_b,
        spec_a_and_b_unrelated_and_b_blocks,
        &["a", "b"],
    );
    let Diagnostics::Available { prefix, obligation } = &d else {
        panic!("the recomputation must reproduce the search's answer here: {d:?}");
    };
    assert_eq!(
        prefix,
        &vec![("a".to_owned(), 1usize), ("b".to_owned(), 1usize)],
        "the best attempt must be the full one, or (M1) is what failed"
    );
    assert_eq!(
        *obligation,
        Obligation::StatusMismatch {
            thread: "b".to_owned(),
            spec: "blocked".to_owned(),
            imp: "done".to_owned(),
        },
        "a (M2) obligation here means `obligation()`'s (M2) loop has drifted \
         from `morphism::order_is_reflected` — and therefore that \
         `MissingPullBack` is *not* dead code and H-1 is wrong"
    );
}

// ---------------------------------------------------------------------------
// H2 — what the completion gate's diagnostic actually says
// ---------------------------------------------------------------------------

/// **Correction, kept from round 4.** The first version of this test claimed to
/// reach `Obligation::NoOfferablePassedPhi` and was named for it. It does not:
/// the fixture yields `StatusMismatch { spec: "blocked", imp: "done" }`,
/// because at a completion gate `outer.complete` is true, so `obligation()`'s
/// (M3) block runs — and a specification thread that cannot *stop* is exactly a
/// status difference. (M3) claims the case before the fallthrough can.
///
/// **So P9.5d stays open and F-8's second half is untouched.** No fixture
/// reaching the fallthrough has been constructed by anyone on this topic.
///
/// What the fixture does establish, and nothing else asserts: the (M3) branch
/// is reached on a *single* matched pair and names both sides. H1 reaches (M3)
/// too, but only through a two-pair fixture; this is the minimal one.
///
/// What would break it: removing `obligation()`'s (M3) block, or dropping
/// `Recompute::done`'s `statuses_agree` conjunct. Both **demonstrated** — the
/// first fails this test, `h1`, `h4` and `s5_tests::c14_ex_blocking_…` at
/// 297/4; the second fails this test, `h1`, `h4` and two more.
///
/// *(Corrected for the B1 fix, F-B1c. Until this pass the clause said the (M3)
/// mutation "turns this into the `NoOfferablePassedPhi` fallthrough". Post-fix
/// it does not: the fallthrough now checks its own claim, finds an offer that
/// passes Φ, and declines. Re-measured on the fixed tree, this test's panic is
/// verbatim*
///
/// ```text
/// expected available diagnostics; got Unavailable { because: "the morphism
/// holds on the furthest-following attempt and no extension of it covers,
/// which §7.1's obligation list has no value for; see F-7", kind:
/// NoValueForIt }
/// ```
///
/// *— so the test still discriminates and nothing was blocked, but the
/// consequence the clause named was wrong. The test was right and the clause
/// was corrected, which is the direction this file's method requires.)*
///
/// The round-4 version of this clause also named "`done` dropping its emptiness
/// conjunct". That mutation is **inert**: the line after it,
/// `probed.complete()`, tests the same offer set, so removing
/// `if !probed.offers().is_empty()` from `Recompute::done` changes no answer.
/// Measured — all 293 conformance tests pass under it. No test can be written
/// that fails on it, and the clause has been corrected rather than the test.
#[test]
fn h2_a_specification_that_cannot_stop_is_diagnosed_as_a_status_mismatch() {
    let d = sole_report(
        "cannot-stop",
        imp_one_receive,
        spec_one_receive_then_blocks,
        &["a"],
    );
    let Diagnostics::Available { obligation, .. } = &d else {
        panic!("expected available diagnostics; got {d:?}");
    };
    assert_eq!(
        *obligation,
        Obligation::StatusMismatch {
            thread: "a".to_owned(),
            spec: "blocked".to_owned(),
            imp: "done".to_owned(),
        }
    );
}

// ---------------------------------------------------------------------------
// H3 — a certificate is still reachable
// ---------------------------------------------------------------------------

/// Criterion 2 and blocked item B. S5 tests the three ways to *lose* a
/// certificate; this checks the conjunction still admits one.
///
/// *(The pass originally filed this as covering a gap in S5's suite. That was
/// wrong — `c1_a_certificate_names_its_assumptions` already asserts a
/// certificate is produced, and four existing tests fail when certification is
/// disabled. Kept as a cheap anchor on the reflexive case; the non-reflexive
/// case, which nothing else covers, is H-6.)*
///
/// What would break it: `ConfVerdict::of` never certifying. **Demonstrated** —
/// disabling its `Conforms` branch fails this test, along with four in
/// `s5_tests.rs` and H-6.
#[test]
fn h3_a_genuinely_clean_run_still_yields_a_certificate() {
    let out = verify(
        base(&["a"]).search_budget(4096).build().expect("in-scope config"),
        imp_one_receive,
        imp_one_receive,
    );

    match out.expect("an identical pair must not error") {
        ConfVerdict::Conforms(_) => {}
        other => panic!("a program compared against itself must certify; got {other}"),
    }
}

// ---------------------------------------------------------------------------
// H4 — the recomputation agrees with the search it is describing
// ---------------------------------------------------------------------------

/// Ruling (e): the diagnostics are recomputed outside the search, and a
/// recomputation can disagree with what the search did. `diagnose` answers
/// `Unavailable` when it does, which is the right refusal and a silent loss of
/// the diagnostic. This pins that it does **not** happen on ordinary reports.
///
/// **Two fixtures, and each is needed for a different mutation** — which is the
/// thing the two earlier versions of this test got wrong. `Recompute::done`
/// has two halves and a mid-search gate reaches only the first:
///
/// - the mid-search-gate pair reaches `matches` and stops there
///   (`if !outer.complete { return Ok(true) }`), so it sees a `done` that
///   accepts a merely *following* attempt;
/// - the completion-gate pair runs on past that line, so it sees a `done` that
///   has stopped consulting `statuses_agree`.
///
/// A single fixture of either kind is blind to the other half.
///
/// What would break it: `Recompute::done` accepting `follows` where it requires
/// `matches`, or dropping its `statuses_agree` conjunct — either makes the
/// recomputation answer `Found` where the search answered ⊥, and the
/// diagnostics go `Unavailable`. **Both demonstrated**, and each is caught by
/// one fixture only: `follows` for `matches` by the mid-search pair,
/// `statuses_agree` by the completion pair.
///
/// The mutation the round-4 version named — dropping `done`'s
/// `!probed.offers().is_empty()` conjunct — is **inert in this module**:
/// `Probed::complete()`, which the next line calls, tests the same offer set,
/// so the two guards answer alike. Measured: all 293 conformance tests pass
/// under it. It is an equivalent mutant, not a gap, and no test that survives
/// it is thereby shown to be blind.
#[test]
fn h4_on_a_real_report_the_recomputation_reproduces_the_searchs_answer() {
    // A mid-search gate: `done` is `matches` and nothing else.
    let d = sole_report("extra-send", imp_two_receives, spec_one_receive, &["a"]);
    assert!(
        matches!(d, Diagnostics::Available { .. }),
        "mid-search gate: the recomputation disagreed with the search on a \
         report the search produced, with an ample budget: {d:?}"
    );

    // A completion gate: `done` runs its whole conjunction.
    let d = sole_report(
        "cannot-stop",
        imp_one_receive,
        spec_one_receive_then_blocks,
        &["a"],
    );
    assert!(
        matches!(d, Diagnostics::Available { .. }),
        "completion gate: the recomputation disagreed with the search on a \
         report the search produced, with an ample budget: {d:?}"
    );
}

// ---------------------------------------------------------------------------
// H6 — the gap that is real: certifying a pair that is not reflexive
// ---------------------------------------------------------------------------

/// **The one genuine hole this pass found**, and it was the reviewer who named
/// it. Every other test on this tree that produces a `Conforms` verdict —
/// `c1_a_certificate_names_its_assumptions`, `c11_…`, `c2_…`, `c5_…` and H-3 —
/// verifies a program **against itself**. On a reflexive pair the two graphs
/// are isomorphic, so `matches`, `order_is_reflected` and `statuses_agree` are
/// trivially satisfied: (M2) in particular is satisfied by *equality* of the
/// two orders, which is the one thing it must not require.
///
/// So the fixture is non-reflexive in all three of the directions the morphism
/// is supposed to tolerate, at once:
///
/// - **order** — the implementation orders `a`'s send before `b`'s receive;
///   the specification leaves them concurrent. (M2) runs from the
///   specification *back* to the implementation, so a more ordered
///   implementation conforms;
/// - **destination** — `a` sends to `b` in the implementation and to `main` in
///   the specification, which a send does not observe (CA §4, the relay
///   example);
/// - **behaviour** — the specification's `a` sends `1` *or* `2` under
///   `nondet()`, so it admits strictly more executions than the implementation
///   and the search has to find the branch that matches.
///
/// The first of those is what the round-4 version lacked: with one visible
/// thread and one visible event per side it had a single matched pair, the
/// diagonal was excluded, and (M2) was vacuous — so no tightening of (M2) could
/// be seen. That is why changing `Recompute::phi`'s `follows` to `matches` left
/// it green: on a conforming pair no report is raised, `Recompute` is never
/// asked for a diagnostic, and the mutation is invisible to a certificate test
/// however it is written.
///
/// What would break it, both **demonstrated**:
///
/// - (M2) read as an isomorphism — `vo(spec) != vo(imp)` in place of
///   `vo(spec) && !vo(imp)` in `morphism::order_is_reflected`. Seven tests
///   fail; six are unit-level (M2) assertions in `morphism` and `adversarial`,
///   and this is the only one that fails as a **lost certificate**, which is
///   the direction an over-strict comparison actually harms a user in.
/// - the search taking only the first value of a nondet offer —
///   `search::Search::branch`'s `CToss`/`Choice` arm restricted to
///   `values.into_iter().take(1)`, so the specification's extra behaviour is
///   never explored. Four tests fail, three of them `search`'s own; this is
///   the only one outside that module.
#[test]
fn h6_a_specification_strictly_more_permissive_than_the_implementation_certifies() {
    let out = verify(
        base(&["a", "b"])
            .search_budget(4096)
            .build()
            .expect("in-scope config"),
        imp_a_feeds_b,
        spec_a_and_b_unrelated_nondet,
    );

    match out.expect("this pair must not error") {
        ConfVerdict::Conforms(_) => {}
        other => panic!(
            "a specification admitting strictly more behaviour, and strictly \
             less order, than the implementation must certify it; got {other}"
        ),
    }
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn imp_one_receive() {
    named("a", || crate::send_msg(main_thread_id(), 1u64));
    let _: u64 = crate::recv_msg_block();
}

fn imp_two_receives() {
    named("a", || {
        crate::send_msg(main_thread_id(), 1u64);
        crate::send_msg(main_thread_id(), 2u64);
    });
    let _: u64 = crate::recv_msg_block();
    let _: u64 = crate::recv_msg_block();
}

fn spec_one_receive() {
    named("a", || crate::send_msg(main_thread_id(), 1u64));
    let _: u64 = crate::recv_msg_block();
}

fn spec_one_receive_then_blocks() {
    named("a", || {
        crate::send_msg(main_thread_id(), 1u64);
        let _: u64 = crate::recv_msg_block();
    });
    let _: u64 = crate::recv_msg_block();
}

/// `a` sends straight to `b`, so `a`'s send is `vo`-before `b`'s receive.
///
/// Both declared visible threads are spawned before either program
/// communicates, which §8's spawn-order guard requires — ordering them by a
/// `join` instead would be refused as `SpawnedLate`.
fn imp_a_feeds_b() {
    let bid = named("b", || {
        let _: u64 = crate::recv_msg_block();
    });
    named("a", move || crate::send_msg(bid, 1u64));
}

/// The same two observations with no order between them: `b` reads `main`'s
/// send, and `a` sends the same value somewhere else. `b` then waits for a
/// second message that never comes, so it ends **blocked** where the
/// implementation's `b` ends **done** — the only difference (M1) and (M2)
/// cannot see, and the reason this pair reports at all.
fn spec_a_and_b_unrelated_and_b_blocks() {
    let bid = named("b", || {
        let _: u64 = crate::recv_msg_block();
        let _: u64 = crate::recv_msg_block();
    });
    named("a", || crate::send_msg(main_thread_id(), 1u64));
    crate::send_msg(bid, 1u64);
}

/// The conforming version of the same shape: `b` stops after one message, so
/// the statuses agree and the pair certifies — with the specification strictly
/// less ordered and strictly more permissive than the implementation.
fn spec_a_and_b_unrelated_nondet() {
    let bid = named("b", || {
        let _: u64 = crate::recv_msg_block();
    });
    named("a", || {
        let v = if crate::nondet() { 1u64 } else { 2u64 };
        crate::send_msg(main_thread_id(), v);
    });
    crate::send_msg(bid, 1u64);
}

// ===========================================================================
// B1 — §7.1's fourth value, now that the fallthrough checks its own claim
//
// Round-5 review, finding B1: `Recompute::obligation` emitted
// `Obligation::NoOfferablePassedPhi` unconditionally at the fallthrough, and the
// reviewer's eleven-line fixture showed the sentence it renders — "no offerable
// specification event passed Φ, so the search had nowhere left to go from this
// attempt" — to be **false** where it fired. The lead's fix (owner-ruled option
// (i)) re-probes the attempt and emits the value only when no offer passes Φ,
// returning `None` otherwise, which `diagnose` renders as `Unavailable`. (As of
// the B1b fix, that is `Unavailable { kind: NoValueForIt, .. }`; see the next
// section for why the kind had to exist.)
//
// So the value is now a **conditional**, and a conditional needs both cases
// pinned or half of it is untested. H-7 is the case where the condition is
// false, H-8 the case where it is true. Neither alone establishes the fix: H-8
// passes on the pre-fix tree unchanged, and H-7 passes on a tree that returns
// `None` unconditionally. Together they force the branch.
//
// **The Φ-counts below were measured, not reasoned.** `obligation()`'s
// fallthrough was instrumented to re-probe `graph` and run `self.phi` over every
// offer before returning — the reviewer's own probe, re-applied — and the tree
// restored afterwards:
//
// ```
// A (H-7's pair):  offer (t0,2) RECV  phi=true
//                  offer (t1,2) SEND  phi=false
//                  PROBE-FALLTHROUGH offers=2 phi_passing=1
// B (H-8's pair):  offer (t1,2) SEND  phi=false
//                  PROBE-FALLTHROUGH offers=1 phi_passing=0
// ```
//
// That is what makes H-8 a test of a **true** sentence rather than of a
// coincidence, and it is what rules out the vacuous reading of H-8 — `offers=1`,
// not zero, so the value is emitted over a non-empty offer set and not
// because the attempt was a leaf with nothing to say.
// ===========================================================================

/// **H-7 — the reviewer's B1 fixture, which must no longer claim Φ was empty.**
///
/// The pair is the one round 5 built: the specification's `a` sends twice where
/// the implementation's `a` sends once, and `main` receives on both sides. The
/// overshooting second send fails Φ (`s.len() = 2 > i.len() = 1`, so
/// `observations_follow` is false), which is why the search reports; but `main`'s
/// receive is **invisible**, so installing it leaves the visible rows untouched,
/// `follows` still holds, and it passes Φ. It also leaves `best.vector` at
/// `[1]`, and `Best::offer` replaces only on a *strictly* greater vector — so
/// `best.graph` never moves past the node where both offers are live. The
/// attempt the report names is not a leaf, and before the fix it was told the
/// user it was one.
///
/// The premise is asserted on the graphs: the specification overshoots `a` by
/// exactly one observation. What the premise assertion cannot reach is the other
/// half — that an *invisible* offer is live at `best.graph` and passes Φ —
/// because `best.graph`, `Recompute::probe` and `Recompute::phi` are all private
/// and nothing public exposes the offer set of the chosen attempt. I attempted
/// it three ways before settling: re-probing the pair through
/// `prober::probe_from` from the test (it reconstructs a graph, but not the one
/// `Best` chose, so it proves nothing about the attempt the report names);
/// reading it off `Diagnostics` (the prefix vector is all that survives); and
/// widening `Recompute`'s surface (that is a production edit, so it is a finding
/// and not mine to make). What stands in its place is the instrumentation run
/// recorded in this section's header — `offers=2 phi_passing=1` — and H-8, which
/// is the same pair minus the invisible offer and gets the opposite answer.
///
/// What would break it, **demonstrated**: reverting the fallthrough to the
/// unconditional `Ok(Some(Obligation::NoOfferablePassedPhi))` this fix replaced
/// (MB1 — this test and `h10`, 295/2), or giving the `Ok(None)` arm in
/// `Recompute::diagnose` one of the other `Unavailable` reasons' wording
/// (MB4 — the same two, 295/2). The polarity flip `if !self.phi(..)` does
/// **not** fail this test and I record that rather than claim it does: this
/// pair has two offers, the second of which fails Φ, so the flipped loop still
/// returns `None` here. `h8` is what catches it.
#[test]
fn h7_an_attempt_with_a_phi_passing_offer_is_not_reported_as_phi_empty() {
    let vis = names(&["a"]);
    let imp = run_once(Config::builder().build(), imp_one_receive);
    let spec = run_once(Config::builder().build(), spec_two_sends_one_read);
    assert_eq!(
        wobs(&imp, &vis).unwrap().of("a").len(),
        1,
        "the implementation's `a` must observe one send"
    );
    assert_eq!(
        wobs(&spec, &vis).unwrap().of("a").len(),
        2,
        "the specification's `a` must overshoot by exactly one, or Φ has nothing \
         to reject and the pair does not report"
    );

    let d = sole_report(
        "spec-has-an-extra-send",
        imp_one_receive,
        spec_two_sends_one_read,
        &["a"],
    );
    assert_ne!(
        d,
        Diagnostics::Available {
            prefix: vec![("a".to_owned(), 1usize)],
            obligation: Obligation::NoOfferablePassedPhi,
        },
        "this is round-5 B1 verbatim: an offerable specification event did pass Φ \
         at this attempt (measured: offers=2, phi_passing=1), so the sentence \
         §7.1's fourth value renders is false here"
    );
    let Diagnostics::Unavailable { because, .. } = &d else {
        panic!("expected the fallthrough to decline rather than guess; got {d:?}");
    };
    assert!(
        because.contains("no value for"),
        "the refusal must say §7.1's list has no value for this shape, so the \
         reader is not sent at Φ: {because}"
    );
}

/// **H-8 — and yet the value is reachable, so it is not dead like (M2).**
///
/// If the fix had made §7.1's fourth value unreachable that would be a finding
/// in its own right — `Obligation::NoOfferablePassedPhi` would join
/// `MissingPullBack` as dead code and A14 would need to be told. It has not.
/// The fixture is H-7's minus `main`'s receive on both sides, which is the one
/// offer in H-7 that passed Φ. What is left at the best attempt is the
/// overshooting send and nothing else, so the loop runs to its end and the value
/// is emitted — and here the sentence it renders is **true**.
///
/// The premise, asserted on the graphs, is the same overshoot as H-7's, and it
/// is what forces the attempt to be non-vacuous: the report's prefix is
/// `[("a", 1)]` while the specification's `a` has two observations, so exactly
/// one of the two sends is installed at the attempt the report names and the
/// other is still offerable. The value is therefore emitted over a **non-empty**
/// offer set (measured: `offers=1 phi_passing=0`), not vacuously over a leaf.
///
/// This test passes on the pre-fix tree unchanged — the old code emitted the
/// value unconditionally — so it establishes nothing on its own. It is H-7's
/// other half: the two together are what pin the condition.
///
/// What would break it, both **demonstrated** and each failing this test alone
/// at 296/1: the fallthrough returning `Ok(None)` unconditionally — the
/// over-correction, which would make §7.1's fourth value dead code (MB2) — or
/// its loop reading `if !self.phi(..)?` (MB3).
#[test]
fn h8_an_attempt_where_nothing_offerable_passes_phi_still_names_the_fourth_value() {
    let vis = names(&["a"]);
    let imp = run_once(Config::builder().build(), imp_a_sends_once_unread);
    let spec = run_once(Config::builder().build(), spec_a_sends_twice_unread);
    assert_eq!(wobs(&imp, &vis).unwrap().of("a").len(), 1);
    assert_eq!(
        wobs(&spec, &vis).unwrap().of("a").len(),
        2,
        "the specification's `a` must have a second send left to offer at the \
         best attempt, or this test is the vacuous leaf case it exists to avoid"
    );

    let d = sole_report(
        "no-invisible-offer",
        imp_a_sends_once_unread,
        spec_a_sends_twice_unread,
        &["a"],
    );
    assert_eq!(
        d,
        Diagnostics::Available {
            prefix: vec![("a".to_owned(), 1usize)],
            obligation: Obligation::NoOfferablePassedPhi,
        },
        "§7.1's fourth value must still be reachable; if it is not, it is dead \
         code like `MissingPullBack` and A14 must be told"
    );
    let text = d.to_string();
    assert!(
        text.contains("no offerable specification event passed \u{3a6}"),
        "the value must reach the user as §7.1's sentence:\n{text}"
    );
}

/// **H-9 — the first three obligations still return before the new probe runs.**
///
/// The fix converted every `return Ok(obligation)` above the fallthrough into
/// `return Ok(Some(obligation))`. A conversion that dropped one of them would
/// not fail to compile — `Ok(None)` typechecks everywhere `Ok(Some(..))` does —
/// it would silently hand the case to the new tail, and the user would be told
/// §7.1 has no value for a shape (M1) names perfectly well.
///
/// The pair is `h4`'s mid-search one. At a mid-search gate `outer.complete` is
/// false, so (M3) is skipped and `best.graph` satisfies `follows` and therefore
/// (M2) — which is this module's header argument — leaving (M1) as the only
/// branch that can fire. Pinning it by value pins that the fallthrough is not
/// reached on the ordinary report.
///
/// **What this test does and does not separate itself from, measured rather
/// than claimed.** The (M1) branch is *not* uniquely pinned here:
/// `s5_tests::f_m1_can_only_fail_by_length_at_a_following_attempt` already
/// asserts `ObservationMismatch`'s `spec`, `imp` and `position` on a different
/// pair. So the swallowing mutation (MB5) fails four tests — this one, `h4`,
/// `c9_a_nocover_report_names_a_first_failing_obligation` and `f_m1` — and no
/// claim of uniqueness is made for it. What *is* separated: `f_m1` destructures
/// `ObservationMismatch { spec, imp, position, .. }` and ignores the `thread`
/// field, and nothing else in the crate asserts it, so a (M1) branch that names
/// the wrong visible thread (MB8) fails **this test alone**, 296/1. The thread
/// name is the first thing §7.1's sentence tells the reader, and it was
/// unpinned.
///
/// (M2)'s and (M3)'s branches are pinned by value in `h1` and `h2` and were left
/// alone rather than duplicated here. Both were re-run under a mutation deleting
/// the (M3) block (MB6) and both fail, so they still discriminate post-fix —
/// the consequence `h2`'s rustdoc named for that mutation was stale after the
/// fix — it said the fixture becomes "the `NoOfferablePassedPhi` fallthrough",
/// where post-fix it becomes `Unavailable { .., kind: NoValueForIt }`. That was
/// filed as F-B1c and **has since been corrected in `h2`'s own clause**,
/// re-measured on the fixed tree (297/4).
///
/// What would break it, both **demonstrated**: the (M1) length branch returning
/// `Ok(None)` where it returns `Ok(Some(..))` (MB5 — this test, `h4`, `c9` and
/// `f_m1`, 293/4), or that branch naming a visible thread other than the one
/// whose rows differ (MB8 — this test only, 296/1).
#[test]
fn h9_a_mid_search_report_still_names_the_m1_obligation_and_not_the_fallthrough() {
    let d = sole_report("extra-send", imp_two_receives, spec_one_receive, &["a"]);
    let Diagnostics::Available { obligation, .. } = &d else {
        panic!("the mid-search pair must carry a diagnostic: {d:?}");
    };
    assert!(
        matches!(obligation, Obligation::ObservationMismatch { thread, .. } if thread == "a"),
        "at a mid-search gate (M1) is the only branch that can fire, so anything \
         else here means a branch above the fallthrough stopped returning: \
         {obligation:?}"
    );
}

/// **H-10 — the new refusal is a reason of its own, not one of the old ones.**
///
/// `Diagnostics::Unavailable` carries a free-form `because`, and the fix added a
/// **ninth** construction site to a variant that already had eight — the
/// round-4 version of this sentence said "a fourth", which was wrong arithmetic
/// of mine, corrected here and counted in `h12`. Three of the nine are
/// reachable, and a user who is told "diagnostics unavailable" acts on the
/// difference between them: *the budget ran out* is a knob to turn, *the
/// re-run found a cover* means the recomputation is describing a different
/// question, and *§7.1 has no value for this shape* means the search worked and
/// the enumeration is what fell short. Collapsing the third into either of the
/// first two is how F-7's question gets lost.
///
/// `c9_a_recomputation_that_cannot_reproduce_the_verdict_says_so` pins the
/// budget reason alone, by substring. Nothing compared the reasons to each
/// other.
///
/// What would break it, both **demonstrated** at 295/2 (this test and `h7`):
/// giving the `Ok(None)` arm in `Recompute::diagnose` the text of a check-one
/// reason (MB4), or deleting the arm so the fourth value is emitted
/// unconditionally again and the third reason ceases to exist (MB1). No
/// mutation I tried separates this test from `h7`; its residual is that it is
/// the only test comparing the `Unavailable` reasons **to each other**, where
/// `h7` and `c9_a_recomputation_that_cannot_reproduce_the_verdict_says_so` each
/// check one in isolation and would both survive two reasons being given the
/// same words as a third.
///
/// *(Scope note, added after the B1b fix. This test compares the three reasons
/// by their `because` **strings**, which was the only discriminator when it was
/// written. `Diagnostics::Unavailable` now also carries a `kind`, and the
/// **kind** is what a programmatic caller branches on — that is `h14`'s
/// property, not this one's. The two are not duplicates: `kind` is two-valued
/// and cannot separate the budget reason from the cover-found reason, both of
/// which are `Diverged`. This test remains the only thing keeping those two
/// apart.)*
#[test]
fn h10_the_three_reachable_unavailable_reasons_are_distinguishable() {
    // Reason one: the re-run of `Search::cover` finds a cover, so the
    // recomputation is not describing the question the gate answered.
    let cfg = || Config::builder().with_cons_type(ConsType::FIFO).build();
    let graph = run_once(cfg(), imp_one_receive);
    let found = Recompute::new(
        cfg(),
        std::sync::Arc::new(imp_one_receive),
        names(&["a"]),
        4096,
        true,
    )
    .diagnose(&graph, true);

    // Reason two: no budget to establish anything.
    let exhausted = Recompute::new(
        cfg(),
        std::sync::Arc::new(imp_one_receive),
        names(&["a"]),
        0,
        true,
    )
    .diagnose(&graph, true);

    // Reason three: the fix's own.
    let no_value = sole_report(
        "spec-has-an-extra-send",
        imp_one_receive,
        spec_two_sends_one_read,
        &["a"],
    );

    let mut reasons = Vec::new();
    for (what, d) in [
        ("cover-found", &found),
        ("budget", &exhausted),
        ("no-§7.1-value", &no_value),
    ] {
        let Diagnostics::Unavailable { because, .. } = d else {
            panic!("{what}: expected an unavailable diagnostic, got {d:?}");
        };
        reasons.push((what, because.clone()));
    }
    assert!(reasons[0].1.contains("found a cover"), "{:?}", reasons[0]);
    assert!(reasons[1].1.contains("budget"), "{:?}", reasons[1]);
    assert!(reasons[2].1.contains("no value for"), "{:?}", reasons[2]);
    for i in 0..reasons.len() {
        for j in (i + 1)..reasons.len() {
            assert_ne!(
                reasons[i].1, reasons[j].1,
                "`{}` and `{}` give the user the same sentence",
                reasons[i].0, reasons[j].0
            );
        }
    }
}

// ===========================================================================
// B1b — `Unavailable` had one reason and two meanings
//
// The B1 fix routed a new case — "the morphism holds on the furthest-following
// attempt and no extension of it covers" — through `Diagnostics::Unavailable`,
// whose `Display` appended, unconditionally, *"a recomputation that does not
// reproduce the search's own verdict is not evidence about this report"*. For
// the new case that sentence is **false**: check one (`Search::cover` on the
// reported graph) answered `NoCover`, check two (this module's traversal)
// answered `NoCover`, and (M1)–(M3) all held. Nothing disagreed with anything.
// That was B1's own shape one layer up — a sentence asserting a condition the
// code had not checked — and it is F-B1b in
// `plan/traceForge/log/dev/P3-S5-b1fix.report.md`.
//
// The fix splits the variant with a `kind: UnavailableKind`, `Diverged` (the
// original meaning) against `NoValueForIt` (the recomputation agreed; §7.1's
// four values have no name for what it found — A14). `Display` and
// `spec_side_first_mismatch` both branch on it, and the type is exported.
//
// **Which sites a value test can reach was measured, not assumed.** All nine
// `Diagnostics::Unavailable` construction sites in `diagnose.rs` were
// instrumented with an `eprintln!` and the whole conformance module run at
// `--test-threads=1`; the tree was restored afterwards and md5-checked:
//
// ```
// site 1  Cover::Found                                     1 reach   (h10)
// site 2  Cover::BudgetExhausted                           2 reaches (h10, c9)
// site 3  Err from Search::cover                           0
// site 4  Err from wobs(g1, ..)                            0
// site 5  visit answered something other than NoCover      0
// site 6  Err from visit                                   0
// site 7  best.graph == None                               0
// site 8  Ok(None)  -- NoValueForIt, the new one           2 reaches (h7, h10)
// site 9  Err from obligation()                            0
// ```
//
// So **six of the eight `Diverged` tags are on paths no test executes**. A
// value test cannot check them and saying "they compile" is not checking them,
// which is why `h12` reads the source. Sites 7 and 9 are also where the tag is
// arguably wrong; that is a finding, not something a test can assert, and it is
// in `P3-S5-b1fix-2.report.md`.
// ===========================================================================

/// **H-11 — each kind renders its own sentence, and neither renders the
/// other's.**
///
/// This is F-B1b closed, and it is asserted on the **whole rendered report**
/// rather than on `Diagnostics::to_string()`, because the claim is about what a
/// user reads: the false sentence must be absent from the report, not merely
/// from one field of it.
///
/// Both kinds are reached through real paths rather than built by hand.
/// `NoValueForIt` comes from round 5's pair driven through `verify`;
/// `Diverged` from the budget-exhausted site, which is one of the two
/// pre-existing sites a fixture can reach at all (see this section's table).
/// A hand-built `Diagnostics::Unavailable { .. }` would test `Display` and
/// nothing about whether the production path ever produces that kind.
///
/// Both directions are asserted, and the negative half is the load-bearing one:
/// a fix that added the new sentence while leaving the old one in place would
/// satisfy every positive assertion and still tell the reader two contradictory
/// things.
///
/// What would break it, all three **demonstrated**: swapping the two arms'
/// bodies in `Display for Diagnostics` (MC1 — this test alone, 300/1); folding
/// the `NoValueForIt` arm back into the `Diverged` text, which is F-B1b
/// restored verbatim (MC2 — this test alone, 300/1); or tagging `diagnose`'s
/// `Ok(None)` site `Diverged` instead of `NoValueForIt` (MC3 — this test with
/// `h12`, `h13` and `h14`, 297/4).
#[test]
fn h11_each_unavailable_kind_renders_its_own_sentence_and_not_the_others() {
    // `NoValueForIt`, end to end.
    let text = sole_report_text(
        "spec-has-an-extra-send",
        imp_one_receive,
        spec_two_sends_one_read,
        &["a"],
    );
    assert!(
        text.contains("The recomputation agreed with the search here"),
        "the new kind must say what actually happened — the recomputation agreed \
         and §7.1's list is what fell short:\n{text}"
    );
    assert!(
        text.contains("no name for what it found"),
        "the refusal must point the reader at the enumeration (A14), not at the \
         recomputation:\n{text}"
    );
    assert!(
        !text.contains("does not reproduce the search's own verdict"),
        "F-B1b verbatim: this report's recomputation reproduced the search's \
         verdict exactly, so a sentence saying it did not is false — and it sends \
         the reader at `diagnose.rs` when the question is §7.1's:\n{text}"
    );

    // `Diverged`, from the budget-exhausted site.
    let cfg = || Config::builder().with_cons_type(ConsType::FIFO).build();
    let graph = run_once(cfg(), imp_one_receive);
    let diverged = Recompute::new(
        cfg(),
        std::sync::Arc::new(imp_one_receive),
        names(&["a"]),
        0,
        true,
    )
    .diagnose(&graph, true);
    assert!(
        matches!(
            diverged,
            Diagnostics::Unavailable {
                kind: UnavailableKind::Diverged,
                ..
            }
        ),
        "a budget of zero is a genuine divergence and must stay tagged as one: \
         {diverged:?}"
    );
    let dtext = diverged.to_string();
    assert!(
        dtext.contains("does not reproduce the search's own verdict"),
        "the original sentence must survive for the case it is true of: {dtext}"
    );
    assert!(
        !dtext.contains("agreed with the search"),
        "a divergence must not claim the recomputation agreed: {dtext}"
    );
}

/// **H-12 — the nine construction sites, tagged one at a time rather than
/// mechanically.**
///
/// The fix added `kind` to a variant with eight existing construction sites and
/// tagged all eight `Diverged` in one pass. Six of them are on paths **no test
/// in the crate executes** (measured; table in this section's header), so every
/// value test in this file put together leaves those six checked only by the
/// compiler — and the compiler cannot tell `Diverged` from `NoValueForIt`.
/// Reading the source is the only mechanised check there is, so that is what
/// this does.
///
/// It is deliberately arithmetic rather than a grep. A new `Unavailable` site
/// added later fails this test until whoever adds it says which kind it is,
/// which is the property worth having: the failure mode being guarded is a site
/// getting the default tag by inertia.
///
/// The scan asserts its own coverage before it counts — every textual
/// occurrence of `Diagnostics::Unavailable` must open its brace on its own line
/// with `kind:` on the next, so a site written in some other shape trips the
/// test instead of being silently skipped. The two `spec_side_first_mismatch`
/// *patterns* are counted separately and must carry one kind each, which is
/// what stops the arms there being widened to `..` and re-merged.
///
/// What would break it, all three **demonstrated**: retagging any one of the six
/// unreachable `Diverged` sites as `NoValueForIt` (MC4 — this test **alone**,
/// 300/1, which is the measurement that says it is those six sites' only
/// cover); mis-tagging the reachable `Ok(None)` site (MC3 — this test with
/// `h11`, `h13` and `h14`, 297/4); or collapsing the two
/// `spec_side_first_mismatch` patterns into one (MC5 — this test with `h13`,
/// 299/2). Deleting a site's `kind` outright does **not** reach a test result:
/// it is `error[E0063]: missing field kind in initializer of Diagnostics`, run
/// and recorded as a compile failure rather than dressed up as one.
#[test]
fn h12_every_unavailable_site_in_diagnose_is_tagged_one_at_a_time() {
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/diagnose.rs"),
    )
    .expect("diagnose.rs must be readable");
    let lines: Vec<&str> = src.lines().collect();

    let mut constructions: Vec<(usize, String, String)> = Vec::new();
    let mut patterns: Vec<(usize, String)> = Vec::new();
    let mut occurrences = 0usize;

    for (i, line) in lines.iter().enumerate() {
        if !line.contains("Diagnostics::Unavailable") {
            continue;
        }
        occurrences += 1;
        let t = line.trim();
        assert!(
            t.ends_with("Diagnostics::Unavailable {"),
            "diagnose.rs:{}: this occurrence does not open its brace on its own \
             line, so the scan below cannot see its `kind`. Widen the scan — do \
             not delete this assertion, which is the only thing keeping a site \
             from being skipped in silence: {t}",
            i + 1
        );
        let next = lines[i + 1].trim();
        let kind = next
            .strip_prefix("kind: report::UnavailableKind::")
            .and_then(|k| k.strip_suffix(','))
            .unwrap_or_else(|| {
                panic!(
                    "diagnose.rs:{}: a `Diagnostics::Unavailable` whose next line is \
                     not its `kind`. Every one of them is a sentence a user reads, \
                     and the two kinds say opposite things about whether the \
                     recomputation worked: {next}",
                    i + 2
                )
            });
        if t.starts_with("return ") || t.contains("=>") {
            constructions.push((i + 1, kind.to_owned(), t.to_owned()));
        } else {
            patterns.push((i + 1, kind.to_owned()));
        }
    }

    assert_eq!(occurrences, 11, "nine constructions and two patterns");
    assert_eq!(
        constructions.len(),
        9,
        "the construction sites changed: {constructions:?}"
    );
    assert_eq!(patterns.len(), 2, "the match arms changed: {patterns:?}");

    let diverged: Vec<_> = constructions.iter().filter(|c| c.1 == "Diverged").collect();
    let no_value: Vec<_> = constructions
        .iter()
        .filter(|c| c.1 == "NoValueForIt")
        .collect();
    assert_eq!(
        diverged.len() + no_value.len(),
        9,
        "a third kind appeared without this test being told: {constructions:?}"
    );
    assert_eq!(
        diverged.len(),
        8,
        "exactly the eight pre-fix sites are divergences; if a ninth genuinely \
         is one, say so here: {diverged:?}"
    );
    assert_eq!(
        no_value.len(),
        1,
        "`NoValueForIt` is the `Ok(None)` case and only that: {no_value:?}"
    );
    assert!(
        no_value[0].2.starts_with("Ok(None) =>"),
        "the one `NoValueForIt` site must be the arm where `obligation()` \
         declined to name a value — anywhere else and the kind is claiming the \
         recomputation agreed without that having been established: {:?}",
        no_value[0]
    );

    let mut pattern_kinds: Vec<&str> = patterns.iter().map(|p| p.1.as_str()).collect();
    pattern_kinds.sort_unstable();
    assert_eq!(
        pattern_kinds,
        ["Diverged", "NoValueForIt"],
        "`spec_side_first_mismatch` must keep one arm per kind; a `..` here \
         re-merges the two and is how the distinction quietly goes away: \
         {patterns:?}"
    );
}

/// **H-13 — the triage line does not call the new refusal a divergence.**
///
/// `spec_side_first_mismatch` is the second reader of `Diagnostics`, and it had
/// the same defect as `Display`: one `Unavailable` arm rendering
/// `"unavailable ({because})"`, which reads as *the recomputation failed*. §7.3
/// presents this string next to the ⟨word, status vector⟩ pair, so it is the
/// one line a triaged report gives a reader about why no obligation is named.
///
/// Both inputs are real values — the `NoValueForIt` one from `verify`, the
/// `Diverged` one from the budget site — so the test pins the *composition*
/// (production path produces a kind, this function reads it) rather than
/// `match` on a value written in the test.
///
/// Asserted end to end as well: the h7 pair is re-run with `triage(true)` and
/// the string is required to appear in the rendered `TriageOutcome`. A unit
/// call alone would leave it possible for the plumbing to drop it, which is
/// exactly what `c14_…` exists to prevent for the other kind.
///
/// What would break it, both **demonstrated**: widening the `Diverged` arm's
/// pattern to `kind: _` so it catches both and the new case is folded back into
/// "unavailable (…)" — the pre-fix behaviour — or swapping the two arms'
/// bodies. MC6, the swap, fails **this test alone** at 300/1. MC5, the widening,
/// fails this test *and* `h12` at 299/2, and I record that rather than the
/// uniqueness I predicted: `h12` counts the match **patterns**, so collapsing
/// two arms into one moves its count from 2 to 1. The two catch the same
/// mutation from opposite sides — this one by what a reader is told, `h12` by
/// the arm having ceased to exist — and neither is redundant, since MC6 is
/// invisible to `h12` and MC4 is invisible to this test.
#[test]
fn h13_the_spec_side_first_mismatch_does_not_call_the_new_refusal_a_divergence() {
    let no_value = sole_report(
        "spec-has-an-extra-send",
        imp_one_receive,
        spec_two_sends_one_read,
        &["a"],
    );
    let cfg = || Config::builder().with_cons_type(ConsType::FIFO).build();
    let graph = run_once(cfg(), imp_one_receive);
    let diverged = Recompute::new(
        cfg(),
        std::sync::Arc::new(imp_one_receive),
        names(&["a"]),
        0,
        true,
    )
    .diagnose(&graph, true);

    let m = diagnose::spec_side_first_mismatch(&no_value, &ReportCause::NoCover);
    assert_eq!(
        m, "no §7.1 obligation names this failure; see A14",
        "the new kind must be said as itself; folding it into \"unavailable\" \
         tells the reader the recomputation failed when it agreed"
    );
    assert!(
        !m.starts_with("unavailable"),
        "this is the pre-fix wording, and it is the wrong half of the report to \
         send the reader at: {m}"
    );

    let d = diagnose::spec_side_first_mismatch(&diverged, &ReportCause::NoCover);
    assert!(
        d.starts_with("unavailable (") && d.contains("budget"),
        "a real divergence must keep the wording it had: {d}"
    );
    assert_ne!(m, d, "the two kinds must not give the reader one sentence");

    // …and the string reaches a triaged report, not just this call.
    let v = verify(
        base(&["a"])
            .search_budget(4096)
            .triage(true)
            .build()
            .expect("in-scope config"),
        imp_one_receive,
        spec_two_sends_one_read,
    )
    .expect("the triaged run must not fail");
    let ConfVerdict::Reported(o) = v else {
        panic!("this pair must report under triage too");
    };
    let rendered: Vec<String> = o.reports().iter().map(|r| r.to_string()).collect();
    assert!(
        rendered.iter().any(|t| t.contains("see A14")),
        "§7.3 presents the specification-side first mismatch next to the pair; \
         the new wording must survive the plumbing: {rendered:?}"
    );
}

/// **H-14 — a caller can branch on the kind, which is why it was exported.**
///
/// `mod.rs`'s public-surface note gives the reason a type is exported rather
/// than hidden behind `Display`: to spare a programmatic caller
/// `to_string().contains(..)`. `UnavailableKind` was added to that list, so the
/// commitment is that a caller **outside** `report` can name the type, get it
/// out of a `Diagnostics` obtained from the public entry point, and compare it.
/// A test that matched on `report::UnavailableKind` would prove none of that;
/// this one names it only through `crate::conformance`, the re-export.
///
/// The three traits are used rather than asserted about: `k` is bound to the
/// public path (the re-export names *this* type), copied twice (`Copy`),
/// compared (`PartialEq`), and formatted (`Debug`). Dropping any of them from
/// the derive is a compile failure, recorded as such below.
///
/// What would break it: tagging `diagnose`'s `Ok(None)` site `Diverged`
/// (MC3 — **demonstrated**, this test with `h11`, `h12` and `h13`, 297/4).
///
/// The surface half cannot reach a test result, and both halves were run rather
/// than asserted. Dropping `UnavailableKind` from `mod.rs`'s `pub use` is
/// `error[E0425]/[E0433]: cannot find UnavailableKind in crate::conformance`,
/// and the three sites it names are the three lines below — so this test is
/// what holds the re-export. Dropping `PartialEq` from the derive is
/// `error[E0277]/[E0369]`, and the measurement was worth taking: the first two
/// errors are in **`report.rs` itself**, because `Diagnostics` derives
/// `PartialEq` and now contains this type. So `UnavailableKind: PartialEq` is
/// load-bearing for `Diagnostics: PartialEq`, which `h7`'s `assert_ne!` and
/// every other value comparison of a diagnostic in this file depend on.
#[test]
fn h14_a_caller_can_branch_on_the_unavailable_kind_through_the_public_export() {
    let d = sole_report(
        "spec-has-an-extra-send",
        imp_one_receive,
        spec_two_sends_one_read,
        &["a"],
    );
    let Diagnostics::Unavailable { kind, .. } = d else {
        panic!("this pair's diagnostics are the new refusal: {d:?}");
    };

    // The re-export, not `report::`.
    let k: crate::conformance::UnavailableKind = kind;
    let copied = k;
    assert_eq!(
        k,
        crate::conformance::UnavailableKind::NoValueForIt,
        "the recomputation agreed with the search on this pair, so a caller must \
         be able to read that off the value without parsing English"
    );
    assert_ne!(
        copied,
        crate::conformance::UnavailableKind::Diverged,
        "if the two kinds compared equal the export would buy a caller nothing"
    );
    assert_eq!(
        format!("{k:?}"),
        "NoValueForIt",
        "the variant name is part of the exported surface — it is what a caller \
         logging the kind writes down"
    );
}

// --- B1 fixtures -----------------------------------------------------------

/// Round 5's B1 pair, specification side: one send more than the
/// implementation's `a`, with `main` receiving — the invisible offer that passes
/// Φ at the best attempt and makes the fourth value's sentence false there.
fn spec_two_sends_one_read() {
    named("a", || {
        crate::send_msg(main_thread_id(), 1u64);
        crate::send_msg(main_thread_id(), 2u64);
    });
    let _: u64 = crate::recv_msg_block();
}

/// The same overshoot with the invisible offer removed: `main` spawns and
/// stops, so the only offer at the best attempt is the send Φ rejects.
fn imp_a_sends_once_unread() {
    named("a", || crate::send_msg(main_thread_id(), 1u64));
}

fn spec_a_sends_twice_unread() {
    named("a", || {
        crate::send_msg(main_thread_id(), 1u64);
        crate::send_msg(main_thread_id(), 2u64);
    });
}
