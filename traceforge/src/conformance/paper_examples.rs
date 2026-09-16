//! The draft's worked examples, through the **public entry**.
//!
//! Criterion 16, and the owner's goal 3. Before this file, six example tests
//! existed and every one called `Search::cover` directly on a hand-built
//! `complete_graph(&..)`. A `Cover`-level test passes while the probe is
//! mis-wired, the gates fire at the wrong sites, the report renders the wrong
//! verdict, or the engine never reaches the completion gate — S4 and S5 are
//! precisely the layers those tests do not touch.
//!
//! # The nine, enumerated from `\label{ex:` in the source
//!
//! Not from memory: the project once cited an "Ex. blocking" that the draft
//! does not have, and the name had hardened into a citation in two files.
//!
//! | example | where | level, and why |
//! |---|---|---|
//! | `ex:traces` | `prog.tex:268` | **oracle** — it is about `Traces(P)`, not about the search. `oracle_tests.rs` |
//! | `ex:vis` | `ref2.tex:68` | **oracle** — it publishes `vis` sets, the oracle's own output type |
//! | `ex:graphs` | `ref2.tex:261` | **oracle** — a graph count, which is what collect mode produces |
//! | `ex:relay` | `ref2.tex:89` | **public entry** — here |
//! | `ex:morph` | `ref2.tex:463` | **public entry** — here, all four published answers |
//! | `ex:naive` | `alg.tex:32` | **search** — a *cost* claim about node expansion, which `verify` does not expose. `search.rs` |
//! | `ex:sched` | `alg.tex:886` | **search** — about which offers `SpecStep` may take |
//! | `ex:restart` | `alg.tex:957` | **search** — about `Cover`'s second attempt |
//! | `ex:rebuild` | `alg.tex:981` | **search** — about a conflicting seed |
//!
//! The four marked **search** are claims about the inner algorithm's
//! mechanics, not about a verdict, and `verify` deliberately does not expose
//! node counts or offer order. They stay where they are, and this table is the
//! "stated reason" criterion 16 asks for rather than an omission.
//!
//! # On mutations
//!
//! Every test below names a mutation. **All five were applied at gate 3 and
//! the results are recorded on each test**; four broke their test as derived
//! and one — the (M2) variant's — did not, and its correction is written where
//! it belongs rather than summarised here. The file previously marked four as
//! `UNVERIFIED (gate 3)` and one as "MEASURED: none applied"; those labels are
//! gone because the measurements exist.

use crate::conformance::{verify, ConfBuilder, ConfVerdict};
use crate::{recv_msg_block, send_msg, thread, ConsType, Config};

fn cfg() -> Config {
    Config::builder().with_cons_type(ConsType::FIFO).build()
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

fn conf(visible: &[&str]) -> crate::conformance::ConfConfig {
    ConfBuilder::new()
        .visible_threads(visible.iter().copied())
        .config(cfg())
        .build()
        .expect("in-scope configuration")
}

// ---------------------------------------------------------------------------
// `ex:relay` / `ex:morph`'s base pair.
//
// The draft fixes the orientation at `ref2.tex:464`: "with `P₂` as the
// implementation and `P₁` as the specification". `P₂` is the relay chain.
// ---------------------------------------------------------------------------

/// `P₂`: `A` sends to an invisible relay `R`, which forwards to `C`.
fn p2_relay() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let r = named("r", move || {
        let v: i32 = recv_msg_block();
        send_msg(cid, v);
    });
    send_msg(r.thread().id(), 1i32);
}

/// `P₁`: `A` sends straight to `C`.
fn p1_direct() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 1i32);
}

/// **`ex:morph`'s base pair: `G₁ ⊑ G₂`.** The published answer is that
/// refinement **holds**, and the tool must therefore produce a *certificate* —
/// not merely silence. `mod.rs` states why the distinction matters: the
/// certificate types "are the difference between a certificate and a run that
/// merely produced no report, which is the one distinction the theorem turns
/// on".
///
/// This is the first time the relay example reaches `verify`; the existing
/// `ex_relay_holds` stops at `Cover`.
///
/// **Mutation, MEASURED (gate 3)**: give `Obs::Send` the send's destination —
/// `Send(Val, String)` carrying `format!("{:?}", slab.loc())`, compared in
/// `Obs`'s `PartialEq`. Applied at gate 3 —
/// `ex_morph_base_pair_certifies_through_verify ... FAILED`, 338 passed /
/// 14 failed. `P₂`'s `send(R,1)` and `P₁`'s `send(C,1)` then differ and the
/// relay stops being invisible.
///
/// The label this test carried before gate 3 was "**Mutation, MEASURED**: none
/// applied", which is a contradiction: criterion 19 asks every test to name a
/// mutation *applied and shown to fail it*, and deferring to three sibling
/// tests leaves this one unprotected. One is supplied above.
#[test]
fn ex_morph_base_pair_certifies_through_verify() {
    let verdict = verify(conf(&["main", "c"]), p2_relay, p1_direct).expect("run");
    assert!(
        matches!(verdict, ConfVerdict::Conforms(_)),
        "ex:morph publishes G1 <= G2 for the relay pair; got {verdict:?}"
    );
}

/// **`ex:relay` both ways.** The draft publishes `vis(P₁) = vis(P₂)`, so the
/// pair conforms in *either* orientation — relay insertion adds no `vo` edge,
/// because the direct form already orders the send before the receive through
/// its own `rf` edge.
///
/// This is the end-to-end form of the correction that cost a review round: the
/// project had briefly recorded relay insertion as holding in one direction
/// only.
///
/// **Mutation, MEASURED (gate 3)**: include the send's destination in `Obs` —
/// `Send(Val, String)` carrying `format!("{:?}", slab.loc())`, compared in
/// `Obs`'s `PartialEq`. Applied at gate 3 —
/// `ex_relay_conforms_in_both_orientations ... FAILED`, 338 passed / 14 failed.
/// The derivation from `obs.rs:26-31` was right.
#[test]
fn ex_relay_conforms_in_both_orientations() {
    let a = verify(conf(&["main", "c"]), p2_relay, p1_direct).expect("run");
    assert!(
        matches!(a, ConfVerdict::Conforms(_)),
        "relay as implementation: {a:?}"
    );
    let b = verify(conf(&["main", "c"]), p1_direct, p2_relay).expect("run");
    assert!(
        matches!(b, ConfVerdict::Conforms(_)),
        "relay as specification: {b:?}"
    );
}

/// **`ex:morph`'s (M1) variation**: "Replace the `1` that `A` sends in `P₁` by
/// `2`." Published answer: (M1) fails.
///
/// **Mutation, MEASURED (gate 3)**: make `Obs`'s `PartialEq` ignore the value
/// (both the `Send` and the `Recv(Some(..))` arms return `true`). Applied at
/// gate 3 — `ex_morph_m1_variation_reports_through_verify ... FAILED`, 328
/// passed / 34 failed. The observations then agree and this certifies.
#[test]
fn ex_morph_m1_variation_reports_through_verify() {
    fn p1_value_two() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 2i32);
    }
    let verdict = verify(conf(&["main", "c"]), p2_relay, p1_value_two).expect("run");
    assert!(
        matches!(verdict, ConfVerdict::Reported(_)),
        "the send is observed <snd,A,1> on one side and <snd,A,2> on the other; got {verdict:?}"
    );
}

/// **`ex:morph`'s (M3) variation, in the draft's own orientation**: "let `C` in
/// **`P₁`** perform a second blocking receive that nothing can satisfy … `C`
/// is blocked in the **specification** and done in the implementation".
///
/// `P₁` is the *specification*, and the base pair is the **relay** pair. The
/// project's long-standing `blocking_impl`/`blocking_spec` fixture is the
/// mirror of this on both axes — extra receive in the implementation, direct
/// pair with no relay — so this is the first test of the published direction.
/// It matters because the two are not symmetric: the specification is explored
/// by *probe* and the implementation by the stock engine.
///
/// **Mutation, MEASURED (gate 3)**: drop the `statuses_agree` conjunct from
/// `Search::done` (`search.rs:538`), returning `Ok(true)`. Applied at gate 3 —
/// `ex_morph_m3_variation_papers_orientation_reports_through_verify ...
/// FAILED`, 343 passed / 9 failed. The words agree, so only the status
/// separates these two.
#[test]
fn ex_morph_m3_variation_papers_orientation_reports_through_verify() {
    fn p1_c_blocks() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
            let _w: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    }
    let verdict = verify(conf(&["main", "c"]), p2_relay, p1_c_blocks).expect("run");
    assert!(
        matches!(verdict, ConfVerdict::Reported(_)),
        "C is blocked in the specification and done in the implementation; got {verdict:?}"
    );
}

/// **The mirror of the above**, kept deliberately and labelled as ours.
///
/// Extra receive in the **implementation**, on a direct pair. Also a genuine
/// (M3) mismatch, also reported — but it is *our* construction, not the
/// draft's, and the two directions exercise different engines. Keeping both,
/// with the report saying which is published, is what criterion 4(d) asks for.
///
/// **Mutation, MEASURED (gate 3)**: as above — dropping `statuses_agree` from
/// `Search::done` also fails this test in the same run
/// (`the_mirror_m3_orientation_ours_not_the_papers_also_reports ... FAILED`).
/// The two orientations fail together, which is itself worth recording: the
/// mirror adds a second engine path, not a second discriminator.
#[test]
fn the_mirror_m3_orientation_ours_not_the_papers_also_reports() {
    fn impl_c_blocks() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
            let _w: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    }
    let verdict = verify(conf(&["main", "c"]), impl_c_blocks, p1_direct).expect("run");
    assert!(
        matches!(verdict, ConfVerdict::Reported(_)),
        "C blocked in the implementation, done in the specification; got {verdict:?}"
    );
}

/// **`ex:morph`'s (M2) variation, the draft's own construction.**
///
/// "Instead take the two sends of `ex:graphs`, which no `po` or `rf` path
/// relates, against a specification that orders them: then `vo_{G₂}` has an
/// edge `vo_{G₁}` lacks and (M2) fails."
///
/// The implementation is `ex:traces`' program with `T_vis ⊇ {A,B}`, whose two
/// incomparable visible events are **two sends by two different visible
/// threads**. Ordering two visible *sends* in the specification cannot be done
/// with a message — a message between them would add visible events and change
/// the word — so the ordering mechanism is `join`.
///
/// **This is the first (M2) example anywhere in the tree**: `search.rs` has
/// `ex_relay`, `ex_sched`, `ex_restart`, `ex_rebuild`, `ex_blocking` and
/// `ex_naive`, and no (M2) case. A14 records that the §7.1 (M2) *diagnostic*
/// is unreachable; this is the morphism **conjunct** failing end to end, which
/// is a different claim and a reachable one.
///
/// **Mutation, MEASURED — and the stated one was REFUTED (gate 3)**.
///
/// The line this test carried was "drop `order_is_reflected` from `follows`".
/// Applied at gate 3: **this test still passed**, 351 passed / 1 failed (only
/// `search::tests::phi_holds_the_receive_back_until_the_ordered_send_is_there`
/// fell). Dropping it from `matches` *alone* was also applied: the whole lib
/// suite stayed green at 352 / 0.
///
/// The mutation that does fail this test is dropping `order_is_reflected` from
/// **both** `morphism::follows` **and** `morphism::matches` — 354 passed /
/// 5 failed, this test among them. The two sites are independently sufficient:
/// `follows` rejects the offending specification graph while it is still being
/// extended, and `matches` rejects it at completion, so (M2) has a redundant
/// guard here and no single-site mutation can expose it. Worth knowing before
/// anyone reads a single-site mutation's survival as evidence that the conjunct
/// is dead.
///
/// **A7 applies and is recorded where the result is used**: TraceForge's
/// `porf` is `(po ∪ rf ∪ create ∪ join)⁺` where the draft's is `(po ∪ rf)⁺`,
/// so the `join` orders these two for a reason the draft's model has no events
/// for. Tool and oracle both inherit it, so it cancels in the differential —
/// but the *published* answer is being reproduced by a mechanism the paper
/// does not have, and that is worth saying out loud.
#[test]
fn ex_morph_m2_variation_papers_construction_reports_through_verify() {
    // Impl: ex:traces' program. `a` and `b` send to `c`; nothing orders them.
    fn impl_two_unordered_sends() {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, 1i32));
        let _b = named("b", move || send_msg(cid, 2i32));
    }
    // Spec: the same, except `b` joins `a`, so `a`'s send precedes `b`'s.
    fn spec_sends_ordered_by_join() {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let a = named("a", move || send_msg(cid, 1i32));
        let _b = named("b", move || {
            a.join().unwrap();
            send_msg(cid, 2i32);
        });
    }
    let verdict = verify(
        conf(&["main", "a", "b", "c"]),
        impl_two_unordered_sends,
        spec_sends_ordered_by_join,
    )
    .expect("run");
    assert!(
        matches!(verdict, ConfVerdict::Reported(_)),
        "vo_G2 has an edge vo_G1 lacks, so (M2) fails; got {verdict:?}"
    );
}
