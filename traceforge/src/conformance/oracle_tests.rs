//! The oracle and its capture hook, tested by the agent that did not write
//! them.
//!
//! **Authorship note, and it is the point of this file.** The lead implemented
//! `oracle.rs` and `ctx.rs`'s collect mode *and* wrote the first version of
//! this module. That collapses gates 2 and 3 — the owner's 2026-09-16 ruling is
//! that whoever did not write the code writes the tests — so this file was
//! re-derived from `criteria/P3-S6-harness.md` revision 4 rather than extended.
//! Tests that survived mutation are kept, with their "to break it" lines
//! corrected where the named mutation was measured *not* to break them; the
//! criteria's required tests that had no code at all are added.
//!
//! Every test names the mutation that breaks it, and every one of those
//! mutations was applied to the production code and shown to fail the test —
//! criterion 19. Where a mutation named in a doc comment was measured not to
//! fail its test, the doc comment says so rather than repeating the claim.
//!
//! Layout: group A is the object `vis(G)` (criterion 1), group B the paper's
//! published answers (criterion 4), group C the capture hook's T1–T9
//! (criterion 3), group D the B1 fix (criterion 3's resolution), group E
//! criterion 2's two obligations.

use std::sync::Arc;

use crate::conformance::ctx::{ConfCtx, ConfMode};
use crate::conformance::morphism::{statuses, CompleteExecution, Status};
use crate::conformance::obs::wobs;
use crate::conformance::oracle::{includes, vis_of_program, Inclusion, OracleError, VisSet};
use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::{recv_msg_block, send_msg, thread, ConsType, Config};

type Prog = Arc<dyn Fn() + Send + Sync>;

fn cfg() -> Config {
    Config::builder().with_cons_type(ConsType::FIFO).build()
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

fn names(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

/// `ex:traces`' program, verbatim:
///
/// ```text
/// A: send^p2p(C,1)  ‖  B: send^p2p(C,2)  ‖  C: x := recv^p2p()
/// ```
///
/// The draft: six traces (`ex:traces`), two graphs (`ex:graphs`).
fn ex_traces() -> Prog {
    Arc::new(|| {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, 1i32));
        let _b = named("b", move || send_msg(cid, 2i32));
    })
}

/// Render a `VisSet` as a sorted set of `name:obs` strings, **for assertion
/// messages and for comparing against the paper's own notation only**.
///
/// Never used as the equality relation — that is `VisWord`'s `PartialEq`,
/// which goes through `Obs::eq` and so through `msg_equals`. Rendering here is
/// a convenience for the human reading a failure, exactly the role criterion 1
/// leaves to `canonical_vis`.
fn render(set: &VisSet) -> Vec<String> {
    let mut out: Vec<String> = set
        .iter()
        .map(|w| {
            let word = w
                .word
                .iter()
                .map(|e| {
                    // The paper's own notation: <snd,A,1> / <rcv,C,2>.
                    // Rendering only — never the equality relation.
                    use crate::conformance::obs::Obs;
                    match &e.obs {
                        Obs::Send(v) => format!("<snd,{},{:?}>", e.thread, v.val),
                        Obs::Recv(None) => format!("<rcv,{},bot>", e.thread),
                        Obs::Recv(Some(v)) => format!("<rcv,{},{:?}>", e.thread, v.val),
                    }
                })
                .collect::<Vec<_>>()
                .join("·");
            let st = w
                .statuses
                .iter()
                .map(|(k, v)| format!("{k}={v:?}"))
                .collect::<Vec<_>>()
                .join(",");
            format!("[{word}] {{{st}}}")
        })
        .collect();
    out.sort();
    out
}

// ===========================================================================
// Collect-mode harness.
//
// The oracle's own `vis_of_program` hides the capture hook behind a `VisSet`,
// so group C and group D drive the hook directly: they are about *which
// graphs* are captured and what labels they carry, which is a question no
// `VisSet` can answer.
// ===========================================================================

/// What one ungated collect run produced.
struct Run {
    graphs: Vec<ExecutionGraph>,
    stats: crate::Stats,
    reports: usize,
    collect_errors: Vec<(String, Event)>,
}

/// Run `p` ungated under [`ConfMode::Collect`], optionally collecting.
///
/// Built through `Must::enable_conformance`, which is criterion 3's obligation
/// rather than a convenience: it is what runs `assert_config_in_scope`, arms
/// §9's handler guards and forces `keep_going_after_error = true`, and T6's
/// ending is unreachable without that last one.
fn collect_run(config: Config, visible: &[String], p: Prog, collecting: bool) -> Run {
    use std::cell::RefCell;
    use std::rc::Rc;

    let must = Rc::new(RefCell::new(Must::new(config.clone(), false)));
    {
        let mut ctx = ConfCtx::gate_disabled(config, visible.to_vec(), ConfMode::Collect);
        if collecting {
            ctx.collect_graphs();
        }
        must.borrow_mut().enable_conformance(ctx);
    }
    {
        let _guard = crate::conformance::testing::CurrentMustGuard;
        let f = Arc::new(move || p());
        crate::explore(&must, &f);
    }
    let must_ref = must.borrow();
    let ctx = must_ref.conf_ctx().expect("conformance: context went missing");
    Run {
        graphs: ctx.collected().to_vec(),
        stats: must_ref.stats(),
        reports: ctx.reports().len(),
        collect_errors: ctx.collect_errors().to_vec(),
    }
}

/// The same, with the **gate on** — a real `ConfCtx::new` with a probe worker,
/// which is what T7 and T8 compare against.
fn gated_collect_run(config: Config, visible: &[String], imp: Prog, spec: Prog) -> Vec<String> {
    use std::cell::RefCell;
    use std::rc::Rc;

    let mut ctx = ConfCtx::new(
        config.clone(),
        spec,
        visible.to_vec(),
        crate::conformance::config::DEFAULT_SEARCH_BUDGET,
        false,
    );
    ctx.collect_graphs();
    let must = Rc::new(RefCell::new(Must::new(config, false)));
    must.borrow_mut().enable_conformance(ctx);
    {
        let f = Arc::new(move || imp());
        crate::explore(&must, &f);
    }
    must.borrow_mut().conf_shutdown();
    let must_ref = must.borrow();
    let ctx = must_ref.conf_ctx().expect("conformance: context went missing");
    let mut out: Vec<String> = ctx.collected().iter().map(|g| format!("{g}")).collect();
    out.sort();
    out
}

/// A graph carrying `Block(ConfPrune)` on any thread — the label §4.2's prune
/// writes into *every* thread, and the one no ungated run may produce.
fn has_conf_prune(g: &ExecutionGraph) -> bool {
    g.thread_ids().into_iter().any(|t| {
        (0..g.thread_size(t) as u32).any(|i| {
            matches!(
                g.label(Event::new(t, i)),
                LabelEnum::Block(b) if matches!(b.btype(), BlockType::ConfPrune)
            )
        })
    })
}

/// The statuses of one captured graph, by the §6.3 row-scan rule.
fn statuses_of(g: &ExecutionGraph, visible: &[String]) -> std::collections::BTreeMap<String, Status> {
    let exec = CompleteExecution::try_finished(g).expect("captured graphs are final");
    let w = wobs(g, visible).expect("extraction");
    statuses(exec, &w, visible).expect("statuses")
}

// ===========================================================================
// Group A --- the object. `vis(G)` is the set of linear extensions of `vo(G)`
// over the alphabet `(declared thread name, Obs)` (criterion 1).
// ===========================================================================

/// **`ex:vis`, all three threads visible.** The draft states a cardinality and
/// one member: "its six traces have six distinct visible traces, among them
/// `⟨snd,A,1⟩·⟨snd,B,2⟩·⟨rcv,C,1⟩`".
///
/// Six words out of **two** graphs is the whole point: `Graphs(P)` has two
/// members and DPOR explores one execution each, so the six can only come from
/// enumerating linear extensions of `vo`.
///
/// Membership is asserted as well as cardinality — the draft publishes one
/// member and a test that only counts would pass on six wrong words.
///
/// To break it (all measured): return one canonical linearisation per graph
/// (6 → 2); take `vo` as the extraction order rather than `porf` (6 → 2); an
/// off-by-one in the extension enumerator's terminal test (6 → 4).
#[test]
fn a1_ex_vis_all_visible_has_six_words() {
    let vis = names(&["a", "b", "c"]);
    let set = vis_of_program(cfg(), &vis, move || ex_traces()()).expect("oracle");
    let got = render(&set);
    assert_eq!(
        set.len(),
        6,
        "conformance: ex:vis publishes six distinct visible traces; got:\n{got:#?}"
    );
    assert!(
        got.contains(&"[<snd,a,1>·<snd,b,2>·<rcv,c,1>] {a=Done,b=Done,c=Done}".to_string()),
        "conformance: the draft names this member of the six; got:\n{got:#?}"
    );
}

/// **`ex:vis`, `B` invisible — the only element-by-element check against a
/// published set in the project.** The draft says "only three remain" and
/// lists them:
///
/// ```text
/// ⟨snd,A,1⟩·⟨rcv,C,1⟩
/// ⟨snd,A,1⟩·⟨rcv,C,2⟩
/// ⟨rcv,C,2⟩·⟨snd,A,1⟩
/// ```
///
/// Re-derived rather than transcribed: deleting `s_B` from `ex:traces`' six
/// traces gives `w₁, w₃, w₁, w₁, w₂, w₂`, three distinct. The third puts the
/// **receive before the send**, which exists only because deleting `B` leaves
/// the two `vo`-incomparable — criterion 1's blocker exhibited at size two.
///
/// To break it: return one linearisation per graph (loses `w₃`, 3 → 2); take
/// `vo` as the extraction order rather than `porf` (3 → 2); an off-by-one in
/// the terminal test (3 → 2). All three measured.
///
/// **Not** broken by dropping the thread component, which revision 1 of this
/// file claimed: measured, it still passes. `w₂ = ⟨snd,1⟩·⟨rcv,2⟩` and
/// `w₃ = ⟨rcv,2⟩·⟨snd,1⟩` stay distinct as sequences of bare `Obs`, because
/// `Send` and `Recv` are different variants. The thread component is tested by
/// `a3` instead, which needs two visible threads to exercise it at all.
#[test]
fn a2_ex_vis_with_b_invisible_is_exactly_the_papers_three_words() {
    let vis = names(&["a", "c"]);
    let set = vis_of_program(cfg(), &vis, move || ex_traces()()).expect("oracle");

    let got = render(&set);
    assert_eq!(
        set.len(),
        3,
        "conformance: the draft lists exactly three; got:\n{got:#?}"
    );
    assert!(
        set.iter()
            .all(|w| w.statuses.values().all(|s| *s == Status::Done)),
        "conformance: both visible threads run to completion in every execution"
    );

    let mut want = vec![
        "[<snd,a,1>·<rcv,c,1>] {a=Done,c=Done}".to_string(),
        "[<snd,a,1>·<rcv,c,2>] {a=Done,c=Done}".to_string(),
        "[<rcv,c,2>·<snd,a,1>] {a=Done,c=Done}".to_string(),
    ];
    want.sort();
    assert_eq!(
        got, want,
        "conformance: ex:vis's published set, element by element"
    );
}

/// **The thread component of the alphabet is load-bearing** — criterion 1's
/// third required test, which revision 1 of this file did not have.
///
/// Two *visible* threads each send the **same value** to one invisible sink,
/// with no `porf` path between them. The two interleavings are two words, and
/// they differ in **nothing but which thread observed what**: without the
/// thread component `⟨snd,1⟩·⟨snd,1⟩` is one word, and criterion 1's
/// permissive collapse has happened.
///
/// `obs.rs:36-47` drops the thread component deliberately, and scopes its own
/// justification to comparisons "the algorithm performs". The oracle is not
/// the matching — a `vis` word interleaves threads — so this is the first
/// thing to violate that precondition, and this test is what says so.
///
/// To break it: drop the thread component from `Elem`'s equality (2 → 1).
/// Measured.
#[test]
fn a3_two_visible_threads_interleaving_is_not_conflated() {
    let vis = names(&["p", "q"]);
    let set = vis_of_program(cfg(), &vis, || {
        let sink = named("sink", || {
            let _x: i32 = recv_msg_block();
            let _y: i32 = recv_msg_block();
        });
        let sid = sink.thread().id();
        let _p = named("p", move || send_msg(sid, 1i32));
        let _q = named("q", move || send_msg(sid, 1i32));
    })
    .expect("oracle");

    let got = render(&set);
    assert_eq!(
        set.len(),
        2,
        "conformance: two vo-incomparable visible sends of the same value are two \
         words, distinguished only by the thread; got:\n{got:#?}"
    );
    let mut want = vec![
        "[<snd,p,1>·<snd,q,1>] {p=Done,q=Done}".to_string(),
        "[<snd,q,1>·<snd,p,1>] {p=Done,q=Done}".to_string(),
    ];
    want.sort();
    assert_eq!(got, want, "conformance: both interleavings, and only those");
}

/// **Comparison is `Obs::eq`, never rendered text** — criterion 1's second
/// required test, which revision 1 of this file did not have.
///
/// `1u32` and `1i64` both render `1` through `report::obs_text`, which is
/// `{:?}` of the user's message type. `Obs::eq` goes through `msg_equals`,
/// which downcasts and so answers **false** across types. Text comparison
/// conflates them, in the permissive direction, and couples the oracle's
/// verdict to the report renderer.
///
/// To break it: compare rendered strings in `Elem`'s equality — the two words
/// then match and inclusion holds. Measured.
#[test]
fn a4_same_debug_rendering_different_rust_types_are_not_conflated() {
    let vis = names(&["a"]);
    let imp = || {
        let sink = named("sink", || {
            let _x: u32 = recv_msg_block();
        });
        let sid = sink.thread().id();
        let _a = named("a", move || send_msg(sid, 1u32));
    };
    let spec = || {
        let sink = named("sink", || {
            let _x: i64 = recv_msg_block();
        });
        let sid = sink.thread().id();
        let _a = named("a", move || send_msg(sid, 1i64));
    };
    assert!(
        matches!(
            includes(cfg(), &vis, imp, spec).expect("oracle"),
            Inclusion::Fails { .. }
        ),
        "conformance: 1u32 and 1i64 render identically and are not the same observation"
    );
}

/// **The union in `vis(P) = ⋃_G vis(G)` is a set, not a multiset.**
///
/// `ex:vis` does *not* test this: under the linear-extension algorithm its two
/// graphs contribute 1 and 2 words and none collide, because the receive's
/// observed value differs. The paper's "six traces collapse onto three words"
/// is a property of the *trace* definition, not this one.
///
/// So dedup needs a cross-graph fixture: two **invisible** senders sending the
/// **same** value to one visible receiver. Both graphs yield `⟨rcv,C,7⟩`, so
/// the union must collapse them to one.
///
/// To break it: accumulate into a `Vec` without the membership test (1 → 2).
/// Measured.
#[test]
fn a5_the_union_over_graphs_deduplicates_across_graphs() {
    let vis = names(&["c"]);
    let set = vis_of_program(cfg(), &vis, || {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let _s1 = named("s1", move || send_msg(cid, 7i32));
        let _s2 = named("s2", move || send_msg(cid, 7i32));
    })
    .expect("oracle");
    assert_eq!(
        set.len(),
        1,
        "conformance: two graphs, one word --- the union deduplicates; got:\n{:#?}",
        render(&set)
    );
}

/// **The oracle at the generator's size cap** — ground truth validated at two
/// events is ground truth used at twenty.
///
/// Two visible threads of three mutually `vo`-incomparable events each gives
/// `(3+3)!/(3!·3!) = 20` linear extensions. The number is hand-derived and
/// independent of the enumeration code.
///
/// To break it: an off-by-one in the enumerator's **candidate scan**
/// (`0..items.len()-1`), which makes every set empty (20 → 0); or accumulating
/// without the membership test (20 → 400). Both measured.
///
/// **Not** broken by an off-by-one in the *terminal* test
/// (`chosen.len() + 1 >= items.len()`): measured, it still passes, because
/// each length-5 prefix of a 6-element word determines the word, so the count
/// is unchanged. Revision 1 of this file claimed "any off-by-one" breaks it;
/// that is false as stated, and the two mutations above are what stands.
#[test]
fn a6_twenty_linear_extensions_at_the_grammar_cap() {
    let vis = names(&["p", "q"]);
    let set = vis_of_program(cfg(), &vis, || {
        let sink = named("sink", || {
            for _ in 0..6 {
                let _x: i32 = recv_msg_block();
            }
        });
        let sid = sink.thread().id();
        // `p` and `q` each send three times to an invisible sink. Nothing
        // relates a `p` event to a `q` event by `po` or `rf`, so `vo` orders
        // only within each thread: 3 + 3 events, C(6,3) = 20 interleavings.
        let _p = named("p", move || {
            for i in 0..3 {
                send_msg(sid, 10i32 + i);
            }
        });
        let _q = named("q", move || {
            for i in 0..3 {
                send_msg(sid, 20i32 + i);
            }
        });
    })
    .expect("oracle");
    assert_eq!(
        set.len(),
        20,
        "conformance: (3+3)!/(3!·3!) = 20 linear extensions of vo"
    );
}

/// **Criterion 1's own witness: a pure-(M2) failing pair whose two canonical
/// representatives coincide.** Revision 1 of this file did not have it, and it
/// is the blocker the criterion was written around.
///
/// ```text
/// Impl ≝ A: send(D,1) ‖ R: send(C,9) ‖ C: x := recv()
/// Spec ≝ A: send(R,1) ‖ R: y := recv(); send(C,9) ‖ C: x := recv()
/// ```
///
/// with `Tvis = {A, C}` and `D`, `R` invisible. Both sides observe
/// `⟨snd,A,1⟩` and `⟨rcv,C,9⟩` and both are `done`. In `Impl` no `porf` path
/// relates the two visible events, so `vis(G_Impl) = {s_A·r_C, r_C·s_A}`; in
/// `Spec` `porf` runs `s_A → R.recv → R.send → r_C`, so
/// `vis(G_Spec) = {s_A·r_C}`. Inclusion therefore **fails**, with `r_C·s_A` as
/// the witness — and a representative-based oracle answers "holds", because
/// the representatives are identical.
///
/// The reverse direction is asserted too, and it is criterion 5's
/// **non-reflexive positive**: `vis(Spec) ⊆ vis(Impl)` holds strictly, the two
/// programs are not isomorphic, and an oracle that always answered "fails"
/// would be caught here.
///
/// To break it: return one canonical linearisation per graph — the failing
/// direction becomes `Holds`. Measured.
#[test]
fn a7_criterion_1s_pure_m2_witness_fails_and_its_converse_holds() {
    let vis = names(&["a", "c"]);
    let imp = || {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        // `d` is the sink that makes `a`'s send lead nowhere.
        let d = named("d", || {
            let _x: i32 = recv_msg_block();
        });
        let did = d.thread().id();
        let _r = named("r", move || send_msg(cid, 9i32));
        let _a = named("a", move || send_msg(did, 1i32));
    };
    let spec = || {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let r = named("r", move || {
            let _y: i32 = recv_msg_block();
            send_msg(cid, 9i32);
        });
        let rid = r.thread().id();
        let _a = named("a", move || send_msg(rid, 1i32));
    };

    match includes(cfg(), &vis, imp, spec).expect("oracle") {
        Inclusion::Holds => panic!(
            "conformance: the draft's pure-(M2) failing pair must not be reported as holding"
        ),
        Inclusion::Fails { witness } => {
            let w: Vec<String> = witness
                .word
                .iter()
                .map(|e| {
                    use crate::conformance::obs::Obs;
                    match &e.obs {
                        Obs::Send(_) => format!("snd,{}", e.thread),
                        Obs::Recv(_) => format!("rcv,{}", e.thread),
                    }
                })
                .collect();
            assert_eq!(
                w,
                vec!["rcv,c".to_string(), "snd,a".to_string()],
                "conformance: the witness is the receive-before-send word, which only \
                 vo-incomparability produces"
            );
        }
    }

    // Non-reflexive positive: the specification is strictly more ordered, so
    // its one word is among the implementation's two.
    assert!(
        matches!(
            includes(cfg(), &vis, spec, imp).expect("oracle"),
            Inclusion::Holds
        ),
        "conformance: vis(Spec) is a strict subset of vis(Impl), so this direction holds"
    );
}

// ===========================================================================
// Group B --- the paper's published answers (criterion 4).
// ===========================================================================

/// **`ex:graphs`: the program has two graphs.** A published *count*, and the
/// first thing collect mode should be asked, because the number is not six: a
/// hook firing per trace, per linearisation, or twice per execution is caught
/// here immediately. This is criterion 3's **T4**.
///
/// To break it: record at all five `Gate` sites instead of `Gate::Completion`
/// (2 → 6). Measured.
#[test]
fn b1_ex_graphs_collect_mode_sees_exactly_two_graphs() {
    let vis = names(&["a", "b", "c"]);
    let run = collect_run(cfg(), &vis, ex_traces(), true);
    assert_eq!(
        run.graphs.len(),
        2,
        "conformance: ex:graphs publishes two graphs for ex:traces' program"
    );
}

/// **`ex:relay`, and `ex:morph`'s base pair: refinement holds.**
///
/// The draft fixes the orientation at `ref2.tex:464` — `P₂` (with the relay)
/// is the **implementation**, `P₁` (direct) the **specification** — and states
/// `G₁ ⊑ G₂`. By Thm. morph that is `vis(Impl) ⊆ vis(Spec)`.
///
/// Both directions are asserted, because `ex:relay` publishes
/// `vis(P₁) = vis(P₂)`: the direct form already orders the send before the
/// receive through its own `rf` edge, so inserting a relay changes nothing.
///
/// To break it: include the send's **destination** in the word element — the
/// relay then makes `main`'s send a different observation on the two sides.
/// Measured.
///
/// **Not** broken by comparing rendered text instead of `Obs::eq`: measured,
/// it still passes, and revision 1 of this file claimed otherwise. Both sides
/// render identically here, which is precisely why the text mutation needs its
/// own fixture — `a4`.
#[test]
fn b2_ex_relay_inclusion_holds_both_ways() {
    let vis = names(&["main", "c"]);
    let relay_impl = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let r = named("r", move || {
            let v: i32 = recv_msg_block();
            send_msg(cid, v);
        });
        send_msg(r.thread().id(), 1i32);
    };
    let relay_spec = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    };

    assert!(
        matches!(
            includes(cfg(), &vis, relay_impl, relay_spec).expect("oracle"),
            Inclusion::Holds
        ),
        "conformance: ex:morph states G1 <= G2 for the relay pair"
    );
    assert!(
        matches!(
            includes(cfg(), &vis, relay_spec, relay_impl).expect("oracle"),
            Inclusion::Holds
        ),
        "conformance: ex:relay publishes vis(P1) = vis(P2), so it holds the other way too"
    );
}

/// **`ex:morph`'s (M1) variation: replace the `1` that `A` sends by `2`.**
/// Published answer: (M1) fails, so inclusion fails.
///
/// To break it: make the word element value-blind — compare only the
/// observation's kind (`snd`/`rcv`) and not its value. Measured.
///
/// Revision 1 of this file named "compare `Debug` renderings" here and then
/// observed in the same sentence that `1` and `2` still differ as text, so the
/// named mutation could not fail the test: criterion 19 was undischarged for
/// it. The type-blindness case it was reaching for is `a4`.
#[test]
fn b3_ex_morph_m1_variation_fails() {
    let vis = names(&["main", "c"]);
    let imp = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    };
    let spec = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 2i32);
    };
    assert!(
        matches!(
            includes(cfg(), &vis, imp, spec).expect("oracle"),
            Inclusion::Fails { .. }
        ),
        "conformance: the send is observed <snd,A,1> on one side and <snd,A,2> on the other"
    );
}

/// **`ex:morph`'s (M3) variation, in the draft's own orientation.**
///
/// The draft: "let `C` in **`P₁`** perform a second blocking receive that
/// nothing can satisfy … `C` is blocked in the **specification** and done in
/// the implementation, so (M3) fails." `P₁` is the *specification*, and the
/// base pair is the **relay** pair.
///
/// The project's existing `blocking_impl`/`blocking_spec` fixture is the
/// mirror of this on both axes — extra receive in the implementation, direct
/// pair with no relay. Both are genuine (M3) mismatches; this is the one the
/// paper publishes.
///
/// The blocked second receive contributes **no observation** (it rests at a
/// `Block(Value)`, not a `Recv`), so the two sides' *words* agree and the
/// statuses are the only difference. That is what makes this a status-only
/// test rather than a word test.
///
/// To break it: drop the statuses from `VisWord`'s equality — the words then
/// agree and the pair compares equal. Measured.
#[test]
fn b4_ex_morph_m3_variation_in_the_papers_orientation_fails() {
    let vis = names(&["main", "c"]);
    // P2, the implementation: the relay chain, C receives once and is done.
    let imp = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let r = named("r", move || {
            let v: i32 = recv_msg_block();
            send_msg(cid, v);
        });
        send_msg(r.thread().id(), 1i32);
    };
    // P1, the specification, with C left on a receive nothing can satisfy.
    let spec = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
            let _w: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    };
    assert!(
        matches!(
            includes(cfg(), &vis, imp, spec).expect("oracle"),
            Inclusion::Fails { .. }
        ),
        "conformance: C is blocked in the specification and done in the implementation"
    );
}

// ===========================================================================
// Group C --- the capture hook, criterion 3's T1--T9.
//
// T4 is `b1` above. Two of criterion 3's obligations are marked there as
// review-only and have no test here, deliberately: "`pub(crate)` and ungated,
// not `#[cfg(test)]`" cannot be asserted from a test, because `cfg(test)` is
// true where the test lives and `tests/*.rs` cannot reach a `pub(crate)` item;
// and "read back without a new `Must` method" is a compile-time fact. Both are
// discharged by review plus an ordinary `cargo build`.
// ===========================================================================

/// **T1 — the hook is inert when unused.**
///
/// Collect off gives the same `Stats` as the same program with no conformance
/// context at all, and `collected()` is empty.
///
/// The second half is the discriminating one. To break it: turn collect on by
/// default in `ConfCtx::gate_disabled` (`collected: Some(Vec::new())`).
/// Measured.
///
/// The five-site mutation is deliberately **not** named here: with collect off
/// nothing records whether or not the `Gate::Completion` guard is present, so
/// inertness is identical under both shapes and that pairing is undischargeable
/// (criterion 3's own note; the developer's D-1). The count is T2's business.
#[test]
fn c1_t1_the_hook_is_inert_when_collect_is_off() {
    use std::cell::RefCell;
    use std::rc::Rc;

    let vis = names(&["a", "b", "c"]);
    let off = collect_run(cfg(), &vis, ex_traces(), false);
    assert!(
        off.graphs.is_empty(),
        "conformance: collect is off, so nothing may be captured; got {}",
        off.graphs.len()
    );

    // The same program with no conformance context at all.
    let plain = {
        let must = Rc::new(RefCell::new(Must::new(cfg(), false)));
        let p = ex_traces();
        let f = Arc::new(move || p());
        {
            let _guard = crate::conformance::testing::CurrentMustGuard;
            crate::explore(&must, &f);
        }
        let s = must.borrow().stats();
        s
    };
    assert_eq!(
        (off.stats.execs, off.stats.block),
        (plain.execs, plain.block),
        "conformance: a non-collecting gate-disabled run explores what a plain run explores"
    );
}

/// **T2 — the captured count is `Stats.execs + Stats.block`, exactly.**
///
/// The equality is exact because `is_consistent` is **vacuous in conformance
/// scope** (F38: `Checker::is_consistent` skips every send that is not
/// `TotalOrder`, and `TotalOrder` is refused twice over here), so every
/// execution increments one of the two counters. If `TotalOrder` ever enters
/// scope the equality lapses and this test is the place that says so.
///
/// Asserted on three programs: `ex:traces` (fresh sends, a fresh receive and a
/// backward revisit), a relay chain, and a deadlocking program whose ending is
/// counted in `block` rather than `execs`.
///
/// To break it: drop the `gate == Gate::Completion` discriminant, so the hook
/// records at all five call sites. Measured — on `ex:traces` the count goes
/// 2 → 6 while `execs + block` stays 2.
///
/// **What this test does not assert**, and could not: that the program
/// exercised all four `Gate` kinds. `ConfCtx` has no per-gate counter and
/// adding one would be a production change, so the evidence that the extra
/// sites fire is the mutant's count (6 against 2), reported rather than
/// asserted.
#[test]
fn c2_t2_captured_count_equals_execs_plus_block() {
    let cases: Vec<(&str, Vec<String>, Prog)> = vec![
        ("ex:traces", names(&["a", "b", "c"]), ex_traces()),
        (
            "relay",
            names(&["main", "c"]),
            Arc::new(|| {
                let c = named("c", || {
                    let _v: i32 = recv_msg_block();
                });
                let cid = c.thread().id();
                let r = named("r", move || {
                    let v: i32 = recv_msg_block();
                    send_msg(cid, v);
                });
                send_msg(r.thread().id(), 1i32);
            }),
        ),
        (
            "deadlock",
            names(&["c"]),
            Arc::new(|| {
                let _c = named("c", || {
                    let _v: i32 = recv_msg_block();
                });
            }),
        ),
    ];
    for (label, vis, p) in cases {
        let run = collect_run(cfg(), &vis, p, true);
        assert_eq!(
            run.graphs.len(),
            run.stats.execs + run.stats.block,
            "conformance: {label}: one capture per execution ending, and \
             is_consistent is vacuous in scope (F38), so the equality is exact"
        );
    }
}

/// **T3 — every captured graph is final.**
///
/// Def. visg is defined only "for `G` with `next_P(G) = ∅`", and the draft says
/// it again: "a graph that still admits an event has neither a status nor a set
/// of visible traces". `CompleteExecution::try_finished` is the crate's own
/// recognition of the same precondition.
///
/// This fails the five-site mutation by **kind** where T2 fails it by **count**,
/// and the two read differently: T2 says "too many", T3 says "not graphs of the
/// right sort". Measured — under the mutation, `try_finished` returns `None` on
/// the mid-execution captures.
#[test]
fn c3_t3_every_captured_graph_is_final() {
    let vis = names(&["a", "b", "c"]);
    let run = collect_run(cfg(), &vis, ex_traces(), true);
    assert!(!run.graphs.is_empty(), "conformance: nothing was captured");
    for (i, g) in run.graphs.iter().enumerate() {
        assert!(
            CompleteExecution::try_finished(g).is_some(),
            "conformance: captured graph {i} still admits an event, so Def. visg \
             does not apply to it --- the hook fired somewhere other than the \
             completion gate"
        );
    }
}

/// **T5 — a deadlocking program has that ending captured, and a visible
/// thread's extracted `Status` is `Blocked`.**
///
/// The predicate matters: criterion 2(a) requires the blocked class, and a test
/// that only counted graphs would be satisfied by capturing the ending and
/// misclassifying it. `Gate::outer_complete` is deliberately `true` for blocked
/// endings, and the gate precedes `check_blocked` in `complete_execution`.
///
/// To break it: capture only endings where the graph is not blocked
/// (`gate == Gate::Completion && g1.check_blocked().is_none()`), which is
/// "gate only on all-threads-completed". Measured.
#[test]
fn c4_t5_a_deadlock_ending_is_captured_and_reads_blocked() {
    let vis = names(&["c"]);
    let run = collect_run(
        cfg(),
        &vis,
        Arc::new(|| {
            let _c = named("c", || {
                let _v: i32 = recv_msg_block();
            });
        }),
        true,
    );
    assert_eq!(
        run.graphs.len(),
        1,
        "conformance: the one deadlocking execution is captured"
    );
    assert_eq!(
        run.stats.block, 1,
        "conformance: and the engine counts it as blocked, not as a completed exec"
    );
    let st = statuses_of(&run.graphs[0], &vis);
    assert_eq!(
        st["c"],
        Status::Blocked,
        "conformance: the visible thread rests on a receive nothing can satisfy"
    );
}

/// **T6 — a failed assertion is captured, and the status extracts `Errored` by
/// the row-scan rule rather than the last-label rule.**
///
/// Two preconditions, both named because the ending is unreachable without
/// them. `enable_conformance` forces `keep_going_after_error = true`, so the
/// engine does not stop at the failure. And per §6.3/**F28**,
/// `traceforge::assert` installs its `Block(Assert)` *without* a `switch()`,
/// so the thread can append `End` after it and the execution still counts as
/// complete — a row reading `… BLK Assert, END`.
///
/// So the test asserts the F28 shape directly: the thread's **last** label is
/// `End`, not a `Block`, and the status is nevertheless `Errored`. A test that
/// only counted graphs would pass for the wrong reason.
///
/// To break it: replace `status_of`'s whole-row scan with a look at the last
/// label — the status becomes `Done`. Measured.
#[test]
fn c5_t6_a_failed_assertion_reads_errored_by_row_scan() {
    let vis = names(&["w"]);
    let run = collect_run(
        cfg(),
        &vis,
        Arc::new(|| {
            let _w = named("w", || {
                crate::assert(false);
            });
        }),
        true,
    );
    assert_eq!(run.graphs.len(), 1, "conformance: one execution, captured");
    let g = &run.graphs[0];

    let w = wobs(g, &vis).expect("extraction");
    let tid = w.row("w").and_then(|r| r.thread()).expect("w resolved");
    assert!(
        matches!(g.thread_last(tid), Some(LabelEnum::End(_))),
        "conformance: F28 --- assert installs its Block without yielding, so the row \
         ends `BLK Assert, END` and a last-label rule would call this thread done; \
         row last label was {:?}",
        g.thread_last(tid)
    );

    let st = statuses_of(g, &vis);
    assert_eq!(
        st["w"],
        Status::Errored,
        "conformance: the row scan finds the Block(Assert) that the last label hides"
    );
}

/// **T7 — on a conforming pair, the gated run's captured set equals the
/// ungated run's.**
///
/// This is decision C's headline equality, and criterion 3 derives it rather
/// than pinning it: on a run that produces **no report**, `pruned` is never
/// set, `conf_prune` never runs, and the gated run explores exactly what the
/// ungated run explores.
///
/// **T7 alone protects nothing**, and that is criterion 3's own finding (the
/// developer's D-6): it is *inert* under the mutation that moves the hook below
/// `ctx.rs`'s `if self.pruned` return, because on a no-report run `pruned` is
/// never set. `c7` is the companion that catches that. This test is kept
/// because the equality is the design's claim and nothing else states it.
#[test]
fn c6_t7_on_a_conforming_pair_the_gated_set_equals_the_ungated_set() {
    let vis = names(&["main", "c"]);
    let relay_impl: Prog = Arc::new(|| {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let r = named("r", move || {
            let v: i32 = recv_msg_block();
            send_msg(cid, v);
        });
        send_msg(r.thread().id(), 1i32);
    });
    let relay_spec: Prog = Arc::new(|| {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    });

    let gated = gated_collect_run(cfg(), &vis, relay_impl.clone(), relay_spec);
    let ungated = {
        let mut v: Vec<String> = collect_run(cfg(), &vis, relay_impl, true)
            .graphs
            .iter()
            .map(|g| format!("{g}"))
            .collect();
        v.sort();
        v
    };
    assert_eq!(
        gated, ungated,
        "conformance: no report means no prune, so the two runs explore the same graphs"
    );
}

/// **T8 — on a *reporting* pair, the `Block(ConfPrune)`-truncated graph is
/// present in the gated set.**
///
/// This is the half of criterion 3's block quote that is otherwise a claim with
/// no test: on a reporting run the two sets are **incomparable**, the gated run
/// gaining one truncated graph per pruned execution. It is also the only test
/// that protects the hook's placement above `ctx.rs`'s `if self.pruned` return,
/// which T7 cannot (see `c6`).
///
/// To break it: move the capture below that return. Measured.
#[test]
fn c7_t8_a_reporting_run_keeps_its_confprune_truncated_graph() {
    let vis = names(&["main", "c"]);
    // A pair the tool reports on: the implementation sends 1, the
    // specification sends 2, so (M1) fails at the first visible event.
    let imp: Prog = Arc::new(|| {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    });
    let spec: Prog = Arc::new(|| {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 2i32);
    });

    use std::cell::RefCell;
    use std::rc::Rc;
    let mut ctx = ConfCtx::new(
        cfg(),
        spec,
        vis.clone(),
        crate::conformance::config::DEFAULT_SEARCH_BUDGET,
        false,
    );
    ctx.collect_graphs();
    let must = Rc::new(RefCell::new(Must::new(cfg(), false)));
    must.borrow_mut().enable_conformance(ctx);
    {
        let f = Arc::new(move || imp());
        crate::explore(&must, &f);
    }
    must.borrow_mut().conf_shutdown();
    let must_ref = must.borrow();
    let c = must_ref.conf_ctx().expect("conformance: context went missing");
    assert!(
        !c.reports().is_empty(),
        "conformance: the fixture must actually report, or this test is vacuous"
    );
    assert!(
        c.collected().iter().any(has_conf_prune),
        "conformance: the gated run captures the pruned execution's truncated graph, \
         which is what places the hook above the `pruned` early return"
    );
}

/// **T9 — a panicking program leaves no stale `Must`, and the next program
/// runs clean.**
///
/// `explore` and `explore_with_pool` both call `Must::set_current(Some(..))`
/// and **neither clears it**, so a corpus run that puts a panicking program
/// next to a clean one leaves a stale `Must` in the thread-local. The oracle
/// uses `explore`, and guards it with `CurrentMustGuard`.
///
/// To break it: delete the `CurrentMustGuard` binding from
/// `oracle::vis_of_program` — the **first** assertion below fails, because the
/// panic unwinds out of `explore` with the thread-local still pointing at the
/// dead run's `Must`. Measured.
///
/// **The second assertion is measured *not* to discriminate**, and that is
/// recorded rather than hidden (criterion 19's what-was-attempted rule).
/// Criterion 3 words T9 as "the second must not observe a stale `Must`", and
/// with the guard removed the clean run still passes: `explore` calls
/// `set_current(Some(..))` before anything reads the thread-local, so it
/// overwrites the stale pointer rather than tripping over it. The observable
/// consequence of the missing guard is therefore the *leak itself*, not a
/// second run's behaviour, and that is what the first assertion pins. What the
/// leak costs is a `Must` — and its probe worker thread — kept alive on the
/// thread-local past the end of its run; a consequence test would need a
/// reader between `Must::new` and `explore`, and `vis_of_program` has none.
#[test]
fn c8_t9_a_panicking_program_leaves_no_stale_must() {
    let vis = names(&["a"]);
    let boom = std::panic::catch_unwind(|| {
        vis_of_program(cfg(), &vis, || {
            let _a = named("a", || panic!("deliberate: the corpus contains bad programs"));
        })
    });
    assert!(
        boom.is_err(),
        "conformance: the panicking program must unwind out of the oracle, or this \
         test is not exercising the guard at all"
    );
    assert!(
        Must::current().is_none(),
        "conformance: the panicking run left its Must in the thread-local --- \
         CurrentMustGuard is what clears it, and explore does not"
    );

    // And the next program runs. Not a discriminator (see the doc comment);
    // kept because it is criterion 3's own wording of T9.
    let set = vis_of_program(cfg(), &vis, || {
        let sink = named("sink", || {
            let _x: i32 = recv_msg_block();
        });
        let sid = sink.thread().id();
        let _a = named("a", move || send_msg(sid, 1i32));
    })
    .expect("conformance: the clean run must not observe a stale Must");
    assert_eq!(
        set.len(),
        1,
        "conformance: one visible send, one word --- unaffected by the panicking run"
    );
}

// ===========================================================================
// Group D --- the B1 fix (Poll 3, route 1).
// ===========================================================================

/// **A declared *visible* thread's failed assertion is captured without
/// pruning.** Criterion 3's required test for the B1 resolution.
///
/// B1: `conf_assert_failure` consults neither the probe, nor the worker, nor
/// the mode, and `ConfCtx::report_visible_error` tests only `self.pruned`. So
/// an *ungated* run still reports and prunes on a visible thread's assertion
/// failure, and `conf_prune` appends `Block(ConfPrune)` to **every** thread —
/// corrupting every *other* visible thread's status and word, and ending the
/// execution, which under-approximates `vis(P)` in the permissive direction.
///
/// **Why the obvious test does not discriminate.** The count equality
/// (`collected == execs + block`) holds while the contents are wrong, and a
/// test written with an *invisible* assertion takes `record_invisible_error`,
/// which never pruned in the first place — it passes while the visible case
/// stays broken. So the assertions here are about **contents**:
///
/// 1. no captured graph carries a `Block(ConfPrune)` label on any thread;
/// 2. the sibling visible thread's row is **complete** — both of its sends are
///    in the word — rather than truncated by `stop()`;
/// 3. the errored thread's status extracts `Errored` by row scan;
/// 4. `ctx.reports()` is empty;
/// 5. exactly one recorded error, carrying the **declared** visible name `w`
///    and not `lib.rs`'s runtime task name.
///
/// To break it: revert `Collect`'s arm in `report_visible_error` to return
/// `Prune`. Measured; the count assertion still passes under the mutation,
/// which is the demonstration that the count was never the discriminator.
#[test]
fn d1_a_visible_assertion_failure_under_collect_records_without_pruning() {
    let vis = names(&["w", "s"]);
    let run = collect_run(
        cfg(),
        &vis,
        Arc::new(|| {
            let sink = named("sink", || {
                let _x: i32 = recv_msg_block();
                let _y: i32 = recv_msg_block();
            });
            let sid = sink.thread().id();
            // `w` is spawned **first**, so under the mutation its assertion
            // fires before the sibling has run and the truncation is visible.
            let _w = named("w", || {
                crate::assert(false);
            });
            // The sibling: two visible sends, so a `stop()` truncates its row
            // observably.
            let _s = named("s", move || {
                send_msg(sid, 1i32);
                send_msg(sid, 2i32);
            });
        }),
        true,
    );

    // The count, first --- and it is here to be *shown* not to discriminate.
    assert_eq!(
        run.graphs.len(),
        run.stats.execs + run.stats.block,
        "conformance: the count equality holds under the mutation too; it is not \
         the discriminator"
    );
    assert!(!run.graphs.is_empty(), "conformance: nothing was captured");

    for (i, g) in run.graphs.iter().enumerate() {
        assert!(
            !has_conf_prune(g),
            "conformance: captured graph {i} carries Block(ConfPrune) --- collect mode \
             pruned, so every thread's row is truncated and vis(P) is under-approximated"
        );
        let w = wobs(g, &vis).expect("extraction");
        assert_eq!(
            w.of("s").len(),
            2,
            "conformance: captured graph {i}: the sibling visible thread's row is \
             truncated --- stop() ended the execution before its second send"
        );
        let st = statuses_of(g, &vis);
        assert_eq!(
            st["w"],
            Status::Errored,
            "conformance: captured graph {i}: the failed assertion is not lost"
        );
    }

    assert_eq!(
        run.reports, 0,
        "conformance: collect mode records the failure, it does not report it"
    );
    assert_eq!(
        run.collect_errors.len(),
        1,
        "conformance: recorded exactly once --- a silent Continue is the failure mode \
         to guard against, and so is a duplicate"
    );
    assert_eq!(
        run.collect_errors[0].0, "w",
        "conformance: the **declared** visible name, not lib.rs's runtime task name"
    );
}

// ===========================================================================
// Group E --- criterion 2.
// ===========================================================================

/// **Criterion 2(a): dropping the blocked/errored class changes a verdict.**
///
/// `Graphs(P)` is "consistent and admits no further event", so a deadlocked run
/// is a final configuration and belongs in it. Here the implementation's only
/// ending is a deadlock — `c` waits for a second message that never comes —
/// while the specification completes. The statuses differ, so inclusion fails.
///
/// Drop the blocked class and the implementation's `vis` set becomes **empty**,
/// `∅ ⊆ anything` holds, and the oracle answers the opposite. That is the
/// permissive direction, and on the specification side it is the false-alarm
/// direction.
///
/// To break it: capture only endings where the graph is not blocked, i.e.
/// `gate == Gate::Completion && g1.check_blocked().is_none()`. Measured.
#[test]
fn e1_dropping_the_blocked_class_flips_the_verdict() {
    let vis = names(&["main", "c"]);
    let imp = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
            let _w: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    };
    let spec = || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    };
    assert!(
        matches!(
            includes(cfg(), &vis, imp, spec).expect("oracle"),
            Inclusion::Fails { .. }
        ),
        "conformance: c is blocked in the implementation and done in the specification, \
         and a blocked run is a final configuration"
    );
}

/// **Criterion 2(b): a bounded exploration is a hard error, not a note.**
///
/// A truncated enumeration weakens `⊆` in the **permissive** direction
/// silently, so the oracle refuses to answer rather than answering from an
/// under-approximation. Prose candour is not a control.
///
/// To break it: delete the `config.max_iterations.is_some()` guard in
/// `oracle::vis_of_program` — the oracle then answers from one execution of a
/// two-execution program. Measured.
#[test]
fn e2_a_bounded_exploration_is_a_hard_error() {
    let vis = names(&["a", "b", "c"]);
    let bounded = Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_max_iterations(1)
        .build();
    let got = vis_of_program(bounded, &vis, move || ex_traces()());
    match got {
        Err(OracleError::Truncated { .. }) => {}
        other => panic!(
            "conformance: a bounded run must be refused, not answered; got {other:?}"
        ),
    }
}
