//! P4-APPARATUS gate 3: the tester's tests for `sig.rs`, `canon.rs`,
//! `witness.rs` and `cert.rs` (criteria `P4-APPARATUS.md` revision 4.1).
//!
//! Every expected value below was derived from the paper (`alg.tex` §8.1–8.6,
//! `hit.tex` §11.3, `appendix.tex`) and the criteria's engine facts E1–E5
//! **before** the four modules were read; the derivations are written out in
//! `plan/traceForge/log/dev/P4-APPARATUS.report.md`, Part 0, under the labels
//! `D1`..`D18` cited on each test. Nothing here was copied from a run.
//!
//! Fixture rule (E1) for every paper-derived `vo`/`ord`/`cone`/`covered` value:
//! `main` is invisible, is the only spawner, spawns first, never joins, and
//! performs no send or receive. All fixture threads use the asyn model
//! (`ConsType::Bag`) unless a corpus pair fixes its own configuration.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::canon::{CanonLabel, CanonSet, CanonicalGraph, Declared, Dest, ThreadKey};
use crate::conformance::cert::Certificate;
use crate::conformance::ctx::{ConfCtx, ConfMode};
use crate::conformance::morphism::{
    matches, order_is_reflected, statuses, statuses_agree, CompleteExecution,
};
use crate::conformance::obs::{is_visible_event, wobs, ObsError, Wobs};
use crate::conformance::probe::{NondetValue, Offer};
use crate::conformance::prober::{install, install_nondet, install_recv, probe_from};
use crate::conformance::sig::{cone, covered, ord, Sig, SigBuckets, Summary, VPos, VisOrder};
use crate::conformance::testing::CurrentMustGuard;
use crate::conformance::witness::WitnessCache;
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::msg::Val;
use crate::must::Must;
use crate::thread::{main_thread_id, ThreadId};
use crate::{recv_msg, recv_msg_block, send_msg, thread, Config, ConsType, Nondet};

type Prog = Arc<dyn Fn() + Send + Sync>;

// ===========================================================================
// Harness
// ===========================================================================

fn asyn() -> Config {
    Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .build()
}

fn vis(ns: &[&str]) -> Vec<String> {
    ns.iter().map(|s| (*s).to_string()).collect()
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
}

fn prog<F: Fn() + Send + Sync + 'static>(f: F) -> Prog {
    Arc::new(f)
}

/// Every complete graph of `p`, by an ungated Must exploration that keeps
/// each execution's graph at its end (the oracle's `Collect` mode).
fn graphs_of(config: Config, visible: &[String], p: Prog) -> Vec<ExecutionGraph> {
    let must = Rc::new(RefCell::new(Must::new(config.clone(), false)));
    {
        let mut ctx = ConfCtx::gate_disabled(config, visible.to_vec(), ConfMode::Collect);
        ctx.collect_graphs();
        must.borrow_mut().enable_conformance(ctx);
    }
    {
        let _guard = CurrentMustGuard;
        let f = Arc::new(move || p());
        crate::explore(&must, &f);
    }
    let m = must.borrow();
    m.conf_ctx()
        .expect("conformance: the collect context went missing")
        .collected()
        .to_vec()
}

fn w(g: &ExecutionGraph, v: &[String]) -> Wobs {
    wobs(g, v).expect("conformance: wobs on a fixture graph")
}

fn summary(g: &ExecutionGraph, v: &[String]) -> Summary {
    let exec = CompleteExecution::assume_finished_at_gate(g);
    Summary::of(exec, &w(g, v), v).expect("conformance: summary on a fixture graph")
}

fn sig(g: &ExecutionGraph, v: &[String]) -> Sig {
    let exec = CompleteExecution::assume_finished_at_gate(g);
    Sig::of(exec, &w(g, v), v).expect("conformance: sig on a fixture graph")
}

fn ordv(g: &ExecutionGraph, v: &[String]) -> VisOrder {
    ord(g, &w(g, v), v)
}

fn conev(g1: &ExecutionGraph, m: &ExecutionGraph, v: &[String]) -> bool {
    cone(g1, &w(g1, v), m, &w(m, v), v)
}

fn canon(g: &ExecutionGraph, v: &[String]) -> CanonicalGraph {
    CanonicalGraph::of(g, v).expect("conformance: canonical form of a fixture graph")
}

fn vp(t: &str, i: usize) -> VPos {
    VPos {
        thread: t.to_string(),
        index: i,
    }
}

fn pair(a: (&str, usize), b: (&str, usize)) -> (VPos, VPos) {
    (vp(a.0, a.1), vp(b.0, b.1))
}

fn name_of(g: &ExecutionGraph, t: ThreadId) -> Option<String> {
    g.get_thread_tclab(t).name().clone()
}

fn tid_named(g: &ExecutionGraph, n: &str) -> ThreadId {
    g.thread_ids()
        .into_iter()
        .find(|t| name_of(g, *t).as_deref() == Some(n))
        .unwrap_or_else(|| panic!("conformance: no thread named {n} in the fixture graph"))
}

/// The single send event of thread `n` (fixture threads send at most once
/// unless stated otherwise).
fn send_of(g: &ExecutionGraph, n: &str) -> Event {
    let t = tid_named(g, n);
    (0..g.thread_size(t) as u32)
        .map(|i| Event::new(t, i))
        .find(|e| matches!(g.label(*e), LabelEnum::SendMsg(_)))
        .unwrap_or_else(|| panic!("conformance: thread {n} has no send"))
}

fn recv_source(g: &ExecutionGraph, n: &str, k: usize) -> Option<Event> {
    let t = tid_named(g, n);
    let recvs: Vec<Event> = (0..g.thread_size(t) as u32)
        .map(|i| Event::new(t, i))
        .filter(|e| matches!(g.label(*e), LabelEnum::RecvMsg(_)))
        .collect();
    match g.label(recvs[k]) {
        LabelEnum::RecvMsg(r) => r.rf(),
        _ => unreachable!("conformance: filtered to receives"),
    }
}

/// The one graph of a program that has exactly one (asserted: the
/// derivation says so).
fn only_graph(p: Prog, v: &[String]) -> ExecutionGraph {
    let gs = graphs_of(asyn(), v, p);
    assert_eq!(
        gs.len(),
        1,
        "conformance: the derivation says this program has exactly one complete graph"
    );
    gs.into_iter().next().unwrap()
}

// --- a prober-driven graph builder: one installation order, chosen here ----

#[derive(Clone)]
struct Driver {
    config: Config,
    p: Prog,
    offers: Vec<Offer>,
    graph: ExecutionGraph,
}

impl Driver {
    fn start(config: Config, p: Prog) -> Self {
        Self {
            config,
            p,
            offers: Vec::new(),
            graph: ExecutionGraph::default(),
        }
        .reprobed()
    }

    fn reprobed(mut self) -> Self {
        let p = self.p.clone();
        let (offers, graph) =
            probe_from(self.config.clone(), self.graph.clone(), move || p()).into_parts();
        self.offers = offers;
        self.graph = graph;
        self
    }

    fn with_graph(&self, g: ExecutionGraph) -> Self {
        Self {
            config: self.config.clone(),
            p: self.p.clone(),
            offers: Vec::new(),
            graph: g,
        }
        .reprobed()
    }

    fn offer_of(&self, t: &str) -> Offer {
        self.offers
            .iter()
            .find(|o| name_of(&self.graph, o.pos().thread).as_deref() == Some(t))
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "conformance: no offer for thread {t}; offers: {:?}",
                    self.offers
                )
            })
    }

    fn send(&self, t: &str) -> Self {
        let o = self.offer_of(t);
        self.with_graph(install(self.config.clone(), self.graph.clone(), &o))
    }

    fn recv(&self, t: &str, from: Option<&str>) -> Self {
        let o = self.offer_of(t);
        let rf = from.map(|f| {
            *o.sources()
                .iter()
                .find(|s| name_of(&self.graph, s.thread).as_deref() == Some(f))
                .unwrap_or_else(|| panic!("conformance: {t} cannot read from {f}"))
        });
        self.with_graph(install_recv(
            self.config.clone(),
            self.graph.clone(),
            &o,
            rf,
        ))
    }

    fn nondet(&self, t: &str, v: NondetValue) -> Self {
        let o = self.offer_of(t);
        self.with_graph(install_nondet(
            self.config.clone(),
            self.graph.clone(),
            &o,
            v,
        ))
    }

    fn is_complete(&self) -> bool {
        self.offers.is_empty() && CompleteExecution::try_finished(&self.graph).is_some()
    }
}

// ===========================================================================
// Fixtures (all E1: invisible `main` spawns, nothing else)
// ===========================================================================

/// Criterion 1 Impl: `A: n := nondet({0}); send(C,n) ‖ C: x := recv()`.
fn c1_impl() {
    let c = named("c", || {
        let _x: usize = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || {
        let n = (0..=0usize).nondet();
        send_msg(cid, n);
    });
}

/// Criterion 1 Spec: `A: send(C,0) ‖ C: recv()`.
fn c1_spec() {
    let c = named("c", || {
        let _x: usize = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 0usize));
}

/// `A: send(C,v) ‖ C: recv()`.
fn direct_of<T: crate::msg::Message + Clone + PartialEq + std::fmt::Debug + Sync + 'static>(
    v: T,
) -> Prog {
    prog(move || {
        let c = named("c", || {
            let _x: T = recv_msg_block();
        });
        let cid = c.thread().id();
        let v = v.clone();
        let _a = named("a", move || send_msg(cid, v));
    })
}

/// `A: send(C,1) ‖ C: skip` — criterion 4(c)'s Impl.
fn c4c_impl() {
    let c = named("c", || {});
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 1i32));
}

/// ex:cone Spec: `A: send(C,9) ‖ C: x := recv^b()`.
fn ex_cone_spec() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 9i32));
}

/// ex:cone Impl: `A: skip ‖ D: send(C,9) ‖ C: x := recv^b()`.
fn ex_cone_impl() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", || {});
    let _d = named("d", move || send_msg(cid, 9i32));
}

/// Relay Spec: `A: send(R,9) ‖ R(inv): y := recv(); send(C,y) ‖ C: recv()`.
fn relay_spec() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let r = named("r", move || {
        let y: i32 = recv_msg_block();
        send_msg(cid, y);
    });
    let rid = r.thread().id();
    let _a = named("a", move || send_msg(rid, 9i32));
}

/// Clause (2) Spec: `B: send(A,1) ‖ A: recv()`.
fn c2_spec() {
    let a = named("a", || {
        let _x: i32 = recv_msg_block();
    });
    let aid = a.thread().id();
    let _b = named("b", move || send_msg(aid, 1i32));
}

/// Clause (2) Impl: `B: send(X,1) ‖ X(inv): recv() ‖ D(inv): send(A,1) ‖ A: recv()`.
fn c2_impl() {
    let a = named("a", || {
        let _x: i32 = recv_msg_block();
    });
    let aid = a.thread().id();
    let x = named("x", || {
        let _y: i32 = recv_msg_block();
    });
    let xid = x.thread().id();
    let _b = named("b", move || send_msg(xid, 1i32));
    let _d = named("d", move || send_msg(aid, 1i32));
}

/// Clause (1): `A: send(X,v)`, `X` invisible and idle.
fn c1clause_of(v: i32) -> Prog {
    prog(move || {
        let x = named("x", || {});
        let xid = x.thread().id();
        let _a = named("a", move || send_msg(xid, v));
    })
}

/// Blocking pair Impl: `A: send(C,1) ‖ C: recv(); recv()`.
fn blocking_impl() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
        let _y: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 1i32));
}

/// `A: send(C,va) ‖ B: send(C,vb) ‖ C: x := recv()`.
fn two_senders(va: i32, vb: i32) -> Prog {
    prog(move || {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, va));
        let _b = named("b", move || send_msg(cid, vb));
    })
}

/// Criterion 16's "both" program: `A: send(R,1) ‖ R(inv): y := recv_nb();
/// send(B,5) ‖ B: recv()`, `Tvis = {A,B}`.
fn relay_nb() {
    let b = named("b", || {
        let _z: i32 = recv_msg_block();
    });
    let bid = b.thread().id();
    let r = named("r", move || {
        let _y: Option<i32> = recv_msg();
        send_msg(bid, 5i32);
    });
    let rid = r.thread().id();
    let _a = named("a", move || send_msg(rid, 1i32));
}

// ===========================================================================
// A. sig.rs
// ===========================================================================

/// **Criterion 1 (D1).** `vpos` counts visible events only. Both sides
/// transport their one order pair to `((a,0),(c,0))`; `covered` holds.
/// The control asserts E2's relation that makes the raw-index mutation bite:
/// the Impl send sits exactly one index past the Spec send.
#[test]
fn c01_vpos_counts_visible_events_only() {
    let v = vis(&["a", "c"]);
    let g1 = only_graph(prog(c1_impl), &v);
    let g2 = only_graph(prog(c1_spec), &v);
    let expected: VisOrder = [pair(("a", 0), ("c", 0))].into_iter().collect();
    assert_eq!(ordv(&g1, &v), expected, "conformance: Impl ord (D1)");
    assert_eq!(ordv(&g2, &v), expected, "conformance: Spec ord (D1)");
    assert!(
        covered(&summary(&g1, &v), &summary(&g2, &v)),
        "conformance: D1 says the Impl graph is covered by the Spec graph"
    );
    // Control (E2): the raw indices differ, so a raw-index vpos would differ.
    assert_eq!(
        send_of(&g1, "a").index,
        send_of(&g2, "a").index + 1,
        "conformance: E2 — the Choice sits between Begin and the send on the Impl side"
    );
}

/// **Criterion 2 (D2).** `Sig` equality is word equality by `Obs::eq` plus
/// status equality; equal graphs from two separate runs give equal `Sig`s;
/// a value difference and a status-only difference each give unequal ones.
#[test]
fn c02_sig_equality_is_the_morphisms() {
    let v = vis(&["a", "b", "c"]);
    let run1 = graphs_of(asyn(), &v, two_senders(1, 2));
    let run2 = graphs_of(asyn(), &v, two_senders(1, 2));
    assert_eq!(run1.len(), 2, "conformance: C reads A or B");
    let by_val = |gs: &[ExecutionGraph], src: &str| -> ExecutionGraph {
        gs.iter()
            .find(|g| recv_source(g, "c", 0) == Some(send_of(g, src)))
            .cloned()
            .expect("conformance: graph with the requested source")
    };
    let a1 = by_val(&run1, "a");
    let a2 = by_val(&run2, "a");
    let b1 = by_val(&run1, "b");
    assert!(
        sig(&a1, &v) == sig(&a2, &v),
        "conformance: same graph, two runs"
    );
    assert!(
        sig(&a1, &v) != sig(&b1, &v),
        "conformance: C's word differs"
    );

    // Status-only difference: the Blocking pair.
    let vb = vis(&["a", "c"]);
    let gi = only_graph(prog(blocking_impl), &vb);
    let gs = only_graph(direct_of(1i32), &vb);
    let (si, ss) = (sig(&gi, &vb), sig(&gs, &vb));
    for t in ["a", "c"] {
        assert!(
            si.word(t) == ss.word(t),
            "conformance: Blocking pair words agree at {t} (D2 control)"
        );
    }
    assert_ne!(
        si.status("c"),
        ss.status("c"),
        "conformance: statuses differ"
    );
    assert!(
        si != ss,
        "conformance: status-only difference must break Sig equality"
    );
}

/// **Criterion 3 (D3).** `SigKey` equal / `Sig` unequal → two slots in one
/// key; equal `Sig` → one slot; a different payload type → a different key.
#[test]
fn c03_sigkey_is_a_sound_projection_and_buckets_resolve_it() {
    let v = vis(&["a", "c"]);
    let g1 = only_graph(direct_of(1i32), &v);
    let g1b = only_graph(direct_of(1i32), &v);
    let g2 = only_graph(direct_of(2i32), &v);
    let gb = only_graph(direct_of(true), &v);
    let (s1, s1b, s2, sb) = (sig(&g1, &v), sig(&g1b, &v), sig(&g2, &v), sig(&gb, &v));
    assert!(
        s1 == s1b && s1.key() == s1b.key(),
        "conformance: equal sig, equal key"
    );
    assert!(s1 != s2, "conformance: values 1 and 2 differ");
    assert_eq!(s1.key(), s2.key(), "conformance: same shape, same key");
    assert_ne!(s1.key(), sb.key(), "conformance: type name is in the key");

    let mut idx: SigBuckets<Vec<&'static str>> = SigBuckets::new();
    idx.entry(s1.clone(), Vec::new).push("one");
    idx.entry(s2.clone(), Vec::new).push("two");
    assert_eq!(
        idx.len(),
        2,
        "conformance: equal keys, unequal sigs: two slots"
    );
    idx.entry(s1b.clone(), Vec::new).push("one-again");
    assert_eq!(idx.len(), 2, "conformance: equal sigs share one slot");
    assert_eq!(
        idx.get(&s1).cloned(),
        Some(vec!["one", "one-again"]),
        "conformance: the slot for value 1"
    );
    assert_eq!(
        idx.get(&s2).cloned(),
        Some(vec!["two"]),
        "conformance: value 2's slot"
    );
    assert!(idx.get(&sb).is_none(), "conformance: no bool slot");
}

/// **Criterion 4(c) (D4c).** `order_is_reflected` true, `ord(g₂) ⊄ ord(g₁)`.
#[test]
fn c04c_ord_containment_is_stricter_than_order_is_reflected() {
    let v = vis(&["a", "c"]);
    let g1 = only_graph(prog(c4c_impl), &v);
    let g2 = only_graph(direct_of(1i32), &v);
    let o1 = ordv(&g1, &v);
    let o2 = ordv(&g2, &v);
    assert_eq!(o1, VisOrder::new(), "conformance: ord(g1) = ∅");
    assert_eq!(
        o2,
        [pair(("a", 0), ("c", 0))].into_iter().collect::<VisOrder>(),
        "conformance: ord(g2)"
    );
    assert!(!o2.is_subset(&o1), "conformance: ord(g2) ⊄ ord(g1)");
    assert!(
        order_is_reflected(&g2, &g1, &w(&g2, &v), &w(&g1, &v), &v),
        "conformance: (M2) on matched positions passes vacuously"
    );
}

// --- the corpus for criteria 4(a)/(b), 5, 7, 8, 20 -------------------------

struct CorpusPair {
    name: String,
    config: Config,
    visible: Vec<String>,
    imp: Prog,
    spec: Prog,
}

fn cp(name: &str, config: Config, visible: &[&str], imp: Prog, spec: Prog) -> CorpusPair {
    CorpusPair {
        name: name.to_string(),
        config,
        visible: vis(visible),
        imp,
        spec,
    }
}

// paper_examples.rs, reproduced (those programs are private to that module).
fn pe_p2_relay() {
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
fn pe_p1_direct() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 1i32);
}
fn pe_p1_value_two() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 2i32);
}
fn pe_c_blocks() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
        let _w: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 1i32);
}
fn pe_two_unordered_sends() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 1i32));
    let _b = named("b", move || send_msg(cid, 2i32));
}
fn pe_sends_ordered_by_join() {
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
// refinement_suite.rs, reproduced.
fn rs_visible_error() {
    let _w = named("w", || {
        crate::assert(false);
    });
}
fn rs_visible_ok() {
    let _w = named("w", || {});
}
fn rs_cross_model(relay: bool, v2: i32) -> Prog {
    prog(move || {
        let (tx1, rx1) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::NoOrder)
            .build();
        let (tx2, rx2) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::CausalOrder)
            .build();
        let _c1 = named("c1", move || {
            let _v = rx1.recv_msg_block();
        });
        let _c2 = named("c2", move || {
            let _v = rx2.recv_msg_block();
        });
        if relay {
            let r = named("r", move || {
                let v: i32 = recv_msg_block();
                tx1.send_msg(v);
            });
            send_msg(r.thread().id(), 1i32);
        } else {
            tx1.send_msg(1i32);
        }
        tx2.send_msg(v2);
    })
}

fn fifo() -> Config {
    Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_seed(0)
        .build()
}

fn corpus() -> Vec<CorpusPair> {
    let mut out = Vec::new();
    let mc = &["main", "c"];
    // paper_examples
    out.push(cp(
        "pe:relay/direct",
        fifo(),
        mc,
        prog(pe_p2_relay),
        prog(pe_p1_direct),
    ));
    out.push(cp(
        "pe:direct/relay",
        fifo(),
        mc,
        prog(pe_p1_direct),
        prog(pe_p2_relay),
    ));
    out.push(cp(
        "pe:relay/two",
        fifo(),
        mc,
        prog(pe_p2_relay),
        prog(pe_p1_value_two),
    ));
    out.push(cp(
        "pe:relay/blocks",
        fifo(),
        mc,
        prog(pe_p2_relay),
        prog(pe_c_blocks),
    ));
    out.push(cp(
        "pe:blocks/direct",
        fifo(),
        mc,
        prog(pe_c_blocks),
        prog(pe_p1_direct),
    ));
    out.push(cp(
        "pe:m2",
        fifo(),
        &["main", "a", "b", "c"],
        prog(pe_two_unordered_sends),
        prog(pe_sends_ordered_by_join),
    ));
    out.push(cp(
        "pe:m2-mirror",
        fifo(),
        &["main", "a", "b", "c"],
        prog(pe_sends_ordered_by_join),
        prog(pe_two_unordered_sends),
    ));
    // refinement_suite, under each in-scope model
    for model in [ConsType::Bag, ConsType::FIFO, ConsType::Causal] {
        let c = Config::builder().with_cons_type(model).with_seed(0).build();
        out.push(cp(
            "rs:relayed/direct",
            c.clone(),
            mc,
            prog(pe_p2_relay),
            prog(pe_p1_direct),
        ));
        out.push(cp(
            "rs:relayed/two",
            c.clone(),
            mc,
            prog(pe_p2_relay),
            prog(pe_p1_value_two),
        ));
        out.push(cp(
            "rs:error/ok",
            c.clone(),
            &["w"],
            prog(rs_visible_error),
            prog(rs_visible_ok),
        ));
    }
    let mcc = &["main", "c1", "c2"];
    out.push(cp(
        "rs:xmodel",
        fifo(),
        mcc,
        rs_cross_model(true, 2),
        rs_cross_model(false, 2),
    ));
    out.push(cp(
        "rs:xmodel-mut",
        fifo(),
        mcc,
        rs_cross_model(true, 2),
        rs_cross_model(false, 3),
    ));
    // this file's own fixtures
    let ac = &["a", "c"];
    out.push(cp(
        "t:ex_cone",
        asyn(),
        ac,
        prog(ex_cone_impl),
        prog(ex_cone_spec),
    ));
    out.push(cp(
        "t:relay",
        asyn(),
        ac,
        prog(ex_cone_impl),
        prog(relay_spec),
    ));
    out.push(cp(
        "t:c2",
        asyn(),
        &["a", "b"],
        prog(c2_impl),
        prog(c2_spec),
    ));
    out.push(cp(
        "t:c2-mirror",
        asyn(),
        &["a", "b"],
        prog(c2_spec),
        prog(c2_impl),
    ));
    out.push(cp(
        "t:blocking",
        asyn(),
        ac,
        prog(blocking_impl),
        direct_of(1i32),
    ));
    out.push(cp(
        "t:two",
        asyn(),
        &["a", "b", "c"],
        two_senders(1, 2),
        two_senders(1, 2),
    ));
    out.push(cp(
        "t:relay_nb",
        asyn(),
        &["a", "b"],
        prog(relay_nb),
        prog(relay_nb),
    ));
    out.push(cp("t:c1", asyn(), ac, prog(c1_impl), prog(c1_spec)));
    // the generator's pairs, violating ones included
    for p in crate::conformance::generator::corpus(0x5EED, 1) {
        out.push(CorpusPair {
            name: format!("gen:{:?}:{}", p.mode, p.seed),
            config: p.config.clone(),
            visible: p.visible.clone(),
            imp: p.implementation.clone(),
            spec: p.specification.clone(),
        });
    }
    out
}

struct CorpusGraphs {
    name: String,
    visible: Vec<String>,
    imp: Vec<ExecutionGraph>,
    spec: Vec<ExecutionGraph>,
}

fn corpus_graphs() -> Vec<CorpusGraphs> {
    corpus()
        .into_iter()
        .map(|p| CorpusGraphs {
            imp: graphs_of(p.config.clone(), &p.visible, p.imp.clone()),
            spec: graphs_of(p.config.clone(), &p.visible, p.spec.clone()),
            name: p.name,
            visible: p.visible,
        })
        .collect()
}

fn same_lengths(a: &Wobs, b: &Wobs, v: &[String]) -> bool {
    v.iter().all(|t| a.of(t).len() == b.of(t).len())
}

/// **Criteria 4(a), 4(b), 5, 8 (second half), 20, over the corpus.**
/// Engine-against-engine; E1 does not bind. Every positive implication is
/// accompanied by a positive count, and the negations are counted too so a
/// corpus that never makes the compared sides differ is caught.
#[test]
fn c04ab_c05_c08b_c20_corpus_agreement() {
    let mut pairs = 0usize;
    let (mut sub_true, mut sub_false, mut eqlen_oir) = (0usize, 0usize, 0usize);
    let (mut cov_true, mut cov_false, mut cov_and_cone) = (0usize, 0usize, 0usize);
    let (mut vis_events, mut invis_events) = (0usize, 0usize);
    let mut failures = Vec::new();
    for cg in corpus_graphs() {
        let v = &cg.visible;
        assert!(
            !cg.imp.is_empty() && !cg.spec.is_empty(),
            "conformance: corpus pair {} produced no graph",
            cg.name
        );
        // Criterion 20: wobs rows and is_visible_event agree on every event.
        for g in cg.imp.iter().chain(cg.spec.iter()) {
            let wg = w(g, v);
            let in_rows: BTreeSet<Event> = v
                .iter()
                .flat_map(|t| wg.of(t).iter().map(|(e, _)| *e))
                .collect();
            for t in g.thread_ids() {
                for i in 0..g.thread_size(t) as u32 {
                    let e = Event::new(t, i);
                    let iv = is_visible_event(g, e, v);
                    if iv != in_rows.contains(&e) {
                        failures.push(format!("{}: c20 disagreement at {e}", cg.name));
                    }
                    if iv {
                        vis_events += 1;
                    } else {
                        invis_events += 1;
                    }
                }
            }
        }
        for g1 in &cg.imp {
            let (w1, s1) = (w(g1, v), summary(g1, v));
            let st1 = statuses(CompleteExecution::assume_finished_at_gate(g1), &w1, v)
                .expect("conformance: impl statuses");
            for g2 in &cg.spec {
                pairs += 1;
                let (w2, s2) = (w(g2, v), summary(g2, v));
                // 4(a)/(b)
                let sub = s2.ord.is_subset(&s1.ord);
                let oir = order_is_reflected(g2, g1, &w2, &w1, v);
                if sub {
                    sub_true += 1;
                    if !oir {
                        failures.push(format!("{}: 4(a) ord ⊆ but (M2) fails", cg.name));
                    }
                } else {
                    sub_false += 1;
                }
                if same_lengths(&w1, &w2, v) && oir {
                    eqlen_oir += 1;
                    if !sub {
                        failures.push(format!(
                            "{}: 4(b) equal lengths, (M2) holds, ord ⊄",
                            cg.name
                        ));
                    }
                }
                // 5
                let st2 = statuses(CompleteExecution::assume_finished_at_gate(g2), &w2, v)
                    .expect("conformance: spec statuses");
                let phase3 = matches(g2, g1, &w2, &w1, v) && statuses_agree(&st2, &st1);
                let cov = covered(&s1, &s2);
                if cov != phase3 {
                    failures.push(format!("{}: c5 covered={cov} phase3={phase3}", cg.name));
                }
                // 8, second half: covered ⟹ cone on complete G1
                if cov {
                    cov_true += 1;
                    if conev(g1, g2, v) {
                        cov_and_cone += 1;
                    } else {
                        failures.push(format!("{}: c8 covered but not cone", cg.name));
                    }
                } else {
                    cov_false += 1;
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "conformance: corpus failures: {failures:#?}"
    );
    // Vacuity controls: both sides of every implication occur.
    assert!(pairs >= 40, "conformance: corpus too small: {pairs} pairs");
    assert!(
        sub_true > 0 && sub_false > 0,
        "conformance: ord ⊆ both ways"
    );
    assert!(eqlen_oir > 0, "conformance: 4(b) exercised");
    assert!(
        cov_true > 0 && cov_false > 0,
        "conformance: covered both ways"
    );
    assert_eq!(cov_true, cov_and_cone, "conformance: c8 count");
    assert!(
        vis_events > 0 && invis_events > 0,
        "conformance: c20 both ways"
    );
    // Recorded for the report (visible through --nocapture only on failure).
    let _ = (pairs, sub_true, sub_false, eqlen_oir, cov_true, cov_false);
}

/// The `debug_assert!`s criterion 18 (iii) and E3 rely on are live in the
/// test profile; without this the (iii) cross-check would be vacuous.
#[test]
#[allow(clippy::assertions_on_constants)]
fn debug_assertions_are_on() {
    assert!(
        cfg!(debug_assertions),
        "conformance: debug assertions are off"
    );
}

/// **Criterion 6 (D6): `cone`, each clause isolated.**
#[test]
fn c06_clause3_ex_cone() {
    let v = vis(&["a", "c"]);
    let g1 = only_graph(prog(ex_cone_impl), &v);
    let m = only_graph(prog(ex_cone_spec), &v);
    // Clause (1) and (2) hold (D6): words prefix, one matched event.
    let (w1, wm) = (w(&g1, &v), w(&m, &v));
    assert_eq!(
        w1.of("a").len(),
        0,
        "conformance: A has no visible event in G1"
    );
    assert!(
        w1.of("c")[0].1 == wm.of("c")[0].1,
        "conformance: C's words agree"
    );
    assert!(
        !conev(&g1, &m, &v),
        "conformance: ex:cone — clause (3) fails"
    );
}

#[test]
fn c06_clause3_through_a_relay() {
    let v = vis(&["a", "c"]);
    let g1 = only_graph(prog(ex_cone_impl), &v);
    let m = only_graph(prog(relay_spec), &v);
    // Control: the porf path A0 ⇝ C0 in M goes through the invisible relay;
    // A0 is not an immediate predecessor of C0.
    let c0_src = recv_source(&m, "c", 0).expect("conformance: C reads");
    assert_eq!(
        name_of(&m, c0_src.thread).as_deref(),
        Some("r"),
        "conformance: relay"
    );
    assert!(
        !conev(&g1, &m, &v),
        "conformance: relay — clause (3) fails transitively"
    );
}

#[test]
fn c06_clause2() {
    let v = vis(&["a", "b"]);
    let g1 = only_graph(prog(c2_impl), &v);
    let m = only_graph(prog(c2_spec), &v);
    // Control: clause (1) holds — words are equal although B's destination
    // differs (paper obs carries no destination); clause (3) holds.
    let (w1, wm) = (w(&g1, &v), w(&m, &v));
    for t in ["a", "b"] {
        assert_eq!(
            w1.of(t).len(),
            wm.of(t).len(),
            "conformance: lengths at {t}"
        );
        assert!(
            w1.of(t)[0].1 == wm.of(t)[0].1,
            "conformance: words agree at {t}"
        );
    }
    assert_eq!(ordv(&g1, &v), VisOrder::new(), "conformance: ord(G1) = ∅");
    assert_eq!(
        ordv(&m, &v),
        [pair(("b", 0), ("a", 0))].into_iter().collect::<VisOrder>(),
        "conformance: ord(M)"
    );
    assert!(!conev(&g1, &m, &v), "conformance: clause (2) fails");
}

#[test]
fn c06_clause2_mirror_is_true() {
    let v = vis(&["a", "b"]);
    let g1 = only_graph(prog(c2_spec), &v);
    let m = only_graph(prog(c2_impl), &v);
    assert_eq!(
        ordv(&g1, &v),
        [pair(("b", 0), ("a", 0))].into_iter().collect::<VisOrder>(),
        "conformance: ord(G1)"
    );
    assert_eq!(
        ordv(&m, &v),
        VisOrder::new(),
        "conformance: vo_M on visible = ∅"
    );
    assert!(conev(&g1, &m, &v), "conformance: mirror — cone holds");
}

#[test]
fn c06_clause1() {
    let v = vis(&["a"]);
    let g1 = only_graph(c1clause_of(2), &v);
    let m = only_graph(c1clause_of(1), &v);
    assert!(!conev(&g1, &m, &v), "conformance: clause (1) fails");
    // Control: identical value passes, so the failure is the value.
    let m2 = only_graph(c1clause_of(2), &v);
    assert!(conev(&g1, &m2, &v), "conformance: same value passes");
}

// --- criterion 7: prefixes ---------------------------------------------------

/// Porf-closed restrictions of `g`: the porf view of every event, and the
/// union of every two such views. Each is a `def:ext` prefix of `g`.
fn prefixes(g: &ExecutionGraph) -> Vec<(crate::vector_clock::VectorClock, ExecutionGraph)> {
    let mut views: Vec<crate::vector_clock::VectorClock> = Vec::new();
    let evs: Vec<Event> = g
        .thread_ids()
        .into_iter()
        .flat_map(|t| (0..g.thread_size(t) as u32).map(move |i| Event::new(t, i)))
        .collect();
    for e in &evs {
        views.push(spawn_closed(g, g.porf(*e)));
    }
    let base = views.clone();
    for (i, a) in base.iter().enumerate() {
        for b in base.iter().skip(i + 1) {
            let mut u = a.clone();
            u.update(b);
            views.push(spawn_closed(g, u));
        }
    }
    let mut out: Vec<(crate::vector_clock::VectorClock, ExecutionGraph)> = Vec::new();
    for v in views {
        if out.iter().any(|(u, _)| vc_eq(u, &v)) {
            continue;
        }
        let r = g.copy_to_view(&v);
        out.push((v, r));
    }
    out
}

/// Close a porf-closed view under "`TCreate` in view ⇒ the child's `Begin`
/// in view", the shape `cut_to_view`'s `check_spawn_invariants` accepts
/// (`exec_graph.rs`). Unlike the earlier "every thread's `Begin`" base, a
/// view that stops before a `TCreate` leaves the child unspawned (round 01
/// m2).
fn spawn_closed(
    g: &ExecutionGraph,
    mut v: crate::vector_clock::VectorClock,
) -> crate::vector_clock::VectorClock {
    loop {
        let mut grew = false;
        for t in g.thread_ids() {
            for i in 0..g.thread_size(t) as u32 {
                let e = Event::new(t, i);
                if !v.contains(e) {
                    continue;
                }
                if let LabelEnum::TCreate(tc) = g.label(e) {
                    let child = Event::new(tc.cid(), 0);
                    if !v.contains(child) {
                        v.update(&g.porf(child));
                        grew = true;
                    }
                }
            }
        }
        if !grew {
            return v;
        }
    }
}

fn has_unspawned(g: &ExecutionGraph, v: &[String]) -> bool {
    let wg = w(g, v);
    v.iter()
        .any(|t| wg.row(t).is_some_and(|r| r.is_unspawned()))
}

fn vc_le(a: &crate::vector_clock::VectorClock, b: &crate::vector_clock::VectorClock) -> bool {
    a.entries().all(|(t, i)| b.get(t).is_some_and(|j| j >= i))
}

fn vc_eq(a: &crate::vector_clock::VectorClock, b: &crate::vector_clock::VectorClock) -> bool {
    vc_le(a, b) && vc_le(b, a)
}

/// **Criterion 7 (D7).** `cone(G₁',M) ⟹ cone(G₁,M)` for `G₁ ⊆ G₁'` porf-closed
/// restrictions, over several corpus pairs, against every witness; the
/// number of `(G₁',M)` with `cone` true is asserted positive, and so is the
/// number of `(G₁, M)` where a smaller prefix passes and a larger one fails
/// (the implication is not an equivalence on this corpus).
#[test]
fn c07_cone_is_monotone_downward() {
    let pairs = [
        cp(
            "ex_cone",
            asyn(),
            &["a", "c"],
            prog(ex_cone_impl),
            prog(ex_cone_spec),
        ),
        cp(
            "relay",
            asyn(),
            &["a", "c"],
            prog(ex_cone_impl),
            prog(relay_spec),
        ),
        cp(
            "two",
            asyn(),
            &["a", "b", "c"],
            two_senders(1, 2),
            two_senders(1, 2),
        ),
        cp(
            "relay_nb",
            asyn(),
            &["a", "b"],
            prog(relay_nb),
            prog(relay_nb),
        ),
        cp("c2", asyn(), &["a", "b"], prog(c2_impl), prog(c2_spec)),
        cp("c2m", asyn(), &["a", "b"], prog(c2_spec), prog(c2_impl)),
        cp(
            "pe",
            fifo(),
            &["main", "c"],
            prog(pe_p2_relay),
            prog(pe_c_blocks),
        ),
    ];
    let (mut big_true, mut small_true_big_false, mut checked) = (0usize, 0usize, 0usize);
    let mut failures = Vec::new();
    for p in &pairs {
        let v = &p.visible;
        let imps = graphs_of(p.config.clone(), v, p.imp.clone());
        let specs = graphs_of(p.config.clone(), v, p.spec.clone());
        for g in &imps {
            let pre = prefixes(g);
            for m in &specs {
                // G1' ranges over g itself and its prefixes; G1 over prefixes ⊆ G1'.
                let mut bigs: Vec<(Option<&crate::vector_clock::VectorClock>, &ExecutionGraph)> =
                    vec![(None, g)];
                bigs.extend(pre.iter().map(|(vc, r)| (Some(vc), r)));
                for (bvc, big) in &bigs {
                    let cb = conev(big, m, v);
                    if cb {
                        big_true += 1;
                    }
                    for (svc, small) in &pre {
                        if let Some(bvc) = bvc {
                            if !vc_le(svc, bvc) {
                                continue;
                            }
                        }
                        checked += 1;
                        let cs = conev(small, m, v);
                        if cb && !cs {
                            failures.push(format!("{}: cone(G1') but not cone(G1)", p.name));
                        }
                        if cs && !cb {
                            small_true_big_false += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "conformance: lem:witness(2) violated: {failures:#?}"
    );
    assert!(
        big_true > 0,
        "conformance: no (G1',M) with cone true — vacuous"
    );
    assert!(
        small_true_big_false > 0,
        "conformance: never strict — suspicious"
    );
    assert!(
        checked > 100,
        "conformance: too few (G1,G1',M) triples: {checked}"
    );
}

/// **Criterion 8 (D8), first half.** Blocking pair: `cone` true, `covered`
/// false.
#[test]
fn c08_blocking_pair_cone_true_covered_false() {
    let v = vis(&["a", "c"]);
    let g1 = only_graph(prog(blocking_impl), &v);
    let m = only_graph(direct_of(1i32), &v);
    assert!(
        conev(&g1, &m, &v),
        "conformance: cone holds on the Blocking pair"
    );
    assert!(
        !covered(&summary(&g1, &v), &summary(&m, &v)),
        "conformance: covered fails on statuses"
    );
}

/// **Criterion 9 (D9)**: §11.3's computed instance, on `VisOrder` values.
#[test]
fn c09_hitting_set_instance() {
    // The signature: w_A = ⟨snd,A,1⟩, w_B = ⟨snd,B,2⟩, both done.
    let v = vis(&["a", "b"]);
    let g = only_graph(
        prog(|| {
            let x = named("x", || {});
            let xid = x.thread().id();
            let _a = named("a", move || send_msg(xid, 1i32));
            let _b = named("b", move || send_msg(xid, 2i32));
        }),
        &v,
    );
    let s = sig(&g, &v);
    let vpos: BTreeSet<VPos> = ["a", "b"]
        .iter()
        .flat_map(|t| (0..s.word(t).len()).map(move |i| vp(t, i)))
        .collect();
    let (alpha, beta) = (vp("a", 0), vp("b", 0));
    assert_eq!(
        vpos,
        [alpha.clone(), beta.clone()].into_iter().collect(),
        "conformance: vpos(s)"
    );
    let u: VisOrder = vpos
        .iter()
        .flat_map(|p| vpos.iter().map(move |q| (p.clone(), q.clone())))
        .filter(|(p, q)| p != q)
        .collect();
    let ab = (alpha.clone(), beta.clone());
    let ba = (beta.clone(), alpha.clone());
    assert_eq!(
        u,
        [ab.clone(), ba.clone()].into_iter().collect(),
        "conformance: U(s)"
    );
    let q1: VisOrder = [ab.clone()].into_iter().collect();
    let q2: VisOrder = [ba.clone()].into_iter().collect();
    let p1 = VisOrder::new();
    let p2: VisOrder = [ab.clone()].into_iter().collect();
    let mk = |o: &VisOrder| Summary {
        sig: s.clone(),
        ord: o.clone(),
    };
    assert!(
        !covered(&mk(&p1), &mk(&q1)),
        "conformance: P1 not covered by Q1"
    );
    assert!(
        !covered(&mk(&p1), &mk(&q2)),
        "conformance: P1 not covered by Q2"
    );
    assert!(covered(&mk(&p2), &mk(&q1)), "conformance: P2 covered by Q1");
    assert!(
        !covered(&mk(&p2), &mk(&q2)),
        "conformance: P2 not covered by Q2"
    );
    let a1: VisOrder = u.difference(&p1).cloned().collect();
    let a2: VisOrder = u.difference(&p2).cloned().collect();
    assert_eq!(a1, u, "conformance: A1 = U");
    assert_eq!(a2, q2, "conformance: A2 = {{(β,α)}}");
    assert!(
        !a2.is_disjoint(&q2) && a2.is_disjoint(&q1),
        "conformance: A2 misses Q1"
    );
}

/// **Criterion 10.** The order type is `VisOrder`; `ord` returns it.
#[test]
fn c10_the_order_type_is_visorder() {
    fn takes(_: &VisOrder) {}
    let v = vis(&["a", "c"]);
    let g = only_graph(direct_of(1i32), &v);
    let o: VisOrder = ordv(&g, &v);
    takes(&o);
    let _: &BTreeSet<(VPos, VPos)> = &o;
    assert_eq!(o.len(), 1, "conformance: one pair");
}

// ===========================================================================
// B. canon.rs
// ===========================================================================

fn label_at(c: &CanonicalGraph, k: &ThreadKey, i: u32) -> CanonLabel {
    c.label_at(&(k.clone(), i))
        .cloned()
        .unwrap_or_else(|| panic!("conformance: no event at {k:?}/{i}"))
}

fn key_of_named(g: &ExecutionGraph, v: &[String], n: &str) -> ThreadKey {
    Declared::of(g, v).expect("conformance: resolver").key(
        g,
        tid_named(g, n),
        Event::new(tid_named(g, n), 0),
    )
}

fn index_where(g: &ExecutionGraph, n: &str, f: impl Fn(&LabelEnum) -> bool) -> u32 {
    let t = tid_named(g, n);
    (0..g.thread_size(t) as u32)
        .find(|i| f(g.label(Event::new(t, *i))))
        .unwrap_or_else(|| panic!("conformance: no matching label in {n}"))
}

/// **Criterion 11 (D11): destinations.** A send to a declared visible
/// thread, a send to an invisible thread, and a send on an unnamed channel.
#[test]
fn c11_destinations_are_mapped() {
    let v = vis(&["a", "c"]);
    let p = prog(|| {
        let (tx, rx) = crate::channel::Builder::<i32>::new().build();
        let c = named("c", move || {
            let _v: i32 = rx.recv_msg_block();
            let _n: Option<i32> = recv_msg();
        });
        let cid = c.thread().id();
        let x = named("x", move || send_msg(cid, 7i32));
        let xid = x.thread().id();
        let _a = named("a", move || {
            send_msg(xid, 8i32);
            tx.send_msg(5);
        });
    });
    let gs = graphs_of(asyn(), &v, p);
    assert!(!gs.is_empty(), "conformance: graphs");
    for g in &gs {
        let c = canon(g, &v);
        let kx = key_of_named(g, &v, "x");
        let ka = key_of_named(g, &v, "a");
        let km = Declared::of(g, &v).expect("conformance: resolver").key(
            g,
            main_thread_id(),
            Event::new(main_thread_id(), 0),
        );
        assert_eq!(
            key_of_named(g, &v, "c"),
            ThreadKey::Declared("c".into()),
            "conformance: c"
        );
        assert!(
            matches!(kx, ThreadKey::Origination(_)),
            "conformance: x undeclared"
        );
        // x's send → Dest::Thread(Declared("c")).
        let xs = index_where(g, "x", |l| matches!(l, LabelEnum::SendMsg(_)));
        match label_at(&c, &kx, xs) {
            CanonLabel::Send { dst, .. } => assert_eq!(
                dst,
                Dest::Thread(ThreadKey::Declared("c".into())),
                "conformance: x → c"
            ),
            l => panic!("conformance: expected a send, got {l:?}"),
        }
        // a's first send → Dest::Thread(key(x)), x being invisible.
        let a_sends: Vec<u32> = {
            let t = tid_named(g, "a");
            (0..g.thread_size(t) as u32)
                .filter(|i| matches!(g.label(Event::new(t, *i)), LabelEnum::SendMsg(_)))
                .collect()
        };
        assert_eq!(a_sends.len(), 2, "conformance: a sends twice");
        match label_at(&c, &ka, a_sends[0]) {
            CanonLabel::Send { dst, .. } => {
                assert_eq!(dst, Dest::Thread(kx.clone()), "conformance: a → x")
            }
            l => panic!("conformance: expected a send, got {l:?}"),
        }
        // a's channel send → Dest::Channel(key(main), index of main's Unique).
        let u = index_where(g, "main", |l| matches!(l, LabelEnum::Unique(_)));
        assert_eq!(
            label_at(&c, &km, u),
            CanonLabel::Unique,
            "conformance: Unique"
        );
        match label_at(&c, &ka, a_sends[1]) {
            CanonLabel::Send { dst, .. } => assert_eq!(
                dst,
                Dest::Channel(km.clone(), u),
                "conformance: a → main's unnamed channel"
            ),
            l => panic!("conformance: expected a send, got {l:?}"),
        }
        // Recv blocking flags.
        let kc = ThreadKey::Declared("c".into());
        let recvs: Vec<u32> = {
            let t = tid_named(g, "c");
            (0..g.thread_size(t) as u32)
                .filter(|i| matches!(g.label(Event::new(t, *i)), LabelEnum::RecvMsg(_)))
                .collect()
        };
        assert!(
            matches!(
                label_at(&c, &kc, recvs[0]),
                CanonLabel::Recv { blocking: true, .. }
            ),
            "conformance: blocking receive"
        );
        assert!(
            matches!(
                label_at(&c, &kc, recvs[1]),
                CanonLabel::Recv {
                    blocking: false,
                    ..
                }
            ),
            "conformance: non-blocking receive"
        );
    }
}

/// **Criterion 11: the unnamed-channel fixture on its own**, so that a
/// thread-destination failure cannot mask it: one send on a channel built
/// by `channel::Builder::new().build()` in `main`.
#[test]
fn c11_unnamed_channel_destination() {
    let v = vis(&["a", "c"]);
    let p = prog(|| {
        let (tx, rx) = crate::channel::Builder::<i32>::new().build();
        let _c = named("c", move || {
            let _v: i32 = rx.recv_msg_block();
        });
        let _a = named("a", move || tx.send_msg(5));
    });
    let g = only_graph(p, &v);
    let c = canon(&g, &v);
    let km = Declared::of(&g, &v).expect("conformance: resolver").key(
        &g,
        main_thread_id(),
        Event::new(main_thread_id(), 0),
    );
    let u = index_where(&g, "main", |l| matches!(l, LabelEnum::Unique(_)));
    let s = index_where(&g, "a", |l| matches!(l, LabelEnum::SendMsg(_)));
    match label_at(&c, &ThreadKey::Declared("a".into()), s) {
        CanonLabel::Send { dst, .. } => assert_eq!(
            dst,
            Dest::Channel(km, u),
            "conformance: a's send is on main's unnamed channel"
        ),
        l => panic!("conformance: expected a send, got {l:?}"),
    }
}

/// **Criterion 11: the rest of the label projection.** `End{result}`,
/// `TCreate`/`TJoin` children, `CToss`, `Choice`, and every `Block` kind but
/// `ConfPrune`.
#[test]
fn c11_label_zoo() {
    let v = vis(&["c"]);
    let p = prog(|| {
        let val = thread::Builder::new()
            .name("val".to_string())
            .spawn(|| 42i32)
            .unwrap();
        let _s = named("s", || crate::assume_impl(false, None));
        let _e = named("e", || crate::assert(false));
        let blk = named("blk", || {
            let _x: i32 = recv_msg_block();
        });
        let _j = named("j", move || {
            let _ = blk.join();
        });
        let _c = named("c", || {
            let _k = (1..=2usize).nondet();
            let _t = crate::nondet();
        });
        let _r = val.join();
    });
    let gs = graphs_of(asyn(), &v, p);
    assert_eq!(
        gs.len(),
        4,
        "conformance: two Choice values × two CToss values"
    );
    let mut seen_choices = BTreeSet::new();
    let mut seen_toss = BTreeSet::new();
    for g in &gs {
        let c = canon(g, &v);
        let k = |n: &str| key_of_named(g, &v, n);
        let km = Declared::of(g, &v).expect("conformance: resolver").key(
            g,
            main_thread_id(),
            Event::new(main_thread_id(), 0),
        );
        // End{result} of `val`.
        let end = index_where(g, "val", |l| matches!(l, LabelEnum::End(_)));
        assert_eq!(
            label_at(&c, &k("val"), end),
            CanonLabel::End {
                result: Val::new(42i32)
            },
            "conformance: End carries the return value"
        );
        // main's TCreate(val) and TJoin(val).
        let tc = index_where(g, "main", |l| match l {
            LabelEnum::TCreate(t) => name_of(g, t.cid()).as_deref() == Some("val"),
            _ => false,
        });
        assert_eq!(
            label_at(&c, &km, tc),
            CanonLabel::TCreate { child: k("val") },
            "conformance: TCreate child"
        );
        let tj = index_where(g, "main", |l| matches!(l, LabelEnum::TJoin(_)));
        assert_eq!(
            label_at(&c, &km, tj),
            CanonLabel::TJoin { child: k("val") },
            "conformance: TJoin child"
        );
        // Block kinds.
        let blk_of = |n: &str| {
            let i = index_where(g, n, |l| matches!(l, LabelEnum::Block(_)));
            label_at(&c, &k(n), i)
        };
        use crate::conformance::canon::BlockKind;
        assert_eq!(
            blk_of("s"),
            CanonLabel::Block {
                kind: BlockKind::Assume
            },
            "conformance: s"
        );
        assert_eq!(
            blk_of("e"),
            CanonLabel::Block {
                kind: BlockKind::Assert
            },
            "conformance: e"
        );
        assert_eq!(
            blk_of("blk"),
            CanonLabel::Block {
                kind: BlockKind::Value
            },
            "conformance: blk"
        );
        assert_eq!(
            blk_of("j"),
            CanonLabel::Block {
                kind: BlockKind::Join(k("blk"))
            },
            "conformance: j"
        );
        assert!(
            blk_of("blk").is_placeholder() && blk_of("j").is_placeholder(),
            "conformance: E5"
        );
        assert!(
            !blk_of("s").is_placeholder() && !blk_of("e").is_placeholder(),
            "conformance: E5"
        );
        // Choice and CToss.
        let ch = index_where(g, "c", |l| matches!(l, LabelEnum::Choice(_)));
        match label_at(&c, &k("c"), ch) {
            CanonLabel::Choice { result, range } => {
                assert_eq!(range, (1, 2), "conformance: Choice range");
                seen_choices.insert(result);
            }
            l => panic!("conformance: expected Choice, got {l:?}"),
        }
        let ct = index_where(g, "c", |l| matches!(l, LabelEnum::CToss(_)));
        match label_at(&c, &k("c"), ct) {
            CanonLabel::CToss { result } => {
                seen_toss.insert(result);
            }
            l => panic!("conformance: expected CToss, got {l:?}"),
        }
        assert_eq!(
            label_at(&c, &k("c"), 0),
            CanonLabel::Begin,
            "conformance: Begin at 0 (E2)"
        );
    }
    assert_eq!(
        seen_choices,
        [1, 2].into_iter().collect(),
        "conformance: Choice results"
    );
    assert_eq!(
        seen_toss,
        [false, true].into_iter().collect(),
        "conformance: CToss results"
    );
}

/// **Criterion 11**: the corpus produces no `Dest::Other`, and sends exist.
#[test]
fn c11_corpus_has_no_dest_other() {
    let (mut sends, mut other) = (0usize, Vec::new());
    for cg in corpus_graphs() {
        for g in cg.imp.iter().chain(cg.spec.iter()) {
            for (p, l) in canon(g, &cg.visible).events() {
                if let CanonLabel::Send { dst, .. } = l {
                    sends += 1;
                    if matches!(dst, Dest::Other(_)) {
                        other.push(format!("{}: {p:?}", cg.name));
                    }
                }
            }
        }
    }
    assert!(
        other.is_empty(),
        "conformance: Dest::Other in the corpus: {other:#?}"
    );
    assert!(
        sends > 100,
        "conformance: too few sends to mean anything: {sends}"
    );
}

/// Criterion 21's `loc.rs` accessors, directly.
#[test]
fn c21_loc_accessors_downcast_the_inner_object() {
    use crate::loc::Loc;
    let t = crate::thread::construct_thread_id(3);
    let thread_loc = Loc::new(crate::channel::Thread(t));
    assert_eq!(
        thread_loc.as_thread_id(),
        Some(t),
        "conformance: channel::Thread"
    );
    assert_eq!(thread_loc.as_event(), None, "conformance: not an event");
    let bare = Loc::new(t);
    assert_eq!(
        bare.as_thread_id(),
        None,
        "conformance: a bare ThreadId is not a thread Loc"
    );
    let e = Event::new(t, 4);
    let ev_loc = Loc::new(e);
    assert_eq!(ev_loc.as_event(), Some(e), "conformance: Event loc");
    assert_eq!(ev_loc.as_thread_id(), None, "conformance: not a thread");
    assert_eq!(
        Loc::new(17u32).as_event(),
        None,
        "conformance: other identifier"
    );
}

// --- criterion 12 ------------------------------------------------------------

/// `p` and `q` (invisible) each wait for main, then spawn `x` / `y`
/// (invisible), which send to main. Which of `x`, `y` is spawned first is
/// the installation order of `p`'s and `q`'s receives.
fn two_parents(x_sends_own_id: bool) -> Prog {
    prog(move || {
        let p = named("p", move || {
            let _: i32 = recv_msg_block();
            let _x = named("x", move || {
                if x_sends_own_id {
                    send_msg(main_thread_id(), thread::current_id());
                } else {
                    send_msg(main_thread_id(), 1i32);
                }
            });
        });
        let q = named("q", || {
            let _: i32 = recv_msg_block();
            let _y = named("y", || send_msg(main_thread_id(), 2i32));
        });
        send_msg(p.thread().id(), 0i32);
        send_msg(q.thread().id(), 0i32);
    })
}

fn two_orders(p: Prog) -> (ExecutionGraph, ExecutionGraph) {
    let d = Driver::start(asyn(), p).send("main").send("main");
    let o1 = d.recv("p", Some("main")).recv("q", Some("main"));
    let o2 = d.recv("q", Some("main")).recv("p", Some("main"));
    let o1 = o1.send("x").send("y");
    let o2 = o2.send("y").send("x");
    assert!(
        o1.is_complete() && o2.is_complete(),
        "conformance: both orders complete"
    );
    (o1.graph, o2.graph)
}

/// **Criterion 12 (D12).** One graph through two installation orders whose
/// spawns come from two parents: the `ThreadId`s differ (control), the
/// canonical forms are equal.
#[test]
fn c12_thread_identity_survives_two_installation_orders() {
    let v = vis(&["p"]);
    let (g1, g2) = two_orders(two_parents(false));
    assert_ne!(
        tid_named(&g1, "x"),
        tid_named(&g2, "x"),
        "conformance: control — x's ThreadId must differ between the two orders"
    );
    let (c1, c2) = (canon(&g1, &v), canon(&g2, &v));
    assert!(c1 == c2, "conformance: one graph, one canonical form");
    assert_eq!(c1.key(), c2.key(), "conformance: and one key");
    let mut set = CanonSet::new();
    assert!(set.insert(c1), "conformance: first insert");
    assert!(!set.insert(c2), "conformance: second order is a repeat");
    // Declared vs Origination, and never an undeclared name.
    assert_eq!(
        key_of_named(&g1, &v, "p"),
        ThreadKey::Declared("p".into()),
        "conformance: p"
    );
    for n in ["q", "x", "y"] {
        assert!(
            matches!(key_of_named(&g1, &v, n), ThreadKey::Origination(_)),
            "conformance: {n} is keyed by origination, not by its name"
        );
    }
}

/// **Criterion 12, E4's pinned limitation.** When `x` sends its own
/// `ThreadId`, the same graph gets two forms. Expected, documented.
#[test]
fn c12_e4_a_thread_id_in_a_value_gives_two_keys() {
    let v = vis(&["p"]);
    let (g1, g2) = two_orders(two_parents(true));
    assert!(
        canon(&g1, &v) != canon(&g2, &v),
        "conformance: E4 limitation — a ThreadId in a message value is opaque"
    );
}

/// **Criterion 12**: `AmbiguousName` is propagated as an error.
#[test]
fn c12_ambiguous_name_is_an_error() {
    let v = vis(&["c"]);
    let g = only_graph(
        prog(|| {
            let _c1 = named("c", || {});
            let _c2 = named("c", || {});
        }),
        &v,
    );
    assert_eq!(
        CanonicalGraph::of(&g, &v).err(),
        Some(ObsError::AmbiguousName { name: "c".into() }),
        "conformance: ambiguous declared name"
    );
    // An undeclared duplicate name is fine: both threads are Origination.
    let c = CanonicalGraph::of(&g, &[]).expect("conformance: undeclared duplicates are fine");
    let keys: BTreeSet<ThreadKey> = c.events().iter().map(|(p, _)| p.0.clone()).collect();
    assert_eq!(keys.len(), 3, "conformance: main and two distinct c's");
}

// --- criterion 13 ------------------------------------------------------------

/// **Criterion 13 (D13).** Values compare by `msg_equals`; `CanonSet`
/// resolves a shared key by full equality.
#[test]
fn c13_values_compare_and_the_set_resolves_by_equality() {
    let v = vis(&["a", "c"]);
    let g1 = only_graph(direct_of(1i32), &v);
    let g1b = only_graph(direct_of(1i32), &v);
    let g2 = only_graph(direct_of(2i32), &v);
    let (c1, c1b, c2) = (canon(&g1, &v), canon(&g1b, &v), canon(&g2, &v));
    assert!(c1 == c1b, "conformance: same graph, two runs");
    assert!(c1 != c2, "conformance: value differs");
    assert_eq!(
        c1.key(),
        c2.key(),
        "conformance: shared key (values projected away)"
    );
    let mut s = CanonSet::new();
    assert!(s.insert(c1.clone()), "conformance: insert 1");
    assert!(
        s.insert(c2.clone()),
        "conformance: insert 2 — same key, unequal"
    );
    assert!(!s.insert(c1b), "conformance: repeat");
    assert_eq!(s.len(), 2, "conformance: two members");
    assert!(
        s.contains(&c1) && s.contains(&c2),
        "conformance: both present"
    );
}

fn blanked(mut g: ExecutionGraph) -> ExecutionGraph {
    g.initialize_for_execution();
    g
}

/// **E3**: a form built at the start of replay — every send value pending —
/// panics.
#[test]
#[should_panic(expected = "send value at")]
fn c13_e3_pending_send_value_panics() {
    // `main` sends: its send is the first label the form visits (thread 0),
    // ahead of every pending `End`, so this isolates the send assertion.
    let v = vis(&["c"]);
    let g = blanked(only_graph(prog(pe_p1_direct), &v));
    let _ = CanonicalGraph::of(&g, &v);
}

/// **E3**: the same for a pending `End` result (no send in the program).
#[test]
#[should_panic(expected = "thread result at")]
fn c13_e3_pending_end_result_panics() {
    let v = vis(&["val"]);
    let g = only_graph(
        prog(|| {
            let _v = thread::Builder::new()
                .name("val".to_string())
                .spawn(|| 42i32)
                .unwrap();
        }),
        &v,
    );
    let g = blanked(g);
    let _ = CanonicalGraph::of(&g, &v);
}

/// **A9**: a `NaN` payload makes a graph unequal to itself; `CanonSet`
/// never deduplicates it.
#[test]
fn c13_a9_nan_is_never_deduplicated() {
    let v = vis(&["a", "c"]);
    let g = only_graph(direct_of(f64::NAN), &v);
    let c = canon(&g, &v);
    assert!(c != c.clone(), "conformance: A9 — not reflexive");
    let mut s = CanonSet::new();
    assert!(
        s.insert(c.clone()) && s.insert(c),
        "conformance: both inserted"
    );
    assert_eq!(s.len(), 2, "conformance: A9 — two entries for one graph");
}

// --- criterion 14 ------------------------------------------------------------

fn differing_positions(a: &CanonicalGraph, b: &CanonicalGraph) -> usize {
    assert_eq!(
        a.events().len(),
        b.events().len(),
        "conformance: same shape"
    );
    a.events()
        .iter()
        .zip(b.events())
        .filter(|(x, y)| {
            assert_eq!(x.0, y.0, "conformance: same positions");
            x.1 != y.1
        })
        .count()
}

/// **Criterion 14 (D14).** A `Choice` value, a `CToss` value and a receive
/// source each separate two otherwise-identical graphs.
#[test]
fn c14_choice_ctoss_and_rf_are_in_the_memo_key() {
    let v = vis(&["a"]);
    let choice = graphs_of(
        asyn(),
        &v,
        prog(|| {
            let _a = named("a", || {
                let _k = (0..=1usize).nondet();
            });
        }),
    );
    assert_eq!(choice.len(), 2, "conformance: two Choice values");
    let (x, y) = (canon(&choice[0], &v), canon(&choice[1], &v));
    assert_eq!(
        differing_positions(&x, &y),
        1,
        "conformance: only the Choice differs"
    );
    assert!(x != y, "conformance: Choice value in the key");

    let toss = graphs_of(
        asyn(),
        &v,
        prog(|| {
            let _a = named("a", || {
                let _t = crate::nondet();
            });
        }),
    );
    assert_eq!(toss.len(), 2, "conformance: two CToss values");
    let (x, y) = (canon(&toss[0], &v), canon(&toss[1], &v));
    assert_eq!(
        differing_positions(&x, &y),
        1,
        "conformance: only the CToss differs"
    );
    assert!(x != y, "conformance: CToss value in the key");

    let vr = vis(&["a", "b", "c"]);
    let rf = graphs_of(asyn(), &vr, two_senders(1, 1));
    assert_eq!(rf.len(), 2, "conformance: two sources");
    let (x, y) = (canon(&rf[0], &vr), canon(&rf[1], &vr));
    assert_eq!(
        differing_positions(&x, &y),
        0,
        "conformance: labels identical"
    );
    assert!(x.rf() != y.rf(), "conformance: rf differs");
    assert!(x != y, "conformance: receive source in the key");
}

// ===========================================================================
// C. witness.rs
// ===========================================================================

fn by_c_source(gs: &[ExecutionGraph], src: &str) -> ExecutionGraph {
    gs.iter()
        .find(|g| recv_source(g, "c", 0) == Some(send_of(g, src)))
        .cloned()
        .expect("conformance: graph with that source")
}

fn exec(g: &ExecutionGraph) -> CompleteExecution<'_> {
    CompleteExecution::assume_finished_at_gate(g)
}

/// **Criterion 15.** One admission path. Structural: the only `&mut self`
/// method of `WitnessCache` is `admit_from_sweep`.
#[test]
fn c15_one_admission_path() {
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/witness.rs"),
    )
    .expect("conformance: witness.rs readable");
    let muts: Vec<&str> = src.lines().filter(|l| l.contains("&mut self")).collect();
    assert_eq!(muts.len(), 1, "conformance: one mutating method: {muts:?}");
    let fn_lines: Vec<&str> = src
        .lines()
        .filter(|l| l.trim_start().starts_with("pub(crate) fn admit"))
        .collect();
    assert_eq!(fn_lines.len(), 1, "conformance: one admit fn: {fn_lines:?}");
    assert!(
        src.contains("pub(crate) fn admit_from_sweep(\n        &mut self,\n        exec: CompleteExecution<'_>,"),
        "conformance: admission takes a CompleteExecution"
    );
}

/// **Criterion 16 (D16).** Exact probes, two witnesses, each/neither/both.
#[test]
fn c16_w_is_probed_exactly() {
    let v = vis(&["a", "b", "c"]);
    let specs = graphs_of(asyn(), &v, two_senders(1, 2));
    let (ma, mb) = (by_c_source(&specs, "a"), by_c_source(&specs, "b"));
    let mut wc = WitnessCache::new(v.clone());
    assert_eq!(
        wc.admit_from_sweep(exec(&ma)),
        Ok(true),
        "conformance: admit Ma"
    );
    assert_eq!(
        wc.admit_from_sweep(exec(&mb)),
        Ok(true),
        "conformance: admit Mb"
    );
    let imps = graphs_of(asyn(), &v, two_senders(1, 2));
    let (ga, gb) = (by_c_source(&imps, "a"), by_c_source(&imps, "b"));
    let neither = graphs_of(asyn(), &v, two_senders(3, 4));
    let hit = |g: &ExecutionGraph| -> Option<CanonicalGraph> {
        wc.probe_covered(&summary(g, &v))
            .map(|m| canon(m.graph(), &v))
    };
    assert_eq!(hit(&ga), Some(canon(&ma, &v)), "conformance: Ga → Ma");
    assert_eq!(hit(&gb), Some(canon(&mb, &v)), "conformance: Gb → Mb");
    for g in &neither {
        assert_eq!(hit(g), None, "conformance: neither");
    }
    // probe_cone: each, neither, both.
    let hitc = |g: &ExecutionGraph| -> Option<CanonicalGraph> {
        wc.probe_cone(g, &w(g, &v)).map(|m| canon(m.graph(), &v))
    };
    assert_eq!(hitc(&ga), Some(canon(&ma, &v)), "conformance: cone Ga → Ma");
    assert_eq!(hitc(&gb), Some(canon(&mb, &v)), "conformance: cone Gb → Mb");
    for g in &neither {
        assert_eq!(hitc(g), None, "conformance: cone neither");
    }
    let prefix = Driver::start(asyn(), two_senders(1, 2)).send("a").send("b");
    assert!(
        conev(&prefix.graph, &ma, &v),
        "conformance: prefix passes Ma"
    );
    assert!(
        conev(&prefix.graph, &mb, &v),
        "conformance: prefix passes Mb"
    );
    assert!(
        hitc(&prefix.graph).is_some(),
        "conformance: both — some witness returned"
    );

    // covered, "both": relay_nb, M1 (r reads a) and M2 (r reads ⊥) share sig.
    let vr = vis(&["a", "b"]);
    let rs = graphs_of(asyn(), &vr, prog(relay_nb));
    assert_eq!(rs.len(), 2, "conformance: r reads a or ⊥");
    let r_reads_a = |g: &ExecutionGraph| recv_source(g, "r", 0).is_some();
    let m1 = rs
        .iter()
        .find(|g| r_reads_a(g))
        .cloned()
        .expect("conformance: M1");
    let m2 = rs
        .iter()
        .find(|g| !r_reads_a(g))
        .cloned()
        .expect("conformance: M2");
    assert_eq!(
        ordv(&m1, &vr),
        [pair(("a", 0), ("b", 0))].into_iter().collect::<VisOrder>(),
        "conformance: ord(M1)"
    );
    assert_eq!(ordv(&m2, &vr), VisOrder::new(), "conformance: ord(M2)");
    let (s1, s2) = (summary(&m1, &vr), summary(&m2, &vr));
    assert!(
        covered(&s1, &s1) && covered(&s1, &s2),
        "conformance: G(r←a) by both"
    );
    assert!(
        covered(&s2, &s2) && !covered(&s2, &s1),
        "conformance: G(r←⊥) by M2 only"
    );
    let mut only1 = WitnessCache::new(vr.clone());
    only1
        .admit_from_sweep(exec(&m1))
        .expect("conformance: admit");
    assert!(
        only1.probe_covered(&s1).is_some(),
        "conformance: M1 hit for G(r←a)"
    );
    assert!(
        only1.probe_covered(&s2).is_none(),
        "conformance: M1 miss for G(r←⊥)"
    );
    let mut both = WitnessCache::new(vr.clone());
    both.admit_from_sweep(exec(&m1))
        .expect("conformance: admit");
    both.admit_from_sweep(exec(&m2))
        .expect("conformance: admit");
    assert!(both.probe_covered(&s1).is_some(), "conformance: both hold");
    assert_eq!(
        both.probe_covered(&s2).map(|m| canon(m.graph(), &vr)),
        Some(canon(&m2, &vr)),
        "conformance: G(r←⊥) can only be answered by M2"
    );
}

/// **Criterion 17.** `W` is a set: duplicate admission across runs is a no-op.
#[test]
fn c17_w_is_a_set() {
    let v = vis(&["a", "b", "c"]);
    let run1 = graphs_of(asyn(), &v, two_senders(1, 2));
    let run2 = graphs_of(asyn(), &v, two_senders(1, 2));
    let mut wc = WitnessCache::new(v.clone());
    assert!(wc.is_empty(), "conformance: empty");
    let ma1 = by_c_source(&run1, "a");
    let ma2 = by_c_source(&run2, "a");
    assert_eq!(
        wc.admit_from_sweep(exec(&ma1)),
        Ok(true),
        "conformance: first"
    );
    assert_eq!(
        wc.admit_from_sweep(exec(&ma2)),
        Ok(false),
        "conformance: duplicate"
    );
    assert_eq!(wc.len(), 1, "conformance: one witness");
    assert_eq!(
        wc.admit_from_sweep(exec(&by_c_source(&run2, "b"))),
        Ok(true),
        "conformance: a different witness"
    );
    assert_eq!(wc.len(), 2, "conformance: two witnesses");
    // A9: NaN witnesses are admitted twice (documented).
    let vn = vis(&["a", "c"]);
    let gn = only_graph(direct_of(f64::NAN), &vn);
    let mut wn = WitnessCache::new(vn);
    assert_eq!(
        wn.admit_from_sweep(exec(&gn)),
        Ok(true),
        "conformance: NaN 1"
    );
    assert_eq!(
        wn.admit_from_sweep(exec(&gn)),
        Ok(true),
        "conformance: NaN 2 (A9)"
    );
    assert_eq!(wn.len(), 2, "conformance: A9 overcount");
}

/// **Finding (tester): a failed admission poisons `W`.** `admit_from_sweep`
/// records the canonical form in `seen` *before* computing the summary, and
/// `Summary::of` can fail (`NotSpawned` for a declared name no thread has).
/// The retry then answers `Ok(false)` — "already held" — while `len()` is 0.
/// Expected by criterion 17 ("W is a set; a duplicate admission is a no-op;
/// len is observable"): a graph is reported held iff it is held.
#[test]
fn c17_a_failed_admission_does_not_poison_the_set() {
    let v = vis(&["a", "c", "ghost"]);
    let g = only_graph(direct_of(1i32), &v);
    let mut wc = WitnessCache::new(v);
    assert!(
        wc.admit_from_sweep(exec(&g)).is_err(),
        "conformance: NotSpawned"
    );
    let second = wc.admit_from_sweep(exec(&g));
    assert!(
        !(second == Ok(false) && wc.is_empty()),
        "conformance: W claims to hold a graph it does not hold (second = {second:?}, len = {})",
        wc.len()
    );
}

// ===========================================================================
// D. cert.rs
// ===========================================================================

fn cert_at(g: &ExecutionGraph, v: &[String]) -> Certificate {
    Certificate::absence_established(g, v).expect("conformance: certificate")
}

fn valid(c: &Certificate, g: &ExecutionGraph, v: &[String]) -> bool {
    c.valid_at(g, v).expect("conformance: valid_at")
}

/// `A: send(C,1) ‖ B: send(C,2) ‖ C: x := recv(); t := nondet(); y := recv_nb()`.
fn p18() -> Prog {
    prog(|| {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
            let _t = crate::nondet();
            let _y: Option<i32> = recv_msg();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, 1i32));
        let _b = named("b", move || send_msg(cid, 2i32));
    })
}

/// The criterion-18 graphs, by name, built through the prober.
struct C18 {
    p0: Driver,
    pre: Driver,
    gc: Driver,
    gii: Driver,
    nd_f: Driver,
    nd_t: Driver,
    full_bot: Driver,
    full_b: Driver,
}

fn c18_graphs() -> C18 {
    let p0 = Driver::start(asyn(), p18());
    let pre = p0.send("a").send("b");
    let gc = pre.recv("c", Some("a"));
    let gii = pre.recv("c", Some("b"));
    let nd_f = gc.nondet("c", NondetValue::Toss(false));
    let nd_t = gc.nondet("c", NondetValue::Toss(true));
    let full_bot = nd_f.recv("c", None);
    let full_b = nd_f.recv("c", Some("b"));
    C18 {
        p0,
        pre,
        gc,
        gii,
        nd_f,
        nd_t,
        full_bot,
        full_b,
    }
}

/// **Criterion 18 (D18): the two isolating failures.**
#[test]
fn c18_isolating_failures() {
    let v = vis(&["a", "b", "c"]);
    let g = c18_graphs();
    let c = cert_at(&g.gc.graph, &v);
    assert!(
        valid(&c, &g.gc.graph, &v),
        "conformance: valid at its own set point"
    );
    // (ii)-only: the source sibling. Control: no set-point position missing.
    let here = canon(&g.gii.graph, &v);
    let set = c.set_at().expect("conformance: set").clone();
    assert!(
        set.events().iter().all(|(p, _)| here.label_at(p).is_some()),
        "conformance: (ii)-only control — every position present"
    );
    assert!(!valid(&c, &g.gii.graph, &v), "conformance: (ii)-only fails");
    // (i)-only: one install before. Control: present positions agree.
    let before = canon(&g.pre.graph, &v);
    let missing = set
        .events()
        .iter()
        .filter(|(p, l)| !l.is_placeholder() && before.label_at(p).is_none())
        .count();
    assert_eq!(
        missing, 1,
        "conformance: (i)-only control — exactly C's receive missing"
    );
    assert!(
        set.events()
            .iter()
            .filter(|(p, _)| before.label_at(p).is_some())
            .all(|(p, l)| l.is_placeholder() || before.label_at(p) == Some(l)),
        "conformance: (i)-only control — present positions agree"
    );
    assert!(!valid(&c, &g.pre.graph, &v), "conformance: (i)-only fails");
}

/// **Criterion 18: extensions keep the certificate**, including `SetND` and
/// `SetRF` of the installed event, and an E5 unblocking extension.
#[test]
fn c18_extensions_keep_it() {
    let v = vis(&["a", "b", "c"]);
    let g = c18_graphs();
    let c = cert_at(&g.gc.graph, &v);
    for (n, d) in [
        ("SetND false", &g.nd_f),
        ("SetND true", &g.nd_t),
        ("SetRF ⊥", &g.full_bot),
        ("SetRF b", &g.full_b),
    ] {
        assert!(
            valid(&c, &d.graph, &v),
            "conformance: {n} extends the set point"
        );
    }
    assert!(
        g.full_bot.is_complete() && g.full_b.is_complete(),
        "conformance: completions"
    );
    // E5: the set point holds C's Block{Value} placeholder; G_c has the receive.
    let p0 = canon(&g.p0.graph, &v);
    assert!(
        p0.events().iter().any(|(_, l)| l.is_placeholder()),
        "conformance: E5 control — the set point carries a placeholder"
    );
    let c0 = cert_at(&g.p0.graph, &v);
    assert!(
        valid(&c0, &g.gc.graph, &v),
        "conformance: E5 unblocking extension"
    );
    assert!(
        valid(&c0, &g.full_b.graph, &v),
        "conformance: E5, further on"
    );
    // Forward alternative of a nondet in the set point: label-only failure.
    let cf = cert_at(&g.nd_f.graph, &v);
    assert!(
        !valid(&cf, &g.nd_t.graph, &v),
        "conformance: CToss alternative fails"
    );
    assert!(
        canon(&g.nd_f.graph, &v).rf() == canon(&g.nd_t.graph, &v).rf(),
        "conformance: label-only control — rf identical"
    );
}

/// `R: y := recv_nb() ‖ A: send(R,1) ‖ Z: w := recv_nb() ‖ B: send(Z,2)`.
fn prev() -> Prog {
    prog(|| {
        let r = named("r", || {
            let _y: Option<i32> = recv_msg();
        });
        let rid = r.thread().id();
        let z = named("z", || {
            let _w: Option<i32> = recv_msg();
        });
        let zid = z.thread().id();
        let _a = named("a", move || send_msg(rid, 1i32));
        let _b = named("b", move || send_msg(zid, 2i32));
    })
}

/// **Criterion 18: backward revisits.** The revisit result `g` is built
/// directly (the same graph `SetRF(G|E∖D, r, e)` yields).
#[test]
fn c18_backward_revisits() {
    let v = vis(&["a", "b", "r", "z"]);
    let d = Driver::start(asyn(), prev());
    // Keeps set_at intact: set at {b0}; G = {b0, r0←⊥, a0}; revisit r by a0:
    // D = ∅, the revisited receive is outside the set point.
    let s = d.send("b");
    let g_keep = s.send("a").recv("r", Some("a"));
    assert!(
        valid(&cert_at(&s.graph, &v), &g_keep.graph, &v),
        "conformance: survives"
    );
    // Deletion set intersects set_at: set at {r0←⊥, b0} (b0 after r0);
    // revisit by a0 deletes b0 and re-sources r0.
    let s3 = d.recv("r", None).send("b");
    let g_rev = d.send("a").recv("r", Some("a"));
    assert!(
        !valid(&cert_at(&s3.graph, &v), &g_rev.graph, &v),
        "conformance: dropped"
    );
    // Revisited receive inside the set point, nothing deleted: (ii).
    let s2 = d.recv("r", None);
    assert!(
        !valid(&cert_at(&s2.graph, &v), &g_rev.graph, &v),
        "conformance: (ii)"
    );
}

/// My own reading of (iii): no event of `g` outside the set point is
/// porf-before a non-placeholder event inside it. Computed from the graphs
/// and the canonical positions, independently of `valid_at`.
fn prefix_closed(set: &CanonicalGraph, g: &ExecutionGraph, v: &[String]) -> bool {
    let decl = Declared::of(g, v).expect("conformance: resolver");
    let mut inside = Vec::new();
    let mut outside = Vec::new();
    for t in g.thread_ids() {
        let k = decl.key(g, t, Event::new(t, 0));
        for i in 0..g.thread_size(t) as u32 {
            let e = Event::new(t, i);
            match set.label_at(&(k.clone(), i)) {
                Some(l) if !l.is_placeholder() => inside.push(e),
                Some(_) => {}
                None => outside.push(e),
            }
        }
    }
    !outside
        .iter()
        .any(|&o| inside.iter().any(|&i| o != i && g.in_porf(o, i)))
}

/// **Criterion 18: "(iii) agrees".** Over every `(set_at, g)` this file
/// builds for programs P18 and the revisit program, plus every porf-closed
/// restriction of every complete graph of four programs against every graph
/// of the same program: `valid_at ⟹ (iii)`. Positive counts both ways, and
/// every restriction is valid at the graph it was cut from.
#[test]
fn c18_iii_agrees_corpus_wide() {
    let mut families: Vec<(Vec<String>, Vec<ExecutionGraph>)> = Vec::new();
    let g = c18_graphs();
    families.push((
        vis(&["a", "b", "c"]),
        vec![
            g.p0.graph,
            g.pre.graph,
            g.gc.graph,
            g.gii.graph,
            g.nd_f.graph,
            g.nd_t.graph,
            g.full_bot.graph,
            g.full_b.graph,
        ],
    ));
    let d = Driver::start(asyn(), prev());
    families.push((
        vis(&["a", "b", "r", "z"]),
        vec![
            d.graph.clone(),
            d.send("b").graph,
            d.send("b").send("a").recv("r", Some("a")).graph,
            d.recv("r", None).graph,
            d.recv("r", None).send("b").graph,
            d.send("a").recv("r", Some("a")).graph,
        ],
    ));
    let mut own_cut_valid = 0usize;
    for (vv, p) in [
        (vis(&["a", "b", "c"]), two_senders(1, 2)),
        (vis(&["a", "b"]), prog(relay_nb)),
        (vis(&["a", "c"]), prog(blocking_impl)),
        (vis(&["a", "b"]), prog(c2_impl)),
    ] {
        let complete = graphs_of(asyn(), &vv, p);
        let mut all = complete.clone();
        for c in &complete {
            for (_, r) in prefixes(c) {
                // A restriction is valid at the graph it was cut from.
                assert!(
                    valid(&cert_at(&r, &vv), c, &vv),
                    "conformance: a porf-closed restriction must be extended by its source"
                );
                own_cut_valid += 1;
                all.push(r);
            }
        }
        families.push((vv, all));
    }
    let (mut t, mut f) = (0usize, 0usize);
    let mut bad = Vec::new();
    for (vv, gs) in &families {
        for s in gs {
            let c = cert_at(s, vv);
            let set = c.set_at().expect("conformance: set").clone();
            for gg in gs {
                let ok = valid(&c, gg, vv);
                if ok {
                    t += 1;
                    if !prefix_closed(&set, gg, vv) {
                        bad.push(format!("{set:?} ⊄ {gg:?}"));
                    }
                } else {
                    f += 1;
                }
            }
        }
    }
    assert!(bad.is_empty(), "conformance: (iii) disagrees: {bad:#?}");
    assert!(
        t > 100 && f > 100,
        "conformance: both outcomes exercised: {t} true, {f} false"
    );
    assert!(
        own_cut_valid > 20,
        "conformance: restrictions: {own_cut_valid}"
    );
}

/// **Criterion 19.** Narrow constructibility: only `absence_established`
/// builds a set certificate; an unset certificate is valid nowhere; the two
/// D5 rules behave as named.
#[test]
fn c19_constructibility_and_the_two_rules() {
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/cert.rs"),
    )
    .expect("conformance: cert.rs readable");
    assert_eq!(
        src.matches("set_at: Some(").count(),
        1,
        "conformance: one constructor of a set certificate"
    );
    let v = vis(&["a", "b", "c"]);
    let g = c18_graphs();
    let none = Certificate::none();
    assert!(!none.is_set(), "conformance: none is unset");
    assert!(
        !valid(&none, &g.gc.graph, &v),
        "conformance: unset is valid nowhere"
    );
    let c = cert_at(&g.gc.graph, &v);
    assert!(c.is_set(), "conformance: set");
    assert!(
        c.clone().transfer() == c,
        "conformance: transfer is the identity"
    );
    assert!(
        c.clone().dropped_on_pop() == Certificate::none(),
        "conformance: drop"
    );
    assert!(
        c.clone()
            .kept_at(&g.nd_f.graph, &v)
            .expect("conformance: kept_at")
            == c,
        "conformance: kept where valid"
    );
    assert!(
        c.clone()
            .kept_at(&g.gii.graph, &v)
            .expect("conformance: kept_at")
            == Certificate::none(),
        "conformance: dropped where not"
    );
}

// ===========================================================================
// Criterion 20: nondet and error events of a visible thread are invisible.
// ===========================================================================

#[test]
fn c20_nondet_and_error_events_are_invisible() {
    let v = vis(&["a"]);
    let g = only_graph(
        prog(|| {
            let _a = named("a", || {
                let _k = (0..=0usize).nondet();
                send_msg(main_thread_id(), 1i32);
                crate::assert(false);
            });
        }),
        &v,
    );
    let a = tid_named(&g, "a");
    let mut kinds = Vec::new();
    for i in 0..g.thread_size(a) as u32 {
        let e = Event::new(a, i);
        let is_send = matches!(g.label(e), LabelEnum::SendMsg(_));
        assert_eq!(
            is_visible_event(&g, e, &v),
            is_send,
            "conformance: only the send of a is visible ({e})"
        );
        kinds.push(format!("{}", g.label(e)));
    }
    assert!(
        g.thread_size(a) >= 4,
        "conformance: Begin, Choice, send, Block(Assert) at least: {kinds:?}"
    );
}

/// **Criterion 11 / E4 (round 04 n1).** A `channel::Thread(tid)` whose `tid`
/// has no thread in the graph — reachable only through the public
/// `thread::construct_thread_id` — is a panic, never `Dest::Other`.
/// The message names the position of the label that names the thread (T3).
#[test]
fn c11_n1_a_send_to_an_unspawned_thread_id_panics() {
    let v = vis(&["a"]);
    let g = only_graph(
        prog(|| {
            let _a = named("a", || {
                send_msg(crate::thread::construct_thread_id(99), 1i32)
            });
        }),
        &v,
    );
    let at = send_of(&g, "a");
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = CanonicalGraph::of(&g, &v);
    }));
    let payload = r.expect_err("conformance: an unspawned ThreadId must panic, not map");
    let msg = payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default();
    assert!(
        msg.contains("which no TCreate in the graph spawned"),
        "conformance: E4 panic text: {msg}"
    );
    assert!(
        msg.contains(&format!("the label at {at} names thread")),
        "conformance: the panic must name the position {at}: {msg}"
    );
}

/// **Criterion 18, the documented rule's last sentence.** Validation at a
/// pop — every send value blanked (E3) — is refused loudly rather than
/// silently answering on blanked values.
#[test]
#[should_panic(expected = "still pending")]
fn c18_validation_on_a_blanked_graph_is_refused() {
    let v = vis(&["a", "b", "c"]);
    let g = c18_graphs();
    let c = cert_at(&g.gc.graph, &v);
    let b = blanked(g.full_b.graph.clone());
    let _ = c.valid_at(&b, &v);
}

// ===========================================================================
// Gate 4, round 01: m1, m2, m3
// ===========================================================================

/// The programs whose Impl prefixes the gate-4 tests sweep (criterion 7's
/// set).
fn prefix_pairs() -> Vec<CorpusPair> {
    vec![
        cp(
            "ex_cone",
            asyn(),
            &["a", "c"],
            prog(ex_cone_impl),
            prog(ex_cone_spec),
        ),
        cp(
            "relay",
            asyn(),
            &["a", "c"],
            prog(ex_cone_impl),
            prog(relay_spec),
        ),
        cp(
            "two",
            asyn(),
            &["a", "b", "c"],
            two_senders(1, 2),
            two_senders(1, 2),
        ),
        cp(
            "relay_nb",
            asyn(),
            &["a", "b"],
            prog(relay_nb),
            prog(relay_nb),
        ),
        cp("c2", asyn(), &["a", "b"], prog(c2_impl), prog(c2_spec)),
        cp("c2m", asyn(), &["a", "b"], prog(c2_spec), prog(c2_impl)),
        cp("c1", asyn(), &["a", "c"], prog(c1_impl), prog(c1_spec)),
        cp(
            "pe",
            fifo(),
            &["main", "c"],
            prog(pe_p2_relay),
            prog(pe_c_blocks),
        ),
    ]
}

/// **Round 01 m1 (D-m1).** `cone_from` (summaries) agrees with `cone` (the
/// reference) on every `(G₁, M)`: every complete corpus pair, and every
/// spawn-closed prefix of every Impl graph of the prefix set against every
/// Spec graph. Both verdicts occur.
#[test]
fn m1_cone_from_agrees_with_cone() {
    use crate::conformance::sig::cone_from;
    let (mut t, mut f, mut partial) = (0usize, 0usize, 0usize);
    let mut bad = Vec::new();
    let mut check =
        |name: &str, g1: &ExecutionGraph, m: &ExecutionGraph, v: &[String], part: bool| {
            let w1 = w(g1, v);
            let reference = cone(g1, &w1, m, &w(m, v), v);
            let fast = cone_from(&w1, &ord(g1, &w1, v), &summary(m, v), v);
            if reference != fast {
                bad.push(format!("{name}: cone={reference} cone_from={fast}"));
            }
            if reference {
                t += 1;
            } else {
                f += 1;
            }
            if part {
                partial += 1;
            }
        };
    for cg in corpus_graphs() {
        for g1 in &cg.imp {
            for m in &cg.spec {
                check(&cg.name, g1, m, &cg.visible, false);
            }
        }
    }
    for p in prefix_pairs() {
        let imps = graphs_of(p.config.clone(), &p.visible, p.imp.clone());
        let specs = graphs_of(p.config.clone(), &p.visible, p.spec.clone());
        for g in &imps {
            for (_, r) in prefixes(g) {
                for m in &specs {
                    check(&p.name, &r, m, &p.visible, true);
                }
            }
        }
    }
    assert!(bad.is_empty(), "conformance: cone_from disagrees: {bad:#?}");
    assert!(
        t > 0 && f > 0,
        "conformance: both verdicts: {t} true, {f} false"
    );
    assert!(partial > 0, "conformance: partial G1 exercised: {partial}");
}

/// **Round 01 m2 (D-m2).** The spawn-closed prefix family contains graphs
/// in which a declared visible thread is unspawned, and `cone`,
/// `CanonicalGraph::of` and `valid_at` run on them: `cone` gives an answer
/// and `lem:witness(2)` is checked by `c07` on the same family, the form
/// builds, and a restriction is valid at the graph it was cut from.
#[test]
fn m2_unspawned_declared_threads_are_exercised() {
    let (mut unspawned, mut cone_runs, mut cone_true, mut valid_runs) =
        (0usize, 0usize, 0usize, 0usize);
    for p in prefix_pairs() {
        let v = &p.visible;
        let imps = graphs_of(p.config.clone(), v, p.imp.clone());
        let specs = graphs_of(p.config.clone(), v, p.spec.clone());
        for g in &imps {
            for (_, r) in prefixes(g) {
                if !has_unspawned(&r, v) {
                    continue;
                }
                unspawned += 1;
                for m in &specs {
                    cone_runs += 1;
                    if conev(&r, m, v) {
                        cone_true += 1;
                    }
                }
                let _ = canon(&r, v);
                assert!(
                    valid(&cert_at(&r, v), g, v),
                    "conformance: {}: a restriction with an unspawned thread must be extended by its source",
                    p.name
                );
                valid_runs += 1;
            }
        }
    }
    assert!(
        unspawned > 0,
        "conformance: no prefix with an unspawned declared thread"
    );
    assert!(
        cone_runs > 0 && cone_true > 0,
        "conformance: cone on unspawned rows: {cone_runs} runs, {cone_true} true"
    );
    assert_eq!(valid_runs, unspawned, "conformance: valid_at ran on each");
}

/// **Round 01 m3 (D-m3), plan §5.5.** `cone` on criterion 1's partial Impl
/// graph holding A's send and C's receive, against the Spec graph, is true.
/// This is the fixture on which the raw-index mutation (M01) flips `cone`'s
/// own verdict: A's send is raw index 2 here and 1 in the Spec (E2).
#[test]
fn m3_cone_on_criterion_1s_partial_graph() {
    let v = vis(&["a", "c"]);
    let d = Driver::start(asyn(), prog(c1_impl))
        .nondet("a", NondetValue::Choice(0))
        .send("a");
    let o = d.offer_of("c");
    let src = *o
        .sources()
        .iter()
        .find(|s| name_of(&d.graph, s.thread).as_deref() == Some("a"))
        .expect("conformance: c can read a");
    let g1 = install_recv(d.config.clone(), d.graph.clone(), &o, Some(src));
    let m = only_graph(prog(c1_spec), &v);
    // Controls: partial (C has received but has no `End`: the probe that
    // would install it never ran; A's `End` is forced bookkeeping after its
    // last operation), and the E2 relation.
    let tc = tid_named(&g1, "c");
    assert!(
        !(0..g1.thread_size(tc) as u32)
            .any(|i| matches!(g1.label(Event::new(tc, i)), LabelEnum::End(_))),
        "conformance: c has not ended in G1"
    );
    assert_eq!(
        send_of(&g1, "a").index,
        send_of(&m, "a").index + 1,
        "conformance: E2 — the Choice shifts A's send by one"
    );
    assert!(
        conev(&g1, &m, &v),
        "conformance: cone(G1^{{A0,C0}}, M) holds"
    );
}
