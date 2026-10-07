//! P4-SELECTOR gate 3: the tester's tests for the two selector knobs
//! (criteria `P4-SELECTOR.md` revision 6.1).
//!
//! Every expected value below was derived from the criteria's engine facts
//! S1–S6 and the paper (`alg.tex` §8.3 `ex:naive`, §8.5, §8.7 `ex:restart`,
//! `lem:coverexact`, §8.8) **before** `selector.rs` or the `must.rs` diff was
//! read; the derivations are written out in
//! `plan/traceForge/log/dev/P4-SELECTOR.report.md`, Part 0, under the labels
//! `D1`..`D13` cited on each test. Criteria 5, 7 and 13 are
//! engine-against-engine: their expected values are equalities, and the
//! "before" side of 7 and 13 was recorded on a `bd793be` + Part 1 clone by the
//! code between the `BEGIN-SHARED` / `END-SHARED` markers, which is compiled
//! there verbatim (see the report, Part 1).

// ===================================================================== BEGIN-SHARED
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::canon::CanonicalGraph;
use crate::conformance::config::{ConfBuilder, DEFAULT_SEARCH_BUDGET};
use crate::conformance::ctx::{ConfCtx, ConfMode};
use crate::conformance::prober::probe_once;
use crate::conformance::report::ConfVerdict;
use crate::conformance::testing::CurrentMustGuard;
use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::{recv_msg_block, send_msg, thread, CommunicationModel, Config, ConsType, Nondet};

type Prog = Arc<dyn Fn() + Send + Sync>;

fn prog<F: Fn() + Send + Sync + 'static>(f: F) -> Prog {
    Arc::new(f)
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
}

fn cfg(model: ConsType) -> Config {
    Config::builder().with_cons_type(model).with_seed(0).build()
}

fn vis(ns: &[&str]) -> Vec<String> {
    ns.iter().map(|s| (*s).to_string()).collect()
}

/// An unnamed `asyn` channel of `i32`, created by the calling thread.
fn chan() -> (crate::channel::Sender<i32>, crate::channel::Receiver<i32>) {
    crate::channel::Builder::<i32>::new()
        .with_comm(CommunicationModel::NoOrder)
        .build()
}

// --- fixtures ----------------------------------------------------------------

/// D2 / criterion 2's nested shape (and criterion 13's plain-path program):
/// `main` spawns `p1` then `p2` and ends; `p1` spawns `x`, `p2` spawns `y`;
/// each of the four sends once on a sink channel nobody reads.
fn nested4() {
    let (tx, _rx) = chan();
    let t1 = tx.clone();
    let t2 = tx;
    let _p1 = named("p1", move || {
        let tx_x = t1.clone();
        let _x = named("x", move || tx_x.send_msg(3));
        t1.send_msg(1);
    });
    let _p2 = named("p2", move || {
        let tx_y = t2.clone();
        let _y = named("y", move || tx_y.send_msg(4));
        t2.send_msg(2);
    });
}

/// D3 / criterion 3: spawn order `r1, r2, s`; `main` joins all three.
fn c3_prog() {
    let (tx1, rx1) = chan();
    let (tx2, rx2) = chan();
    let r1 = named("r1", move || {
        let _v: i32 = rx1.recv_msg_block();
    });
    let r2 = named("r2", move || {
        let _v: i32 = rx2.recv_msg_block();
    });
    let s = named("s", move || {
        tx1.send_msg(1);
        tx2.send_msg(2);
    });
    r1.join().unwrap();
    r2.join().unwrap();
    s.join().unwrap();
}

/// D6 / criterion 6: `ex:naive`'s `Impl_k` (`v = 0`) or `Spec_k` (`v = 1`),
/// every mailbox a channel `main` creates before any spawn. Encoding 1
/// (`c_first`) spawns `c, b1..bk, a`; encoding 2 spawns `b1..bk, a, c`.
fn naive(k: usize, v: i32, c_first: bool) -> Prog {
    prog(move || {
        let (tx_a, _rx_a) = chan();
        let (tx_c, rx_c) = chan();
        let spawn_c = |tx_a: crate::channel::Sender<i32>, rx_c: crate::channel::Receiver<i32>| {
            named("c", move || {
                tx_a.send_msg(v);
                for _ in 0..k {
                    let _x: i32 = rx_c.recv_msg_block();
                }
            })
        };
        let spawn_bs = |tx_c: &crate::channel::Sender<i32>| {
            for i in 1..=k {
                let t = tx_c.clone();
                let _b = named(&format!("b{i}"), move || t.send_msg(1));
            }
        };
        if c_first {
            let _c = spawn_c(tx_a, rx_c);
            spawn_bs(&tx_c);
            let _a = named("a", || {});
        } else {
            spawn_bs(&tx_c);
            let _a = named("a", || {});
            let _c = spawn_c(tx_a, rx_c);
        }
    })
}

fn naive_visible(k: usize) -> Vec<String> {
    let mut v = vec!["a".to_string(), "c".to_string()];
    v.extend((1..=k).map(|i| format!("b{i}")));
    v
}

/// D11 / criterion 11: `ex:restart` with `A` a spawned thread (p2p). `Spec`
/// draws `n` from `{5, 6}` by a `Choice` over `5..=6`.
fn restart(spec: bool) -> Prog {
    prog(move || {
        let c = named("c", || {});
        let cid = c.thread().id();
        let _a = named("a", move || {
            if spec {
                let n = (5..=6usize).nondet();
                send_msg(cid, 1i32);
                send_msg(cid, n as i32);
            } else {
                send_msg(cid, 1i32);
                send_msg(cid, 6i32);
            }
        });
    })
}

/// P4-STATEFUL criterion 14b: the enumerator's rendering of `restart(true)`
/// against itself (`Conforms`) is byte-identical to the pre-gate-2 baseline.
#[test]
fn c14b_enumerator_conforms_rendering_matches_the_pre_gate_2_baseline() {
    let cc = ConfBuilder::new()
        .config(Config::builder().with_seed(7).build())
        .visible_threads(vis(&["a", "c"]))
        .build()
        .expect("conformance: the baseline configuration is in scope");
    let verdict = crate::conformance::run(cc, restart(true), restart(true))
        .expect("conformance: the baseline run returned an error");
    assert_eq!(
        format!("{verdict}"),
        super::stateful_baseline::ENUMERATOR_CONFORMS_BASELINE
    );
}

/// D12 / criterion 12, the force: `main` creates `ch1`, `ch2`, spawns `t`,
/// then sends on `ch1`; `t`'s first operation is a send on `ch2`.
fn force_prog() {
    let (tx1, _rx1) = chan();
    let (tx2, _rx2) = chan();
    let _t = named("t", move || tx2.send_msg(2));
    tx1.send_msg(1);
}

/// D12 / criterion 12, the disjunct: `main` spawns `p1` then `p2` and ends;
/// `p1` spawns `x` and ends; `x`'s and `p2`'s first operations are sends.
fn disjunct_prog() {
    let (tx, _rx) = chan();
    let tp = tx.clone();
    let _p1 = named("p1", move || {
        let _x = named("x", move || tp.send_msg(3));
    });
    let _p2 = named("p2", move || tx.send_msg(2));
}

/// S5's witness that `fewest-events` is not a fixed order on engine labels,
/// made into a program: `t`'s send has `n = 1` after the spawn branch and
/// `n = 2` after the nondet branch, against `u`'s third send at `n = 2`, with
/// `orig(u) <lex orig(t)`. `d` receives both, so the order matters to `rf`.
fn s5_witness() {
    let (tx_t, rx_t) = chan();
    let (tx_d, rx_d) = chan();
    let (sink, _rx_sink) = chan();
    let tdu = tx_d.clone();
    let _u = named("u", move || {
        sink.send_msg(0);
        sink.send_msg(0);
        tdu.send_msg(7);
    });
    let tdt = tx_d;
    let _t = named("t", move || {
        let v: i32 = rx_t.recv_msg_block();
        if v == 0 {
            let _k = named("k", || {});
        } else {
            let _b: bool = crate::nondet();
        }
        tdt.send_msg(9);
    });
    let t0 = tx_t.clone();
    let _s0 = named("s0", move || t0.send_msg(0));
    let _s1 = named("s1", move || tx_t.send_msg(1));
    let _d = named("d", move || {
        let _x: i32 = rx_d.recv_msg_block();
        let _y: i32 = rx_d.recv_msg_block();
    });
}

/// `ex:traces` / `ex:rebuild`: two senders, one receiver (thread mailboxes).
fn traces_prog() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 1i32));
    let _b = named("b", move || send_msg(cid, 2i32));
}

/// The same with `c` receiving only `1` (a guarded receive: `recv(λy. y = 1)`
/// written as an assumption on the value read).
fn traces_spec_reads_one() {
    let c = named("c", || {
        let x: i32 = recv_msg_block();
        crate::assume!(x == 1);
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 1i32));
    let _b = named("b", move || send_msg(cid, 2i32));
}

// paper_examples / refinement_suite programs, reproduced (module-private there).
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
fn rs_visible_error() {
    let _w = named("w", || {
        crate::assert(false);
    });
}
fn rs_visible_ok() {
    let _w = named("w", || {});
}

/// The trace program of criterion 13 (i): a nested spawn and a failing
/// assertion, so replay crosses several scheduling points.
fn trace_prog() {
    let (tx, _rx) = chan();
    let _p1 = named("p1", move || {
        let t = tx.clone();
        let _x = named("x", move || t.send_msg(3));
        tx.send_msg(1);
    });
    let _p2 = named("p2", || {
        crate::assert(false);
    });
}

// --- the corpus of criteria 5, 7 and 10 -----------------------------------------

struct CorpusPair {
    name: String,
    config: Config,
    visible: Vec<String>,
    imp: Prog,
    spec: Prog,
}

fn cp(name: &str, config: Config, visible: Vec<String>, imp: Prog, spec: Prog) -> CorpusPair {
    CorpusPair {
        name: name.to_string(),
        config,
        visible,
        imp,
        spec,
    }
}

fn corpus() -> Vec<CorpusPair> {
    let mut out = Vec::new();
    let mc = vis(&["main", "c"]);
    let fifo = || cfg(ConsType::FIFO);
    let bag = || cfg(ConsType::Bag);
    out.push(cp(
        "pe:relay/direct",
        fifo(),
        mc.clone(),
        prog(pe_p2_relay),
        prog(pe_p1_direct),
    ));
    out.push(cp(
        "pe:direct/relay",
        fifo(),
        mc.clone(),
        prog(pe_p1_direct),
        prog(pe_p2_relay),
    ));
    out.push(cp(
        "pe:relay/two",
        fifo(),
        mc.clone(),
        prog(pe_p2_relay),
        prog(pe_p1_value_two),
    ));
    out.push(cp(
        "pe:relay/blocks",
        fifo(),
        mc.clone(),
        prog(pe_p2_relay),
        prog(pe_c_blocks),
    ));
    out.push(cp(
        "pe:blocks/direct",
        fifo(),
        mc.clone(),
        prog(pe_c_blocks),
        prog(pe_p1_direct),
    ));
    out.push(cp(
        "pe:traces/joined",
        fifo(),
        vis(&["a", "b", "c"]),
        prog(traces_prog),
        prog(pe_sends_ordered_by_join),
    ));
    out.push(cp(
        "pe:joined/traces",
        fifo(),
        vis(&["a", "b", "c"]),
        prog(pe_sends_ordered_by_join),
        prog(traces_prog),
    ));
    for (m, model) in [
        ("bag", ConsType::Bag),
        ("fifo", ConsType::FIFO),
        ("cd", ConsType::Causal),
    ] {
        out.push(cp(
            &format!("rs:relayed/direct/{m}"),
            cfg(model),
            mc.clone(),
            prog(pe_p2_relay),
            prog(pe_p1_direct),
        ));
        out.push(cp(
            &format!("rs:error/ok/{m}"),
            cfg(model),
            vis(&["w"]),
            prog(rs_visible_error),
            prog(rs_visible_ok),
        ));
        out.push(cp(
            &format!("t:traces/self/{m}"),
            cfg(model),
            vis(&["a", "b", "c"]),
            prog(traces_prog),
            prog(traces_prog),
        ));
        out.push(cp(
            &format!("t:traces/reads-one/{m}"),
            cfg(model),
            vis(&["a", "b", "c"]),
            prog(traces_prog),
            prog(traces_spec_reads_one),
        ));
    }
    for k in [2usize, 3] {
        for (e, c_first) in [("enc1", true), ("enc2", false)] {
            out.push(cp(
                &format!("t:naive{k}/{e}/impl-spec"),
                bag(),
                naive_visible(k),
                naive(k, 0, c_first),
                naive(k, 1, c_first),
            ));
            out.push(cp(
                &format!("t:naive{k}/{e}/spec-spec"),
                bag(),
                naive_visible(k),
                naive(k, 1, c_first),
                naive(k, 1, c_first),
            ));
        }
    }
    out.push(cp(
        "t:restart",
        fifo(),
        vis(&["a", "c"]),
        restart(false),
        restart(true),
    ));
    out.push(cp(
        "t:restart/rev",
        fifo(),
        vis(&["a", "c"]),
        restart(true),
        restart(false),
    ));
    out.push(cp(
        "t:c3/self",
        bag(),
        vis(&["r1", "r2", "s"]),
        prog(c3_prog),
        prog(c3_prog),
    ));
    out.push(cp(
        "t:s5/self",
        bag(),
        vis(&["d", "u"]),
        prog(s5_witness),
        prog(s5_witness),
    ));
    out.push(cp(
        "t:s5/self/fifo",
        fifo(),
        vis(&["d", "u"]),
        prog(s5_witness),
        prog(s5_witness),
    ));
    out.push(cp(
        "t:nested4/self",
        bag(),
        vis(&["p1", "p2"]),
        prog(nested4),
        prog(nested4),
    ));
    out.push(cp(
        "t:disjunct/self",
        bag(),
        vis(&["p2", "x"]),
        prog(disjunct_prog),
        prog(disjunct_prog),
    ));
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

// --- witnesses ------------------------------------------------------------------

/// FNV-1a over the lines, newline-separated: the baseline stores digests.
fn fnv(lines: &[String]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for l in lines {
        for b in l.bytes().chain(std::iter::once(b'\n')) {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0100_0000_01b3);
        }
    }
    h
}

fn has_conf_prune(g: &ExecutionGraph) -> bool {
    g.thread_ids().into_iter().any(|t| {
        (0..g.thread_size(t) as u32).any(|i| {
            matches!(g.label(Event::new(t, i)),
                LabelEnum::Block(b) if matches!(b.btype(), BlockType::ConfPrune))
        })
    })
}

/// The canonical key of a captured graph. A pruned execution's graph is not a
/// complete graph and never reaches a form (`canon.rs`: `Block{ConfPrune}`);
/// it is witnessed by its installation sequence instead, labelled.
fn key_str(g: &ExecutionGraph, visible: &[String]) -> String {
    if has_conf_prune(g) {
        return format!("PRUNED {:016x}", fnv(&install_seq(g)));
    }
    match CanonicalGraph::of(g, visible) {
        Ok(c) => format!("{c:?}"),
        Err(e) => format!("ERR {e:?}"),
    }
}

/// One execution's labels in installation (stamp) order.
fn install_seq(g: &ExecutionGraph) -> Vec<String> {
    let mut v: Vec<(usize, Event, String)> = Vec::new();
    for t in g.thread_ids() {
        for i in 0..g.thread_size(t) as u32 {
            let e = Event::new(t, i);
            let lab = g.label(e);
            let stamp = if lab.stamped() { lab.stamp() } else { 0 };
            let desc = match lab {
                LabelEnum::CToss(c) => format!("{e:?} CToss({})", c.result()),
                LabelEnum::Choice(c) => format!("{e:?} Choice({})", c.result()),
                LabelEnum::SendMsg(s) => format!("{s} val={:?}", s.val()),
                other => format!("{other}"),
            };
            v.push((stamp, e, desc));
        }
    }
    v.sort_by_key(|a| (a.0, a.1.thread, a.1.index));
    v.into_iter().map(|x| x.2).collect()
}

/// The hand-built gated run of `oracle_tests.rs:161-180`: the canonical keys
/// of every captured Impl graph in exploration order, and the first
/// execution's installation sequence.
fn gated_witness(p: &CorpusPair, budget: usize) -> (Vec<String>, Vec<String>) {
    let mut ctx = ConfCtx::new(
        p.config.clone(),
        Arc::clone(&p.spec),
        p.visible.clone(),
        budget,
        false,
    );
    ctx.collect_graphs();
    let must = Rc::new(RefCell::new(Must::new(p.config.clone(), false)));
    must.borrow_mut().enable_conformance(ctx);
    {
        let _guard = CurrentMustGuard;
        let imp = Arc::clone(&p.imp);
        let f = Arc::new(move || imp());
        crate::explore(&must, &f);
    }
    must.borrow_mut().conf_shutdown();
    let m = must.borrow();
    let ctx = m.conf_ctx().expect("conformance: the context went missing");
    let keys = ctx
        .collected()
        .iter()
        .map(|g| key_str(g, &p.visible))
        .collect();
    let first = ctx.collected().first().map(install_seq).unwrap_or_default();
    (keys, first)
}

/// `verify_conformance_with`'s `Outcome`: the ordered report sequence by kind
/// and canonical key, and `Stats` (executions, blocked).
fn outcome_witness(p: &CorpusPair, budget: usize) -> (Vec<String>, String) {
    let o = crate::conformance::verify_conformance_with(
        p.config.clone(),
        Arc::clone(&p.imp),
        Arc::clone(&p.spec),
        p.visible.clone(),
        budget,
        false,
    );
    let reports = o
        .reports
        .iter()
        .map(|r| format!("{:?} {}", r.kind, key_str(&r.graph, &p.visible)))
        .collect();
    let stats = match &o.stats {
        Some(s) => format!("execs={} block={}", s.execs, s.block),
        None => "no stats".to_string(),
    };
    (reports, stats)
}

/// `run(cc)`: the verdict and the precheck result, `triage = false`.
fn run_witness(p: &CorpusPair, budget: usize) -> String {
    let cc = ConfBuilder::new()
        .config(p.config.clone())
        .visible_threads(p.visible.clone())
        .search_budget(budget)
        .triage(false)
        .build()
        .expect("conformance: a corpus configuration is in scope");
    match crate::conformance::run(cc, Arc::clone(&p.imp), Arc::clone(&p.spec)) {
        Ok(ConfVerdict::Conforms(c)) => format!("conforms spec={:?}", c.outcome.spec_errfree),
        Ok(ConfVerdict::Reported(o)) => format!(
            "reported n={} end={:?} spec={:?}",
            o.reports.len(),
            o.end,
            o.spec_errfree
        ),
        Ok(ConfVerdict::Inconclusive(o)) => format!(
            "inconclusive end={:?} exh={} spec={:?}",
            o.end,
            o.exhaustions.len(),
            o.spec_errfree
        ),
        Err(e) => format!("error {e:?}"),
    }
}

/// `probe_once(cfg, spec)`: the gated run's first probe, its offers in order.
fn probe_witness(p: &CorpusPair) -> Vec<String> {
    let spec = Arc::clone(&p.spec);
    probe_once(p.config.clone(), move || spec())
        .iter()
        .map(|o| {
            format!(
                "{} {:?} {:?} {}",
                o.kind(),
                o.pos(),
                o.sources(),
                o.may_read_nothing()
            )
        })
        .collect()
}

/// Every captured graph of `p` by an ungated Must exploration (the oracle's
/// `Collect` mode: `conf` set, no worker, no reports), in completion order.
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

/// Whether `main` spawns every thread of every graph of `p` (both programs):
/// every origination vector has length at most one.
fn main_spawns_all(graphs: &[ExecutionGraph]) -> bool {
    graphs.iter().all(|g| {
        g.thread_ids()
            .into_iter()
            .all(|t| g.get_thread_tclab(t).origination_vec().len() <= 1)
    })
}

/// Every criterion-7 witness of `p` at `budget`, one line per witness:
/// `name|budget|kind|digest|count`; nested pairs also carry the full content.
fn witness_lines(p: &CorpusPair, budget: usize, nested: bool) -> Vec<String> {
    let (keys, first) = gated_witness(p, budget);
    let (reports, stats) = outcome_witness(p, budget);
    let verdict = vec![run_witness(p, budget)];
    let probe = probe_witness(p);
    let mut out = Vec::new();
    for (kind, v) in [
        ("keys", keys),
        ("first", first),
        ("reports", reports),
        ("stats", vec![stats]),
        ("verdict", verdict),
        ("probe", probe),
    ] {
        out.push(format!(
            "{}|{}|{}|{:016x}|{}",
            p.name,
            budget,
            kind,
            fnv(&v),
            v.len()
        ));
        if nested {
            out.push(format!(
                "{}|{}|{}|FULL|{}",
                p.name,
                budget,
                kind,
                v.join(" ¶ ")
            ));
        }
    }
    out
}

/// Criterion 13 (ii): the plain path — no `conf`, no `probe` — on `nested4`
/// under `LTR`: the first execution's installation sequence (one iteration,
/// exactly `crate::verify`'s single-threaded body) and the full run's `Stats`.
fn plain_nested_witness() -> Vec<String> {
    let first = {
        let c = Config::builder()
            .with_cons_type(ConsType::Bag)
            .with_seed(0)
            .with_max_iterations(1)
            .build();
        let must = Rc::new(RefCell::new(Must::new(c, false)));
        {
            let _guard = CurrentMustGuard;
            let f = Arc::new(nested4);
            crate::explore(&must, &f);
        }
        let g = must.borrow_mut().take_graph();
        install_seq(&g)
    };
    let stats = crate::verify(cfg(ConsType::Bag), nested4);
    let mut out = first;
    out.push(format!(
        "STATS execs={} block={} max_graph_events={}",
        stats.execs, stats.block, stats.max_graph_events
    ));
    out
}
// ===================================================================== END-SHARED

// ===========================================================================
// Tester-side harness (working tree only)
// ===========================================================================

use crate::conformance::config::ScopeField;
use crate::conformance::probe::{NondetValue, Offer};
use crate::conformance::prober::{install, probe_from};
use crate::conformance::search::{Cover, Search};
use crate::conformance::selector::{InnerOrder, Selector};
use crate::runtime::task::TaskId;
use crate::thread::{main_thread_id, ThreadId};
use crate::SchedulePolicy;

const SELECTORS: [Selector; 3] = [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];

fn with_selector(mut c: Config, s: Selector) -> Config {
    c.selector = s;
    c
}

fn thread_name(g: &ExecutionGraph, t: ThreadId) -> String {
    if t == main_thread_id() {
        return "main".to_string();
    }
    g.get_thread_tclab(t)
        .name()
        .clone()
        .unwrap_or_else(|| format!("{t:?}"))
}

fn tid_named(g: &ExecutionGraph, n: &str) -> ThreadId {
    g.thread_ids()
        .into_iter()
        .find(|t| thread_name(g, *t) == n)
        .unwrap_or_else(|| panic!("conformance: no thread named {n} in the fixture graph"))
}

fn task_named(g: &ExecutionGraph, n: &str) -> TaskId {
    g.to_task_id(tid_named(g, n))
        .unwrap_or_else(|| panic!("conformance: thread {n} has no task id"))
}

fn task_name(g: &ExecutionGraph, t: TaskId) -> String {
    thread_name(g, g.to_thread_id(t))
}

fn tasks(g: &ExecutionGraph, ns: &[&str]) -> Vec<TaskId> {
    ns.iter().map(|n| task_named(g, n)).collect()
}

/// Repeatedly pick from `cands` and remove the pick: the selector's order on
/// the set, by thread name.
fn pick_order(s: Selector, g: &ExecutionGraph, cands: &[TaskId]) -> Vec<String> {
    let mut left = cands.to_vec();
    let mut out = Vec::new();
    while !left.is_empty() {
        let p = s
            .pick(g, &left)
            .unwrap_or_else(|| panic!("conformance: {s:?} picked nothing from {left:?}"));
        assert!(
            left.contains(&p),
            "conformance: {s:?} picked {p:?}, not a candidate of {left:?}"
        );
        out.push(task_name(g, p));
        left.retain(|t| *t != p);
    }
    out
}

fn kind(l: &LabelEnum) -> &'static str {
    match l {
        LabelEnum::SendMsg(_) => "send",
        LabelEnum::RecvMsg(_) => "recv",
        LabelEnum::Begin(_) => "begin",
        LabelEnum::End(_) => "end",
        LabelEnum::TCreate(_) => "tcreate",
        LabelEnum::TJoin(_) => "tjoin",
        LabelEnum::Unique(_) => "unique",
        LabelEnum::CToss(_) => "toss",
        LabelEnum::Choice(_) => "choice",
        LabelEnum::Block(_) => "block",
        _ => "other",
    }
}

/// `(thread name, label kind)` of every label of `g`, in stamp order.
fn installs(g: &ExecutionGraph) -> Vec<(String, &'static str)> {
    let mut v: Vec<(usize, Event, String, &'static str)> = Vec::new();
    for t in g.thread_ids() {
        for i in 0..g.thread_size(t) as u32 {
            let e = Event::new(t, i);
            let lab = g.label(e);
            let stamp = if lab.stamped() { lab.stamp() } else { 0 };
            v.push((stamp, e, thread_name(g, t), kind(lab)));
        }
    }
    v.sort_by_key(|a| (a.0, a.1.thread, a.1.index));
    v.into_iter().map(|x| (x.2, x.3)).collect()
}

fn position(seq: &[(String, &'static str)], thread: &str, k: &str) -> usize {
    seq.iter()
        .position(|(n, kk)| n == thread && *kk == k)
        .unwrap_or_else(|| panic!("conformance: no {k} of {thread} in {seq:?}"))
}

/// The first execution's graph of a `Collect` run of `p` under `s`.
fn first_execution(model: ConsType, s: Selector, p: Prog) -> ExecutionGraph {
    graphs_of(with_selector(cfg(model), s), &[], p)
        .into_iter()
        .next()
        .expect("conformance: a Collect run captured no execution")
}

/// The thread names of a probe's offers, in recorded order, plus their kinds.
/// `probe_once` gives the offers; `probe_from` (which `probe_once` wraps)
/// gives the graph whose `TCreate`s name the threads — both must agree.
fn probe_offer_names<F>(config: Config, f: F) -> Vec<(String, &'static str)>
where
    F: Fn() + Send + Sync + Clone + 'static,
{
    let offers = probe_once(config.clone(), f.clone());
    let probed = probe_from(config, ExecutionGraph::default(), f);
    let pos_a: Vec<Event> = offers.iter().map(|o| o.pos()).collect();
    let pos_b: Vec<Event> = probed.offers().iter().map(|o| o.pos()).collect();
    assert_eq!(
        pos_a, pos_b,
        "conformance: two probes of one program disagree"
    );
    offers
        .iter()
        .map(|o| (thread_name(probed.graph(), o.pos().thread), o.kind()))
        .collect()
}

fn pair_with(p: &CorpusPair, config: Config) -> CorpusPair {
    CorpusPair {
        name: p.name.clone(),
        config,
        visible: p.visible.clone(),
        imp: Arc::clone(&p.imp),
        spec: Arc::clone(&p.spec),
    }
}

fn sorted(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v
}

fn dedup(v: &[String]) -> std::collections::BTreeSet<String> {
    v.iter().cloned().collect()
}

// ===========================================================================
// A. Knob A — the Must selector
// ===========================================================================

/// The flat fixture of criterion 2: `t1`, `t2`, `t3` spawned in that order,
/// sending `counts[i]` messages each on a sink.
fn flat(counts: [usize; 3]) -> Prog {
    prog(move || {
        let (tx, _rx) = chan();
        for (i, n) in counts.iter().copied().enumerate() {
            let t = tx.clone();
            let _h = named(&format!("t{}", i + 1), move || {
                for _ in 0..n {
                    t.send_msg(1);
                }
            });
        }
    })
}

/// D2-counting's program (report Part 0 addenda).
fn counting_prog() {
    let (sink, _rx_sink) = chan();
    let (tx_r, rx_r) = chan();
    tx_r.send_msg(5);
    let _k_send = named("k_send", move || sink.send_msg(1));
    let _k_recv = named("k_recv", move || {
        let _v: i32 = rx_r.recv_msg_block();
    });
    let _k_toss = named("k_toss", || {
        let _b: bool = crate::nondet();
    });
    let _k_choice = named("k_choice", || {
        let _n = (0..=1usize).nondet();
    });
    let _k_assert = named("k_assert", || crate::assert(false));
    let _z_unique = named("z_unique", || {
        let _c1 = chan();
        let _c2 = chan();
    });
    let _z_tcreate = named("z_tcreate", || {
        let h = named("z_child", || {});
        h.join().unwrap();
    });
    let (_tx_never, rx_never) = chan();
    let _z_blocked = named("z_blocked", move || {
        let _v: i32 = rx_never.recv_msg_block();
    });
    let _z_plain = named("z_plain", || {});
}

/// **Criterion 1, D1.** `Selector` is fieldless (one byte, no state), `pick`
/// answers `None` on no candidates and a member otherwise, and the same
/// `(graph, candidates)` gives the same pick across two `Must` instances, for
/// every variant and every non-empty candidate subset — and, a consequence of
/// S5's total orders, whatever the order of the candidate slice.
#[test]
fn c01_pick_is_pure_across_two_must_instances() {
    assert_eq!(
        std::mem::size_of::<Selector>(),
        1,
        "conformance: Selector carries state"
    );
    let run = || {
        graphs_of(
            with_selector(cfg(ConsType::Bag), Selector::Ltr),
            &[],
            prog(nested4),
        )
        .pop()
        .expect("conformance: no graph")
    };
    let (g1, g2) = (run(), run());
    let names = ["main", "p1", "p2", "x", "y"];
    let c1 = tasks(&g1, &names);
    let c2 = tasks(&g2, &names);
    assert_eq!(
        c1, c2,
        "conformance: the two runs numbered tasks differently"
    );
    let mut checked = 0;
    for s in SELECTORS {
        assert_eq!(
            s.pick(&g1, &[]),
            None,
            "conformance: {s:?} picked from nothing"
        );
        for mask in 1u32..(1 << names.len()) {
            let sub1: Vec<TaskId> = (0..names.len())
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| c1[i])
                .collect();
            let sub2: Vec<TaskId> = (0..names.len())
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| c2[i])
                .collect();
            let a = s
                .pick(&g1, &sub1)
                .expect("conformance: None on a non-empty set");
            let b = s
                .pick(&g2, &sub2)
                .expect("conformance: None on a non-empty set");
            assert!(
                sub1.contains(&a),
                "conformance: {s:?} picked a non-candidate"
            );
            assert_eq!(
                task_name(&g1, a),
                task_name(&g2, b),
                "conformance: {s:?} impure"
            );
            let mut rev = sub1.clone();
            rev.reverse();
            assert_eq!(
                s.pick(&g1, &rev),
                Some(a),
                "conformance: {s:?} reads slice order"
            );
            let mut rot = sub1.clone();
            rot.rotate_left(1);
            assert_eq!(
                s.pick(&g1, &rot),
                Some(a),
                "conformance: {s:?} reads slice order"
            );
            assert_eq!(
                s.pick(&g1, &sub1),
                Some(a),
                "conformance: {s:?} not repeatable"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 3 * 31);
}

/// **Criterion 2, D2, flat 2/0/1 and 1/1/1.** Direct picks on the final graph
/// of the one execution.
#[test]
fn c02_flat_counts_2_0_1_and_1_1_1() {
    let g = first_execution(ConsType::Bag, Selector::Ltr, flat([2, 0, 1]));
    let c = tasks(&g, &["t1", "t2", "t3"]);
    assert_eq!(pick_order(Selector::Ltr, &g, &c)[0], "t1");
    assert_eq!(pick_order(Selector::FewestEvents, &g, &c)[0], "t2");
    assert_eq!(pick_order(Selector::Reverse, &g, &c)[0], "t3");
    // The whole orders, which follow from the same definitions.
    assert_eq!(pick_order(Selector::Ltr, &g, &c), ["t1", "t2", "t3"]);
    assert_eq!(
        pick_order(Selector::FewestEvents, &g, &c),
        ["t2", "t3", "t1"]
    );
    assert_eq!(pick_order(Selector::Reverse, &g, &c), ["t3", "t2", "t1"]);

    let g = first_execution(ConsType::Bag, Selector::Ltr, flat([1, 1, 1]));
    let c = tasks(&g, &["t1", "t2", "t3"]);
    assert_eq!(pick_order(Selector::FewestEvents, &g, &c)[0], "t1");
    assert_eq!(
        pick_order(Selector::FewestEvents, &g, &c),
        ["t1", "t2", "t3"]
    );
}

/// **Criterion 2, D2-counting.** `fewest-events` counts `SendMsg`, `RecvMsg`,
/// `CToss`, `Choice`, `Block{Assert}` and nothing else.
#[test]
fn c02_fewest_events_counts_the_papers_events_only() {
    let graphs = graphs_of(
        with_selector(cfg(ConsType::Bag), Selector::Ltr),
        &[],
        prog(counting_prog),
    );
    assert!(!graphs.is_empty(), "conformance: no execution captured");
    let fe = Selector::FewestEvents;
    for g in &graphs {
        // The fixture is what D2-counting says it is: `k_assert` holds a
        // `Block{Assert}`, `z_blocked` a `Block{Value}` and no `End`.
        let ka = tid_named(g, "k_assert");
        assert!(
            (0..g.thread_size(ka) as u32).any(|i| matches!(g.label(Event::new(ka, i)),
                LabelEnum::Block(b) if matches!(b.btype(), BlockType::Assert))),
            "conformance: k_assert has no Block{{Assert}}"
        );
        let zb = tid_named(g, "z_blocked");
        assert!(
            !(0..g.thread_size(zb) as u32).any(|i| kind(g.label(Event::new(zb, i))) == "end"),
            "conformance: z_blocked ended"
        );
        for k in ["k_send", "k_recv", "k_toss", "k_choice", "k_assert"] {
            assert_eq!(
                pick_order(fe, g, &tasks(g, &[k, "z_plain"]))[0],
                "z_plain",
                "conformance: {k}'s one event was not counted"
            );
        }
        for (z, why) in [
            ("z_unique", "Unique"),
            ("z_tcreate", "TCreate/TJoin"),
            ("z_blocked", "Block{Value}"),
        ] {
            assert_eq!(
                pick_order(fe, g, &tasks(g, &[z, "z_plain"]))[0],
                z,
                "conformance: {why} was counted as an event"
            );
        }
        assert_eq!(
            pick_order(fe, g, &tasks(g, &["z_unique", "z_blocked"]))[0],
            "z_unique",
            "conformance: End was counted as an event"
        );
        assert_eq!(
            pick_order(
                fe,
                g,
                &tasks(g, &["k_send", "k_recv", "k_toss", "k_choice", "k_assert"])
            )[0],
            "k_send"
        );
    }
}

/// **Criterion 2, D2, nested.** Direct picks on the final graph of an `ltr`
/// `Collect` run of `nested4`, whose task ids are `p1 = 1, p2 = 2, x = 3,
/// y = 4`. No literal vector is asserted (Notation).
#[test]
fn c02_nested_direct_pick_discriminates_against_task_id_order() {
    let g = first_execution(ConsType::Bag, Selector::Ltr, prog(nested4));
    let ids: Vec<usize> = tasks(&g, &["p1", "p2", "x", "y"])
        .into_iter()
        .map(usize::from)
        .collect();
    assert_eq!(
        ids,
        [1, 2, 3, 4],
        "conformance: the criterion's named graph is not this one"
    );
    let c = tasks(&g, &["p1", "p2", "x", "y"]);
    let ltr = pick_order(Selector::Ltr, &g, &c);
    let rev = pick_order(Selector::Reverse, &g, &c);
    let few = pick_order(Selector::FewestEvents, &g, &c);
    assert_eq!(ltr, ["p1", "x", "p2", "y"]);
    assert_eq!(rev, ["y", "p2", "x", "p1"]);
    assert_eq!(few, ["p1", "x", "p2", "y"]);
    for (asc, name) in [
        (["p1", "p2", "x", "y"], "ascending"),
        (["y", "x", "p2", "p1"], "descending"),
    ] {
        for (s, got) in [("ltr", &ltr), ("reverse", &rev), ("fewest", &few)] {
            assert_ne!(
                got.as_slice(),
                asc.as_slice(),
                "conformance: {s} equals {name} TaskId order"
            );
        }
    }
    // With `main` among the candidates: `[]` is the least vector, so `ltr`
    // takes it first and `reverse` last (not the reversed vector, S5), and
    // `fewest-events` first (its row holds no paper event).
    let c = tasks(&g, &["main", "p1", "p2", "x", "y"]);
    assert_eq!(
        pick_order(Selector::Ltr, &g, &c),
        ["main", "p1", "x", "p2", "y"]
    );
    assert_eq!(
        pick_order(Selector::Reverse, &g, &c),
        ["y", "p2", "x", "p1", "main"]
    );
    assert_eq!(
        pick_order(Selector::FewestEvents, &g, &c),
        ["main", "p1", "x", "p2", "y"]
    );
}

/// **Criterion 3, D3.** Spawn order `r1, r2, s`, `main` joining all three:
/// both receivers block before `s` sends, so their receives install only via
/// `unblock_ready`, where the selector decides. First execution only.
#[test]
fn c03_the_pick_at_unblock_ready_decides() {
    for (s, first, second) in [
        (Selector::Ltr, "r1", "r2"),
        (Selector::Reverse, "r2", "r1"),
        (Selector::FewestEvents, "r1", "r2"),
    ] {
        let g = first_execution(ConsType::Bag, s, prog(c3_prog));
        let seq = installs(&g);
        let a = position(&seq, first, "recv");
        let b = position(&seq, second, "recv");
        assert!(
            a < b,
            "conformance: under {s:?} {first}'s receive is not first: {seq:?}"
        );
        // The site was reached: both receives follow `s`'s end (they were
        // blocked while `s` ran), so neither was installed by `next_task`.
        let s_end = position(&seq, "s", "end");
        assert!(
            a > s_end && b > s_end,
            "conformance: {s:?}: a receive did not block: {seq:?}"
        );
    }
}

/// **Criterion 4, D4.** `Arbitrary` is refused under conformance and the
/// refusal names the field; `LTR` is accepted — whatever knob A says.
#[test]
fn c04_arbitrary_is_refused_and_ltr_accepted() {
    for s in SELECTORS {
        let e = ConfBuilder::new()
            .config(
                Config::builder()
                    .with_policy(SchedulePolicy::Arbitrary)
                    .build(),
            )
            .selector(s)
            .visible_threads(["a"])
            .build()
            .err()
            .expect("conformance: Arbitrary was accepted");
        assert_eq!(e.field(), ScopeField::SchedulePolicy);
        assert!(
            e.field().field_name().contains("schedule_policy"),
            "conformance: the refusal names {:?}",
            e.field().field_name()
        );
        ConfBuilder::new()
            .config(Config::builder().with_policy(SchedulePolicy::LTR).build())
            .selector(s)
            .visible_threads(["a"])
            .build()
            .expect("conformance: LTR was refused");
    }
}

/// **Criterion 5, D5.** Corpus-wide, unlimited budget, no early stop:
/// (a) the `Collect` run of each program explores the identical set of graphs
/// (by canonical key) under all three selectors; (b) the enumerator's outer
/// run gives the same verdict, and on conforming pairs explores the identical
/// set.
///
/// Conditions (criterion 5), all here: unlimited budget (`usize::MAX`), no
/// early stop (`stop_at_first_report = false`), and admissibility per corpus
/// family — no pair excluded:
/// - `pe:*` (paper examples): `i32` values; destinations are `ThreadId`-built
///   `Loc`s, canonicalised by `ThreadKey`; no id used by order.
/// - `rs:*` (refinement suite): `i32` values or none; thread-addressed sends
///   only; no id used by order.
/// - `t:traces*`, `t:restart*`: `i32` values; thread-addressed sends; no id
///   used by order.
/// - `t:naive*`, `t:c3`, `t:s5*`, `t:nested4`, `t:disjunct`: `i32` values on
///   unnamed channels (`Dest::Channel`, keyed by the creator's `ThreadKey`);
///   no `ThreadId` in a value or a user-named `Loc`; no id used by order.
/// - `gen:*` (`generator::corpus`): the generator's own exclusions (its module
///   doc: no `ThreadId` in a value, no conditional or order-dependent ids).
///
/// On violating pairs the enumerator's pruned explored sets may differ; their
/// three sizes are recorded in `violating_sets`, carried by every failure
/// message.
#[test]
fn c05_completeness_per_selector_corpus_wide() {
    let mut sides = 0;
    let mut graphs_compared = 0;
    let mut conforming = 0;
    let mut violating = 0;
    let mut failures = Vec::new();
    let mut violating_sets = Vec::new();
    for p in corpus() {
        for (side, prog_) in [("impl", &p.imp), ("spec", &p.spec)] {
            let sets: Vec<Vec<String>> = SELECTORS
                .iter()
                .map(|s| {
                    graphs_of(
                        with_selector(p.config.clone(), *s),
                        &p.visible,
                        Arc::clone(prog_),
                    )
                    .iter()
                    .map(|g| key_str(g, &p.visible))
                    .collect()
                })
                .collect();
            for (i, s) in SELECTORS.iter().enumerate().skip(1) {
                if dedup(&sets[i]) != dedup(&sets[0]) {
                    failures.push(format!("{} {side}: {s:?} explores another set", p.name));
                }
                if sorted(sets[i].clone()) != sorted(sets[0].clone()) {
                    failures.push(format!("{} {side}: {s:?} differs in multiplicity", p.name));
                }
            }
            sides += 1;
            graphs_compared += sets[0].len();
        }
        let runs: Vec<(Vec<String>, Vec<String>)> = SELECTORS
            .iter()
            .map(|s| {
                let q = pair_with(&p, with_selector(p.config.clone(), *s));
                let (keys, _) = gated_witness(&q, usize::MAX);
                let (reports, _) = outcome_witness(&q, usize::MAX);
                (keys, reports)
            })
            .collect();
        let verdicts: Vec<bool> = runs.iter().map(|r| r.1.is_empty()).collect();
        if verdicts.iter().any(|v| *v != verdicts[0]) {
            failures.push(format!(
                "{}: verdicts differ across selectors {verdicts:?}",
                p.name
            ));
        }
        if verdicts[0] {
            conforming += 1;
            for (i, s) in SELECTORS.iter().enumerate().skip(1) {
                if dedup(&runs[i].0) != dedup(&runs[0].0) {
                    failures.push(format!(
                        "{} conforming: {s:?} outer run explores another set",
                        p.name
                    ));
                }
            }
        } else {
            violating += 1;
            let sizes: Vec<usize> = runs.iter().map(|r| dedup(&r.0).len()).collect();
            violating_sets.push(format!("{}: ltr/fewest/reverse explored {sizes:?}", p.name));
        }
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 5 failures: {failures:#?}; violating pairs' explored-set \
         sizes: {violating_sets:#?}"
    );
    assert!(
        sides >= 80 && graphs_compared > 100,
        "conformance: corpus too small ({sides}, {graphs_compared})"
    );
    assert!(
        conforming > 0 && violating > 0,
        "conformance: ({conforming}, {violating})"
    );
}

/// **Criterion 6, D6 (+ D6-fewest, + A24 measured).** `ex:naive` in both
/// encodings, `k = 2, 3`, Impl and Spec, first execution of a `Collect` run.
#[test]
fn c06_ex_naive_under_both_encodings() {
    for k in [2usize, 3] {
        for v in [0, 1] {
            let sends = |c_first: bool, s: Selector| -> Vec<String> {
                installs(&first_execution(ConsType::Bag, s, naive(k, v, c_first)))
                    .into_iter()
                    .filter(|(_, kk)| *kk == "send")
                    .map(|(n, _)| n)
                    .collect()
            };
            for s in SELECTORS {
                // Encoding 1: c's send is the first send installed.
                let e1 = sends(true, s);
                assert_eq!(e1.len(), k + 1);
                assert_eq!(e1[0], "c", "conformance: enc1 k={k} v={v} {s:?}: {e1:?}");
                // Encoding 2: c's send after every b's.
                let e2 = sends(false, s);
                assert_eq!(e2.len(), k + 1);
                assert_eq!(e2[k], "c", "conformance: enc2 k={k} v={v} {s:?}: {e2:?}");
            }
        }
        // The guard passes and the pair is a violation, under each selector.
        let vis_k = naive_visible(k);
        for c_first in [true, false] {
            for s in SELECTORS {
                let o = crate::conformance::verify_conformance_with(
                    with_selector(cfg(ConsType::Bag), s),
                    naive(k, 0, c_first),
                    naive(k, 1, c_first),
                    vis_k.clone(),
                    DEFAULT_SEARCH_BUDGET,
                    false,
                );
                assert!(
                    o.diagnostics.is_empty(),
                    "conformance: diagnostics {:?}",
                    o.diagnostics
                );
                assert!(
                    !o.reports.is_empty(),
                    "conformance: ex:naive reported nothing"
                );
            }
        }
    }
}

/// **Criterion 7, D7.** Under `Ltr` / `Recorded`, `triage = false`, precheck
/// on, at the default budget and unlimited: on every main-spawns-all pair
/// every witness equals the one recorded at `bd793be` + Part 1 by the shared
/// code above ([`BASELINE_C7`]). Nested pairs are classified the same way and
/// their differences printed, not asserted (S5's costs).
#[test]
fn c07_default_behaviour_is_bd793be_on_main_spawns_all_pairs() {
    let base: std::collections::BTreeMap<String, String> = BASELINE_C7
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| {
            let (k, v) = l.rsplit_once('|').expect("conformance: a baseline line");
            let (k, v2) = k.rsplit_once('|').expect("conformance: a baseline line");
            (k.to_string(), format!("{v2}|{v}"))
        })
        .collect();
    let mut asserted = 0;
    let mut nested_pairs = Vec::new();
    let mut nested_diffs = Vec::new();
    let mut failures = Vec::new();
    for p in corpus() {
        let gi = graphs_of(p.config.clone(), &p.visible, Arc::clone(&p.imp));
        let gs = graphs_of(p.config.clone(), &p.visible, Arc::clone(&p.spec));
        let nested = !(main_spawns_all(&gi) && main_spawns_all(&gs));
        let class = if nested { "nested" } else { "main-spawns-all" };
        assert_eq!(
            base.get(&p.name).map(String::as_str),
            Some(format!("CLASS|{class}").as_str()),
            "conformance: {} classified differently from the baseline",
            p.name
        );
        if nested {
            nested_pairs.push(p.name.clone());
        }
        for budget in [DEFAULT_SEARCH_BUDGET, usize::MAX] {
            for line in witness_lines(&p, budget, false) {
                let (k, v) = line.rsplit_once('|').unwrap();
                let (k, v2) = k.rsplit_once('|').unwrap();
                let now = format!("{v2}|{v}");
                let then = base.get(k).cloned().unwrap_or_else(|| "MISSING".into());
                if nested {
                    if now != then {
                        nested_diffs.push(k.to_string());
                    }
                } else {
                    asserted += 1;
                    if now != then {
                        failures.push(format!("{k}: now {now}, at bd793be {then}"));
                    }
                }
            }
        }
    }
    // S5's costs (i) and (ii), derived (D13, D12): on the two nested fixtures
    // the first execution and the first probe's offer order change — and
    // nothing else changes on any nested pair, `s5_witness` included (D-m1).
    let mut expected = std::collections::BTreeSet::new();
    for name in ["t:nested4/self", "t:disjunct/self"] {
        for budget in [DEFAULT_SEARCH_BUDGET, usize::MAX] {
            for kind in ["first", "probe"] {
                expected.insert(format!("{name}|{budget}|{kind}"));
            }
        }
    }
    let got: std::collections::BTreeSet<String> = nested_diffs.iter().cloned().collect();
    assert_eq!(
        got, expected,
        "conformance: the nested-pair differences are not exactly S5's two costs"
    );
    assert!(
        failures.is_empty(),
        "conformance: criterion 7 regressions: {failures:#?}"
    );
    assert!(
        asserted >= 400,
        "conformance: only {asserted} witnesses asserted"
    );
    assert_eq!(
        nested_pairs.len(),
        4,
        "conformance: nested pairs {nested_pairs:?}"
    );
}

// ===========================================================================
// B. Knob B — the inner offer order
// ===========================================================================

fn orders_for_units() -> Vec<InnerOrder> {
    vec![
        InnerOrder::Recorded,
        InnerOrder::Reverse,
        InnerOrder::SendsFirst,
        InnerOrder::Pinned(vec![]),
        InnerOrder::Pinned(vec![5, 6]),
        InnerOrder::Pinned(vec![6, 5]),
        InnerOrder::Pinned(vec![6]),
        InnerOrder::Pinned(vec![7]),
        InnerOrder::Pinned(vec![6, 6]),
        InnerOrder::Pinned(vec![4, 0, 2, 4]),
        InnerOrder::Pinned(vec![1]),
        InnerOrder::Pinned(vec![0, 1]),
    ]
}

/// Offers of every kind a probe records: two sends, a non-blocking receive
/// (offered with ⊥), a toss and a choice, each in its own thread.
fn kb_offers_prog() {
    let (tx, _rx) = chan();
    let (_tx2, rx2) = chan();
    let t1 = tx.clone();
    let _o1 = named("o1", move || t1.send_msg(1));
    let _o2 = named("o2", move || {
        let _v: Option<i32> = rx2.recv_msg();
    });
    let _o3 = named("o3", || {
        let _b: bool = crate::nondet();
    });
    let _o4 = named("o4", move || tx.send_msg(4));
    let _o5 = named("o5", || {
        let _n = (5..=6usize).nondet();
    });
}

/// The criterion's definition of `pinned`, written from criterion 9's text:
/// each listed value that occurs (and is not already taken) in listed order,
/// then the rest in recorded order.
fn pinned_reference(pins: &[usize], values: &[NondetValue]) -> Vec<NondetValue> {
    let num = |v: &NondetValue| match v {
        NondetValue::Toss(b) => usize::from(*b),
        NondetValue::Choice(n) => *n,
    };
    let mut taken = vec![false; values.len()];
    let mut out = Vec::new();
    for p in pins {
        if let Some(i) = (0..values.len()).find(|&i| !taken[i] && num(&values[i]) == *p) {
            taken[i] = true;
            out.push(values[i]);
        }
    }
    out.extend((0..values.len()).filter(|&i| !taken[i]).map(|i| values[i]));
    out
}

fn is_permutation<T: PartialEq + std::fmt::Debug + Clone>(input: &[T], output: &[T]) -> bool {
    if input.len() != output.len() {
        return false;
    }
    let mut used = vec![false; input.len()];
    output.iter().all(
        |o| match (0..input.len()).find(|&i| !used[i] && input[i] == *o) {
            Some(i) => {
                used[i] = true;
                true
            }
            None => false,
        },
    )
}

/// **Criteria 8 and 9, D8/D9: offers.** Every policy is a permutation; the
/// four policies each do what criterion 9 says on the offers sequence.
#[test]
fn c08_c09_offers_permute_as_each_policy_says() {
    let offers = probe_once(cfg(ConsType::Bag), kb_offers_prog);
    let kinds: Vec<&str> = offers.iter().map(|o| o.kind()).collect();
    assert_eq!(
        kinds.len(),
        5,
        "conformance: the fixture's offers are {kinds:?}"
    );
    assert_eq!(
        kinds.iter().filter(|k| **k == "send").count(),
        2,
        "conformance: {kinds:?}"
    );
    let idx = |out: &[&Offer]| -> Vec<usize> {
        out.iter()
            .map(|o| {
                offers
                    .iter()
                    .position(|x| std::ptr::eq(x, *o))
                    .expect("conformance: an offer that is not an input offer")
            })
            .collect()
    };
    for inputs in [&offers[..], &offers[..0], &offers[..1], &offers[1..3]] {
        let n = inputs.len();
        for ord in orders_for_units() {
            let out = ord.offers(inputs);
            let mut got: Vec<usize> = out
                .iter()
                .map(|o| inputs.iter().position(|x| std::ptr::eq(x, *o)).unwrap())
                .collect();
            let expected: Vec<usize> = match &ord {
                InnerOrder::Recorded | InnerOrder::Pinned(_) => (0..n).collect(),
                InnerOrder::Reverse => (0..n).rev().collect(),
                InnerOrder::SendsFirst => {
                    let is_send = |i: &usize| inputs[*i].kind() == "send";
                    let mut v: Vec<usize> = (0..n).filter(is_send).collect();
                    v.extend((0..n).filter(|i| !is_send(i)));
                    v
                }
            };
            assert_eq!(got, expected, "conformance: {ord:?} on {n} offers");
            got.sort_unstable();
            assert_eq!(
                got,
                (0..n).collect::<Vec<_>>(),
                "conformance: {ord:?} is not a permutation"
            );
        }
    }
    // On the full set, sends-first moves both sends to the front, in order.
    let sf = idx(&InnerOrder::SendsFirst.offers(&offers));
    assert_eq!(offers[sf[0]].kind(), "send");
    assert_eq!(offers[sf[1]].kind(), "send");
    assert!(
        sf[0] < sf[1],
        "conformance: sends-first is not stable among sends"
    );
}

/// **Criteria 8 and 9, D8/D9: values.** Every policy is a permutation of a
/// nondet's values; `reverse` reverses, `recorded` and `sends-first` keep,
/// `pinned` follows its definition, including criterion 9's four literal
/// cases on `ex:restart`'s `5..=6`.
#[test]
fn c08_c09_values_permute_as_each_policy_says() {
    use NondetValue::{Choice, Toss};
    let inputs: Vec<Vec<NondetValue>> = vec![
        vec![Toss(false), Toss(true)],
        vec![Choice(5), Choice(6)],
        (0..=4).map(Choice).collect(),
        vec![],
        vec![Choice(3)],
    ];
    for input in &inputs {
        for ord in orders_for_units() {
            let out = ord.values(input.clone());
            assert!(
                is_permutation(input, &out),
                "conformance: {ord:?}.values({input:?}) = {out:?} is not a permutation"
            );
            let expected = match &ord {
                InnerOrder::Recorded | InnerOrder::SendsFirst => input.clone(),
                InnerOrder::Reverse => input.iter().rev().copied().collect(),
                InnerOrder::Pinned(p) => pinned_reference(p, input),
            };
            assert_eq!(out, expected, "conformance: {ord:?}.values({input:?})");
        }
    }
    let r = vec![Choice(5), Choice(6)];
    let pin = |p: Vec<usize>| InnerOrder::Pinned(p).values(r.clone());
    assert_eq!(pin(vec![5, 6]), [Choice(5), Choice(6)]);
    assert_eq!(pin(vec![6, 5]), [Choice(6), Choice(5)]);
    assert_eq!(pin(vec![6]), [Choice(6), Choice(5)]);
    assert_eq!(pin(vec![7]), [Choice(5), Choice(6)]);
    assert_eq!(pin(vec![6, 6]), [Choice(6), Choice(5)]);
    assert_eq!(
        InnerOrder::Reverse.values(vec![Toss(false), Toss(true)]),
        [Toss(true), Toss(false)]
    );
    // The values the probe itself produces for a toss and a choice.
    let offers = probe_once(cfg(ConsType::Bag), kb_offers_prog);
    for o in offers
        .iter()
        .filter(|o| matches!(o.kind(), "nondet" | "choice"))
    {
        let vals = o.nondet_values();
        for ord in orders_for_units() {
            assert!(
                is_permutation(&vals, &ord.values(vals.clone())),
                "conformance: {ord:?}"
            );
        }
    }
}

/// **Criteria 8 and 9, D8/D9: sources.** ⊥ included; `reverse` gives
/// `[⊥, s_m..s_1]`, every other policy leaves the sequence alone.
#[test]
fn c08_c09_sources_permute_as_each_policy_says() {
    let e = |t: u32, i: u32| Some(Event::new(crate::thread::construct_thread_id(t), i));
    let inputs: Vec<Vec<Option<Event>>> = vec![
        vec![e(1, 1), e(2, 1), e(3, 2), None],
        vec![None],
        vec![],
        vec![e(1, 1)],
        vec![e(1, 1), e(2, 1)],
    ];
    for input in &inputs {
        for ord in orders_for_units() {
            let out = ord.sources(input.clone());
            assert!(
                is_permutation(input, &out),
                "conformance: {ord:?} drops a source"
            );
            let expected: Vec<Option<Event>> = match &ord {
                InnerOrder::Reverse => input.iter().rev().copied().collect(),
                _ => input.clone(),
            };
            assert_eq!(out, expected, "conformance: {ord:?}.sources({input:?})");
        }
    }
    assert_eq!(
        InnerOrder::Reverse.sources(vec![e(1, 1), e(2, 1), None]),
        [None, e(2, 1), e(1, 1)]
    );
}

/// **Criterion 10, D10.** Corpus-wide, unlimited budget, no memo (Part 2 has
/// not landed): the enumerator's report keys (multiset) and verdict are the
/// same under `recorded`, `reverse`, `sends-first` and two pins.
#[test]
fn c10_the_answer_is_order_independent() {
    let orders = [
        InnerOrder::Recorded,
        InnerOrder::Reverse,
        InnerOrder::SendsFirst,
        InnerOrder::Pinned(vec![6, 5]),
        InnerOrder::Pinned(vec![1]),
    ];
    let mut failures = Vec::new();
    let mut reported = 0;
    let mut pairs = 0;
    for p in corpus() {
        let runs: Vec<(Vec<String>, usize, String)> = orders
            .iter()
            .map(|ord| {
                let o = crate::conformance::verify_conformance_with_order(
                    p.config.clone(),
                    Arc::clone(&p.imp),
                    Arc::clone(&p.spec),
                    p.visible.clone(),
                    usize::MAX,
                    false,
                    ord.clone(),
                );
                let keys = sorted(
                    o.reports
                        .iter()
                        .map(|r| format!("{:?} {}", r.kind, key_str(&r.graph, &p.visible)))
                        .collect(),
                );
                (keys, o.exhaustions.len(), format!("{:?}", o.end))
            })
            .collect();
        for (i, ord) in orders.iter().enumerate().skip(1) {
            if runs[i] != runs[0] {
                failures.push(format!(
                    "{}: {ord:?} gives {} reports / {} exhaustions / {} against Recorded's {} / {} / {}",
                    p.name, runs[i].0.len(), runs[i].1, runs[i].2, runs[0].0.len(), runs[0].1, runs[0].2
                ));
            }
        }
        if !runs[0].0.is_empty() {
            reported += 1;
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 10 failures: {failures:#?}"
    );
    assert!(
        reported > 0 && reported < pairs,
        "conformance: ({reported} of {pairs} reported)"
    );
}

/// The Impl graph of `ex:restart` after `k` of `a`'s sends, by probe and
/// install (each probe offers exactly `a`'s next send).
fn restart_impl_after(k: usize) -> ExecutionGraph {
    let mut g = ExecutionGraph::default();
    for _ in 0..k {
        let (offers, probed) = probe_from(cfg(ConsType::FIFO), g, {
            let f = restart(false);
            move || f()
        })
        .into_parts();
        assert_eq!(offers.len(), 1, "conformance: ex:restart offers {offers:?}");
        assert_eq!(offers[0].kind(), "send");
        g = install(cfg(ConsType::FIFO), probed, &offers[0]);
    }
    g
}

/// The complete Impl graph of `ex:restart`: both sends installed, then one
/// more probe, which must offer nothing and lets `a` reach its `End`.
fn restart_impl_complete() -> ExecutionGraph {
    let g = restart_impl_after(2);
    let (offers, probed) = probe_from(cfg(ConsType::FIFO), g, {
        let f = restart(false);
        move || f()
    })
    .into_parts();
    assert!(
        offers.is_empty(),
        "conformance: ex:restart still offers {offers:?}"
    );
    probed
}

fn choices_of(g: &ExecutionGraph, n: &str) -> Vec<usize> {
    let t = tid_named(g, n);
    (0..g.thread_size(t) as u32)
        .filter_map(|i| match g.label(Event::new(t, i)) {
            LabelEnum::Choice(c) => Some(c.result()),
            _ => None,
        })
        .collect()
}

fn found(c: Cover) -> ExecutionGraph {
    match c {
        Cover::Found(g) => g,
        other => panic!("conformance: expected a cover, got {other:?}"),
    }
}

/// **Criterion 11, D11.** `ex:restart`: the `Cover` at `a`'s first send from
/// `H = ∅` returns a witness whose choice is the first value the order tries;
/// the second `Cover` (complete `G₁`) takes `6` from either seed; and the
/// whole run conforms under both pins.
#[test]
fn c11_ex_restart_first_witness_follows_the_pin() {
    let v = vis(&["a", "c"]);
    let g1 = restart_impl_after(1);
    let g2 = restart_impl_complete();
    for (ord, first) in [
        (InnerOrder::Pinned(vec![5, 6]), 5),
        (InnerOrder::Pinned(vec![6, 5]), 6),
        (InnerOrder::Recorded, 5),
        (InnerOrder::Reverse, 6),
        (InnerOrder::Pinned(vec![6]), 6),
        (InnerOrder::Pinned(vec![7]), 5),
    ] {
        let s = Search::new(
            cfg(ConsType::FIFO),
            restart(true),
            v.clone(),
            DEFAULT_SEARCH_BUDGET,
        )
        .with_inner_order(ord.clone());
        let h = found(s.cover(&g1, false, ExecutionGraph::default()).unwrap());
        assert_eq!(
            choices_of(&h, "a"),
            [first],
            "conformance: {ord:?}'s first witness"
        );
        let h2 = found(s.cover(&g2, true, h).unwrap());
        assert_eq!(
            choices_of(&h2, "a"),
            [6],
            "conformance: {ord:?}'s second witness"
        );
    }
    for ord in [
        InnerOrder::Pinned(vec![5, 6]),
        InnerOrder::Pinned(vec![6, 5]),
    ] {
        let cc = ConfBuilder::new()
            .config(cfg(ConsType::FIFO))
            .visible_threads(["a", "c"])
            .inner_order(ord.clone())
            .build()
            .unwrap();
        assert_eq!(cc.inner_order, ord);
        let verdict = crate::conformance::run(cc, restart(false), restart(true));
        assert!(
            matches!(verdict, Ok(ConfVerdict::Conforms(_))),
            "conformance: ex:restart under {ord:?}: {verdict:?}"
        );
    }
}

/// **D-transport (my addition).** Knob B reaches `spec_visit`'s offers loop:
/// `reverse` installs the invisible send before the visible one, `recorded`
/// and `sends-first` do not (report Part 0 addenda).
#[test]
fn kb_offers_order_reaches_the_inner_search() {
    let spec = prog(|| {
        let (tx, _rx) = chan();
        let t2 = tx.clone();
        let _c = named("c", move || tx.send_msg(1));
        let _i = named("i", move || t2.send_msg(5));
    });
    let imp = prog(|| {
        let (tx, _rx) = chan();
        let _c = named("c", move || tx.send_msg(1));
    });
    let g1 = graphs_of(cfg(ConsType::Bag), &vis(&["c"]), imp).remove(0);
    let first = probe_offer_names(cfg(ConsType::Bag), {
        let s = Arc::clone(&spec);
        move || s()
    });
    assert_eq!(
        first,
        [("c".to_string(), "send"), ("i".to_string(), "send")]
    );
    for (ord, i_sends) in [
        (InnerOrder::Recorded, false),
        (InnerOrder::SendsFirst, false),
        (InnerOrder::Reverse, true),
    ] {
        let s = Search::new(
            cfg(ConsType::Bag),
            Arc::clone(&spec),
            vis(&["c"]),
            DEFAULT_SEARCH_BUDGET,
        )
        .with_inner_order(ord.clone());
        let h = found(s.cover(&g1, false, ExecutionGraph::default()).unwrap());
        let has = installs(&h).iter().any(|(n, k)| n == "i" && *k == "send");
        assert_eq!(has, i_sends, "conformance: {ord:?}: H = {:?}", installs(&h));
    }
}

// ===========================================================================
// C. Plumbing
// ===========================================================================

/// **Criterion 12 / S4.** The builder sets both knobs; knob A is copied into
/// the engine `Config` after `.config()`, so it wins over a `Config` carrying
/// another selector, whichever order the setters were called in.
#[test]
fn c12_the_builder_copies_both_knobs_after_config() {
    let d = ConfBuilder::new().build().unwrap();
    assert_eq!(d.config.selector, Selector::Ltr);
    assert_eq!(d.inner_order, InnerOrder::Recorded);
    assert_eq!(Selector::default(), Selector::Ltr);
    assert_eq!(InnerOrder::default(), InnerOrder::Recorded);
    let before = ConfBuilder::new()
        .selector(Selector::Reverse)
        .config(cfg(ConsType::Bag))
        .build()
        .unwrap();
    assert_eq!(
        before.config.selector,
        Selector::Reverse,
        "conformance: .config() overwrote knob A"
    );
    let after = ConfBuilder::new()
        .config(cfg(ConsType::Bag))
        .selector(Selector::FewestEvents)
        .inner_order(InnerOrder::Pinned(vec![6, 5]))
        .build()
        .unwrap();
    assert_eq!(after.config.selector, Selector::FewestEvents);
    assert_eq!(after.inner_order, InnerOrder::Pinned(vec![6, 5]));
    let carried = ConfBuilder::new()
        .config(with_selector(cfg(ConsType::Bag), Selector::Reverse))
        .build()
        .unwrap();
    assert_eq!(
        carried.config.selector,
        Selector::Ltr,
        "conformance: the builder's knob A is not the one used"
    );
}

/// **Criterion 12, the force, D12.** With `cfg.selector = Reverse` as the
/// builder copies it, the probe still records `[main, t]`. Control: a
/// `Collect` run under the same `Reverse` installs `t`'s send first, so a
/// leak would show.
#[test]
fn c12_probe_from_forces_ltr() {
    let cc = ConfBuilder::new()
        .config(cfg(ConsType::Bag))
        .selector(Selector::Reverse)
        .visible_threads(["t"])
        .build()
        .unwrap();
    assert_eq!(cc.config.selector, Selector::Reverse);
    let offers = probe_offer_names(cc.config.clone(), force_prog);
    assert_eq!(
        offers,
        [("main".to_string(), "send"), ("t".to_string(), "send")]
    );
    let seq: Vec<String> = installs(&first_execution(
        ConsType::Bag,
        Selector::Reverse,
        prog(force_prog),
    ))
    .into_iter()
    .filter(|(_, k)| *k == "send")
    .map(|(n, _)| n)
    .collect();
    assert_eq!(
        seq,
        ["t", "main"],
        "conformance: the control does not discriminate"
    );
}

/// **Criterion 12, the `probe.is_some()` disjunct, D12.** The probe orders by
/// origination: `[x, p2]`. Control: the plain path (`TaskId` order) runs
/// `p2` before `x`, so a probe outside the predicate would record `[p2, x]`.
#[test]
fn c12_the_probe_consults_the_selector() {
    let cc = ConfBuilder::new()
        .config(cfg(ConsType::Bag))
        .visible_threads(["p2", "x"])
        .build()
        .unwrap();
    let offers = probe_offer_names(cc.config.clone(), disjunct_prog);
    assert_eq!(
        offers,
        [("x".to_string(), "send"), ("p2".to_string(), "send")]
    );
    let c = Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .with_max_iterations(1)
        .build();
    let must = Rc::new(RefCell::new(Must::new(c, false)));
    {
        let _guard = CurrentMustGuard;
        let f = Arc::new(disjunct_prog);
        crate::explore(&must, &f);
    }
    let g = must.borrow_mut().take_graph();
    let seq = installs(&g);
    assert!(
        position(&seq, "p2", "send") < position(&seq, "x", "send"),
        "conformance: the control does not discriminate: {seq:?}"
    );
}

/// **Criterion 13 (i), D13.** A trace written at `bd793be` (no `selector`
/// field; [`OLD_TRACE`], minified, content unchanged) still deserialises —
/// its `Config` reads `selector = Ltr` — and `replay` reproduces its error
/// with the message recorded at `bd793be` ([`BASELINE_C13_TRACE`]).
#[test]
fn c13_an_old_trace_still_loads_and_replays() {
    // A trace is loaded by a build with the features it was written under:
    // under `symbolic` the engine `Config` has a further field, `symbolic`,
    // with no `#[serde(default)]` (pre-existing; see the report), so each
    // suite uses the trace its own feature set wrote at `bd793be`.
    let trace: &str = if cfg!(feature = "symbolic") {
        OLD_TRACE_SYMBOLIC
    } else {
        OLD_TRACE
    };
    assert!(
        !trace.contains("\"selector\""),
        "conformance: the fixture is not an old trace"
    );
    let v: serde_json::Value = serde_json::from_str(trace).unwrap();
    let c: Config = serde_json::from_value(v["config"].clone())
        .expect("conformance: a bd793be Config no longer deserialises");
    assert_eq!(c.selector, Selector::Ltr);
    let path =
        std::env::temp_dir().join(format!("p4-selector-old-trace-{}.json", std::process::id()));
    std::fs::write(&path, trace).unwrap();
    let r = std::panic::catch_unwind(|| crate::replay(trace_prog, path.to_str().unwrap()));
    let _ = std::fs::remove_file(&path);
    let msg = match &r {
        Ok(_) => "NO PANIC".to_string(),
        Err(e) => e
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "non-string panic".into()),
    };
    assert_eq!(
        format!("replay: {msg}"),
        BASELINE_C13_TRACE.lines().nth(1).unwrap()
    );
}

/// **Criterion 13 (ii), D13.** The plain path is untouched: `nested4` under
/// `crate::verify`'s body with `LTR` has the first execution and `Stats`
/// recorded at `bd793be`. Derived content, asserted too: `TCreate(y)`
/// precedes `End(x)` there, while a `Collect` run under `Ltr` (origination
/// order) puts `End(x)` first — S5's cost (i), measured.
#[test]
fn c13_the_plain_path_is_untouched() {
    let now = plain_nested_witness();
    let then: Vec<String> = BASELINE_C13_PLAIN.lines().map(str::to_string).collect();
    assert_eq!(now, then, "conformance: the plain path changed");
    let c = Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .with_max_iterations(1)
        .build();
    let must = Rc::new(RefCell::new(Must::new(c, false)));
    {
        let _guard = CurrentMustGuard;
        let f = Arc::new(nested4);
        crate::explore(&must, &f);
    }
    let plain = installs(&must.borrow_mut().take_graph());
    assert!(
        position(&plain, "p2", "tcreate") < position(&plain, "x", "end"),
        "conformance: {plain:?}"
    );
    let conf = installs(&first_execution(
        ConsType::Bag,
        Selector::Ltr,
        prog(nested4),
    ));
    assert!(
        position(&conf, "x", "end") < position(&conf, "p2", "tcreate"),
        "conformance: {conf:?}"
    );
}

// ===========================================================================
// Baselines recorded at `bd793be` + Part 1 (scratch clone, 2026-10-06 13:16
// CEST) by the shared code above. Not edited by hand.
// ===========================================================================

/// Criterion 7: `name|budget|witness|fnv64|count`, and `name|CLASS|class`.
const BASELINE_C7: &str = r###"pe:relay/direct|CLASS|main-spawns-all
pe:relay/direct|10000|keys|a33635d92d11b149|1
pe:relay/direct|10000|first|bcd38eab914f44c7|11
pe:relay/direct|10000|reports|cbf29ce484222325|0
pe:relay/direct|10000|stats|72264964d365b243|1
pe:relay/direct|10000|verdict|37293ffe99d90e09|1
pe:relay/direct|10000|probe|f299b227aad0118e|1
pe:relay/direct|18446744073709551615|keys|a33635d92d11b149|1
pe:relay/direct|18446744073709551615|first|bcd38eab914f44c7|11
pe:relay/direct|18446744073709551615|reports|cbf29ce484222325|0
pe:relay/direct|18446744073709551615|stats|72264964d365b243|1
pe:relay/direct|18446744073709551615|verdict|37293ffe99d90e09|1
pe:relay/direct|18446744073709551615|probe|f299b227aad0118e|1
pe:direct/relay|CLASS|main-spawns-all
pe:direct/relay|10000|keys|6f5a5ad9a32f340f|1
pe:direct/relay|10000|first|3e3091a2a9e60967|6
pe:direct/relay|10000|reports|cbf29ce484222325|0
pe:direct/relay|10000|stats|72264964d365b243|1
pe:direct/relay|10000|verdict|37293ffe99d90e09|1
pe:direct/relay|10000|probe|f9842f7c64891485|1
pe:direct/relay|18446744073709551615|keys|6f5a5ad9a32f340f|1
pe:direct/relay|18446744073709551615|first|3e3091a2a9e60967|6
pe:direct/relay|18446744073709551615|reports|cbf29ce484222325|0
pe:direct/relay|18446744073709551615|stats|72264964d365b243|1
pe:direct/relay|18446744073709551615|verdict|37293ffe99d90e09|1
pe:direct/relay|18446744073709551615|probe|f9842f7c64891485|1
pe:relay/two|CLASS|main-spawns-all
pe:relay/two|10000|keys|c00582cb3766f583|1
pe:relay/two|10000|first|ee8c136659ee3a12|9
pe:relay/two|10000|reports|b250bf1e36f0e6a0|1
pe:relay/two|10000|stats|0033f6cd178ab08f|1
pe:relay/two|10000|verdict|d43e671bb94b7f6d|1
pe:relay/two|10000|probe|f299b227aad0118e|1
pe:relay/two|18446744073709551615|keys|c00582cb3766f583|1
pe:relay/two|18446744073709551615|first|ee8c136659ee3a12|9
pe:relay/two|18446744073709551615|reports|b250bf1e36f0e6a0|1
pe:relay/two|18446744073709551615|stats|0033f6cd178ab08f|1
pe:relay/two|18446744073709551615|verdict|d43e671bb94b7f6d|1
pe:relay/two|18446744073709551615|probe|f299b227aad0118e|1
pe:relay/blocks|CLASS|main-spawns-all
pe:relay/blocks|10000|keys|a33635d92d11b149|1
pe:relay/blocks|10000|first|bcd38eab914f44c7|11
pe:relay/blocks|10000|reports|7339804426d092e3|1
pe:relay/blocks|10000|stats|0033f6cd178ab08f|1
pe:relay/blocks|10000|verdict|d43e671bb94b7f6d|1
pe:relay/blocks|10000|probe|f299b227aad0118e|1
pe:relay/blocks|18446744073709551615|keys|a33635d92d11b149|1
pe:relay/blocks|18446744073709551615|first|bcd38eab914f44c7|11
pe:relay/blocks|18446744073709551615|reports|7339804426d092e3|1
pe:relay/blocks|18446744073709551615|stats|0033f6cd178ab08f|1
pe:relay/blocks|18446744073709551615|verdict|d43e671bb94b7f6d|1
pe:relay/blocks|18446744073709551615|probe|f299b227aad0118e|1
pe:blocks/direct|CLASS|main-spawns-all
pe:blocks/direct|10000|keys|b9d670bef88c41ed|1
pe:blocks/direct|10000|first|58f22179065c8d63|6
pe:blocks/direct|10000|reports|a0bab71cd84e4ca7|1
pe:blocks/direct|10000|stats|0033f6cd178ab08f|1
pe:blocks/direct|10000|verdict|d43e671bb94b7f6d|1
pe:blocks/direct|10000|probe|f299b227aad0118e|1
pe:blocks/direct|18446744073709551615|keys|b9d670bef88c41ed|1
pe:blocks/direct|18446744073709551615|first|58f22179065c8d63|6
pe:blocks/direct|18446744073709551615|reports|a0bab71cd84e4ca7|1
pe:blocks/direct|18446744073709551615|stats|0033f6cd178ab08f|1
pe:blocks/direct|18446744073709551615|verdict|d43e671bb94b7f6d|1
pe:blocks/direct|18446744073709551615|probe|f299b227aad0118e|1
pe:traces/joined|CLASS|main-spawns-all
pe:traces/joined|10000|keys|4466ee2aa7f118ac|1
pe:traces/joined|10000|first|04a6b8ad735e30c7|15
pe:traces/joined|10000|reports|cdfafa3cccd963f1|1
pe:traces/joined|10000|stats|0033f6cd178ab08f|1
pe:traces/joined|10000|verdict|d43e671bb94b7f6d|1
pe:traces/joined|10000|probe|fa499f6e6bcc01d1|1
pe:traces/joined|18446744073709551615|keys|4466ee2aa7f118ac|1
pe:traces/joined|18446744073709551615|first|04a6b8ad735e30c7|15
pe:traces/joined|18446744073709551615|reports|cdfafa3cccd963f1|1
pe:traces/joined|18446744073709551615|stats|0033f6cd178ab08f|1
pe:traces/joined|18446744073709551615|verdict|d43e671bb94b7f6d|1
pe:traces/joined|18446744073709551615|probe|fa499f6e6bcc01d1|1
pe:joined/traces|CLASS|main-spawns-all
pe:joined/traces|10000|keys|cf70762e0434ae6f|2
pe:joined/traces|10000|first|b6d422c3282c10b0|14
pe:joined/traces|10000|reports|cbf29ce484222325|0
pe:joined/traces|10000|stats|e452be540d0e6450|1
pe:joined/traces|10000|verdict|37293ffe99d90e09|1
pe:joined/traces|10000|probe|5e820863eeb8e7ca|2
pe:joined/traces|18446744073709551615|keys|cf70762e0434ae6f|2
pe:joined/traces|18446744073709551615|first|b6d422c3282c10b0|14
pe:joined/traces|18446744073709551615|reports|cbf29ce484222325|0
pe:joined/traces|18446744073709551615|stats|e452be540d0e6450|1
pe:joined/traces|18446744073709551615|verdict|37293ffe99d90e09|1
pe:joined/traces|18446744073709551615|probe|5e820863eeb8e7ca|2
rs:relayed/direct/bag|CLASS|main-spawns-all
rs:relayed/direct/bag|10000|keys|1c3470f2a7aaebe7|1
rs:relayed/direct/bag|10000|first|bcd38eab914f44c7|11
rs:relayed/direct/bag|10000|reports|cbf29ce484222325|0
rs:relayed/direct/bag|10000|stats|72264964d365b243|1
rs:relayed/direct/bag|10000|verdict|37293ffe99d90e09|1
rs:relayed/direct/bag|10000|probe|f299b227aad0118e|1
rs:relayed/direct/bag|18446744073709551615|keys|1c3470f2a7aaebe7|1
rs:relayed/direct/bag|18446744073709551615|first|bcd38eab914f44c7|11
rs:relayed/direct/bag|18446744073709551615|reports|cbf29ce484222325|0
rs:relayed/direct/bag|18446744073709551615|stats|72264964d365b243|1
rs:relayed/direct/bag|18446744073709551615|verdict|37293ffe99d90e09|1
rs:relayed/direct/bag|18446744073709551615|probe|f299b227aad0118e|1
rs:error/ok/bag|CLASS|main-spawns-all
rs:error/ok/bag|10000|keys|44fa79cb181def07|1
rs:error/ok/bag|10000|first|960d38bec6a0a826|6
rs:error/ok/bag|10000|reports|04a213715c3976c4|1
rs:error/ok/bag|10000|stats|0033f6cd178ab08f|1
rs:error/ok/bag|10000|verdict|d43e671bb94b7f6d|1
rs:error/ok/bag|10000|probe|cbf29ce484222325|0
rs:error/ok/bag|18446744073709551615|keys|44fa79cb181def07|1
rs:error/ok/bag|18446744073709551615|first|960d38bec6a0a826|6
rs:error/ok/bag|18446744073709551615|reports|04a213715c3976c4|1
rs:error/ok/bag|18446744073709551615|stats|0033f6cd178ab08f|1
rs:error/ok/bag|18446744073709551615|verdict|d43e671bb94b7f6d|1
rs:error/ok/bag|18446744073709551615|probe|cbf29ce484222325|0
t:traces/self/bag|CLASS|main-spawns-all
t:traces/self/bag|10000|keys|4ac630bec4d39e7e|2
t:traces/self/bag|10000|first|6ac2b4be11c8dcd2|13
t:traces/self/bag|10000|reports|cbf29ce484222325|0
t:traces/self/bag|10000|stats|e452be540d0e6450|1
t:traces/self/bag|10000|verdict|37293ffe99d90e09|1
t:traces/self/bag|10000|probe|5e820863eeb8e7ca|2
t:traces/self/bag|18446744073709551615|keys|4ac630bec4d39e7e|2
t:traces/self/bag|18446744073709551615|first|6ac2b4be11c8dcd2|13
t:traces/self/bag|18446744073709551615|reports|cbf29ce484222325|0
t:traces/self/bag|18446744073709551615|stats|e452be540d0e6450|1
t:traces/self/bag|18446744073709551615|verdict|37293ffe99d90e09|1
t:traces/self/bag|18446744073709551615|probe|5e820863eeb8e7ca|2
t:traces/reads-one/bag|CLASS|main-spawns-all
t:traces/reads-one/bag|10000|keys|4ac630bec4d39e7e|2
t:traces/reads-one/bag|10000|first|6ac2b4be11c8dcd2|13
t:traces/reads-one/bag|10000|reports|40f2e5a1bd0ebf1a|1
t:traces/reads-one/bag|10000|stats|7222e764d362d5e6|1
t:traces/reads-one/bag|10000|verdict|d43e671bb94b7f6d|1
t:traces/reads-one/bag|10000|probe|5e820863eeb8e7ca|2
t:traces/reads-one/bag|18446744073709551615|keys|4ac630bec4d39e7e|2
t:traces/reads-one/bag|18446744073709551615|first|6ac2b4be11c8dcd2|13
t:traces/reads-one/bag|18446744073709551615|reports|40f2e5a1bd0ebf1a|1
t:traces/reads-one/bag|18446744073709551615|stats|7222e764d362d5e6|1
t:traces/reads-one/bag|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:traces/reads-one/bag|18446744073709551615|probe|5e820863eeb8e7ca|2
rs:relayed/direct/fifo|CLASS|main-spawns-all
rs:relayed/direct/fifo|10000|keys|a33635d92d11b149|1
rs:relayed/direct/fifo|10000|first|bcd38eab914f44c7|11
rs:relayed/direct/fifo|10000|reports|cbf29ce484222325|0
rs:relayed/direct/fifo|10000|stats|72264964d365b243|1
rs:relayed/direct/fifo|10000|verdict|37293ffe99d90e09|1
rs:relayed/direct/fifo|10000|probe|f299b227aad0118e|1
rs:relayed/direct/fifo|18446744073709551615|keys|a33635d92d11b149|1
rs:relayed/direct/fifo|18446744073709551615|first|bcd38eab914f44c7|11
rs:relayed/direct/fifo|18446744073709551615|reports|cbf29ce484222325|0
rs:relayed/direct/fifo|18446744073709551615|stats|72264964d365b243|1
rs:relayed/direct/fifo|18446744073709551615|verdict|37293ffe99d90e09|1
rs:relayed/direct/fifo|18446744073709551615|probe|f299b227aad0118e|1
rs:error/ok/fifo|CLASS|main-spawns-all
rs:error/ok/fifo|10000|keys|44fa79cb181def07|1
rs:error/ok/fifo|10000|first|960d38bec6a0a826|6
rs:error/ok/fifo|10000|reports|04a213715c3976c4|1
rs:error/ok/fifo|10000|stats|0033f6cd178ab08f|1
rs:error/ok/fifo|10000|verdict|d43e671bb94b7f6d|1
rs:error/ok/fifo|10000|probe|cbf29ce484222325|0
rs:error/ok/fifo|18446744073709551615|keys|44fa79cb181def07|1
rs:error/ok/fifo|18446744073709551615|first|960d38bec6a0a826|6
rs:error/ok/fifo|18446744073709551615|reports|04a213715c3976c4|1
rs:error/ok/fifo|18446744073709551615|stats|0033f6cd178ab08f|1
rs:error/ok/fifo|18446744073709551615|verdict|d43e671bb94b7f6d|1
rs:error/ok/fifo|18446744073709551615|probe|cbf29ce484222325|0
t:traces/self/fifo|CLASS|main-spawns-all
t:traces/self/fifo|10000|keys|df5d661c2f0917b2|2
t:traces/self/fifo|10000|first|6ac2b4be11c8dcd2|13
t:traces/self/fifo|10000|reports|cbf29ce484222325|0
t:traces/self/fifo|10000|stats|e452be540d0e6450|1
t:traces/self/fifo|10000|verdict|37293ffe99d90e09|1
t:traces/self/fifo|10000|probe|5e820863eeb8e7ca|2
t:traces/self/fifo|18446744073709551615|keys|df5d661c2f0917b2|2
t:traces/self/fifo|18446744073709551615|first|6ac2b4be11c8dcd2|13
t:traces/self/fifo|18446744073709551615|reports|cbf29ce484222325|0
t:traces/self/fifo|18446744073709551615|stats|e452be540d0e6450|1
t:traces/self/fifo|18446744073709551615|verdict|37293ffe99d90e09|1
t:traces/self/fifo|18446744073709551615|probe|5e820863eeb8e7ca|2
t:traces/reads-one/fifo|CLASS|main-spawns-all
t:traces/reads-one/fifo|10000|keys|df5d661c2f0917b2|2
t:traces/reads-one/fifo|10000|first|6ac2b4be11c8dcd2|13
t:traces/reads-one/fifo|10000|reports|295ebc00a7cb057a|1
t:traces/reads-one/fifo|10000|stats|7222e764d362d5e6|1
t:traces/reads-one/fifo|10000|verdict|d43e671bb94b7f6d|1
t:traces/reads-one/fifo|10000|probe|5e820863eeb8e7ca|2
t:traces/reads-one/fifo|18446744073709551615|keys|df5d661c2f0917b2|2
t:traces/reads-one/fifo|18446744073709551615|first|6ac2b4be11c8dcd2|13
t:traces/reads-one/fifo|18446744073709551615|reports|295ebc00a7cb057a|1
t:traces/reads-one/fifo|18446744073709551615|stats|7222e764d362d5e6|1
t:traces/reads-one/fifo|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:traces/reads-one/fifo|18446744073709551615|probe|5e820863eeb8e7ca|2
rs:relayed/direct/cd|CLASS|main-spawns-all
rs:relayed/direct/cd|10000|keys|490fb543c59e6c23|1
rs:relayed/direct/cd|10000|first|bcd38eab914f44c7|11
rs:relayed/direct/cd|10000|reports|cbf29ce484222325|0
rs:relayed/direct/cd|10000|stats|72264964d365b243|1
rs:relayed/direct/cd|10000|verdict|37293ffe99d90e09|1
rs:relayed/direct/cd|10000|probe|f299b227aad0118e|1
rs:relayed/direct/cd|18446744073709551615|keys|490fb543c59e6c23|1
rs:relayed/direct/cd|18446744073709551615|first|bcd38eab914f44c7|11
rs:relayed/direct/cd|18446744073709551615|reports|cbf29ce484222325|0
rs:relayed/direct/cd|18446744073709551615|stats|72264964d365b243|1
rs:relayed/direct/cd|18446744073709551615|verdict|37293ffe99d90e09|1
rs:relayed/direct/cd|18446744073709551615|probe|f299b227aad0118e|1
rs:error/ok/cd|CLASS|main-spawns-all
rs:error/ok/cd|10000|keys|44fa79cb181def07|1
rs:error/ok/cd|10000|first|960d38bec6a0a826|6
rs:error/ok/cd|10000|reports|04a213715c3976c4|1
rs:error/ok/cd|10000|stats|0033f6cd178ab08f|1
rs:error/ok/cd|10000|verdict|d43e671bb94b7f6d|1
rs:error/ok/cd|10000|probe|cbf29ce484222325|0
rs:error/ok/cd|18446744073709551615|keys|44fa79cb181def07|1
rs:error/ok/cd|18446744073709551615|first|960d38bec6a0a826|6
rs:error/ok/cd|18446744073709551615|reports|04a213715c3976c4|1
rs:error/ok/cd|18446744073709551615|stats|0033f6cd178ab08f|1
rs:error/ok/cd|18446744073709551615|verdict|d43e671bb94b7f6d|1
rs:error/ok/cd|18446744073709551615|probe|cbf29ce484222325|0
t:traces/self/cd|CLASS|main-spawns-all
t:traces/self/cd|10000|keys|34977a8623b73a0e|2
t:traces/self/cd|10000|first|6ac2b4be11c8dcd2|13
t:traces/self/cd|10000|reports|cbf29ce484222325|0
t:traces/self/cd|10000|stats|e452be540d0e6450|1
t:traces/self/cd|10000|verdict|37293ffe99d90e09|1
t:traces/self/cd|10000|probe|5e820863eeb8e7ca|2
t:traces/self/cd|18446744073709551615|keys|34977a8623b73a0e|2
t:traces/self/cd|18446744073709551615|first|6ac2b4be11c8dcd2|13
t:traces/self/cd|18446744073709551615|reports|cbf29ce484222325|0
t:traces/self/cd|18446744073709551615|stats|e452be540d0e6450|1
t:traces/self/cd|18446744073709551615|verdict|37293ffe99d90e09|1
t:traces/self/cd|18446744073709551615|probe|5e820863eeb8e7ca|2
t:traces/reads-one/cd|CLASS|main-spawns-all
t:traces/reads-one/cd|10000|keys|34977a8623b73a0e|2
t:traces/reads-one/cd|10000|first|6ac2b4be11c8dcd2|13
t:traces/reads-one/cd|10000|reports|1a4b3014ac952a34|1
t:traces/reads-one/cd|10000|stats|7222e764d362d5e6|1
t:traces/reads-one/cd|10000|verdict|d43e671bb94b7f6d|1
t:traces/reads-one/cd|10000|probe|5e820863eeb8e7ca|2
t:traces/reads-one/cd|18446744073709551615|keys|34977a8623b73a0e|2
t:traces/reads-one/cd|18446744073709551615|first|6ac2b4be11c8dcd2|13
t:traces/reads-one/cd|18446744073709551615|reports|1a4b3014ac952a34|1
t:traces/reads-one/cd|18446744073709551615|stats|7222e764d362d5e6|1
t:traces/reads-one/cd|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:traces/reads-one/cd|18446744073709551615|probe|5e820863eeb8e7ca|2
t:naive2/enc1/impl-spec|CLASS|main-spawns-all
t:naive2/enc1/impl-spec|10000|keys|5a533aa711c18af7|1
t:naive2/enc1/impl-spec|10000|first|7bf095e1fd3fd3dc|17
t:naive2/enc1/impl-spec|10000|reports|9b532f74fc436d3d|1
t:naive2/enc1/impl-spec|10000|stats|0033f6cd178ab08f|1
t:naive2/enc1/impl-spec|10000|verdict|d43e671bb94b7f6d|1
t:naive2/enc1/impl-spec|10000|probe|3e21f00b26e157d7|3
t:naive2/enc1/impl-spec|18446744073709551615|keys|5a533aa711c18af7|1
t:naive2/enc1/impl-spec|18446744073709551615|first|7bf095e1fd3fd3dc|17
t:naive2/enc1/impl-spec|18446744073709551615|reports|9b532f74fc436d3d|1
t:naive2/enc1/impl-spec|18446744073709551615|stats|0033f6cd178ab08f|1
t:naive2/enc1/impl-spec|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:naive2/enc1/impl-spec|18446744073709551615|probe|3e21f00b26e157d7|3
t:naive2/enc1/spec-spec|CLASS|main-spawns-all
t:naive2/enc1/spec-spec|10000|keys|3f458bc747ea699f|2
t:naive2/enc1/spec-spec|10000|first|c96cd9fa99d26e7c|20
t:naive2/enc1/spec-spec|10000|reports|cbf29ce484222325|0
t:naive2/enc1/spec-spec|10000|stats|e452be540d0e6450|1
t:naive2/enc1/spec-spec|10000|verdict|37293ffe99d90e09|1
t:naive2/enc1/spec-spec|10000|probe|3e21f00b26e157d7|3
t:naive2/enc1/spec-spec|18446744073709551615|keys|3f458bc747ea699f|2
t:naive2/enc1/spec-spec|18446744073709551615|first|c96cd9fa99d26e7c|20
t:naive2/enc1/spec-spec|18446744073709551615|reports|cbf29ce484222325|0
t:naive2/enc1/spec-spec|18446744073709551615|stats|e452be540d0e6450|1
t:naive2/enc1/spec-spec|18446744073709551615|verdict|37293ffe99d90e09|1
t:naive2/enc1/spec-spec|18446744073709551615|probe|3e21f00b26e157d7|3
t:naive2/enc2/impl-spec|CLASS|main-spawns-all
t:naive2/enc2/impl-spec|10000|keys|6366d1e7910765cd|1
t:naive2/enc2/impl-spec|10000|first|00fb4758c2cd04f2|22
t:naive2/enc2/impl-spec|10000|reports|b4a17377f6486ffa|1
t:naive2/enc2/impl-spec|10000|stats|0033f6cd178ab08f|1
t:naive2/enc2/impl-spec|10000|verdict|d43e671bb94b7f6d|1
t:naive2/enc2/impl-spec|10000|probe|f00e9df3dabf8f4a|3
t:naive2/enc2/impl-spec|18446744073709551615|keys|6366d1e7910765cd|1
t:naive2/enc2/impl-spec|18446744073709551615|first|00fb4758c2cd04f2|22
t:naive2/enc2/impl-spec|18446744073709551615|reports|b4a17377f6486ffa|1
t:naive2/enc2/impl-spec|18446744073709551615|stats|0033f6cd178ab08f|1
t:naive2/enc2/impl-spec|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:naive2/enc2/impl-spec|18446744073709551615|probe|f00e9df3dabf8f4a|3
t:naive2/enc2/spec-spec|CLASS|main-spawns-all
t:naive2/enc2/spec-spec|10000|keys|6316396cc5c47b0f|2
t:naive2/enc2/spec-spec|10000|first|42431cbb00b5d309|20
t:naive2/enc2/spec-spec|10000|reports|cbf29ce484222325|0
t:naive2/enc2/spec-spec|10000|stats|e452be540d0e6450|1
t:naive2/enc2/spec-spec|10000|verdict|37293ffe99d90e09|1
t:naive2/enc2/spec-spec|10000|probe|f00e9df3dabf8f4a|3
t:naive2/enc2/spec-spec|18446744073709551615|keys|6316396cc5c47b0f|2
t:naive2/enc2/spec-spec|18446744073709551615|first|42431cbb00b5d309|20
t:naive2/enc2/spec-spec|18446744073709551615|reports|cbf29ce484222325|0
t:naive2/enc2/spec-spec|18446744073709551615|stats|e452be540d0e6450|1
t:naive2/enc2/spec-spec|18446744073709551615|verdict|37293ffe99d90e09|1
t:naive2/enc2/spec-spec|18446744073709551615|probe|f00e9df3dabf8f4a|3
t:naive3/enc1/impl-spec|CLASS|main-spawns-all
t:naive3/enc1/impl-spec|10000|keys|7ae28cbc950b4273|1
t:naive3/enc1/impl-spec|10000|first|5d75711112f80899|20
t:naive3/enc1/impl-spec|10000|reports|5aab47ceb79ce21f|1
t:naive3/enc1/impl-spec|10000|stats|0033f6cd178ab08f|1
t:naive3/enc1/impl-spec|10000|verdict|d43e671bb94b7f6d|1
t:naive3/enc1/impl-spec|10000|probe|c653a1d205d1d945|4
t:naive3/enc1/impl-spec|18446744073709551615|keys|7ae28cbc950b4273|1
t:naive3/enc1/impl-spec|18446744073709551615|first|5d75711112f80899|20
t:naive3/enc1/impl-spec|18446744073709551615|reports|5aab47ceb79ce21f|1
t:naive3/enc1/impl-spec|18446744073709551615|stats|0033f6cd178ab08f|1
t:naive3/enc1/impl-spec|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:naive3/enc1/impl-spec|18446744073709551615|probe|c653a1d205d1d945|4
t:naive3/enc1/spec-spec|CLASS|main-spawns-all
t:naive3/enc1/spec-spec|10000|keys|48a9c71ab34a0b2f|6
t:naive3/enc1/spec-spec|10000|first|dfab0a5143198f2a|25
t:naive3/enc1/spec-spec|10000|reports|cbf29ce484222325|0
t:naive3/enc1/spec-spec|10000|stats|1ce954a41bce8a5c|1
t:naive3/enc1/spec-spec|10000|verdict|37293ffe99d90e09|1
t:naive3/enc1/spec-spec|10000|probe|c653a1d205d1d945|4
t:naive3/enc1/spec-spec|18446744073709551615|keys|48a9c71ab34a0b2f|6
t:naive3/enc1/spec-spec|18446744073709551615|first|dfab0a5143198f2a|25
t:naive3/enc1/spec-spec|18446744073709551615|reports|cbf29ce484222325|0
t:naive3/enc1/spec-spec|18446744073709551615|stats|1ce954a41bce8a5c|1
t:naive3/enc1/spec-spec|18446744073709551615|verdict|37293ffe99d90e09|1
t:naive3/enc1/spec-spec|18446744073709551615|probe|c653a1d205d1d945|4
t:naive3/enc2/impl-spec|CLASS|main-spawns-all
t:naive3/enc2/impl-spec|10000|keys|d1b1386b006c9e6e|1
t:naive3/enc2/impl-spec|10000|first|53a984c91c7e095a|27
t:naive3/enc2/impl-spec|10000|reports|ba99dc77e2338881|1
t:naive3/enc2/impl-spec|10000|stats|0033f6cd178ab08f|1
t:naive3/enc2/impl-spec|10000|verdict|d43e671bb94b7f6d|1
t:naive3/enc2/impl-spec|10000|probe|48d20afc624cb712|4
t:naive3/enc2/impl-spec|18446744073709551615|keys|d1b1386b006c9e6e|1
t:naive3/enc2/impl-spec|18446744073709551615|first|53a984c91c7e095a|27
t:naive3/enc2/impl-spec|18446744073709551615|reports|ba99dc77e2338881|1
t:naive3/enc2/impl-spec|18446744073709551615|stats|0033f6cd178ab08f|1
t:naive3/enc2/impl-spec|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:naive3/enc2/impl-spec|18446744073709551615|probe|48d20afc624cb712|4
t:naive3/enc2/spec-spec|CLASS|main-spawns-all
t:naive3/enc2/spec-spec|10000|keys|c3cb5cd0f7ce9e07|6
t:naive3/enc2/spec-spec|10000|first|e0fe90bb416fdae8|25
t:naive3/enc2/spec-spec|10000|reports|cbf29ce484222325|0
t:naive3/enc2/spec-spec|10000|stats|1ce954a41bce8a5c|1
t:naive3/enc2/spec-spec|10000|verdict|37293ffe99d90e09|1
t:naive3/enc2/spec-spec|10000|probe|48d20afc624cb712|4
t:naive3/enc2/spec-spec|18446744073709551615|keys|c3cb5cd0f7ce9e07|6
t:naive3/enc2/spec-spec|18446744073709551615|first|e0fe90bb416fdae8|25
t:naive3/enc2/spec-spec|18446744073709551615|reports|cbf29ce484222325|0
t:naive3/enc2/spec-spec|18446744073709551615|stats|1ce954a41bce8a5c|1
t:naive3/enc2/spec-spec|18446744073709551615|verdict|37293ffe99d90e09|1
t:naive3/enc2/spec-spec|18446744073709551615|probe|48d20afc624cb712|4
t:restart|CLASS|main-spawns-all
t:restart|10000|keys|b2a049616386ce96|1
t:restart|10000|first|413ac194d5ad36da|9
t:restart|10000|reports|cbf29ce484222325|0
t:restart|10000|stats|72264964d365b243|1
t:restart|10000|verdict|37293ffe99d90e09|1
t:restart|10000|probe|ad26cbd62a74bcb4|1
t:restart|18446744073709551615|keys|b2a049616386ce96|1
t:restart|18446744073709551615|first|413ac194d5ad36da|9
t:restart|18446744073709551615|reports|cbf29ce484222325|0
t:restart|18446744073709551615|stats|72264964d365b243|1
t:restart|18446744073709551615|verdict|37293ffe99d90e09|1
t:restart|18446744073709551615|probe|ad26cbd62a74bcb4|1
t:restart/rev|CLASS|main-spawns-all
t:restart/rev|10000|keys|3de5b2eea4072854|2
t:restart/rev|10000|first|36764ca7295185db|12
t:restart/rev|10000|reports|aed8ffc90017a1a1|1
t:restart/rev|10000|stats|7222e764d362d5e6|1
t:restart/rev|10000|verdict|d43e671bb94b7f6d|1
t:restart/rev|10000|probe|fa499f6e6bcc01d1|1
t:restart/rev|18446744073709551615|keys|3de5b2eea4072854|2
t:restart/rev|18446744073709551615|first|36764ca7295185db|12
t:restart/rev|18446744073709551615|reports|aed8ffc90017a1a1|1
t:restart/rev|18446744073709551615|stats|7222e764d362d5e6|1
t:restart/rev|18446744073709551615|verdict|d43e671bb94b7f6d|1
t:restart/rev|18446744073709551615|probe|fa499f6e6bcc01d1|1
t:c3/self|CLASS|main-spawns-all
t:c3/self|10000|keys|7cef436af384cae1|1
t:c3/self|10000|first|723a878c0f8e8c86|19
t:c3/self|10000|reports|cbf29ce484222325|0
t:c3/self|10000|stats|72264964d365b243|1
t:c3/self|10000|verdict|37293ffe99d90e09|1
t:c3/self|10000|probe|28ad1e275cd3cf9e|1
t:c3/self|18446744073709551615|keys|7cef436af384cae1|1
t:c3/self|18446744073709551615|first|723a878c0f8e8c86|19
t:c3/self|18446744073709551615|reports|cbf29ce484222325|0
t:c3/self|18446744073709551615|stats|72264964d365b243|1
t:c3/self|18446744073709551615|verdict|37293ffe99d90e09|1
t:c3/self|18446744073709551615|probe|28ad1e275cd3cf9e|1
t:s5/self|CLASS|nested
t:s5/self|10000|keys|42a5928d2b5a9fa7|6
t:s5/self|10000|first|b8fd6ec43f11d155|31
t:s5/self|10000|reports|cbf29ce484222325|0
t:s5/self|10000|stats|1ce954a41bce8a5c|1
t:s5/self|10000|verdict|37293ffe99d90e09|1
t:s5/self|10000|probe|729cb8e175e3b331|3
t:s5/self|18446744073709551615|keys|42a5928d2b5a9fa7|6
t:s5/self|18446744073709551615|first|b8fd6ec43f11d155|31
t:s5/self|18446744073709551615|reports|cbf29ce484222325|0
t:s5/self|18446744073709551615|stats|1ce954a41bce8a5c|1
t:s5/self|18446744073709551615|verdict|37293ffe99d90e09|1
t:s5/self|18446744073709551615|probe|729cb8e175e3b331|3
t:s5/self/fifo|CLASS|nested
t:s5/self/fifo|10000|keys|42a5928d2b5a9fa7|6
t:s5/self/fifo|10000|first|b8fd6ec43f11d155|31
t:s5/self/fifo|10000|reports|cbf29ce484222325|0
t:s5/self/fifo|10000|stats|1ce954a41bce8a5c|1
t:s5/self/fifo|10000|verdict|37293ffe99d90e09|1
t:s5/self/fifo|10000|probe|729cb8e175e3b331|3
t:s5/self/fifo|18446744073709551615|keys|42a5928d2b5a9fa7|6
t:s5/self/fifo|18446744073709551615|first|b8fd6ec43f11d155|31
t:s5/self/fifo|18446744073709551615|reports|cbf29ce484222325|0
t:s5/self/fifo|18446744073709551615|stats|1ce954a41bce8a5c|1
t:s5/self/fifo|18446744073709551615|verdict|37293ffe99d90e09|1
t:s5/self/fifo|18446744073709551615|probe|729cb8e175e3b331|3
t:nested4/self|CLASS|nested
t:nested4/self|10000|keys|ce045214a4bccecd|1
t:nested4/self|10000|first|ffb1fff2f9fcedd3|18
t:nested4/self|10000|reports|cbf29ce484222325|0
t:nested4/self|10000|stats|72264964d365b243|1
t:nested4/self|10000|verdict|37293ffe99d90e09|1
t:nested4/self|10000|probe|1129f472c81ef725|4
t:nested4/self|18446744073709551615|keys|ce045214a4bccecd|1
t:nested4/self|18446744073709551615|first|ffb1fff2f9fcedd3|18
t:nested4/self|18446744073709551615|reports|cbf29ce484222325|0
t:nested4/self|18446744073709551615|stats|72264964d365b243|1
t:nested4/self|18446744073709551615|verdict|37293ffe99d90e09|1
t:nested4/self|18446744073709551615|probe|1129f472c81ef725|4
t:disjunct/self|CLASS|nested
t:disjunct/self|10000|keys|fc47de5f8c295671|1
t:disjunct/self|10000|first|a6bdd7a7ee6d7ace|13
t:disjunct/self|10000|reports|cbf29ce484222325|0
t:disjunct/self|10000|stats|72264964d365b243|1
t:disjunct/self|10000|verdict|37293ffe99d90e09|1
t:disjunct/self|10000|probe|5e820863eeb8e7ca|2
t:disjunct/self|18446744073709551615|keys|fc47de5f8c295671|1
t:disjunct/self|18446744073709551615|first|a6bdd7a7ee6d7ace|13
t:disjunct/self|18446744073709551615|reports|cbf29ce484222325|0
t:disjunct/self|18446744073709551615|stats|72264964d365b243|1
t:disjunct/self|18446744073709551615|verdict|37293ffe99d90e09|1
t:disjunct/self|18446744073709551615|probe|5e820863eeb8e7ca|2
gen:Identity:24301|CLASS|main-spawns-all
gen:Identity:24301|10000|keys|56b23553c9c9a733|1
gen:Identity:24301|10000|first|3e3091a2a9e60967|6
gen:Identity:24301|10000|reports|cbf29ce484222325|0
gen:Identity:24301|10000|stats|72264964d365b243|1
gen:Identity:24301|10000|verdict|37293ffe99d90e09|1
gen:Identity:24301|10000|probe|f299b227aad0118e|1
gen:Identity:24301|18446744073709551615|keys|56b23553c9c9a733|1
gen:Identity:24301|18446744073709551615|first|3e3091a2a9e60967|6
gen:Identity:24301|18446744073709551615|reports|cbf29ce484222325|0
gen:Identity:24301|18446744073709551615|stats|72264964d365b243|1
gen:Identity:24301|18446744073709551615|verdict|37293ffe99d90e09|1
gen:Identity:24301|18446744073709551615|probe|f299b227aad0118e|1
gen:InvisibleRefactor:4294991597|CLASS|main-spawns-all
gen:InvisibleRefactor:4294991597|10000|keys|8003a91691940363|1
gen:InvisibleRefactor:4294991597|10000|first|c116a60eeb18cd57|11
gen:InvisibleRefactor:4294991597|10000|reports|cbf29ce484222325|0
gen:InvisibleRefactor:4294991597|10000|stats|72264964d365b243|1
gen:InvisibleRefactor:4294991597|10000|verdict|37293ffe99d90e09|1
gen:InvisibleRefactor:4294991597|10000|probe|f299b227aad0118e|1
gen:InvisibleRefactor:4294991597|18446744073709551615|keys|8003a91691940363|1
gen:InvisibleRefactor:4294991597|18446744073709551615|first|c116a60eeb18cd57|11
gen:InvisibleRefactor:4294991597|18446744073709551615|reports|cbf29ce484222325|0
gen:InvisibleRefactor:4294991597|18446744073709551615|stats|72264964d365b243|1
gen:InvisibleRefactor:4294991597|18446744073709551615|verdict|37293ffe99d90e09|1
gen:InvisibleRefactor:4294991597|18446744073709551615|probe|f299b227aad0118e|1
gen:VisibleMutation:8589958893|CLASS|main-spawns-all
gen:VisibleMutation:8589958893|10000|keys|6b14f71e56e195e0|1
gen:VisibleMutation:8589958893|10000|first|6007a2066df65880|6
gen:VisibleMutation:8589958893|10000|reports|ff3d8c252f21732a|1
gen:VisibleMutation:8589958893|10000|stats|0033f6cd178ab08f|1
gen:VisibleMutation:8589958893|10000|verdict|d43e671bb94b7f6d|1
gen:VisibleMutation:8589958893|10000|probe|f299b227aad0118e|1
gen:VisibleMutation:8589958893|18446744073709551615|keys|6b14f71e56e195e0|1
gen:VisibleMutation:8589958893|18446744073709551615|first|6007a2066df65880|6
gen:VisibleMutation:8589958893|18446744073709551615|reports|ff3d8c252f21732a|1
gen:VisibleMutation:8589958893|18446744073709551615|stats|0033f6cd178ab08f|1
gen:VisibleMutation:8589958893|18446744073709551615|verdict|d43e671bb94b7f6d|1
gen:VisibleMutation:8589958893|18446744073709551615|probe|f299b227aad0118e|1
gen:DecoupleImpl:12884926189|CLASS|main-spawns-all
gen:DecoupleImpl:12884926189|10000|keys|1ea4aa01d30d617d|1
gen:DecoupleImpl:12884926189|10000|first|9a56b2a3551e7a1f|19
gen:DecoupleImpl:12884926189|10000|reports|08fe35eb8954888e|1
gen:DecoupleImpl:12884926189|10000|stats|0033f6cd178ab08f|1
gen:DecoupleImpl:12884926189|10000|verdict|d43e671bb94b7f6d|1
gen:DecoupleImpl:12884926189|10000|probe|28ad1e275cd3cf9e|1
gen:DecoupleImpl:12884926189|18446744073709551615|keys|1ea4aa01d30d617d|1
gen:DecoupleImpl:12884926189|18446744073709551615|first|9a56b2a3551e7a1f|19
gen:DecoupleImpl:12884926189|18446744073709551615|reports|08fe35eb8954888e|1
gen:DecoupleImpl:12884926189|18446744073709551615|stats|0033f6cd178ab08f|1
gen:DecoupleImpl:12884926189|18446744073709551615|verdict|d43e671bb94b7f6d|1
gen:DecoupleImpl:12884926189|18446744073709551615|probe|28ad1e275cd3cf9e|1
gen:DecoupleSpec:17179893485|CLASS|main-spawns-all
gen:DecoupleSpec:17179893485|10000|keys|6ee70348c901d258|1
gen:DecoupleSpec:17179893485|10000|first|9783aefeb5c66c36|14
gen:DecoupleSpec:17179893485|10000|reports|cbf29ce484222325|0
gen:DecoupleSpec:17179893485|10000|stats|72264964d365b243|1
gen:DecoupleSpec:17179893485|10000|verdict|37293ffe99d90e09|1
gen:DecoupleSpec:17179893485|10000|probe|1b1969c6551f8f08|2
gen:DecoupleSpec:17179893485|18446744073709551615|keys|6ee70348c901d258|1
gen:DecoupleSpec:17179893485|18446744073709551615|first|9783aefeb5c66c36|14
gen:DecoupleSpec:17179893485|18446744073709551615|reports|cbf29ce484222325|0
gen:DecoupleSpec:17179893485|18446744073709551615|stats|72264964d365b243|1
gen:DecoupleSpec:17179893485|18446744073709551615|verdict|37293ffe99d90e09|1
gen:DecoupleSpec:17179893485|18446744073709551615|probe|1b1969c6551f8f08|2
gen:SpecBlocks:21474860781|CLASS|main-spawns-all
gen:SpecBlocks:21474860781|10000|keys|b2497cab7f8b3825|1
gen:SpecBlocks:21474860781|10000|first|31cdd4f0d2f870cf|6
gen:SpecBlocks:21474860781|10000|reports|d8231965baa665c3|1
gen:SpecBlocks:21474860781|10000|stats|0033f6cd178ab08f|1
gen:SpecBlocks:21474860781|10000|verdict|d43e671bb94b7f6d|1
gen:SpecBlocks:21474860781|10000|probe|f299b227aad0118e|1
gen:SpecBlocks:21474860781|18446744073709551615|keys|b2497cab7f8b3825|1
gen:SpecBlocks:21474860781|18446744073709551615|first|31cdd4f0d2f870cf|6
gen:SpecBlocks:21474860781|18446744073709551615|reports|d8231965baa665c3|1
gen:SpecBlocks:21474860781|18446744073709551615|stats|0033f6cd178ab08f|1
gen:SpecBlocks:21474860781|18446744073709551615|verdict|d43e671bb94b7f6d|1
gen:SpecBlocks:21474860781|18446744073709551615|probe|f299b227aad0118e|1
gen:UnionCovered:25769828077|CLASS|main-spawns-all
gen:UnionCovered:25769828077|10000|keys|cd9cbaddfd5b29f7|1
gen:UnionCovered:25769828077|10000|first|d754a66eab55c0d5|17
gen:UnionCovered:25769828077|10000|reports|cbf29ce484222325|0
gen:UnionCovered:25769828077|10000|stats|72264964d365b243|1
gen:UnionCovered:25769828077|10000|verdict|37293ffe99d90e09|1
gen:UnionCovered:25769828077|10000|probe|1b1969c6551f8f08|2
gen:UnionCovered:25769828077|18446744073709551615|keys|cd9cbaddfd5b29f7|1
gen:UnionCovered:25769828077|18446744073709551615|first|d754a66eab55c0d5|17
gen:UnionCovered:25769828077|18446744073709551615|reports|cbf29ce484222325|0
gen:UnionCovered:25769828077|18446744073709551615|stats|72264964d365b243|1
gen:UnionCovered:25769828077|18446744073709551615|verdict|37293ffe99d90e09|1
gen:UnionCovered:25769828077|18446744073709551615|probe|1b1969c6551f8f08|2
"###;

/// Criterion 13 (ii): `plain_nested_witness()` at `bd793be`.
const BASELINE_C13_PLAIN: &str = r###"(t0, 0): BEGIN
(t0, 1): UNIQUE [NoOrder]
(t0, 2): TCREATE(t1:"p1")
(t1, 0): BEGIN
(t0, 3): TCREATE(t2:"p2")
(t2, 0): BEGIN
(t1, 1): TCREATE(t3:"x")
(t3, 0): BEGIN
(t1, 2): SEND(TSome(Loc(Event { thread: ThreadId { opaque_id: 0 }, index: 1 })), Val { val: 1, type_name: "i32" }) val=Val { val: 1, type_name: "i32" }
(t1, 3): END
(t2, 1): TCREATE(t4:"y")
(t4, 0): BEGIN
(t2, 2): SEND(TSome(Loc(Event { thread: ThreadId { opaque_id: 0 }, index: 1 })), Val { val: 2, type_name: "i32" }) val=Val { val: 2, type_name: "i32" }
(t2, 3): END
(t3, 1): SEND(TSome(Loc(Event { thread: ThreadId { opaque_id: 0 }, index: 1 })), Val { val: 3, type_name: "i32" }) val=Val { val: 3, type_name: "i32" }
(t3, 2): END
(t4, 1): SEND(TSome(Loc(Event { thread: ThreadId { opaque_id: 0 }, index: 1 })), Val { val: 4, type_name: "i32" }) val=Val { val: 4, type_name: "i32" }
(t4, 2): END
STATS execs=1 block=0 max_graph_events=18"###;

/// Criterion 13 (i): the panic messages of `verify` and `replay` at `bd793be`.
const BASELINE_C13_TRACE: &str = r###"verify: assertion failed: cond
replay: assertion failed: cond"###;

/// Criterion 13 (i): the error trace `verify` wrote at `bd793be` for
/// `trace_prog` (minified; `serde_json` round-trip checked equal).
const OLD_TRACE: &str = r###"{"sorted_error_graph":{"label_order":[{"Begin":{"label":{"pos":{"thread":"t0","index":0},"stamp":0,"cached_porf":{"clock":[0]},"cached_posw":{"clock":[0]}},"parent":null,"sym_id":null}},{"Unique":{"label":{"pos":{"thread":"t0","index":1},"stamp":1,"cached_porf":{"clock":[1]},"cached_posw":{"clock":[1]}},"comm":"NoOrder"}},{"TCreate":{"label":{"pos":{"thread":"t0","index":2},"stamp":2,"cached_porf":{"clock":[2]},"cached_posw":{"clock":[2]}},"cid":"t1","name":"p1","is_daemon":false,"sym_cid":null,"origination_vec":[2],"filtered_origination_vec":[0]}},{"TCreate":{"label":{"pos":{"thread":"t0","index":3},"stamp":4,"cached_porf":{"clock":[3]},"cached_posw":{"clock":[3]}},"cid":"t2","name":"p2","is_daemon":false,"sym_cid":null,"origination_vec":[3],"filtered_origination_vec":[1]}},{"Begin":{"label":{"pos":{"thread":"t2","index":0},"stamp":5,"cached_porf":{"clock":[null,null,0]},"cached_posw":{"clock":[null,null,0]}},"parent":{"thread":"t0","index":3},"sym_id":null}},{"Block":{"label":{"pos":{"thread":"t2","index":1},"stamp":10,"cached_porf":{"clock":[3,null,1]},"cached_posw":{"clock":[3,null,1]}},"btype":"Assert"}}],"labels":[{"thread":"t2","index":1},{"thread":"t0","index":1},{"thread":"t0","index":3},{"thread":"t0","index":2},{"thread":"t0","index":0},{"thread":"t2","index":0}]},"error_state":{"graph":{"threads":[{"tid":"t0","task_id":0,"tclab":{"label":{"pos":{"thread":"t0","index":0},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t0","name":"main","is_daemon":false,"sym_cid":null,"origination_vec":[],"filtered_origination_vec":[]},"labels":[{"Begin":{"label":{"pos":{"thread":"t0","index":0},"stamp":0,"cached_porf":{"clock":[0]},"cached_posw":{"clock":[0]}},"parent":null,"sym_id":null}},{"Unique":{"label":{"pos":{"thread":"t0","index":1},"stamp":1,"cached_porf":{"clock":[1]},"cached_posw":{"clock":[1]}},"comm":"NoOrder"}},{"TCreate":{"label":{"pos":{"thread":"t0","index":2},"stamp":2,"cached_porf":{"clock":[2]},"cached_posw":{"clock":[2]}},"cid":"t1","name":"p1","is_daemon":false,"sym_cid":null,"origination_vec":[2],"filtered_origination_vec":[0]}},{"TCreate":{"label":{"pos":{"thread":"t0","index":3},"stamp":4,"cached_porf":{"clock":[3]},"cached_posw":{"clock":[3]}},"cid":"t2","name":"p2","is_daemon":false,"sym_cid":null,"origination_vec":[3],"filtered_origination_vec":[1]}}]},{"tid":"t1","task_id":1,"tclab":{"label":{"pos":{"thread":"t0","index":2},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t1","name":"p1","is_daemon":false,"sym_cid":null,"origination_vec":[2],"filtered_origination_vec":[0]},"labels":[{"Begin":{"label":{"pos":{"thread":"t1","index":0},"stamp":3,"cached_porf":{"clock":[null,0]},"cached_posw":{"clock":[null,0]}},"parent":{"thread":"t0","index":2},"sym_id":null}},{"TCreate":{"label":{"pos":{"thread":"t1","index":1},"stamp":6,"cached_porf":{"clock":[2,1]},"cached_posw":{"clock":[2,1]}},"cid":"t3","name":"x","is_daemon":false,"sym_cid":null,"origination_vec":[2,1],"filtered_origination_vec":[0,0]}},{"SendMsg":{"label":{"pos":{"thread":"t1","index":2},"stamp":8,"cached_porf":{"clock":[2,2]},"cached_posw":{"clock":[2,2]}},"loc":{"sender_tid":"t1","tag":null},"comm":"NoOrder","lossy":false,"dropped":false,"sb":{"clock":[]},"reader":null,"monitor_readers":[]}},{"End":{"label":{"pos":{"thread":"t1","index":3},"stamp":9,"cached_porf":{"clock":[2,3]},"cached_posw":{"clock":[2,3]}}}}]},{"tid":"t2","task_id":2,"tclab":{"label":{"pos":{"thread":"t0","index":3},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t2","name":"p2","is_daemon":false,"sym_cid":null,"origination_vec":[3],"filtered_origination_vec":[1]},"labels":[{"Begin":{"label":{"pos":{"thread":"t2","index":0},"stamp":5,"cached_porf":{"clock":[null,null,0]},"cached_posw":{"clock":[null,null,0]}},"parent":{"thread":"t0","index":3},"sym_id":null}},{"Block":{"label":{"pos":{"thread":"t2","index":1},"stamp":10,"cached_porf":{"clock":[3,null,1]},"cached_posw":{"clock":[3,null,1]}},"btype":"Assert"}}]},{"tid":"t3","task_id":3,"tclab":{"label":{"pos":{"thread":"t1","index":1},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t3","name":"x","is_daemon":false,"sym_cid":null,"origination_vec":[2,1],"filtered_origination_vec":[0,0]},"labels":[{"Begin":{"label":{"pos":{"thread":"t3","index":0},"stamp":7,"cached_porf":{"clock":[null,null,null,0]},"cached_posw":{"clock":[null,null,null,0]}},"parent":{"thread":"t1","index":1},"sym_id":null}}]}],"stamp":10,"task_id_map":{"3":"t3","2":"t2","1":"t1","0":"t0"},"finished_threads":["t1"],"dropped_sends":0},"rqueue":{}},"error_found":true,"current_event":null,"replay_mode":true,"config":{"stack_size":32768,"progress_report":0,"thread_threshold":1000,"warnings_as_errors":false,"keep_going_after_error":false,"mode":"Verification","cons_type":"Bag","schedule_policy":"LTR","max_iterations":null,"verbose":0,"seed":0,"symmetry":false,"vr":false,"lossy_budget":0,"dot_file":null,"trace_file":null,"error_trace_file":"/tmp/claude-1000/-local-home-mkhoshechin-Documents-github-jmc/f7035fa9-3516-4abc-859d-0d83a6e50536/scratchpad/sel/old_trace.json","turmoil_trace_file":null,"parallel":false,"parallel_workers":null,"partitioned_parallelization":false,"partitioned_num_threads":null,"partitioned_branching":"RevisitQueueRayon","warmup":100,"iterations_until_split":100,"state_batch_size":1,"keep_per_execution_coverage":false,"predetermined_choices":{},"predetermined_global_choices":{},"pretty_graph_printing":false}}"###;

// ===========================================================================
// Beyond the criteria: trying to break S5's class claim (completeness per
// selector) where revisits meet nested spawns. Not in the shared block, so
// the criterion-7 baseline is unaffected.
// ===========================================================================

/// `r` receives three times; `x` (spawned by `p1`), `p1`, `y` (spawned by
/// `p2`) and, under a toss, `z` (spawned by `y`) send to it. `bad` changes
/// `y`'s value, for a violating variant.
fn nested_race(bad: bool) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let _r = named("r", move || {
            for _ in 0..3 {
                let _v: i32 = rx.recv_msg_block();
            }
        });
        let t1 = tx.clone();
        let _p1 = named("p1", move || {
            let tx_x = t1.clone();
            let _x = named("x", move || tx_x.send_msg(1));
            t1.send_msg(2);
        });
        let _p2 = named("p2", move || {
            let ty = tx.clone();
            let _y = named("y", move || {
                ty.send_msg(if bad { 5 } else { 3 });
                if crate::nondet() {
                    let tz = ty.clone();
                    let _z = named("z", move || tz.send_msg(4));
                }
            });
        });
    })
}

/// Non-blocking receives against nested senders: `r` polls twice.
fn nested_nb() {
    let (tx, rx) = chan();
    let _r = named("r", move || {
        let _a: Option<i32> = rx.recv_msg();
        let _b: Option<i32> = rx.recv_msg();
    });
    let _p = named("p", move || {
        let tq = tx.clone();
        let _q = named("q", move || tq.send_msg(1));
        tx.send_msg(2);
    });
}

/// A spawn chain `a → b → c`, each sending to `r`, which receives twice.
fn deep_chain() {
    let (tx, rx) = chan();
    let _r = named("r", move || {
        let _a: i32 = rx.recv_msg_block();
        let _b: i32 = rx.recv_msg_block();
    });
    let _a = named("a", move || {
        let tb = tx.clone();
        let _b = named("b", move || {
            let tc = tb.clone();
            let _c = named("c", move || tc.send_msg(3));
            tb.send_msg(2);
        });
        tx.send_msg(1);
    });
}

fn adversarial_pairs() -> Vec<CorpusPair> {
    let mut out = Vec::new();
    for (m, model) in [
        ("bag", ConsType::Bag),
        ("fifo", ConsType::FIFO),
        ("cd", ConsType::Causal),
    ] {
        out.push(cp(
            &format!("adv:race/{m}"),
            cfg(model),
            vis(&["r"]),
            nested_race(false),
            nested_race(false),
        ));
        out.push(cp(
            &format!("adv:race-bad/{m}"),
            cfg(model),
            vis(&["r"]),
            nested_race(true),
            nested_race(false),
        ));
        out.push(cp(
            &format!("adv:nb/{m}"),
            cfg(model),
            vis(&["r"]),
            prog(nested_nb),
            prog(nested_nb),
        ));
        out.push(cp(
            &format!("adv:chain/{m}"),
            cfg(model),
            vis(&["r"]),
            prog(deep_chain),
            prog(deep_chain),
        ));
    }
    for p in crate::conformance::generator::corpus(0xC0FF_EE00, 4) {
        out.push(CorpusPair {
            name: format!("gen4:{:?}:{}", p.mode, p.seed),
            config: p.config.clone(),
            visible: p.visible.clone(),
            imp: p.implementation.clone(),
            spec: p.specification.clone(),
        });
    }
    out
}

/// Criterion 5's two checks, unchanged, on [`adversarial_pairs`]: nested
/// spawns racing into one receiver under all three models, a toss-guarded
/// nested spawn, non-blocking receives, a spawn chain, and 28 more generated
/// pairs.
#[test]
fn adv_completeness_per_selector_on_nested_races() {
    let mut failures = Vec::new();
    let mut graphs = 0;
    let mut violating = 0;
    let pairs = adversarial_pairs();
    for p in &pairs {
        for (side, prog_) in [("impl", &p.imp), ("spec", &p.spec)] {
            let sets: Vec<Vec<String>> = SELECTORS
                .iter()
                .map(|s| {
                    graphs_of(
                        with_selector(p.config.clone(), *s),
                        &p.visible,
                        Arc::clone(prog_),
                    )
                    .iter()
                    .map(|g| key_str(g, &p.visible))
                    .collect()
                })
                .collect();
            for (i, s) in SELECTORS.iter().enumerate().skip(1) {
                if sorted(sets[i].clone()) != sorted(sets[0].clone()) {
                    failures.push(format!(
                        "{} {side}: {s:?} gives {} graphs ({} distinct) against Ltr's {} ({})",
                        p.name,
                        sets[i].len(),
                        dedup(&sets[i]).len(),
                        sets[0].len(),
                        dedup(&sets[0]).len()
                    ));
                }
            }
            graphs += sets[0].len();
        }
        let runs: Vec<(Vec<String>, Vec<String>)> = SELECTORS
            .iter()
            .map(|s| {
                let q = pair_with(p, with_selector(p.config.clone(), *s));
                (
                    gated_witness(&q, usize::MAX).0,
                    outcome_witness(&q, usize::MAX).0,
                )
            })
            .collect();
        if runs.iter().any(|r| r.1.is_empty() != runs[0].1.is_empty()) {
            failures.push(format!("{}: verdicts differ across selectors", p.name));
        }
        if runs[0].1.is_empty() {
            for (i, s) in SELECTORS.iter().enumerate().skip(1) {
                if dedup(&runs[i].0) != dedup(&runs[0].0) {
                    failures.push(format!(
                        "{} conforming: {s:?} outer run explores another set",
                        p.name
                    ));
                }
            }
        } else {
            violating += 1;
        }
    }
    assert!(failures.is_empty(), "conformance: {failures:#?}");
    assert!(violating > 0, "conformance: no adversarial pair violated");
    assert!(
        graphs >= 2 * pairs.len(),
        "conformance: only {graphs} graphs over {} pairs",
        pairs.len()
    );
}

/// A Spec that fails a visible assertion only on one interleaving: `w`
/// asserts that the first value it reads is `1`, and two senders race.
fn spec_racy_assert() {
    let (tx, rx) = chan();
    let _w = named("w", move || {
        let v: i32 = rx.recv_msg_block();
        crate::assert(v == 1);
    });
    let t2 = tx.clone();
    let _a = named("a", move || tx.send_msg(1));
    let _b = named("b", move || t2.send_msg(2));
}

/// The same race behind an invisible thread (the precheck's other `Err` arm).
fn spec_racy_assert_invisible() {
    let (tx, rx) = chan();
    let _hidden = named("hidden", move || {
        let v: i32 = rx.recv_msg_block();
        crate::assert(v == 1);
    });
    let t2 = tx.clone();
    let _a = named("a", move || tx.send_msg(1));
    let _b = named("b", move || t2.send_msg(2));
}

/// **S6 (beyond the criteria).** The precheck's `Ok` versus
/// `SpecNotErrorFree` does not depend on knob A: every corpus pair, plus two
/// Specs whose assertion fails on one interleaving only (visible and
/// invisible), give the same `run(cc)` outcome class under all three
/// selectors. Triage off (S6: its outcome is selector-dependent by design).
#[test]
fn s6_precheck_outcome_is_selector_independent() {
    let mut pairs: Vec<CorpusPair> = corpus();
    for (m, model) in [("bag", ConsType::Bag), ("fifo", ConsType::FIFO)] {
        pairs.push(cp(
            &format!("s6:racy/{m}"),
            cfg(model),
            vis(&["w", "a", "b"]),
            prog(spec_racy_assert),
            prog(spec_racy_assert),
        ));
        pairs.push(cp(
            &format!("s6:racy-invisible/{m}"),
            cfg(model),
            vis(&["a", "b"]),
            prog(spec_racy_assert_invisible),
            prog(spec_racy_assert_invisible),
        ));
    }
    let mut failures = Vec::new();
    let mut rejected = 0;
    for p in &pairs {
        let classes: Vec<String> = SELECTORS
            .iter()
            .map(|s| {
                let cc = ConfBuilder::new()
                    .config(p.config.clone())
                    .visible_threads(p.visible.clone())
                    .search_budget(usize::MAX)
                    .selector(*s)
                    .triage(false)
                    .build()
                    .unwrap();
                match crate::conformance::run(cc, Arc::clone(&p.imp), Arc::clone(&p.spec)) {
                    Ok(ConfVerdict::Conforms(_)) => "conforms".to_string(),
                    Ok(ConfVerdict::Reported(_)) => "reported".to_string(),
                    Ok(ConfVerdict::Inconclusive(_)) => "inconclusive".to_string(),
                    Err(e) => {
                        let d = format!("{e:?}");
                        d.split(|c: char| !c.is_alphanumeric())
                            .next()
                            .unwrap_or("")
                            .to_string()
                    }
                }
            })
            .collect();
        if classes.iter().any(|c| *c != classes[0]) {
            failures.push(format!("{}: {classes:?}", p.name));
        }
        if !matches!(
            classes[0].as_str(),
            "conforms" | "reported" | "inconclusive"
        ) {
            rejected += 1;
        }
    }
    assert!(failures.is_empty(), "conformance: {failures:#?}");
    assert!(
        rejected >= 4,
        "conformance: the precheck rejected only {rejected} pairs"
    );
}

/// Criterion 13 (i), for the `--features symbolic` suite: the error trace a
/// `symbolic` build wrote at `bd793be` for `trace_prog` (minified; `serde_json`
/// round-trip checked equal; the same panic messages as [`BASELINE_C13_TRACE`]).
const OLD_TRACE_SYMBOLIC: &str = r###"{"sorted_error_graph":{"label_order":[{"Begin":{"label":{"pos":{"thread":"t0","index":0},"stamp":0,"cached_porf":{"clock":[0]},"cached_posw":{"clock":[0]}},"parent":null,"sym_id":null}},{"Unique":{"label":{"pos":{"thread":"t0","index":1},"stamp":1,"cached_porf":{"clock":[1]},"cached_posw":{"clock":[1]}},"comm":"NoOrder"}},{"TCreate":{"label":{"pos":{"thread":"t0","index":2},"stamp":2,"cached_porf":{"clock":[2]},"cached_posw":{"clock":[2]}},"cid":"t1","name":"p1","is_daemon":false,"sym_cid":null,"origination_vec":[2],"filtered_origination_vec":[0]}},{"TCreate":{"label":{"pos":{"thread":"t0","index":3},"stamp":4,"cached_porf":{"clock":[3]},"cached_posw":{"clock":[3]}},"cid":"t2","name":"p2","is_daemon":false,"sym_cid":null,"origination_vec":[3],"filtered_origination_vec":[1]}},{"Begin":{"label":{"pos":{"thread":"t2","index":0},"stamp":5,"cached_porf":{"clock":[null,null,0]},"cached_posw":{"clock":[null,null,0]}},"parent":{"thread":"t0","index":3},"sym_id":null}},{"Block":{"label":{"pos":{"thread":"t2","index":1},"stamp":10,"cached_porf":{"clock":[3,null,1]},"cached_posw":{"clock":[3,null,1]}},"btype":"Assert"}}],"labels":[{"thread":"t2","index":0},{"thread":"t0","index":0},{"thread":"t2","index":1},{"thread":"t0","index":2},{"thread":"t0","index":1},{"thread":"t0","index":3}]},"error_state":{"graph":{"threads":[{"tid":"t0","task_id":0,"tclab":{"label":{"pos":{"thread":"t0","index":0},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t0","name":"main","is_daemon":false,"sym_cid":null,"origination_vec":[],"filtered_origination_vec":[]},"labels":[{"Begin":{"label":{"pos":{"thread":"t0","index":0},"stamp":0,"cached_porf":{"clock":[0]},"cached_posw":{"clock":[0]}},"parent":null,"sym_id":null}},{"Unique":{"label":{"pos":{"thread":"t0","index":1},"stamp":1,"cached_porf":{"clock":[1]},"cached_posw":{"clock":[1]}},"comm":"NoOrder"}},{"TCreate":{"label":{"pos":{"thread":"t0","index":2},"stamp":2,"cached_porf":{"clock":[2]},"cached_posw":{"clock":[2]}},"cid":"t1","name":"p1","is_daemon":false,"sym_cid":null,"origination_vec":[2],"filtered_origination_vec":[0]}},{"TCreate":{"label":{"pos":{"thread":"t0","index":3},"stamp":4,"cached_porf":{"clock":[3]},"cached_posw":{"clock":[3]}},"cid":"t2","name":"p2","is_daemon":false,"sym_cid":null,"origination_vec":[3],"filtered_origination_vec":[1]}}]},{"tid":"t1","task_id":1,"tclab":{"label":{"pos":{"thread":"t0","index":2},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t1","name":"p1","is_daemon":false,"sym_cid":null,"origination_vec":[2],"filtered_origination_vec":[0]},"labels":[{"Begin":{"label":{"pos":{"thread":"t1","index":0},"stamp":3,"cached_porf":{"clock":[null,0]},"cached_posw":{"clock":[null,0]}},"parent":{"thread":"t0","index":2},"sym_id":null}},{"TCreate":{"label":{"pos":{"thread":"t1","index":1},"stamp":6,"cached_porf":{"clock":[2,1]},"cached_posw":{"clock":[2,1]}},"cid":"t3","name":"x","is_daemon":false,"sym_cid":null,"origination_vec":[2,1],"filtered_origination_vec":[0,0]}},{"SendMsg":{"label":{"pos":{"thread":"t1","index":2},"stamp":8,"cached_porf":{"clock":[2,2]},"cached_posw":{"clock":[2,2]}},"loc":{"sender_tid":"t1","tag":null},"comm":"NoOrder","lossy":false,"dropped":false,"sb":{"clock":[]},"reader":null,"monitor_readers":[]}},{"End":{"label":{"pos":{"thread":"t1","index":3},"stamp":9,"cached_porf":{"clock":[2,3]},"cached_posw":{"clock":[2,3]}}}}]},{"tid":"t2","task_id":2,"tclab":{"label":{"pos":{"thread":"t0","index":3},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t2","name":"p2","is_daemon":false,"sym_cid":null,"origination_vec":[3],"filtered_origination_vec":[1]},"labels":[{"Begin":{"label":{"pos":{"thread":"t2","index":0},"stamp":5,"cached_porf":{"clock":[null,null,0]},"cached_posw":{"clock":[null,null,0]}},"parent":{"thread":"t0","index":3},"sym_id":null}},{"Block":{"label":{"pos":{"thread":"t2","index":1},"stamp":10,"cached_porf":{"clock":[3,null,1]},"cached_posw":{"clock":[3,null,1]}},"btype":"Assert"}}]},{"tid":"t3","task_id":3,"tclab":{"label":{"pos":{"thread":"t1","index":1},"stamp":null,"cached_porf":{"clock":[]},"cached_posw":{"clock":[]}},"cid":"t3","name":"x","is_daemon":false,"sym_cid":null,"origination_vec":[2,1],"filtered_origination_vec":[0,0]},"labels":[{"Begin":{"label":{"pos":{"thread":"t3","index":0},"stamp":7,"cached_porf":{"clock":[null,null,null,0]},"cached_posw":{"clock":[null,null,null,0]}},"parent":{"thread":"t1","index":1},"sym_id":null}}]}],"stamp":10,"task_id_map":{"0":"t0","1":"t1","2":"t2","3":"t3"},"finished_threads":["t1"],"dropped_sends":0},"rqueue":{}},"error_found":true,"current_event":null,"replay_mode":true,"config":{"stack_size":32768,"progress_report":0,"thread_threshold":1000,"warnings_as_errors":false,"keep_going_after_error":false,"mode":"Verification","cons_type":"Bag","schedule_policy":"LTR","max_iterations":null,"verbose":0,"seed":0,"symmetry":false,"vr":false,"lossy_budget":0,"dot_file":null,"trace_file":null,"error_trace_file":"/tmp/claude-1000/-local-home-mkhoshechin-Documents-github-jmc/f7035fa9-3516-4abc-859d-0d83a6e50536/scratchpad/sel/old_trace_symbolic.json","turmoil_trace_file":null,"parallel":false,"parallel_workers":null,"partitioned_parallelization":false,"partitioned_num_threads":null,"partitioned_branching":"RevisitQueueRayon","warmup":100,"iterations_until_split":100,"state_batch_size":1,"keep_per_execution_coverage":false,"predetermined_choices":{},"predetermined_global_choices":{},"pretty_graph_printing":false,"symbolic":false}}"###;

// ===========================================================================
// Gate-4 round 01 (M1): knob B's transport is observable at a finite budget.
// Derivations DR-a, DR-b, DR-c in the report's "Gate-4 round 01 follow-up".
// ===========================================================================

/// The least per-attempt budget in `1..=12` at which `cover` answers `Found`
/// (`None` if none does): the node count of the answering attempt.
fn found_threshold(
    ord: &InnerOrder,
    g1: &ExecutionGraph,
    complete: bool,
    seed: &ExecutionGraph,
) -> Option<usize> {
    (1..=12).find(|b| {
        let s = Search::new(cfg(ConsType::FIFO), restart(true), vis(&["a", "c"]), *b)
            .with_inner_order(ord.clone());
        matches!(
            s.cover(g1, complete, seed.clone()).unwrap(),
            Cover::Found(_)
        )
    })
}

/// **DR-a, measured.** Per-gate node counts on `ex:restart`: 3 / 2 / 1 under
/// `[6,5]`, 3 / 6 / 6 under `[5,6]` (a 1-node seed attempt, then a rebuild
/// with a fresh budget needing 6).
#[test]
fn m1a_ex_restart_node_counts_per_gate() {
    let g1 = restart_impl_after(1);
    let g2 = restart_impl_after(2);
    let g3 = restart_impl_complete();
    let first = |ord: &InnerOrder| {
        let s = Search::new(
            cfg(ConsType::FIFO),
            restart(true),
            vis(&["a", "c"]),
            DEFAULT_SEARCH_BUDGET,
        )
        .with_inner_order(ord.clone());
        found(s.cover(&g1, false, ExecutionGraph::default()).unwrap())
    };
    for (ord, expect) in [
        (InnerOrder::Pinned(vec![6, 5]), [3, 2, 1]),
        (InnerOrder::Reverse, [3, 2, 1]),
        (InnerOrder::Pinned(vec![5, 6]), [3, 6, 6]),
        (InnerOrder::Recorded, [3, 6, 6]),
    ] {
        let h1 = first(&ord);
        let t1 = found_threshold(&ord, &g1, false, &ExecutionGraph::default());
        let t2 = found_threshold(&ord, &g2, false, &h1);
        // The Completion gate's seed: gate 2's witness when gate 2 succeeds
        // within the run's budget (`[6,5]`), else gate 1's (`[5,6]` at 3–5).
        let seed3 = if expect[1] == 2 {
            let s = Search::new(
                cfg(ConsType::FIFO),
                restart(true),
                vis(&["a", "c"]),
                DEFAULT_SEARCH_BUDGET,
            )
            .with_inner_order(ord.clone());
            found(s.cover(&g2, false, h1.clone()).unwrap())
        } else {
            h1.clone()
        };
        let t3 = found_threshold(&ord, &g3, true, &seed3);
        assert_eq!(
            [t1, t2, t3],
            expect.map(Some),
            "conformance: {ord:?}'s per-gate node counts"
        );
    }
}

/// **DR-a / M1(a).** At `search_budget ∈ {3,4,5}` knob B decides `run(cc)`'s
/// verdict on `ex:restart`; at 6 every order conforms.
#[test]
fn m1a_at_a_finite_budget_knob_b_decides_the_verdict() {
    let verdict = |budget: usize, ord: InnerOrder| {
        let cc = ConfBuilder::new()
            .config(cfg(ConsType::FIFO))
            .visible_threads(["a", "c"])
            .search_budget(budget)
            .triage(false)
            .inner_order(ord)
            .build()
            .unwrap();
        match crate::conformance::run(cc, restart(false), restart(true)) {
            Ok(ConfVerdict::Conforms(_)) => "conforms",
            Ok(ConfVerdict::Inconclusive(_)) => "inconclusive",
            Ok(ConfVerdict::Reported(_)) => "reported",
            Err(_) => "error",
        }
    };
    for budget in [3, 4, 5] {
        assert_eq!(
            verdict(budget, InnerOrder::Pinned(vec![6, 5])),
            "conforms",
            "conformance: budget {budget}"
        );
        assert_eq!(
            verdict(budget, InnerOrder::Reverse),
            "conforms",
            "conformance: budget {budget}"
        );
        assert_eq!(
            verdict(budget, InnerOrder::Pinned(vec![5, 6])),
            "inconclusive",
            "conformance: budget {budget}"
        );
        assert_eq!(
            verdict(budget, InnerOrder::Recorded),
            "inconclusive",
            "conformance: budget {budget}"
        );
    }
    for ord in [
        InnerOrder::Pinned(vec![6, 5]),
        InnerOrder::Reverse,
        InnerOrder::Pinned(vec![5, 6]),
        InnerOrder::Recorded,
    ] {
        assert_eq!(
            verdict(6, ord.clone()),
            "conforms",
            "conformance: budget 6 under {ord:?}"
        );
    }
}

/// DR-b′'s program (the verdict's DR-b sent from `main` before spawning the
/// visible receiver, which §8's spawn-order guard refuses): an invisible `w`
/// sends `1` twice on one `NoOrder` channel; the visible `r` joins `w`, then
/// receives once — so its receive is offered only with both sources present.
fn two_sources() {
    let (tx, rx) = chan();
    let w = named("w", move || {
        tx.send_msg(1);
        tx.send_msg(1);
    });
    let _r = named("r", move || {
        w.join().unwrap();
        let _v: i32 = rx.recv_msg_block();
    });
}

fn recv_rf(g: &ExecutionGraph, n: &str) -> Option<Event> {
    let t = tid_named(g, n);
    (0..g.thread_size(t) as u32)
        .find_map(|i| g.recv_label(Event::new(t, i)).map(|r| r.rf()))
        .expect("conformance: the receiver installed no receive")
}

/// **DR-b / M1(b).** `rf_options`' order reaches the search: the two `H`s'
/// receives read different sends under `Recorded` and `Reverse`, whichever
/// source the checker lists first.
#[test]
fn m1b_rf_options_order_reaches_the_inner_search() {
    let v = vis(&["r"]);
    let graphs = graphs_of(cfg(ConsType::Bag), &v, prog(two_sources));
    assert_eq!(
        graphs.len(),
        2,
        "conformance: two_sources has {} graphs",
        graphs.len()
    );
    for g1 in &graphs {
        let h = |ord: InnerOrder| {
            let s = Search::new(
                cfg(ConsType::Bag),
                prog(two_sources),
                v.clone(),
                DEFAULT_SEARCH_BUDGET,
            )
            .with_inner_order(ord);
            found(s.cover(g1, true, ExecutionGraph::default()).unwrap())
        };
        let (a, b) = (
            recv_rf(&h(InnerOrder::Recorded), "r"),
            recv_rf(&h(InnerOrder::Reverse), "r"),
        );
        assert!(
            a.is_some() && b.is_some(),
            "conformance: a receive read nothing"
        );
        assert_ne!(
            a, b,
            "conformance: Recorded and Reverse read the same source"
        );
    }
}

/// DR-c's pair: Spec `c` sends a value chosen from `1..=2`; Impl `c` sends 3.
fn dr_c(spec: bool) -> Prog {
    prog(move || {
        let (tx, _rx) = chan();
        let _c = named("c", move || {
            if spec {
                let n = (1..=2usize).nondet();
                tx.send_msg(n as i32);
            } else {
                tx.send_msg(3);
            }
        });
    })
}

/// The listed examples of an `ObservationMismatch`'s spec text.
fn listed_examples(d: &crate::conformance::report::Diagnostics) -> Vec<String> {
    use crate::conformance::report::{Diagnostics, Obligation};
    match d {
        Diagnostics::Available {
            obligation:
                Obligation::ObservationMismatch {
                    thread,
                    position,
                    spec,
                    ..
                },
            ..
        } => {
            assert_eq!((thread.as_str(), *position), ("c", 0), "conformance: {d:?}");
            let after = spec
                .split(" observed ")
                .nth(1)
                .unwrap_or_else(|| panic!("conformance: no examples in {spec:?}"));
            let listed = after
                .split(" at this position")
                .next()
                .expect("conformance: an example list");
            listed.split(", ").map(str::to_string).collect()
        }
        other => panic!("conformance: expected an observation mismatch, got {other:?}"),
    }
}

/// **DR-c / M1(c).** `Recompute`'s order reaches the obligation through
/// `SeenAt`'s recording order: the examples are listed `1, 2` under
/// `Recorded` and `2, 1` under `Reverse` — directly, and through `run(cc)`'s
/// report.
#[test]
fn m1c_recompute_order_reaches_the_obligation() {
    use crate::conformance::diagnose::Recompute;
    let v = vis(&["c"]);
    let g1 = graphs_of(cfg(ConsType::Bag), &v, dr_c(false)).remove(0);
    let direct = |ord: InnerOrder| {
        Recompute::new(
            cfg(ConsType::Bag),
            dr_c(true),
            v.clone(),
            DEFAULT_SEARCH_BUDGET,
            true,
        )
        .with_inner_order(ord)
        .diagnose(&g1, true)
    };
    let rec = listed_examples(&direct(InnerOrder::Recorded));
    let rev = listed_examples(&direct(InnerOrder::Reverse));
    assert_eq!(rec.len(), 2, "conformance: {rec:?}");
    assert!(
        rec[0].contains('1') && rec[1].contains('2'),
        "conformance: {rec:?}"
    );
    let mut back = rec.clone();
    back.reverse();
    assert_eq!(
        rev, back,
        "conformance: Reverse did not reverse the examples"
    );

    let through_run = |ord: InnerOrder| {
        let cc = ConfBuilder::new()
            .config(cfg(ConsType::Bag))
            .visible_threads(["c"])
            .triage(false)
            .inner_order(ord)
            .build()
            .unwrap();
        match crate::conformance::run(cc, dr_c(false), dr_c(true)) {
            Ok(ConfVerdict::Reported(o)) => listed_examples(&o.reports[0].diagnostics),
            other => panic!("conformance: DR-c was not reported: {other:?}"),
        }
    };
    assert_eq!(through_run(InnerOrder::Recorded), rec);
    assert_eq!(
        through_run(InnerOrder::Reverse),
        rev,
        "conformance: run(cc) did not carry knob B to Recompute"
    );
}
