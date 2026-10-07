//! P4-ENUMERATOR gate 3: the tester's tests for the aligned enumerator
//! (criteria `P4-ENUMERATOR.md` revision 4.1).
//!
//! Every expected value below was derived from the criteria's engine facts
//! N1–N8 (with `P4-SELECTOR`'s S1–S6 and `P4-APPARATUS`'s E1–E5) and the paper
//! (`alg.tex` §8.1, §8.4, §8.7 `alg:cover`, `lem:memo`, `ex:restart`,
//! `ex:rebuild`, `lem:coverexact`, `cor:absence`, §8.8) **before** the lead's
//! diff was read; the derivations are written out in
//! `plan/traceForge/log/dev/P4-ENUMERATOR.report.md`, Part 0, under the labels
//! `D1`..`D14` cited on each test. Tests are named by criterion.
//!
//! Conventions this file keeps because `s5_tests`' source scans read it: no
//! print macro anywhere, and every panic-family message starts with
//! `conformance:`.

use std::sync::Arc;

use crate::conformance::canon::CanonicalGraph;
use crate::conformance::config::ConfConfig;
use crate::conformance::prober::{install, probe_from};
use crate::conformance::report::{ConfCounters, ConfVerdict, CoverCounters};
use crate::conformance::search::{Cover, Search, SearchOpts};
use crate::conformance::selector::{InnerOrder, Selector};
use crate::conformance::{ConfBuilder, ConfError, Outcome, ReportGate, ReportTag, SearchEnd};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::thread::construct_thread_id;
use crate::{send_msg, thread, CommunicationModel, Config, ConsType, Nondet};

type Prog = Arc<dyn Fn() + Send + Sync>;

const UNLIMITED: usize = usize::MAX;

fn prog<F: Fn() + Send + Sync + 'static>(f: F) -> Prog {
    Arc::new(f)
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
}

fn cfg(model: ConsType) -> Config {
    Config::builder().with_cons_type(model).with_seed(0).build()
}

fn with_selector(mut c: Config, s: Selector) -> Config {
    c.selector = s;
    c
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

fn opts(inner_order: InnerOrder, memo: bool) -> SearchOpts {
    SearchOpts {
        inner_order,
        memo,
        instrument: true,
    }
}

/// The engine-only path (`verify_conformance_with_opts`): no precheck, no
/// diagnostics, no triage.
fn engine(
    config: Config,
    imp: &Prog,
    spec: &Prog,
    visible: &[&str],
    budget: usize,
    o: SearchOpts,
) -> Outcome {
    crate::conformance::verify_conformance_with_opts(
        config,
        Arc::clone(imp),
        Arc::clone(spec),
        vis(visible),
        budget,
        false,
        o,
    )
}

fn cc(config: Config, visible: &[&str]) -> ConfBuilder {
    ConfBuilder::new()
        .config(config)
        .visible_threads(visible.to_vec())
        .triage(false)
}

fn run(c: ConfConfig, imp: &Prog, spec: &Prog) -> Result<ConfVerdict, ConfError> {
    crate::conformance::run(c, Arc::clone(imp), Arc::clone(spec))
}

fn class(v: &Result<ConfVerdict, ConfError>) -> String {
    match v {
        Ok(ConfVerdict::Conforms(_)) => "conforms".to_string(),
        Ok(ConfVerdict::Reported(o)) => format!("reported:{}", o.reports().len()),
        Ok(ConfVerdict::Inconclusive(_)) => "inconclusive".to_string(),
        Err(e) => format!("error:{e:?}"),
    }
}

/// The full canonical form of a graph (values included), the canonical report
/// key of plan §6; `ERR` if the form refuses the graph.
fn full_key(g: &ExecutionGraph, visible: &[String]) -> String {
    match CanonicalGraph::of(g, visible) {
        Ok(c) => format!("{c:?}"),
        Err(e) => format!("ERR {e:?}"),
    }
}

/// The counters' own key string for a graph: `format!("{:?}", key())`.
fn counter_key(g: &ExecutionGraph, visible: &[String]) -> String {
    let c = CanonicalGraph::of(g, visible)
        .unwrap_or_else(|e| panic!("conformance: no canonical form: {e:?}"));
    format!("{:?}", c.key())
}

/// Criterion 13's partition identities, which hold on every run — aborted
/// runs included since gate-4 round 01 m1 (the aborting `Cover`'s counters are
/// accounted too, so `per_cover.len() == cover_calls` with no exception).
fn assert_partition(c: &ConfCounters, what: &str) {
    assert_eq!(
        c.gate_invocations,
        c.gate_skipped_inert
            + c.gate_skipped_replay
            + c.gate_skipped_pruned
            + c.gate_skipped_disabled
            + c.gate_skipped_aborted
            + c.cover_calls,
        "conformance: {what}: the gate buckets do not partition the invocations: {c:?}"
    );
    assert_eq!(
        c.per_cover.len(),
        c.cover_calls,
        "conformance: {what}: per-Cover records vs Cover calls"
    );
    let sum = |f: &dyn Fn(&CoverCounters) -> usize| c.per_cover.iter().map(f).sum::<usize>();
    assert_eq!(
        c.spec_visit_calls,
        sum(&|p| p.spec_visit_calls),
        "conformance: {what}: SpecVisit total"
    );
    assert_eq!(
        c.spec_visit_calls,
        c.spec_visit_calls_extend + c.spec_visit_calls_rebuild,
        "conformance: {what}: SpecVisit per attempt"
    );
    assert_eq!(
        c.memo_hits,
        sum(&|p| p.memo_hits),
        "conformance: {what}: hits"
    );
    assert_eq!(
        c.rebuilds_taken,
        sum(&|p| usize::from(p.rebuild_taken)),
        "conformance: {what}: rebuilds"
    );
    for p in &c.per_cover {
        assert_eq!(
            p.spec_visit_calls,
            p.spec_visit_calls_extend + p.spec_visit_calls_rebuild,
            "conformance: {what}: per-Cover attempts {p:?}"
        );
        assert!(
            !(p.rebuild_taken && p.rebuild_skipped_initial_seed),
            "conformance: {what}: a Cover both took and skipped its rebuild {p:?}"
        );
        assert_eq!(
            p.spec_visit_calls_rebuild > 0,
            p.rebuild_taken,
            "conformance: {what}: rebuild calls without a rebuild {p:?}"
        );
    }
}

fn calls(c: &ConfCounters) -> Vec<usize> {
    c.per_cover.iter().map(|p| p.spec_visit_calls).collect()
}

// =========================================================================
// Fixtures
// =========================================================================

/// `ex:naive`'s `Impl_k` (`v = 0`) or `Spec_k` (`v = 1`), every mailbox a
/// channel `main` creates before any spawn. Encoding 1 (`c_first`) spawns
/// `c, b1..bk, a`; encoding 2 spawns `b1..bk, a, c`. With `d_asserts`, a
/// visible `d` spawned last fails an assertion (Impl side only).
fn naive_d(k: usize, v: i32, c_first: bool, d_asserts: Option<bool>) -> Prog {
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
        if let Some(fails) = d_asserts {
            let _d = named("d", move || {
                if fails {
                    crate::assert(false);
                }
            });
        }
    })
}

fn naive(k: usize, v: i32, c_first: bool) -> Prog {
    naive_d(k, v, c_first, None)
}

fn naive_visible(k: usize) -> Vec<String> {
    let mut v = vec!["a".to_string(), "c".to_string()];
    v.extend((1..=k).map(|i| format!("b{i}")));
    v
}

fn naive_vis_refs(v: &[String]) -> Vec<&str> {
    v.iter().map(String::as_str).collect()
}

/// `ex:restart` (p2p as `selector_tests::restart`): `main` spawns `c` (skip)
/// then `a`; Impl `a: send(c,1); send(c,6)`; Spec draws `n` from `5..=6`.
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

/// P4-STATEFUL criterion 14b: the enumerator's rendering of `naive_d` at
/// `k = 2` (`Reported`) is byte-identical to the pre-gate-2 baseline.
#[test]
fn c14b_enumerator_reported_rendering_matches_the_pre_gate_2_baseline() {
    let cc = ConfBuilder::new()
        .config(Config::builder().with_seed(7).build())
        .visible_threads(naive_visible(2))
        .build()
        .expect("conformance: the baseline configuration is in scope");
    let verdict = run(cc, &naive_d(2, 0, true, None), &naive_d(2, 1, true, None))
        .expect("conformance: the baseline run returned an error");
    let got = format!("{verdict}");
    // L1 (gate 3): the baseline was captured under the default features. Under
    // `symbolic`, `Config` carries one more field, so the serialized replay
    // information is longer and only the "(N bytes of JSON)" figure differs;
    // that figure alone is normalised there. The default build keeps exact
    // byte identity.
    #[cfg(not(feature = "symbolic"))]
    assert_eq!(got, super::stateful_baseline::ENUMERATOR_REPORTED_BASELINE);
    #[cfg(feature = "symbolic")]
    assert_eq!(
        json_lengths_normalised(&got),
        json_lengths_normalised(super::stateful_baseline::ENUMERATOR_REPORTED_BASELINE)
    );
}

/// Every "(<digits> bytes of JSON)" replaced by "(N bytes of JSON)"; asserts
/// that each occurrence carries digits (L1, `symbolic` only).
#[cfg(feature = "symbolic")]
fn json_lengths_normalised(s: &str) -> String {
    let parts: Vec<&str> = s.split(" bytes of JSON)").collect();
    assert!(
        parts.len() > 1,
        "conformance: no JSON length in the rendering"
    );
    let mut out = String::new();
    for (i, p) in parts.iter().enumerate() {
        if i + 1 == parts.len() {
            out.push_str(p);
            continue;
        }
        let head = p.trim_end_matches(|c: char| c.is_ascii_digit());
        assert!(
            head.ends_with('(') && head.len() < p.len(),
            "conformance: a JSON length without digits"
        );
        out.push_str(head);
        out.push_str("N bytes of JSON)");
    }
    out
}

/// What `c` does in the `ex:traces` family.
#[derive(Clone, Copy)]
enum CRecv {
    /// `x := recv()`.
    Plain,
    /// The paper's `recv(λy. y = 1)`: a receive that **cannot read** `b`'s
    /// message at all — a tag filter, since `a` tags its message `1` and `b`
    /// tags its `2` on both sides (Part 0, D5's encoding caveat).
    OnlyFromA,
    /// `x := recv(); if x == 2 { assert(false) }` (criterion 9's second
    /// fixture).
    AssertOnTwo,
    /// `x := recv(); assume(x == 1)` — **not** the paper's guarded receive
    /// (D5's caveat, recorded as a test of its own).
    AssumeOne,
}

/// `ex:traces` / `ex:rebuild` / §5.1: `main` creates one channel and spawns
/// `a, c, b`; `a` sends `1` (tag 1), `b` sends `2` (tag 2).
fn traces(c: CRecv) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let ta = tx.clone();
        let _a = named("a", move || ta.send_tagged_msg(1, 1));
        let _c = named("c", move || match c {
            CRecv::Plain => {
                let _x: i32 = rx.recv_msg_block();
            }
            CRecv::OnlyFromA => {
                let _x: i32 = rx.recv_tagged_msg_block(|t| t == Some(1));
            }
            CRecv::AssertOnTwo => {
                let x: i32 = rx.recv_msg_block();
                if x == 2 {
                    crate::assert(false);
                }
            }
            CRecv::AssumeOne => {
                let x: i32 = rx.recv_msg_block();
                crate::assume!(x == 1);
            }
        });
        let _b = named("b", move || tx.send_tagged_msg(2, 2));
    })
}

/// Criterion 9's first fixture: `main` spawns `c` (`t1`, one receive) then
/// `a` (`t2`): `a: send(c,1)`, then `assert(false)` when `asserts`.
fn send_then_assert(asserts: bool) -> Prog {
    prog(move || {
        let c = named("c", || {
            let _x: i32 = crate::recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || {
            send_msg(cid, 1i32);
            if asserts {
                crate::assert(false);
            }
        });
    })
}

/// The Blocking pair: `c` receives twice (Impl) or once (Spec); `main` sends 1.
fn blocking(twice: bool) -> Prog {
    prog(move || {
        let c = named("c", move || {
            let _v: i32 = crate::recv_msg_block();
            if twice {
                let _w: i32 = crate::recv_msg_block();
            }
        });
        send_msg(c.thread().id(), 1i32);
    })
}

/// `GrowingExhaustion × FreshRecv`: `main` spawns `c` and sends `1` tagged
/// `2`; Impl's `c` receives it, Spec's `c` accepts only tag `1`.
fn tag_recv(spec: bool) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let _c = named("c", move || {
            let _x: i32 = if spec {
                rx.recv_tagged_msg_block(|t| t == Some(1))
            } else {
                rx.recv_msg_block()
            };
        });
        tx.send_tagged_msg(2, 1);
    })
}

fn visible_error(fails: bool) -> Prog {
    prog(move || {
        let _w = named("w", move || {
            if fails {
                crate::assert(false);
            }
        });
    })
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
        g = install(cfg(ConsType::FIFO), probed, &offers[0]);
    }
    g
}

/// The complete Impl graph of `ex:restart`: one more probe lets `a` end.
fn restart_impl_complete() -> ExecutionGraph {
    let g = restart_impl_after(2);
    let (offers, probed) = probe_from(cfg(ConsType::FIFO), g, {
        let f = restart(false);
        move || f()
    })
    .into_parts();
    assert!(
        offers.is_empty(),
        "conformance: ex:restart offers {offers:?}"
    );
    probed
}

fn tid_named(g: &ExecutionGraph, n: &str) -> crate::thread::ThreadId {
    g.thread_ids()
        .into_iter()
        .find(|t| g.get_thread_tclab(*t).name().as_deref() == Some(n))
        .unwrap_or_else(|| panic!("conformance: no thread named {n}"))
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

fn last_label_kind(g: &ExecutionGraph, n: &str) -> &'static str {
    let t = tid_named(g, n);
    match g.label(Event::new(t, g.thread_size(t) as u32 - 1)) {
        LabelEnum::End(_) => "end",
        LabelEnum::SendMsg(_) => "send",
        LabelEnum::RecvMsg(_) => "recv",
        LabelEnum::Begin(_) => "begin",
        LabelEnum::Block(_) => "block",
        LabelEnum::TCreate(_) => "tcreate",
        _ => "other",
    }
}

/// The thread whose send `n`'s (only) receive reads.
fn reads_from(g: &ExecutionGraph, n: &str) -> Option<String> {
    let t = tid_named(g, n);
    let rf = (0..g.thread_size(t) as u32)
        .find_map(|i| g.recv_label(Event::new(t, i)).map(|r| r.rf()))
        .expect("conformance: no receive")?;
    g.get_thread_tclab(rf.thread).name().clone()
}

/// Every complete graph of `p` by an ungated Must exploration (the oracle's
/// `Collect` mode).
fn graphs_of(config: Config, visible: &[String], p: Prog) -> Vec<ExecutionGraph> {
    use crate::conformance::ctx::{ConfCtx, ConfMode};
    use crate::conformance::testing::CurrentMustGuard;
    use crate::must::Must;
    use std::cell::RefCell;
    use std::rc::Rc;
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

fn found(c: Cover) -> ExecutionGraph {
    match c {
        Cover::Found(g) => g,
        other => panic!("conformance: expected a cover, got {other:?}"),
    }
}

// =========================================================================
// A. Memoisation (criteria 1–4)
// =========================================================================

/// **Criteria 1–2, D1/D2.** `ex:naive` `k = 3`, encoding 2, `Reverse`,
/// `Recorded`, unlimited, instrumented: gates `b1, b2, b3` take 2 calls each;
/// `c`'s gate is a 1-call seed attempt that inserts `K({1,2,3})`, then a
/// rebuild of **16** calls memo off and **13** memo on (6 hits, all of level
/// 3 hits on the seed's key), **8** distinct keys in both arms, `NoCover`.
#[test]
fn c01_c02_memo_scope_key_and_hit_accounting_on_ex_naive_k3() {
    let v = naive_visible(3);
    let vr = naive_vis_refs(&v);
    let config = with_selector(cfg(ConsType::Bag), Selector::Reverse);
    for (memo, rebuild_calls, hits, total) in [(false, 16, 0, 23), (true, 13, 6, 20)] {
        let o = engine(
            config.clone(),
            &naive(3, 0, false),
            &naive(3, 1, false),
            &vr,
            UNLIMITED,
            opts(InnerOrder::Recorded, memo),
        );
        let c = &o.counters;
        let what = format!("memo={memo}");
        assert_partition(c, &what);
        assert_eq!(o.reports.len(), 1, "conformance: {what}: reports");
        assert_eq!(
            ReportGate::of(o.reports[0].gate),
            ReportGate::FreshSend,
            "conformance: {what}: the report's gate"
        );
        assert_eq!(c.cover_calls, 4, "conformance: {what}: Cover calls");
        for (i, p) in c.per_cover[..3].iter().enumerate() {
            assert_eq!(
                (p.spec_visit_calls, p.rebuild_taken, p.memo_hits),
                (2, false, 0),
                "conformance: {what}: b{} gate {p:?}",
                i + 1
            );
        }
        let g = &c.per_cover[3];
        assert_eq!(
            g.spec_visit_calls_extend, 1,
            "conformance: {what}: seed attempt"
        );
        assert_eq!(
            g.spec_visit_calls_rebuild, rebuild_calls,
            "conformance: {what}: rebuild calls"
        );
        assert_eq!(g.memo_hits, hits, "conformance: {what}: hits per Cover");
        assert!(g.rebuild_taken, "conformance: {what}: rebuild taken");
        assert_eq!(
            g.distinct_keys, 8,
            "conformance: {what}: per-Cover distinct"
        );
        assert_eq!(
            g.per_attempt_distinct,
            [1, 8],
            "conformance: {what}: per-attempt distinct (the seed key met in both)"
        );
        assert_eq!(c.spec_visit_calls, total, "conformance: {what}: run total");
        assert_eq!(c.memo_hits, hits, "conformance: {what}: run hits");
        assert_eq!(
            c.per_cover
                .iter()
                .map(|p| p.distinct_keys)
                .collect::<Vec<_>>(),
            [2, 2, 2, 8],
            "conformance: {what}: per-Cover distinct keys"
        );
        assert_eq!(
            c.distinct_keys_run_wide, 8,
            "conformance: {what}: run-wide distinct"
        );
        assert_eq!(c.rebuilds_taken, 1, "conformance: {what}: rebuilds");
        assert_eq!(c.cover_exhaustions, 0, "conformance: {what}: exhaustions");
        assert!(
            c.explored_complete_keys.is_empty(),
            "conformance: {what}: no unpruned completion"
        );
        assert_eq!(
            c.max_paper_events_per_execution, 4,
            "conformance: {what}: L = k+1"
        );
        assert_eq!(
            c.paper_events_at_first_report,
            Some(4),
            "conformance: {what}: paper events at the first report"
        );
    }
}

/// **Criterion 1, the boundary.** One `Search` instance answering two `Cover`
/// calls in a row keeps no set between them: the second call's figures are
/// exactly a fresh instance's (D3's gate-2 numbers under `[5,6]`, memo on).
#[test]
fn c01_nothing_survives_across_cover_calls_on_one_instance() {
    let g1 = restart_impl_after(1);
    let g2 = restart_impl_after(2);
    let search = || {
        Search::new(
            cfg(ConsType::FIFO),
            restart(true),
            vis(&["a", "c"]),
            UNLIMITED,
        )
        .with_opts(opts(InnerOrder::Pinned(vec![5, 6]), true))
    };
    let s = search();
    let (h1, c1) = s.cover_counted(&g1, false, ExecutionGraph::default());
    let h1 = found(h1.unwrap());
    assert_eq!(
        choices_of(&h1, "a"),
        [5],
        "conformance: the first witness takes 5"
    );
    assert_eq!(c1.spec_visit_calls, 3, "conformance: gate 1 calls");
    let (h2, c2) = s.cover_counted(&g2, false, h1.clone());
    let (h2f, c2f) = search().cover_counted(&g2, false, h1);
    let (h2, h2f) = (h2.unwrap(), h2f.unwrap());
    assert_eq!(
        choices_of(&found(h2), "a"),
        [6],
        "conformance: gate 2 takes 6"
    );
    assert_eq!(choices_of(&found(h2f), "a"), [6]);
    assert_eq!(
        (
            c2.spec_visit_calls_extend,
            c2.spec_visit_calls_rebuild,
            c2.memo_hits,
            c2.distinct_keys
        ),
        (1, 6, 1, 6),
        "conformance: gate 2 on the reused instance {c2:?}"
    );
    assert_eq!(
        (
            c2.spec_visit_calls,
            c2.memo_hits,
            c2.distinct_keys,
            c2.per_attempt_distinct
        ),
        (
            c2f.spec_visit_calls,
            c2f.memo_hits,
            c2f.distinct_keys,
            c2f.per_attempt_distinct
        ),
        "conformance: a reused instance differs from a fresh one"
    );
}

/// **Criterion 3, §5.8, D3.** `ex:restart` under `Pinned([5,6])`, memo on,
/// unlimited: no report, the first carried witness holds choice 5, and the
/// second `Cover` meets **6** distinct keys (2 under `[6,5]`). Mutation "reuse
/// the visited set across `Cover` calls" turns this into a false report at
/// `a`'s second send.
#[test]
fn c03_memo_scope_mutation_test_on_ex_restart() {
    let v = vis(&["a", "c"]);
    for (ord, gate2) in [
        (InnerOrder::Pinned(vec![5, 6]), (1, 6, 1, 6, true)),
        (InnerOrder::Pinned(vec![6, 5]), (2, 0, 0, 2, false)),
    ] {
        let o = engine(
            cfg(ConsType::FIFO),
            &restart(false),
            &restart(true),
            &["a", "c"],
            UNLIMITED,
            opts(ord.clone(), true),
        );
        let c = &o.counters;
        assert_partition(c, &format!("{ord:?}"));
        assert!(
            o.reports.is_empty(),
            "conformance: {ord:?}: ex:restart reported {:?}",
            o.reports
        );
        assert_eq!(o.end, SearchEnd::StateSpaceExhausted);
        assert_eq!(c.cover_calls, 3, "conformance: {ord:?}: Cover calls");
        let g = &c.per_cover[1];
        assert_eq!(
            (
                g.spec_visit_calls_extend,
                g.spec_visit_calls_rebuild,
                g.memo_hits,
                g.distinct_keys,
                g.rebuild_taken
            ),
            gate2,
            "conformance: {ord:?}: the second Cover {g:?}"
        );
        let verdict = run(
            cc(cfg(ConsType::FIFO), &["a", "c"])
                .inner_order(ord.clone())
                .memo(true)
                .unlimited()
                .build()
                .unwrap(),
            &restart(false),
            &restart(true),
        );
        assert_eq!(
            class(&verdict),
            "conforms",
            "conformance: run(cc) under {ord:?}"
        );
    }
    // The first carried witness contains 5 — without it the mutation is not
    // exercised (§5.8).
    let s = Search::new(cfg(ConsType::FIFO), restart(true), v, UNLIMITED)
        .with_opts(opts(InnerOrder::Pinned(vec![5, 6]), true));
    let h = found(
        s.cover(&restart_impl_after(1), false, ExecutionGraph::default())
            .unwrap(),
    );
    assert_eq!(choices_of(&h, "a"), [5], "conformance: the first witness");
    let h2 = found(s.cover(&restart_impl_after(2), false, h).unwrap());
    let h3 = found(s.cover(&restart_impl_complete(), true, h2).unwrap());
    assert_eq!(choices_of(&h3, "a"), [6]);
}

/// The criterion-4 corpus: `(name, config, visible, imp, spec)`.
fn corpus4() -> Vec<(String, Config, Vec<String>, Prog, Prog)> {
    let mut out: Vec<(String, Config, Vec<String>, Prog, Prog)> = Vec::new();
    let mut push = |n: &str, c: Config, v: Vec<String>, i: Prog, s: Prog| {
        out.push((n.to_string(), c, v, i, s));
    };
    let abc = vis(&["a", "b", "c"]);
    for (m, model) in [
        ("bag", ConsType::Bag),
        ("fifo", ConsType::FIFO),
        ("cd", ConsType::Causal),
    ] {
        push(
            &format!("traces/self/{m}"),
            cfg(model),
            abc.clone(),
            traces(CRecv::Plain),
            traces(CRecv::Plain),
        );
        push(
            &format!("traces/only-a/{m}"),
            cfg(model),
            abc.clone(),
            traces(CRecv::Plain),
            traces(CRecv::OnlyFromA),
        );
        push(
            &format!("traces/assume/{m}"),
            cfg(model),
            abc.clone(),
            traces(CRecv::Plain),
            traces(CRecv::AssumeOne),
        );
        push(
            &format!("blocking/{m}"),
            cfg(model),
            vis(&["main", "c"]),
            blocking(true),
            blocking(false),
        );
        push(
            &format!("blocking/rev/{m}"),
            cfg(model),
            vis(&["main", "c"]),
            blocking(false),
            blocking(true),
        );
        push(
            &format!("verr/{m}"),
            cfg(model),
            vis(&["w"]),
            visible_error(true),
            visible_error(false),
        );
    }
    push(
        "restart",
        cfg(ConsType::FIFO),
        vis(&["a", "c"]),
        restart(false),
        restart(true),
    );
    push(
        "restart/rev",
        cfg(ConsType::FIFO),
        vis(&["a", "c"]),
        restart(true),
        restart(false),
    );
    push(
        "restart/both",
        cfg(ConsType::FIFO),
        vis(&["a", "c"]),
        restart(true),
        restart(true),
    );
    push(
        "tag-recv",
        cfg(ConsType::Bag),
        vis(&["main", "c"]),
        tag_recv(false),
        tag_recv(true),
    );
    for k in [2usize, 3] {
        for (e, c_first) in [("enc1", true), ("enc2", false)] {
            for (sn, sel) in [("ltr", Selector::Ltr), ("rev", Selector::Reverse)] {
                let c = with_selector(cfg(ConsType::Bag), sel);
                push(
                    &format!("naive{k}/{e}/{sn}/impl-spec"),
                    c.clone(),
                    naive_visible(k),
                    naive(k, 0, c_first),
                    naive(k, 1, c_first),
                );
                push(
                    &format!("naive{k}/{e}/{sn}/spec-spec"),
                    c,
                    naive_visible(k),
                    naive(k, 1, c_first),
                    naive(k, 1, c_first),
                );
            }
        }
    }
    for p in crate::conformance::generator::corpus(0xE7E7_0004, 2) {
        push(
            &format!("gen:{:?}:{}", p.mode, p.seed),
            p.config.clone(),
            p.visible.clone(),
            p.implementation.clone(),
            p.specification.clone(),
        );
    }
    out
}

/// **Criterion 4, D4.** Memo on changes no answer at unlimited budget: per
/// pair, the report keys (gate + cause + full canonical form; the semantic tag is a
/// function of gate and cause, `ReportTag::of`, so it is determined by the key) and the verdict
/// are identical with memo on and off; only the counters differ. Admissibility
/// (F41/F44/F79): every value is `i32`/`u64`, every destination a thread
/// mailbox or an unnamed channel, the only other `ThreadId` use is none (the
/// tag filter reads tags, not ids); generator pairs are the same family
/// `selector_tests` c05 labelled admissible. Inconclusive pairs (either arm)
/// are collected and excluded — none is expected at unlimited budget.
#[test]
fn c04_memo_changes_no_answer_corpus_wide() {
    let mut compared = 0usize;
    let mut differing_counters = 0usize;
    let mut inconclusive = Vec::new();
    for (name, config, visible, imp, spec) in corpus4() {
        let vr: Vec<&str> = visible.iter().map(String::as_str).collect();
        let keys = |o: &Outcome| {
            let mut k: Vec<String> = o
                .reports
                .iter()
                .map(|r| {
                    let gate = ReportGate::of(r.gate);
                    let cause = match r.kind {
                        crate::conformance::ctx::ReportKind::NoCover => "NoCover",
                        crate::conformance::ctx::ReportKind::VisibleError { .. } => "VisibleError",
                    };
                    format!("{gate:?} {cause} {}", full_key(&r.graph, &visible))
                })
                .collect();
            k.sort();
            k
        };
        let off = engine(
            config.clone(),
            &imp,
            &spec,
            &vr,
            UNLIMITED,
            opts(InnerOrder::Recorded, false),
        );
        let on = engine(
            config.clone(),
            &imp,
            &spec,
            &vr,
            UNLIMITED,
            opts(InnerOrder::Recorded, true),
        );
        assert!(off.spec_error.is_none() && on.spec_error.is_none());
        if !off.exhaustions.is_empty() || !on.exhaustions.is_empty() {
            inconclusive.push(name.clone());
            continue;
        }
        assert_eq!(
            keys(&off),
            keys(&on),
            "conformance: {name}: report keys differ"
        );
        assert_eq!(off.end, on.end, "conformance: {name}: end differs");
        assert_eq!(
            off.counters.cover_calls, on.counters.cover_calls,
            "conformance: {name}: the outer exploration differs"
        );
        assert_eq!(
            off.counters.explored_complete_keys, on.counters.explored_complete_keys,
            "conformance: {name}: explored complete graphs differ"
        );
        assert!(
            on.counters.spec_visit_calls <= off.counters.spec_visit_calls,
            "conformance: {name}: memo on made more calls than memo off"
        );
        if on.counters.spec_visit_calls != off.counters.spec_visit_calls {
            differing_counters += 1;
        }
        let verdict = |memo: bool| {
            class(&run(
                cc(config.clone(), &vr)
                    .unlimited()
                    .memo(memo)
                    .skip_spec_errfree_check(true)
                    .build()
                    .unwrap(),
                &imp,
                &spec,
            ))
        };
        assert_eq!(
            verdict(false),
            verdict(true),
            "conformance: {name}: verdict differs"
        );
        compared += 1;
    }
    assert!(
        inconclusive.is_empty(),
        "conformance: inconclusive at unlimited budget: {inconclusive:?}"
    );
    assert!(
        compared >= 40,
        "conformance: only {compared} pairs compared"
    );
    assert!(
        differing_counters > 0,
        "conformance: memo never changed a counter, so it was never exercised"
    );
}

// =========================================================================
// B. Two tag layers (criteria 5–6)
// =========================================================================

fn reported(v: &Result<ConfVerdict, ConfError>) -> &crate::conformance::ConfOutcome {
    match v {
        Ok(ConfVerdict::Reported(o)) => o,
        other => panic!(
            "conformance: expected a Reported verdict, got {}",
            class(other)
        ),
    }
}

/// **Criteria 5–6, D5/D6.** One fixture per row of the tag table, each
/// asserting both tags, the `certifies()` text, and the rendering line.
#[test]
fn c05_c06_the_tag_table_one_fixture_per_row() {
    type Row<'a> = (
        &'a str,
        Config,
        Vec<&'a str>,
        Prog,
        Prog,
        ReportGate,
        ReportTag,
    );
    let rows: Vec<Row> = vec![
        (
            "visible error",
            cfg(ConsType::FIFO),
            vec!["w"],
            visible_error(true),
            visible_error(false),
            ReportGate::NotAGate,
            ReportTag::VisibleError,
        ),
        (
            "blocking pair",
            cfg(ConsType::FIFO),
            vec!["main", "c"],
            blocking(true),
            blocking(false),
            ReportGate::Completion,
            ReportTag::CompleteCoverage,
        ),
        (
            "ex:naive enc 2, C's send",
            with_selector(cfg(ConsType::Bag), Selector::Reverse),
            vec!["a", "c", "b1", "b2", "b3"],
            naive(3, 0, false),
            naive(3, 1, false),
            ReportGate::FreshSend,
            ReportTag::GrowingExhaustion,
        ),
        (
            "tag-filtered receive",
            cfg(ConsType::Bag),
            vec!["main", "c"],
            tag_recv(false),
            tag_recv(true),
            ReportGate::FreshRecv,
            ReportTag::GrowingExhaustion,
        ),
        (
            "§5.1, C reads 2 (N2: a complete graph at a growing gate)",
            cfg(ConsType::Bag),
            vec!["a", "b", "c"],
            traces(CRecv::Plain),
            traces(CRecv::OnlyFromA),
            ReportGate::RevisitApply,
            ReportTag::GrowingExhaustion,
        ),
    ];
    for (name, config, visible, imp, spec, gate, tag) in rows {
        let v = run(
            cc(config, &visible).unlimited().build().unwrap(),
            &imp,
            &spec,
        );
        let o = reported(&v);
        assert_eq!(o.reports().len(), 1, "conformance: {name}: reports");
        let r = &o.reports()[0];
        assert_eq!(
            (r.gate(), r.tag()),
            (gate, tag),
            "conformance: {name}: tags"
        );
        let text = r.tag().certifies();
        let needle = match tag {
            ReportTag::GrowingExhaustion => "cor:absence",
            ReportTag::CompleteCoverage => "lem:coverexact (2)",
            ReportTag::VisibleError => "not a C1-absence claim",
        };
        assert!(
            text.contains(needle),
            "conformance: {name}: certifies() = {text}"
        );
        let shown = format!("{r}");
        assert!(
            shown.contains(&format!("certifies ({tag:?}): {text}")),
            "conformance: {name}: rendering lacks the certificate line:\n{shown}"
        );
    }
    // The three texts are pairwise distinct (one certificate each).
    let t = [
        ReportTag::GrowingExhaustion.certifies(),
        ReportTag::CompleteCoverage.certifies(),
        ReportTag::VisibleError.certifies(),
    ];
    assert!(t[0] != t[1] && t[1] != t[2] && t[0] != t[2]);
    assert!(t[2].contains('\u{a7}') && t[2].contains("8.1"));
}

/// **D5's caveat, measured.** `recv(); assume(x == 1)` is not the paper's
/// guarded receive: Spec's `c` observes 2 and blocks after it, so the growing
/// `RevisitApply` gate **matches** and the report moves to `Completion`
/// (`CompleteCoverage`). Criterion 10 therefore uses the tag filter.
#[test]
fn c05_assume_after_receive_reports_at_completion_not_revisit_apply() {
    let v = run(
        cc(cfg(ConsType::Bag), &["a", "b", "c"])
            .unlimited()
            .build()
            .unwrap(),
        &traces(CRecv::Plain),
        &traces(CRecv::AssumeOne),
    );
    let o = reported(&v);
    let tags: Vec<(ReportGate, ReportTag)> =
        o.reports().iter().map(|r| (r.gate(), r.tag())).collect();
    assert_eq!(
        tags,
        [(ReportGate::Completion, ReportTag::CompleteCoverage)],
        "conformance: the assume encoding's report"
    );
}

// =========================================================================
// C. Budget → inconclusive (criteria 7–8)
// =========================================================================

/// **Criterion 7, D7.** `ex:naive` `k = 4`, encoding 2, `Reverse`,
/// `Recorded`: below 65 (memo off) / 33 (memo on) every run is
/// inconclusive with zero reports; at the boundary it reports once.
#[test]
fn c07_exhaustion_is_inconclusive_never_a_report() {
    let v = naive_visible(4);
    let vr = naive_vis_refs(&v);
    let config = with_selector(cfg(ConsType::Bag), Selector::Reverse);
    let imp = naive(4, 0, false);
    let spec = naive(4, 1, false);
    let verdict = |budget: usize, memo: bool| {
        run(
            cc(config.clone(), &vr)
                .search_budget(budget)
                .memo(memo)
                .build()
                .unwrap(),
            &imp,
            &spec,
        )
    };
    for (budget, memo) in [
        (1, false),
        (2, false),
        (8, false),
        (64, false),
        (8, true),
        (32, true),
    ] {
        let what = format!("budget {budget} memo {memo}");
        let vd = verdict(budget, memo);
        let o = match &vd {
            Ok(ConfVerdict::Inconclusive(o)) => o,
            other => panic!(
                "conformance: {what}: expected Inconclusive, got {}",
                class(other)
            ),
        };
        assert!(o.reports().is_empty(), "conformance: {what}: reports");
        assert!(
            !o.exhaustions().is_empty(),
            "conformance: {what}: exhaustions"
        );
        assert!(o.inconclusive(), "conformance: {what}: inconclusive()");
        assert_eq!(o.counters().cover_exhaustions, o.exhaustions().len());
        assert_eq!(
            o.end(),
            SearchEnd::StateSpaceExhausted,
            "conformance: {what}"
        );
        let shown = format!("{}", vd.as_ref().unwrap());
        let line = format!(
            "inconclusive: the inner search ran out of budget {} time",
            o.exhaustions().len()
        );
        assert!(
            shown.contains(&line),
            "conformance: {what}: rendering:\n{shown}"
        );
        if budget >= 2 {
            // D7: every b_i gate answers in 2 calls; c's send gate exhausts.
            let pc = &o.counters().per_cover;
            for p in &pc[..4] {
                assert_eq!(p.spec_visit_calls, 2, "conformance: {what}: a b gate {p:?}");
            }
            assert!(pc[4].spec_visit_calls_extend == 1 && pc[4].rebuild_taken);
            assert_eq!(
                pc[4].spec_visit_calls_rebuild, budget,
                "conformance: {what}"
            );
        }
    }
    for (budget, memo) in [(65, false), (33, true)] {
        let what = format!("budget {budget} memo {memo}");
        let vd = verdict(budget, memo);
        let o = reported(&vd);
        assert_eq!(o.reports().len(), 1, "conformance: {what}: reports");
        assert_eq!(
            (o.reports()[0].gate(), o.reports()[0].tag()),
            (ReportGate::FreshSend, ReportTag::GrowingExhaustion)
        );
        assert!(!o.inconclusive(), "conformance: {what}");
        assert_eq!(
            o.counters().per_cover[4].spec_visit_calls_rebuild,
            budget,
            "conformance: {what}: the boundary is exact"
        );
    }
}

/// **Criterion 7, the rendering's two other cases.** A `MaxIterations`
/// inconclusive run with zero exhaustions does not claim budget exhaustion;
/// a `Reported` run with exhaustions is `inconclusive()` and still renders its
/// report as a candidate violation.
#[test]
fn c07_rendering_only_when_exhaustions_and_reported_with_exhaustions() {
    let bounded = Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .with_max_iterations(1)
        .build();
    let vd = run(
        cc(bounded, &["a", "b", "c"]).unlimited().build().unwrap(),
        &traces(CRecv::Plain),
        &traces(CRecv::Plain),
    );
    let o = match &vd {
        Ok(ConfVerdict::Inconclusive(o)) => o,
        other => panic!("conformance: expected Inconclusive, got {}", class(other)),
    };
    assert!(o.exhaustions().is_empty() && !o.inconclusive());
    assert!(matches!(o.end(), SearchEnd::MaxIterations(_)));
    let shown = format!("{}", vd.as_ref().unwrap());
    assert!(
        !shown.contains("ran out of budget"),
        "conformance: a bounded run claims exhaustion:\n{shown}"
    );

    let mut v = naive_visible(4);
    v.push("d".to_string());
    let vr = naive_vis_refs(&v);
    let vd = run(
        cc(with_selector(cfg(ConsType::Bag), Selector::Reverse), &vr)
            .search_budget(8)
            .build()
            .unwrap(),
        &naive_d(4, 0, false, Some(true)),
        &naive_d(4, 1, false, Some(false)),
    );
    let o = reported(&vd);
    assert!(
        o.inconclusive(),
        "conformance: exhaustions were not counted"
    );
    assert!(o
        .reports()
        .iter()
        .all(|r| r.tag() == ReportTag::VisibleError));
    let shown = format!("{}", vd.as_ref().unwrap());
    assert!(
        shown.contains("certifies (VisibleError)"),
        "conformance:\n{shown}"
    );
}

/// **Criterion 8, D8.** `unlimited()` is `usize::MAX`, and under it the
/// criterion-7 pair, memo off, reports (65 fits).
#[test]
fn c08_unlimited_is_expressible() {
    let c = ConfBuilder::new().unlimited().build().unwrap();
    assert_eq!(c.search_budget(), usize::MAX);
    let v = naive_visible(4);
    let vr = naive_vis_refs(&v);
    let vd = run(
        cc(with_selector(cfg(ConsType::Bag), Selector::Reverse), &vr)
            .unlimited()
            .build()
            .unwrap(),
        &naive(4, 0, false),
        &naive(4, 1, false),
    );
    assert_eq!(reported(&vd).reports().len(), 1);
}

// =========================================================================
// D. Spec assertion-safety (criterion 9)
// =========================================================================

fn trace_path(tag: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!("tf-p4-enum-{}-{tag}.json", std::process::id()))
}

/// **Criterion 9, fixture 1, D9.** Spec `a: send(c,1); assert(false)`; Impl
/// without the assert. Under both `keep_going_after_error` settings: `run`
/// returns `Err(SpecNotAssertionSafe { "a", "(t2, 2)" })`; engine-only:
/// `spec_error`, no report, `end = SpecNotAssertionSafe`, one execution not
/// blocked (`Continue`, not `Prune`), the two later gates inert, no trace
/// file. (The `PANIC_HOOK` is a private thread-local of the worker thread,
/// unobservable here; the trace file is the observable `persist` would leave,
/// though `store_replay_information` already skips probes.)
#[test]
fn c09_spec_assertion_in_a_probe_aborts_the_run() {
    for keep_going in [false, true] {
        let path = trace_path(&format!("c09-{keep_going}"));
        let _ = std::fs::remove_file(&path);
        let config = Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_seed(0)
            .with_keep_going_after_error(keep_going)
            .with_error_trace(path.to_str().unwrap())
            .build();
        let what = format!("keep_going={keep_going}");
        let v = run(
            cc(config.clone(), &["a", "c"])
                .skip_spec_errfree_check(true)
                .build()
                .unwrap(),
            &send_then_assert(false),
            &send_then_assert(true),
        );
        assert_eq!(
            v.as_ref().err(),
            Some(&ConfError::SpecNotAssertionSafe {
                thread: "a".to_string(),
                pos: format!("{}", Event::new(construct_thread_id(2), 2)),
            }),
            "conformance: {what}: run(cc) = {}",
            class(&v)
        );
        let o = engine(
            config.clone(),
            &send_then_assert(false),
            &send_then_assert(true),
            &["a", "c"],
            UNLIMITED,
            opts(InnerOrder::Recorded, false),
        );
        assert_eq!(
            o.spec_error,
            Some(("a".to_string(), Event::new(construct_thread_id(2), 2))),
            "conformance: {what}"
        );
        assert!(o.reports.is_empty(), "conformance: {what}: reports");
        assert!(o.exhaustions.is_empty(), "conformance: {what}");
        assert_eq!(
            o.end,
            SearchEnd::SpecNotAssertionSafe,
            "conformance: {what}"
        );
        let stats = o.stats.as_ref().expect("conformance: no stats");
        assert_eq!(
            (stats.execs, stats.block),
            (1, 0),
            "conformance: {what}: the aborted execution was blocked (a Prune?)"
        );
        let c = &o.counters;
        assert_partition(c, &what);
        assert_eq!(c.cover_calls, 1, "conformance: {what}: Cover calls");
        // The aborting call, accounted (round 01 m1): root, then `a`'s send,
        // whose probe asserts; no rebuild (the seed is initial and the call
        // ended in `Err`).
        assert_eq!(calls(c), [2], "conformance: {what}: the aborting Cover");
        assert_eq!(
            c.gate_skipped_aborted, 2,
            "conformance: {what}: c's receive gate and the completion gate are inert"
        );
        assert!(
            !path.exists(),
            "conformance: {what}: a trace file was written"
        );
    }
}

/// **Criterion 9, round 04 m2.** After the abort, an Impl visible thread's
/// assertion is recorded as a diagnostic, never a report.
#[test]
fn c09_report_visible_error_is_guarded_after_the_abort() {
    let o = engine(
        cfg(ConsType::FIFO),
        &send_then_assert(true),
        &send_then_assert(true),
        &["a", "c"],
        UNLIMITED,
        opts(InnerOrder::Recorded, false),
    );
    assert!(o.spec_error.is_some(), "conformance: no abort");
    assert!(
        o.reports.is_empty(),
        "conformance: a report after the abort: {:?}",
        o.reports
    );
    assert_eq!(o.end, SearchEnd::SpecNotAssertionSafe);
    assert!(
        o.diagnostics.iter().any(|d| d.thread == "a"
            && matches!(
                d.reason,
                crate::conformance::ctx::DiagnosticReason::AfterPrune
            )),
        "conformance: the Impl assertion was not recorded: {:?}",
        o.diagnostics
    );
}

/// **Criterion 9, fixture 2 (round 03 M1, D-c).** The `RevisitApply` abort
/// on `ex:rebuild`'s encoding: `Err(SpecNotAssertionSafe { "c", .. })`;
/// engine-only `spec_error`, no reports, `end = SpecNotAssertionSafe`, exactly
/// 5 `Cover` calls (the 5th aborted) and none after it.
#[test]
fn c09_the_revisit_apply_abort() {
    for keep_going in [false, true] {
        let what = format!("keep_going={keep_going}");
        let config = Config::builder()
            .with_cons_type(ConsType::Bag)
            .with_seed(0)
            .with_keep_going_after_error(keep_going)
            .build();
        let v = run(
            cc(config.clone(), &["a", "b", "c"])
                .skip_spec_errfree_check(true)
                .unlimited()
                .build()
                .unwrap(),
            &traces(CRecv::Plain),
            &traces(CRecv::AssertOnTwo),
        );
        match &v {
            Err(ConfError::SpecNotAssertionSafe { thread, pos }) => {
                assert_eq!(thread, "c", "conformance: {what}");
                assert!(pos.starts_with("(t"), "conformance: {what}: pos {pos}");
            }
            other => panic!(
                "conformance: {what}: expected the abort, got {}",
                class(other)
            ),
        }
        let o = engine(
            config,
            &traces(CRecv::Plain),
            &traces(CRecv::AssertOnTwo),
            &["a", "b", "c"],
            UNLIMITED,
            opts(InnerOrder::Recorded, false),
        );
        assert_eq!(
            o.spec_error.as_ref().map(|s| s.0.as_str()),
            Some("c"),
            "conformance: {what}"
        );
        assert!(o.reports.is_empty(), "conformance: {what}: reports");
        assert_eq!(
            o.end,
            SearchEnd::SpecNotAssertionSafe,
            "conformance: {what}"
        );
        let c = &o.counters;
        assert_partition(c, &what);
        assert_eq!(c.cover_calls, 5, "conformance: {what}: Cover calls");
        // Execution 1's four `Cover` calls, then the aborting one, now
        // accounted (round 01 m1): a 1-call seed attempt, then a rebuild of 4
        // (root, `{a}`, `{a,b}`, `{a,b,c←b}` whose probe asserts).
        assert_eq!(
            calls(c),
            [2, 2, 2, 1, 5],
            "conformance: {what}: per-Cover calls, the aborting one last"
        );
        assert!(c.per_cover[4].rebuild_taken, "conformance: {what}");
        assert!(
            c.gate_skipped_aborted >= 1,
            "conformance: {what}: no gate was inert after the abort"
        );
    }
}

// =========================================================================
// E. Bug-class tests (criteria 10–12)
// =========================================================================

/// **Criterion 10, §5.1, D10.** The explored complete graphs are exactly two
/// — `{c reads a}` at completion and `{c reads b}` at the `RevisitApply`
/// report, in the cut shape — and the report set is exactly the latter,
/// `GrowingExhaustion` at `RevisitApply`.
#[test]
fn c10_the_deletion_set_keeps_the_revisiting_send() {
    let visible = vis(&["a", "b", "c"]);
    let o = engine(
        cfg(ConsType::Bag),
        &traces(CRecv::Plain),
        &traces(CRecv::OnlyFromA),
        &["a", "b", "c"],
        UNLIMITED,
        opts(InnerOrder::Recorded, false),
    );
    assert!(o.spec_error.is_none());
    assert_eq!(o.reports.len(), 1, "conformance: reports {:?}", o.reports);
    let r = &o.reports[0];
    assert_eq!(ReportGate::of(r.gate), ReportGate::RevisitApply);
    assert_eq!(reads_from(&r.graph, "c").as_deref(), Some("b"));
    // The cut shape: b and c without End, a with it. **main without it**:
    // measured, against criterion 13's caveat ("A's and main's End
    // survive") — main's End is installed after every child has ended, so its
    // stamp exceeds r's and the cut deletes it (report, T-finding T1).
    assert_eq!(
        [
            last_label_kind(&r.graph, "a"),
            last_label_kind(&r.graph, "b"),
            last_label_kind(&r.graph, "c"),
            last_label_kind(&r.graph, "main"),
        ],
        ["end", "send", "recv", "tcreate"],
        "conformance: the RevisitApply graph's shape:\n{}",
        r.graph
    );
    let c = &o.counters;
    assert_partition(c, "c10");
    assert_eq!(calls(c), [2, 2, 2, 1, 6], "conformance: per-Cover calls");
    assert_eq!(c.rebuilds_taken, 1);
    assert_eq!(c.max_paper_events_per_execution, 3, "conformance: L");
    assert_eq!(c.paper_events_at_first_report, Some(3));
    // The explored complete Impl graphs, criterion 13's observable.
    let all = graphs_of(cfg(ConsType::Bag), &visible, traces(CRecv::Plain));
    assert_eq!(all.len(), 2, "conformance: ex:traces has two graphs");
    let reads_a = all
        .iter()
        .find(|g| reads_from(g, "c").as_deref() == Some("a"))
        .expect("conformance: no c-reads-a graph");
    assert_eq!(
        c.explored_complete_keys,
        [counter_key(reads_a, &visible)],
        "conformance: the completion-captured keys"
    );
    assert_eq!(
        c.report_keys,
        [(ReportGate::RevisitApply, counter_key(&r.graph, &visible))],
        "conformance: the report keys"
    );
    let mut union: Vec<String> = c.explored_complete_keys.clone();
    union.extend(c.report_keys.iter().map(|(_, k)| k.clone()));
    union.sort();
    union.dedup();
    assert_eq!(
        union.len(),
        2,
        "conformance: explored complete graphs {union:?}"
    );
    // The cut-shape caveat: the report key is not the completion key of the
    // same paper graph.
    let reads_b = all
        .iter()
        .find(|g| reads_from(g, "c").as_deref() == Some("b"))
        .expect("conformance: no c-reads-b graph");
    assert_ne!(counter_key(reads_b, &visible), c.report_keys[0].1);
}

/// **Criterion 11, §5.2, D11.** The Blocking pair: the receive gate's
/// partial match is `Found`, never coverage; the report is
/// `CompleteCoverage` at `Completion`.
#[test]
fn c11_the_blocking_pair_reports_complete_coverage() {
    let o = engine(
        cfg(ConsType::FIFO),
        &blocking(true),
        &blocking(false),
        &["main", "c"],
        UNLIMITED,
        opts(InnerOrder::Recorded, false),
    );
    assert_eq!(o.reports.len(), 1);
    assert_eq!(ReportGate::of(o.reports[0].gate), ReportGate::Completion);
    let c = &o.counters;
    assert_partition(c, "c11");
    // main's send gate and c's receive gate are Found; completion is not.
    assert_eq!(c.cover_calls, 3, "conformance: Cover calls {c:?}");
    assert_eq!(c.executions, 1);
}

/// **Criterion 12, D12 — `ex:restart` × "drop `ln:rebuild`".** Memo off:
/// `Recorded` takes exactly one rebuild (gate 2), `Reverse` and
/// `Pinned([6,5])` none; all conform.
#[test]
fn c12_ex_restart_takes_one_rebuild_under_recorded() {
    for (ord, rebuilds, per) in [
        (InnerOrder::Recorded, 1, vec![3, 7, 1]),
        (InnerOrder::Pinned(vec![5, 6]), 1, vec![3, 7, 1]),
        (InnerOrder::Reverse, 0, vec![3, 2, 1]),
        (InnerOrder::Pinned(vec![6, 5]), 0, vec![3, 2, 1]),
    ] {
        let o = engine(
            cfg(ConsType::FIFO),
            &restart(false),
            &restart(true),
            &["a", "c"],
            UNLIMITED,
            opts(ord.clone(), false),
        );
        assert!(
            o.reports.is_empty(),
            "conformance: {ord:?}: {:?}",
            o.reports
        );
        assert_partition(&o.counters, &format!("{ord:?}"));
        assert_eq!(o.counters.rebuilds_taken, rebuilds, "conformance: {ord:?}");
        assert_eq!(calls(&o.counters), per, "conformance: {ord:?}");
    }
}

/// **Criterion 12, D12 — `ex:restart-both`** (Impl = Spec =
/// `restart(true)`, `Ltr`, `Pinned([6,5])`, memo off): the outer explores `5`
/// first, the pair conforms, execution 2's first gate rebuilds (the engine
/// carries one `H` across the nondet's forward revisit, as rounds 03–04
/// derived), so two rebuilds in all.
#[test]
fn c12_ex_restart_both_conforms_with_the_opposite_pin() {
    let o = engine(
        cfg(ConsType::FIFO),
        &restart(true),
        &restart(true),
        &["a", "c"],
        UNLIMITED,
        opts(InnerOrder::Pinned(vec![6, 5]), false),
    );
    assert!(o.reports.is_empty(), "conformance: {:?}", o.reports);
    let c = &o.counters;
    assert_partition(c, "restart-both");
    assert_eq!(c.executions, 2, "conformance: two outer executions");
    assert!(
        c.explored_complete_keys[0].contains("Choice { result: 5"),
        "conformance: the outer did not explore 5 first: {}",
        c.explored_complete_keys[0]
    );
    assert!(c.explored_complete_keys[1].contains("Choice { result: 6"));
    assert_eq!(calls(c), [3, 7, 1, 4, 2, 1], "conformance: per-Cover calls");
    assert_eq!(c.rebuilds_taken, 2);
}

/// **Criterion 12, D12 — `ex:rebuild`** conforming (Impl = Spec =
/// `ex:traces`, `a, c, b`, `Ltr`, `Recorded`, memo off): one rebuild, at the
/// `RevisitApply` gate; 6 `Cover` calls, 13 `SpecVisit` calls.
#[test]
fn c12_ex_rebuild_conforms_with_one_rebuild() {
    let o = engine(
        cfg(ConsType::Bag),
        &traces(CRecv::Plain),
        &traces(CRecv::Plain),
        &["a", "b", "c"],
        UNLIMITED,
        opts(InnerOrder::Recorded, false),
    );
    assert!(o.reports.is_empty(), "conformance: {:?}", o.reports);
    assert_eq!(o.end, SearchEnd::StateSpaceExhausted);
    let c = &o.counters;
    assert_partition(c, "ex:rebuild");
    assert_eq!(calls(c), [2, 2, 2, 1, 5, 1], "conformance: per-Cover calls");
    assert!(c.per_cover[4].rebuild_taken);
    assert_eq!(c.rebuilds_taken, 1);
    assert_eq!(c.spec_visit_calls, 13);
    assert_eq!(c.cover_exhaustions, 0);
    assert_eq!(c.executions, 2);
    assert_eq!(c.max_paper_events_per_execution, 3);
    assert_eq!(c.paper_events_at_first_report, None);
    let mut keys = c.explored_complete_keys.clone();
    keys.sort();
    keys.dedup();
    assert_eq!(keys.len(), 2, "conformance: two distinct complete graphs");
    assert!(c.report_keys.is_empty());
}

// =========================================================================
// F. Counters (criteria 13–14)
// =========================================================================

/// **Criterion 13.** Instrumentation off (the default and `run(cc)`'s
/// setting) leaves every key counter at zero while the plain counters still
/// count; `ConfOutcome::counters()` carries them and a wall time.
#[test]
fn c13_key_counters_are_instrumentation_only() {
    let v = naive_visible(3);
    let vr = naive_vis_refs(&v);
    let config = with_selector(cfg(ConsType::Bag), Selector::Reverse);
    let o = engine(
        config.clone(),
        &naive(3, 0, false),
        &naive(3, 1, false),
        &vr,
        UNLIMITED,
        SearchOpts {
            inner_order: InnerOrder::Recorded,
            memo: true,
            instrument: false,
        },
    );
    let c = &o.counters;
    assert_partition(c, "uninstrumented");
    assert_eq!((c.spec_visit_calls, c.memo_hits), (20, 6));
    assert_eq!(c.distinct_keys_run_wide, 0);
    assert!(c.explored_complete_keys.is_empty() && c.report_keys.is_empty());
    assert!(c
        .per_cover
        .iter()
        .all(|p| p.distinct_keys == 0 && p.per_attempt_distinct == [0, 0]));
    let vd = run(
        cc(config, &vr).unlimited().memo(true).build().unwrap(),
        &naive(3, 0, false),
        &naive(3, 1, false),
    );
    let oc = reported(&vd).counters();
    assert_eq!(
        (oc.spec_visit_calls, oc.memo_hits, oc.cover_calls),
        (20, 6, 4)
    );
    assert_eq!(oc.paper_events_at_first_report, Some(4));
}

/// `ndk` of `bench.rs:519` (P3-F63's family), copied: `c` receives `n`
/// times; each sender `s_i` sends `a` or `b` by `nondet()`.
fn ndk(senders: Vec<(u64, u64)>) -> Prog {
    prog(move || {
        let takes = senders.len();
        let c = named("c", move || {
            for _ in 0..takes {
                let _: u64 = crate::recv_msg_block();
            }
        })
        .thread()
        .id();
        for (i, (a, b)) in senders.iter().copied().enumerate() {
            let _ = named(&format!("s{}", i + 1), move || {
                send_msg(c, if crate::nondet() { a } else { b })
            });
        }
    })
}

/// F63's figures for one run: (nodes, Σ per-attempt F63 distinct, Σ
/// per-attempt canonical distinct, run-wide canonical distinct, largest
/// attempt's nodes and its F63 / canonical distinct).
fn f63_figures(o: &Outcome) -> (usize, usize, usize, usize, (usize, usize, usize)) {
    let c = &o.counters;
    let f63: usize = c
        .per_cover
        .iter()
        .map(|p| p.f63_per_attempt_distinct.iter().sum::<usize>())
        .sum();
    let canon: usize = c
        .per_cover
        .iter()
        .map(|p| p.per_attempt_distinct.iter().sum::<usize>())
        .sum();
    let mut largest = (0, 0, 0);
    for p in &c.per_cover {
        for (n, i) in [
            (p.spec_visit_calls_extend, 0),
            (p.spec_visit_calls_rebuild, 1),
        ] {
            if n > largest.0 {
                largest = (n, p.f63_per_attempt_distinct[i], p.per_attempt_distinct[i]);
            }
        }
    }
    (
        c.spec_visit_calls,
        f63,
        canon,
        c.distinct_keys_run_wide,
        largest,
    )
}

fn ndk_engine(imp: Vec<(u64, u64)>, spec: Vec<(u64, u64)>, budget: usize) -> Outcome {
    let (i, s) = (ndk(imp), ndk(spec));
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            engine(
                cfg(ConsType::FIFO),
                &i,
                &s,
                &["c"],
                budget,
                opts(InnerOrder::Recorded, false),
            )
        })
        .expect("conformance: could not spawn the ndk thread")
        .join()
        .expect("conformance: the ndk thread panicked")
}

/// **Criterion 14 (i)–(ii), the cheap half.** `ndk2` conforming under F63's
/// settings (FIFO, seed 0, engine-only, budget 10 000, memo off): no report,
/// no exhaustion; F63's within-attempt definition (nodes over Σ per-attempt
/// input-`Display` distinct) is at least 1, and the canonical per-attempt
/// count never exceeds the `Display` one on this family (the canonical form
/// merges only what the `Display` already merges, plus insertion order).
#[test]
fn c14_f63_definitions_on_ndk2() {
    let o = ndk_engine(vec![(1, 2); 2], vec![(1, 2); 2], 10_000);
    assert!(o.reports.is_empty() && o.exhaustions.is_empty());
    let (nodes, f63, canon, run_wide, _) = f63_figures(&o);
    assert!(nodes >= f63 && f63 > 0, "conformance: {nodes} {f63}");
    assert!(
        canon <= f63,
        "conformance: canonical {canon} > Display {f63}"
    );
    assert!(run_wide <= canon && run_wide > 0);
    // T4 follow-up: F63's across-attempt denominator, the run-wide
    // input-`Display` set, is non-empty and at most the per-attempt sum.
    let f63_run_wide = o.counters.f63_distinct_run_wide;
    assert!(
        f63_run_wide > 0 && f63_run_wide <= f63,
        "conformance: run-wide Display {f63_run_wide} vs per-attempt sum {f63}"
    );
}

/// **Criterion 14, the measurement.** `#[ignore]`d: it runs `ndk3 bad_A` at
/// budget 10 000 (tens of seconds). Writes its figures to the file named by
/// `ENUM_C14_OUT` (a file, not a print: `s5_tests` scans this file).
#[test]
#[ignore]
fn c14_f63_figures_measured() {
    let mut out = String::new();
    for (name, imp, spec) in [
        ("ndk2 conf", vec![(1, 2); 2], vec![(1, 2); 2]),
        ("ndk3 conf", vec![(1, 2); 3], vec![(1, 2); 3]),
        ("ndk3 bad_A", vec![(1, 2); 3], vec![(1, 1), (1, 1), (1, 2)]),
    ] {
        let t = std::time::Instant::now();
        let o = ndk_engine(imp, spec, 10_000);
        let (nodes, f63, canon, run_wide, largest) = f63_figures(&o);
        out.push_str(&format!(
            "{name}: reports={} exh={} covers={} nodes={nodes} sum_f63_attempt={f63} \
             sum_canon_attempt={canon} run_wide_canon={run_wide} within_f63={:.2} \
             within_canon={:.2} across_canon={:.2} largest_attempt=(nodes {}, f63 {}, canon {}) \
             largest_f63={:.2} largest_canon={:.2} per_cover_distinct_sum={} \
             run_wide_f63={} across_f63={:.2} product_f63={:.1} secs={:.1}\n",
            o.reports.len(),
            o.exhaustions.len(),
            o.counters.cover_calls,
            nodes as f64 / f63 as f64,
            nodes as f64 / canon as f64,
            canon as f64 / run_wide as f64,
            largest.0,
            largest.1,
            largest.2,
            largest.0 as f64 / largest.1 as f64,
            largest.0 as f64 / largest.2 as f64,
            o.counters
                .per_cover
                .iter()
                .map(|p| p.distinct_keys)
                .sum::<usize>(),
            o.counters.f63_distinct_run_wide,
            f63 as f64 / o.counters.f63_distinct_run_wide as f64,
            nodes as f64 / o.counters.f63_distinct_run_wide as f64,
            t.elapsed().as_secs_f64(),
        ));
    }
    if let Ok(p) = std::env::var("ENUM_C14_OUT") {
        std::fs::write(p, out).expect("conformance: could not write the figures");
    }
}
