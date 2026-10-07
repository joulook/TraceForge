//! P4-STATEFUL gate 3: the tester's tests for `SVerify`, the stateful checker
//! (criteria `P4-STATEFUL.md` revision 5.1).
//!
//! Every expected value below was derived from the criteria's engine facts
//! T1–T6 and the paper (`alg.tex` §8.1–§8.3 `lem:sig`, `alg:stateful`,
//! `thm:stateful`, `ex:naive`; §8.8; `hit.tex` §11) **before** `stateful.rs`
//! or the diffs were read; the derivations are written out in
//! `plan/traceForge/log/dev/P4-STATEFUL.report.md`, gate-3 Part 0, under the
//! labels `D1`..`D14b` cited on each test. Tests are named by criterion.
//! Expected rendered texts are transcribed from the criteria, not copied from
//! the module's constants.
//!
//! Conventions this file keeps because `s5_tests`' source scans read it: no
//! print macro anywhere, and every panic-family message starts with
//! `conformance:`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::conformance::canon::CanonicalGraph;
use crate::conformance::config::ConfConfig;
use crate::conformance::ctx::Diagnostic;
use crate::conformance::morphism::{matches, statuses, statuses_agree, CompleteExecution};
use crate::conformance::obs::wobs;
use crate::conformance::report::{ConfVerdict, StatefulCounters};
use crate::conformance::selector::Selector;
use crate::conformance::sig::{SigBuckets, Summary, VPos, VisOrder};
use crate::conformance::stateful::{run_with, StatefulOutcome};
use crate::conformance::{
    ConfBuilder, ConfError, ConfNote, ConfOutcome, Diagnostics, Engine, NotACertificate,
    ReplaySnapshot, ReportCause, ReportGate, ReportTag, ScopeField, SearchEnd, SpecErrFreedom,
};
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;
use crate::thread::construct_thread_id;
use crate::{recv_msg_block, send_msg, thread, CommunicationModel, Config, ConsType, Nondet};

type Prog = Arc<dyn Fn() + Send + Sync>;

// =========================================================================
// Harness
// =========================================================================

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

/// A stateful `ConfBuilder`: `engine(Stateful)`, nothing else set.
fn sb(config: Config, visible: &[String]) -> ConfBuilder {
    ConfBuilder::new()
        .config(config)
        .visible_threads(visible.to_vec())
        .engine(Engine::Stateful)
}

fn built(b: ConfBuilder) -> ConfConfig {
    b.build()
        .expect("conformance: the test configuration is in scope")
}

/// The engine-only entry point (criterion 12).
fn rw(cc: &ConfConfig, imp: &Prog, spec: &Prog, keep: bool) -> StatefulOutcome {
    run_with(cc, imp, spec, keep)
}

/// The public path (`conformance::run`, dispatching on the engine).
fn run(cc: ConfConfig, imp: &Prog, spec: &Prog) -> Result<ConfVerdict, ConfError> {
    crate::conformance::run(cc, Arc::clone(imp), Arc::clone(spec))
}

fn class(v: &Result<ConfVerdict, ConfError>) -> String {
    match v {
        Ok(ConfVerdict::Conforms(_)) => "conforms".to_string(),
        Ok(ConfVerdict::Reported(o)) => format!("reported:{}", o.reports().len()),
        Ok(ConfVerdict::Inconclusive(_)) => "inconclusive".to_string(),
        Err(e) => format!("error:{e:?}"),
    }
}

fn outcome(v: &Result<ConfVerdict, ConfError>) -> &ConfOutcome {
    match v {
        Ok(ConfVerdict::Conforms(c)) => c.outcome(),
        Ok(ConfVerdict::Reported(o)) | Ok(ConfVerdict::Inconclusive(o)) => o,
        Err(e) => panic!("conformance: expected a verdict, got {e:?}"),
    }
}

/// The full canonical form (values included): plan §6's report key.
fn full_key(g: &ExecutionGraph, visible: &[String]) -> String {
    match CanonicalGraph::of(g, visible) {
        Ok(c) => format!("{c:?}"),
        Err(e) => format!("ERR {e:?}"),
    }
}

fn sorted(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v
}

fn report_keys(o: &StatefulOutcome, visible: &[String]) -> Vec<String> {
    sorted(
        o.reports
            .iter()
            .map(|(g, _)| full_key(g, visible))
            .collect(),
    )
}

fn label_count(g: &ExecutionGraph) -> usize {
    g.thread_ids().into_iter().map(|t| g.thread_size(t)).sum()
}

fn summary(g: &ExecutionGraph, v: &[String]) -> Summary {
    let w = wobs(g, v).expect("conformance: wobs on a fixture graph");
    Summary::of(CompleteExecution::assume_finished_at_gate(g), &w, v)
        .expect("conformance: summary on a fixture graph")
}

/// The slot of `g`'s signature in `index`.
fn slot<'a>(
    index: &'a SigBuckets<BTreeSet<VisOrder>>,
    g: &ExecutionGraph,
    v: &[String],
) -> Option<&'a BTreeSet<VisOrder>> {
    index.get(&summary(g, v).sig)
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

fn ev(t: u32, i: u32) -> Event {
    Event::new(construct_thread_id(t), i)
}

/// The counters as a comparable row (criterion 8's fields, wall times out).
fn row(c: &StatefulCounters) -> [usize; 12] {
    [
        c.spec_graphs,
        c.impl_graphs,
        c.sig_key_buckets,
        c.signatures,
        c.orders_held,
        c.lookups,
        c.lookups_signature_miss,
        c.lookups_containment_tested,
        c.lookups_succeeded,
        c.lookups_failed_after_tests,
        c.containment_tests,
        c.reports,
    ]
}

/// Criterion 8's identities, and the structural facts every completed
/// (unbounded, unstopped) run must satisfy (D1).
fn assert_identities(o: &StatefulOutcome, what: &str) {
    let c = &o.counters;
    assert_eq!(
        c.lookups,
        c.lookups_signature_miss + c.lookups_containment_tested,
        "conformance: {what}: lookups = sig_miss + tested: {c:?}"
    );
    assert_eq!(
        c.lookups_containment_tested,
        c.lookups_succeeded + c.lookups_failed_after_tests,
        "conformance: {what}: tested = succeeded + failed: {c:?}"
    );
    assert_eq!(
        c.reports,
        c.lookups_signature_miss + c.lookups_failed_after_tests,
        "conformance: {what}: reports = sig_miss + failed: {c:?}"
    );
    assert!(
        c.containment_tests >= c.lookups_containment_tested,
        "conformance: {what}: tests >= tested: {c:?}"
    );
    assert_eq!(
        c.reports,
        o.reports.len(),
        "conformance: {what}: the counter vs the list"
    );
    assert_eq!(
        c.lookups, c.impl_graphs,
        "conformance: {what}: one lookup per Impl completion"
    );
    assert_eq!(
        c.signatures,
        o.index.len(),
        "conformance: {what}: signatures = SigBuckets::len"
    );
    assert_eq!(
        c.sig_key_buckets,
        o.index.key_buckets(),
        "conformance: {what}: key buckets"
    );
    assert!(
        c.sig_key_buckets <= c.signatures && c.signatures <= c.orders_held,
        "conformance: {what}: buckets <= slots <= orders: {c:?}"
    );
    assert!(
        c.orders_held <= c.spec_graphs,
        "conformance: {what}: orders after dedup <= Spec graphs: {c:?}"
    );
    assert_eq!(
        o.executions, c.impl_graphs,
        "conformance: {what}: executions = Impl completions"
    );
}

fn assert_counts(c: &StatefulCounters, expected: [usize; 12], what: &str) {
    assert_eq!(
        row(c),
        expected,
        "conformance: {what}: [spec, impl, key_buckets, sigs, orders, lookups, sig_miss, \
         tested, succeeded, failed_after, tests, reports]"
    );
}

/// The panic payload's message, if any.
fn panic_text(r: std::thread::Result<impl Sized>) -> Option<String> {
    match r {
        Ok(_) => None,
        Err(p) => Some(
            p.downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_else(|| "<non-string payload>".to_string()),
        ),
    }
}

// =========================================================================
// Texts, transcribed from the criteria (T4, T6) and the pre-existing engine
// =========================================================================

const T6_EACH_UNCOVERED: &str = "Every graph in this list is an uncovered complete graph of the \
     implementation: each was looked up in an index of every specification graph, and either no \
     specification graph has its signature or no order stored under its signature is contained \
     in its own (lem:sig).";

const T6_EXACTLY: &str = "The list is exactly the set of such graphs (thm:stateful): both \
     enumerations reached the end of their state spaces.";

const T6_CONFORMS_LINE: &str = "conformance: silence. Every complete graph of the \
     implementation is covered by one of the specification (thm:stateful), and both \
     enumerations reached the end of their state spaces.";

const T6_CERTIFIES_STATEFUL: &str = "no graph of the specification covers the reported \
     complete graph: its signature has no slot in the index, or no order in the slot is \
     contained in the graph's (lem:sig, thm:stateful)";

const T6_NOT_PRODUCED: &str = "the stateful engine computes no inner-search diagnostics; \
     this report is a failed signature or containment lookup (lem:sig)";

const T6_NOT_PRODUCED_MISMATCH: &str =
    "not produced: the stateful engine computes no inner-search diagnostics";

const T4_TAIL: &str = "Either fix the specification, or — on the enumerator — accept the \
     assumption with `ConfBuilder::skip_spec_errfree_check(true)`, which records it in the \
     verdict. Under `Engine::CompleteFirst` that flag skips only the precheck: a sweep that \
     meets a specification assertion failure still aborts the run. Under `Engine::Gated`, as \
     under `CompleteFirst`. Under `Engine::Stateful` it has no effect and the only remedy is \
     fixing the specification.";

/// T4's `detail` body after its leading article.
fn t4_detail(visibility: &str, thread: &str, pos: &str) -> String {
    format!(
        "{visibility} thread `{thread}` failed an assertion at {pos} during the stateful \
         engine's enumeration of the specification (its index run, which replaces the §5.4 \
         precheck)"
    )
}

// The enumerator's texts that the stateful arm must not print (as rendered in
// the pre-gate-2 baseline, `stateful_baseline.rs`).
const ENUM_SETTLED: &str = "What this report establishes (Lemma gate";
const ENUM_UNSETTLED: &str = "What this report does not establish";
const ENUM_NOT_COMPLETE: &str = "This list is not a complete set of violations";
const ENUM_SILENCE_LINE: &str = "conformance: silence. No candidate violation, no exhausted \
     search budget, and the outer loop reached the end of its state space.";
const RESIDUAL: &str = "\"Candidate\" has two named sources: (i) single-cover is sufficient \
     but not necessary for trace inclusion, so a union of specification graphs may still cover \
     these traces; (ii) the lemmas this rests on carry the open A4 transport gap.";
const ONLY_SILENCE: &str = "Only silence is a verdict: a run that produced no report, hit no \
     search budget and reached the end of its state space is the certificate, and nothing \
     else is.";
const TRIAGE_CAVEAT: &str = "triage is off (the default)";
const TRUNC_CONFIG: &str = "**This list is truncated by configuration.** \
     `stop_at_first_report` was set, so the outer loop stopped at the report below and looked \
     for no others. There may be more; this run did not ask.";

fn trunc_bound(n: u64) -> String {
    format!(
        "**This list is truncated by a bound you set.** `Config::max_iterations` was {n}, so \
         the outer loop stopped after counting that many endings rather than after seeing them \
         all. There may be more reports; this run did not look."
    )
}

// =========================================================================
// Fixtures
// =========================================================================

/// `ex:naive` encoding 1 (`P4-SELECTOR` criterion 6's first): `main`
/// (undeclared) creates `c`'s and `a`'s mailboxes as channels, then spawns
/// `c, b1..bk, a`. `c` sends `v` to `a`, then receives `k` times; each `b_i`
/// sends `1` to `c`; `a` skips.
fn naive(k: usize, v: i32) -> Prog {
    prog(move || {
        let (tx_a, _rx_a) = chan();
        let (tx_c, rx_c) = chan();
        let _c = named("c", move || {
            tx_a.send_msg(v);
            for _ in 0..k {
                let _x: i32 = rx_c.recv_msg_block();
            }
        });
        for i in 1..=k {
            let t = tx_c.clone();
            let _b = named(&format!("b{i}"), move || t.send_msg(1));
        }
        let _a = named("a", || {});
    })
}

fn naive_visible(k: usize) -> Vec<String> {
    let mut v = vec!["a".to_string(), "c".to_string()];
    v.extend((1..=k).map(|i| format!("b{i}")));
    v
}

/// `ex:restart` (p2p): `main` spawns `c` (skip) then `a`; Impl `a: send(c,1);
/// send(c,6)`; Spec draws `n` from `5..=6`.
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

/// The Blocking pair: `c` receives twice (Impl) or once (Spec); `main` sends 1.
fn blocking(twice: bool) -> Prog {
    prog(move || {
        let c = named("c", move || {
            let _v: i32 = recv_msg_block();
            if twice {
                let _w: i32 = recv_msg_block();
            }
        });
        send_msg(c.thread().id(), 1i32);
    })
}

/// Plan §6's oracle regression: `w: assert(false)` against `w: skip`.
fn visible_error(fails: bool) -> Prog {
    prog(move || {
        let _w = named("w", move || {
            if fails {
                crate::assert(false);
            }
        });
    })
}

/// Criterion 7's Spec: `a: send(C,1) ‖ b: send(C,1) ‖ c: recv(); recv()`, one
/// channel.
fn c7_spec() -> Prog {
    prog(|| {
        let (tx, rx) = chan();
        let _c = named("c", move || {
            let _x: i32 = rx.recv_msg_block();
            let _y: i32 = rx.recv_msg_block();
        });
        let ta = tx.clone();
        let _a = named("a", move || ta.send_msg(1));
        let _b = named("b", move || tx.send_msg(1));
    })
}

/// Criterion 7's Impl: two channels; `c` receives from `a`'s first when
/// `a_first`, else from `b`'s first.
fn c7_impl(a_first: bool) -> Prog {
    prog(move || {
        let (tx_a, rx_a) = chan();
        let (tx_b, rx_b) = chan();
        let _c = named("c", move || {
            if a_first {
                let _x: i32 = rx_a.recv_msg_block();
                let _y: i32 = rx_b.recv_msg_block();
            } else {
                let _x: i32 = rx_b.recv_msg_block();
                let _y: i32 = rx_a.recv_msg_block();
            }
        });
        let _a = named("a", move || tx_a.send_msg(1));
        let _b = named("b", move || tx_b.send_msg(1));
    })
}

/// `P4-APPARATUS` criterion 6's clause (2) Spec: `b: send(a,1) ‖ a: recv()`.
fn c2_spec() -> Prog {
    prog(|| {
        let a = named("a", || {
            let _x: i32 = recv_msg_block();
        });
        let aid = a.thread().id();
        let _b = named("b", move || send_msg(aid, 1i32));
    })
}

/// Clause (2) Impl: `b: send(x,1) ‖ x(inv): recv() ‖ d(inv): send(a,1) ‖ a: recv()`.
fn c2_impl() -> Prog {
    prog(|| {
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
    })
}

/// `ex:cone`'s Spec: `a: send(c,9) ‖ c: recv()`.
fn ex_cone_spec() -> Prog {
    prog(|| {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, 9i32));
    })
}

/// The relay: `a: send(r,9) ‖ r(inv): y := recv(); send(c,y) ‖ c: recv()`.
fn relay_spec() -> Prog {
    prog(|| {
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
    })
}

/// `a: send(c,v) ‖ c: recv()`.
fn direct_of<T>(v: T) -> Prog
where
    T: crate::msg::Message + Clone + PartialEq + std::fmt::Debug + Sync + 'static,
{
    prog(move || {
        let c = named("c", || {
            let _x: T = recv_msg_block();
        });
        let cid = c.thread().id();
        let v = v.clone();
        let _a = named("a", move || send_msg(cid, v));
    })
}

/// `a: send(c,va) ‖ b: send(c,vb) ‖ c: x := recv()`.
fn two_senders<T>(va: T, vb: T) -> Prog
where
    T: crate::msg::Message + Clone + PartialEq + std::fmt::Debug + Sync + 'static,
{
    prog(move || {
        let c = named("c", || {
            let _x: T = recv_msg_block();
        });
        let cid = c.thread().id();
        let va = va.clone();
        let vb = vb.clone();
        let _a = named("a", move || send_msg(cid, va));
        let _b = named("b", move || send_msg(cid, vb));
    })
}

/// D3 (invisible): `main` spawns `v` (visible, skip) then `w` (invisible),
/// which fails an assertion first when `asserts`.
fn inv_assert(asserts: bool) -> Prog {
    prog(move || {
        let _v = named("v", || {});
        let _w = named("w", move || {
            if asserts {
                crate::assert(false);
            }
        });
    })
}

/// D3 (both): `main` spawns `w` (invisible, asserts) then `v` (visible,
/// asserts) — the invisible failure is installed first under `Ltr`.
fn both_assert() -> Prog {
    prog(|| {
        let _w = named("w", || crate::assert(false));
        let _v = named("v", || crate::assert(false));
    })
}

/// D3 (revisit, Spec side): `v` visible skip; invisible `w` receives once
/// from a channel two invisible senders (`s1` sends 1, `s2` sends 2) write;
/// `w` fails on 2 — only in the execution the revisit produces.
fn inv_assert_on_revisit(asserts: bool) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let _v = named("v", || {});
        let _w = named("w", move || {
            let x: i32 = rx.recv_msg_block();
            if asserts && x == 2 {
                crate::assert(false);
            }
        });
        let t1 = tx.clone();
        let _s1 = named("s1", move || t1.send_msg(1));
        let _s2 = named("s2", move || tx.send_msg(2));
    })
}

/// The shape `ctx.rs`'s gate comment worries about: an invisible `w` fails
/// an assertion **before** a visible receive is revisited, so its
/// `Block(Assert)` survives `revisit_view` into the next execution. `main`
/// spawns `w, c, a, b`; `a` sends 1 and `b` sends 2 to `c`'s mailbox; `c`
/// receives once. Visible: `a, b, c`.
fn inv_block_before_revisit(asserts: bool) -> Prog {
    prog(move || {
        let _w = named("w", move || {
            if asserts {
                crate::assert(false);
            }
        });
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, 1i32));
        let _b = named("b", move || send_msg(cid, 2i32));
    })
}

/// Round 02 m3(b): `main` spawns the four threads in `order`; `w` (invisible)
/// fails an assertion when `asserts`; `c` receives once from one `NoOrder`
/// channel on which `a` sends 1 and `b` sends 2. Visible: `a, b, c`.
fn race_on_channel(order: [&'static str; 4], asserts: bool) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let mut rx = Some(rx);
        for n in order {
            match n {
                "w" => {
                    let _w = named("w", move || {
                        if asserts {
                            crate::assert(false);
                        }
                    });
                }
                "c" => {
                    let rx = rx.take().expect("conformance: c spawned twice");
                    let _c = named("c", move || {
                        let _x: i32 = rx.recv_msg_block();
                    });
                }
                "a" | "b" => {
                    let t = tx.clone();
                    let v = if n == "a" { 1 } else { 2 };
                    let _s = named(n, move || t.send_msg(v));
                }
                other => panic!("conformance: unknown thread {other}"),
            }
        }
    })
}

/// A per-channel `TotalOrder` (mailbox) channel, sent on.
fn total_order_channel() -> Prog {
    prog(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new()
            .with_comm(CommunicationModel::TotalOrder)
            .build();
        let _w = named("w", move || tx.send_msg(1));
    })
}

// --- the corpus of criteria 4 and 13 ------------------------------------------

/// `ex:traces` with thread mailboxes: `a` sends 1, `b` sends 2, `c` receives.
fn traces_prog(c_assumes_one: bool) -> Prog {
    prog(move || {
        let c = named("c", move || {
            let x: i32 = recv_msg_block();
            if c_assumes_one {
                crate::assume!(x == 1);
            }
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, 1i32));
        let _b = named("b", move || send_msg(cid, 2i32));
    })
}

fn pe_p2_relay() -> Prog {
    prog(|| {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let r = named("r", move || {
            let v: i32 = recv_msg_block();
            send_msg(cid, v);
        });
        send_msg(r.thread().id(), 1i32);
    })
}

fn pe_p1_direct(v: i32) -> Prog {
    prog(move || {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), v);
    })
}

fn pe_sends_ordered_by_join() -> Prog {
    prog(|| {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let a = named("a", move || send_msg(cid, 1i32));
        let _b = named("b", move || {
            a.join().unwrap();
            send_msg(cid, 2i32);
        });
    })
}

/// `P4-SELECTOR`'s nested shape: `p1` spawns `x`, `p2` spawns `y`; all send
/// to a sink.
fn nested4() -> Prog {
    prog(|| {
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
    })
}

/// `P4-SELECTOR`'s criterion-3 program: spawn order `r1, r2, s`; `main` joins.
fn c3_prog() -> Prog {
    prog(|| {
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
    })
}

struct Pair {
    name: String,
    config: Config,
    visible: Vec<String>,
    imp: Prog,
    spec: Prog,
}

fn pr(name: &str, config: Config, visible: Vec<String>, imp: Prog, spec: Prog) -> Pair {
    Pair {
        name: name.to_string(),
        config,
        visible,
        imp,
        spec,
    }
}

/// Admissible pairs only (A9 excluded: no NaN anywhere; `i32`/`u64` values;
/// thread mailboxes or unnamed channels; the generator's own exclusions).
fn corpus() -> Vec<Pair> {
    let mut out = Vec::new();
    let mc = vis(&["main", "c"]);
    let abc = vis(&["a", "b", "c"]);
    for (m, model) in [
        ("bag", ConsType::Bag),
        ("fifo", ConsType::FIFO),
        ("cd", ConsType::Causal),
    ] {
        let c = || cfg(model);
        out.push(pr(
            &format!("relay/direct/{m}"),
            c(),
            mc.clone(),
            pe_p2_relay(),
            pe_p1_direct(1),
        ));
        out.push(pr(
            &format!("direct/relay/{m}"),
            c(),
            mc.clone(),
            pe_p1_direct(1),
            pe_p2_relay(),
        ));
        out.push(pr(
            &format!("relay/two/{m}"),
            c(),
            mc.clone(),
            pe_p2_relay(),
            pe_p1_direct(2),
        ));
        out.push(pr(
            &format!("blocking/{m}"),
            c(),
            mc.clone(),
            blocking(true),
            blocking(false),
        ));
        out.push(pr(
            &format!("blocking/rev/{m}"),
            c(),
            mc.clone(),
            blocking(false),
            blocking(true),
        ));
        out.push(pr(
            &format!("verr/{m}"),
            c(),
            vis(&["w"]),
            visible_error(true),
            visible_error(false),
        ));
        out.push(pr(
            &format!("traces/self/{m}"),
            c(),
            abc.clone(),
            traces_prog(false),
            traces_prog(false),
        ));
        out.push(pr(
            &format!("traces/assume/{m}"),
            c(),
            abc.clone(),
            traces_prog(false),
            traces_prog(true),
        ));
        out.push(pr(
            &format!("traces/joined/{m}"),
            c(),
            abc.clone(),
            traces_prog(false),
            pe_sends_ordered_by_join(),
        ));
        out.push(pr(
            &format!("joined/traces/{m}"),
            c(),
            abc.clone(),
            pe_sends_ordered_by_join(),
            traces_prog(false),
        ));
        out.push(pr(
            &format!("c7/a/{m}"),
            c(),
            abc.clone(),
            c7_impl(true),
            c7_spec(),
        ));
        out.push(pr(
            &format!("c7/b/{m}"),
            c(),
            abc.clone(),
            c7_impl(false),
            c7_spec(),
        ));
        out.push(pr(
            &format!("c7/rev/{m}"),
            c(),
            abc.clone(),
            c7_spec(),
            c7_impl(true),
        ));
        out.push(pr(
            &format!("clause2/{m}"),
            c(),
            vis(&["a", "b"]),
            c2_impl(),
            c2_spec(),
        ));
        out.push(pr(
            &format!("clause2/mirror/{m}"),
            c(),
            vis(&["a", "b"]),
            c2_spec(),
            c2_impl(),
        ));
        out.push(pr(
            &format!("cone/relay/{m}"),
            c(),
            vis(&["a", "c"]),
            relay_spec(),
            ex_cone_spec(),
        ));
        out.push(pr(
            &format!("cone/self/{m}"),
            c(),
            vis(&["a", "c"]),
            ex_cone_spec(),
            ex_cone_spec(),
        ));
        out.push(pr(
            &format!("two/12-11/{m}"),
            c(),
            abc.clone(),
            two_senders(1i32, 2i32),
            two_senders(1i32, 1i32),
        ));
        out.push(pr(
            &format!("inv-block-revisit/{m}"),
            c(),
            abc.clone(),
            inv_block_before_revisit(false),
            inv_block_before_revisit(false),
        ));
    }
    for k in [2usize, 3] {
        out.push(pr(
            &format!("naive{k}/impl-spec"),
            cfg(ConsType::Bag),
            naive_visible(k),
            naive(k, 0),
            naive(k, 1),
        ));
        out.push(pr(
            &format!("naive{k}/spec-spec"),
            cfg(ConsType::Bag),
            naive_visible(k),
            naive(k, 1),
            naive(k, 1),
        ));
        out.push(pr(
            &format!("naive{k}/spec-impl"),
            cfg(ConsType::Bag),
            naive_visible(k),
            naive(k, 1),
            naive(k, 0),
        ));
    }
    out.push(pr(
        "inv-nondet/self",
        cfg(ConsType::Bag),
        vis(&["v"]),
        inv_assert_on_revisit(false),
        inv_assert_on_revisit(false),
    ));
    out.push(pr(
        "restart",
        cfg(ConsType::FIFO),
        vis(&["a", "c"]),
        restart(false),
        restart(true),
    ));
    out.push(pr(
        "restart/rev",
        cfg(ConsType::FIFO),
        vis(&["a", "c"]),
        restart(true),
        restart(false),
    ));
    out.push(pr(
        "restart/both",
        cfg(ConsType::FIFO),
        vis(&["a", "c"]),
        restart(true),
        restart(true),
    ));
    out.push(pr(
        "c3/self",
        cfg(ConsType::Bag),
        vis(&["r1", "r2", "s"]),
        c3_prog(),
        c3_prog(),
    ));
    out.push(pr(
        "nested4/self",
        cfg(ConsType::Bag),
        vis(&["p1", "p2"]),
        nested4(),
        nested4(),
    ));
    for (seed, per_mode) in [(0x5EEDu64, 1usize), (0xE7E7_0004, 2)] {
        for p in crate::conformance::generator::corpus(seed, per_mode) {
            out.push(Pair {
                name: format!("gen:{seed:x}:{:?}:{}", p.mode, p.seed),
                config: p.config.clone(),
                visible: p.visible.clone(),
                imp: p.implementation.clone(),
                spec: p.specification.clone(),
            });
        }
    }
    out
}

// =========================================================================
// Criteria 1 and 8 — the two loops, the lookup, the identities
// =========================================================================

/// **Criteria 1 and 8 (D1).** On every corpus pair and every named fixture:
/// the identities hold, one lookup per Impl completion, the kept families
/// match the counters, and the public path runs no inner search (every
/// enumerator counter but the three T6 names is zero).
#[test]
fn c01_c08_identities_on_every_fixture() {
    let mut fixtures = corpus();
    let v_naive = naive_visible(3);
    fixtures.push(pr(
        "naive3/bag",
        cfg(ConsType::Bag),
        v_naive,
        naive(3, 0),
        naive(3, 1),
    ));
    fixtures.push(pr(
        "nan/a9",
        cfg(ConsType::Bag),
        vis(&["a", "c"]),
        direct_of(f64::NAN),
        direct_of(f64::NAN),
    ));
    fixtures.push(pr(
        "nan/two",
        cfg(ConsType::Bag),
        vis(&["a", "b", "c"]),
        two_senders(f64::NAN, f64::NAN),
        two_senders(f64::NAN, f64::NAN),
    ));
    let mut runs = 0;
    for p in fixtures {
        let cc = built(sb(p.config.clone(), &p.visible));
        let o = rw(&cc, &p.imp, &p.spec, true);
        assert!(
            o.spec_errors.is_empty(),
            "conformance: {}: spec errors",
            p.name
        );
        assert_eq!(
            o.spec_end,
            SearchEnd::StateSpaceExhausted,
            "conformance: {}",
            p.name
        );
        assert_eq!(
            o.impl_end,
            SearchEnd::StateSpaceExhausted,
            "conformance: {}",
            p.name
        );
        assert_identities(&o, &p.name);
        assert_eq!(
            o.kept_impl_graphs.len(),
            o.counters.impl_graphs,
            "conformance: {}: kept Impl graphs",
            p.name
        );
        assert_eq!(
            o.kept_spec_graphs.len(),
            o.counters.spec_graphs,
            "conformance: {}: kept Spec graphs",
            p.name
        );
        // The index is exactly the Spec family's summaries (the first loop).
        // A9 (criterion 10): a NaN slot is never found again — checked there.
        let a9 = p.name.starts_with("nan/");
        let mut expect: BTreeMap<String, BTreeSet<VisOrder>> = BTreeMap::new();
        for g in o.kept_spec_graphs.iter().filter(|_| !a9) {
            let s = summary(g, &p.visible);
            let slot = slot(&o.index, g, &p.visible)
                .unwrap_or_else(|| panic!("conformance: {}: a Spec graph has no slot", p.name));
            assert!(
                slot.contains(&s.ord),
                "conformance: {}: a Spec order is missing from its slot",
                p.name
            );
            expect
                .entry(format!("{:?}", s.sig))
                .or_default()
                .insert(s.ord);
        }
        if !a9 {
            let held: usize = expect.values().map(BTreeSet::len).sum();
            assert_eq!(
                held, o.counters.orders_held,
                "conformance: {}: orders_held",
                p.name
            );
            assert_eq!(
                expect.len(),
                o.counters.signatures,
                "conformance: {}: slots",
                p.name
            );
        }
        // The public path: no inner search, no `Cover`, no gate counters.
        let v = run(cc, &p.imp, &p.spec);
        let out = outcome(&v);
        assert_eq!(out.engine(), Engine::Stateful, "conformance: {}", p.name);
        let sc = out
            .stateful_counters()
            .unwrap_or_else(|| panic!("conformance: {}: no stateful counters", p.name));
        assert_eq!(
            row(sc),
            row(&o.counters),
            "conformance: {}: run vs run_with",
            p.name
        );
        let c = out.counters();
        assert_eq!(
            (
                c.cover_calls,
                c.spec_visit_calls,
                c.memo_hits,
                c.gate_invocations
            ),
            (0, 0, 0, 0),
            "conformance: {}: an inner search ran",
            p.name
        );
        assert!(c.per_cover.is_empty() && c.explored_complete_keys.is_empty());
        assert_eq!(
            c.executions, sc.impl_graphs,
            "conformance: {}: executions",
            p.name
        );
        assert!(out.exhaustions().is_empty(), "conformance: {}", p.name);
        // Gate-4 round 01 n3 (D-n3): the stateful engine never exhausts a
        // budget, so `inconclusive()` is false on every outcome.
        assert!(
            !out.inconclusive(),
            "conformance: {}: inconclusive()",
            p.name
        );
        assert_eq!(out.spec_err_freedom(), SpecErrFreedom::Checked);
        runs += 1;
    }
    assert!(runs >= 80, "conformance: only {runs} fixtures");
}

// =========================================================================
// Criterion 2 — admissible inputs, the bound on Impl only
// =========================================================================

/// **Criterion 2 (D2).** `ex:naive` `k = 3`, `max_iterations = 2`: the Spec
/// enumeration is complete (6 graphs, 6 orders, exhausted), the Impl stream
/// stops after 2 completions with `MaxIterations(2)`, 2 reports among the
/// unbounded run's 6, a `BoundedRun` non-certificate, and the truncated
/// rendering.
#[test]
fn c02_max_iterations_bounds_the_impl_run_only() {
    let v = naive_visible(3);
    let bounded = Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .with_max_iterations(2)
        .build();
    let cc = built(sb(bounded, &v));
    let o = rw(&cc, &naive(3, 0), &naive(3, 1), false);
    assert_eq!(
        o.spec_end,
        SearchEnd::StateSpaceExhausted,
        "conformance: Spec end"
    );
    assert_eq!(
        o.impl_end,
        SearchEnd::MaxIterations(2),
        "conformance: Impl end"
    );
    assert_counts(&o.counters, [6, 2, 1, 1, 6, 2, 2, 0, 0, 0, 0, 2], "bounded");
    assert_eq!(
        o.max_paper_events, 7,
        "conformance: L = 2k+1 events of Impl_3"
    );

    let un = rw(
        &built(sb(cfg(ConsType::Bag), &v)),
        &naive(3, 0),
        &naive(3, 1),
        false,
    );
    assert_counts(
        &un.counters,
        [6, 6, 1, 1, 6, 6, 6, 0, 0, 0, 0, 6],
        "unbounded",
    );
    assert_eq!(
        (o.counters.spec_graphs, o.counters.orders_held),
        (un.counters.spec_graphs, un.counters.orders_held),
        "conformance: the Spec side is the unbounded run's"
    );
    let all: BTreeSet<String> = report_keys(&un, &v).into_iter().collect();
    for k in report_keys(&o, &v) {
        assert!(
            all.contains(&k),
            "conformance: a bounded report not in the unbounded set"
        );
    }
    assert_eq!(report_keys(&o, &v).len(), 2);

    let verdict = run(cc, &naive(3, 0), &naive(3, 1));
    match &verdict {
        Ok(ConfVerdict::Reported(out)) => {
            assert_eq!(out.end(), SearchEnd::MaxIterations(2));
            assert!(out
                .not_a_certificate()
                .contains(&NotACertificate::BoundedRun { max_iterations: 2 }));
            let s = format!("{}", verdict.as_ref().unwrap());
            assert!(
                s.contains(T6_EACH_UNCOVERED),
                "conformance: always-true sentence: {s}"
            );
            assert!(
                !s.contains(T6_EXACTLY),
                "conformance: exactly-the-set on a bounded run: {s}"
            );
            assert!(
                s.contains(&trunc_bound(2)),
                "conformance: truncation text: {s}"
            );
        }
        other => panic!("conformance: expected Reported, got {}", class(other)),
    }
}

/// **Criterion 2.** `mbox` is refused at `build` under the stateful engine.
#[test]
fn c02_mailbox_is_refused_at_build() {
    let e = sb(cfg(ConsType::Mailbox), &vis(&["w"]))
        .build()
        .err()
        .expect("conformance: a Mailbox configuration was accepted");
    assert_eq!(e.field(), ScopeField::ConsType);
}

/// **Criterion 2 / T2.** A per-channel `TotalOrder` is refused at runtime by a
/// panic that names **this** engine ("stateful"), on either side, sent from a
/// spawned thread or from `main`.
#[test]
fn c02_a_total_order_channel_panics_naming_the_stateful_engine() {
    let v = vis(&["w"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let on_main = prog(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new()
            .with_comm(CommunicationModel::TotalOrder)
            .build();
        let _w = named("w", || {});
        tx.send_msg(1);
    });
    for (side, imp, spec) in [
        ("spec", visible_error(false), total_order_channel()),
        ("impl", total_order_channel(), visible_error(false)),
        ("spec/main", visible_error(false), on_main.clone()),
        ("impl/main", on_main.clone(), visible_error(false)),
    ] {
        let payload = panic_text(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || {
                rw(&cc, &imp, &spec, false);
            },
        )))
        .unwrap_or_else(|| panic!("conformance: {side}: a TotalOrder channel ran"));
        // A model thread's panic is re-raised by the runtime as "A panic was
        // detected\noriginal panic: <message>"; read the original from the
        // payload (no global hook, so no race with parallel tests).
        let original = payload
            .split("original panic: ")
            .nth(1)
            .unwrap_or(payload.as_str());
        assert!(
            original.starts_with(
                "stateful: `a TotalOrder (mailbox) send` is outside conformance scope"
            ),
            "conformance: {side}: no refusal naming the stateful engine: {payload:?}"
        );
    }
}

// =========================================================================
// Criterion 3 — the index run is the precheck
// =========================================================================

fn spec_not_error_free(v: &Result<ConfVerdict, ConfError>) -> String {
    match v {
        Err(ConfError::SpecNotErrorFree { detail }) => detail.clone(),
        other => panic!(
            "conformance: expected SpecNotErrorFree, got {}",
            class(other)
        ),
    }
}

/// **Criterion 3 (D3).** An invisible and a visible Spec assertion failure:
/// under both `skip_spec_errfree_check` settings, `run` returns
/// `SpecNotErrorFree` naming the thread and position in the engine's own
/// words, and the Impl side never ran.
#[test]
fn c03_spec_assertion_safety_is_the_index_run() {
    /// (case, Spec, Tvis, visibility word, thread, position, visible).
    type Case<'a> = (&'a str, Prog, Vec<String>, &'a str, &'a str, Event, bool);
    let cases: [Case; 2] = [
        (
            "invisible",
            inv_assert(true),
            vis(&["v"]),
            "invisible",
            "w",
            ev(2, 1),
            false,
        ),
        (
            "visible",
            visible_error(true),
            vis(&["w"]),
            "visible",
            "w",
            ev(1, 1),
            true,
        ),
    ];
    for (what, spec, v, visibility, thread, pos, visible) in cases {
        let imp = if visible {
            visible_error(false)
        } else {
            inv_assert(false)
        };
        for skip in [false, true] {
            let cc = built(sb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(skip));
            let o = rw(&cc, &imp, &spec, true);
            assert_eq!(
                o.spec_errors,
                vec![(thread.to_string(), pos, visible)],
                "conformance: {what}/{skip}: spec_errors"
            );
            assert_eq!(
                o.counters.impl_graphs, 0,
                "conformance: {what}/{skip}: Impl ran"
            );
            assert_eq!(
                o.impl_end,
                SearchEnd::Unknown,
                "conformance: {what}/{skip}: impl_end"
            );
            assert!(
                o.reports.is_empty() && o.kept_impl_graphs.is_empty() && o.impl_notes.is_empty()
            );
            assert_eq!(o.counters.lookups, 0);
            assert_eq!(o.spec_end, SearchEnd::StateSpaceExhausted);
            assert_eq!(
                o.counters.spec_graphs, 1,
                "conformance: {what}: the Spec has one graph"
            );

            let r = run(cc, &imp, &spec);
            let detail = spec_not_error_free(&r);
            let body = t4_detail(visibility, thread, &pos.to_string());
            assert!(
                detail.contains(&body),
                "conformance: {what}/{skip}: detail {detail:?} lacks {body:?}"
            );
            assert!(
                !detail.contains("precheck run of the specification"),
                "conformance: {what}/{skip}: the precheck answered, not the index run: {detail}"
            );
            let shown = format!("{}", r.unwrap_err());
            assert!(
                shown.contains(T4_TAIL),
                "conformance: {what}: the tail: {shown}"
            );
            assert!(shown.contains("stateful engine's enumeration"));
        }
    }
}

/// **Criterion 3 / 12.** A visible and an invisible failure in one Spec:
/// visible entries first, and `detail` names the visible one. Under `Ltr`
/// the invisible `w` fails first, so the order is the engine's sorting.
#[test]
fn c03_visible_failures_come_first() {
    let v = vis(&["v"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &inv_assert(false), &both_assert(), false);
    assert_eq!(
        o.spec_errors,
        vec![
            ("v".to_string(), ev(2, 1), true),
            ("w".to_string(), ev(1, 1), false)
        ],
        "conformance: visible first"
    );
    let detail = spec_not_error_free(&run(cc, &inv_assert(false), &both_assert()));
    assert!(
        detail.contains(&t4_detail("visible", "v", "(t2, 1)")),
        "conformance: detail names the visible failure: {detail}"
    );
}

/// **Criterion 3, the recorded behaviour.** An invisible Spec failure that
/// exists only in a revisited execution: the run still answers
/// `SpecNotErrorFree`; nothing panics.
#[test]
fn c03_an_invisible_failure_reached_by_a_revisit() {
    let v = vis(&["v"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(
        &cc,
        &inv_assert_on_revisit(false),
        &inv_assert_on_revisit(true),
        false,
    );
    assert_eq!(o.counters.spec_graphs, 2, "conformance: w reads 1, then 2");
    assert_eq!(o.spec_errors, vec![("w".to_string(), ev(2, 2), false)]);
    assert_eq!(
        (o.counters.impl_graphs, o.impl_end),
        (0, SearchEnd::Unknown)
    );
}

fn tid_named(g: &ExecutionGraph, n: &str) -> crate::thread::ThreadId {
    g.thread_ids()
        .into_iter()
        .find(|t| g.get_thread_tclab(*t).name().as_deref() == Some(n))
        .unwrap_or_else(|| panic!("conformance: no thread named {n}"))
}

/// How the second execution of a "`c` reads `a`, then `b`" fixture was
/// restored, told apart by stamps (stamps only increase; a carried label keeps
/// its stamp): on the revisited graph a **forward** revisit's receive was
/// installed after its source send, a **backward** revisit's before it.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Revisit {
    Forward,
    Backward,
}

/// Gate-4 round 01 m1(a), D-m1, and round 02 m3(b): the shape occurred. On
/// both kept graphs: `w`'s `Block(Assert)` sits at index 1 with a stamp
/// **below** `c`'s receive — the restoration (`cut_to_stamp` for a forward
/// revisit, `revisit_view` for a backward one) keeps every label stamped at
/// or below the receive — `c` reads `a` in execution 1 and `b` in execution 2
/// (the revisit happened), the revisit took the `path` asked for (measured by
/// the receive's stamp against its source's on graph 1), and the kept graph
/// has no unreplayed event. Since the block is in the revisited execution's
/// graph, `initialize_for_execution` put it in `unreplayed_events`, and the
/// completion gate found the set empty: the entry was drained during that
/// execution (`process_event` is the set's only remover), which the old
/// "can never be drained" comment denied.
fn assert_block_survives_the_revisit(gs: &[ExecutionGraph], side: &str, path: Revisit) {
    use crate::event_label::{BlockType, LabelEnum};
    assert_eq!(gs.len(), 2, "conformance: {side}: two executions");
    for (i, (g, reads)) in gs.iter().zip(["a", "b"]).enumerate() {
        let w = tid_named(g, "w");
        let c = tid_named(g, "c");
        let block = Event::new(w, 1);
        assert!(
            matches!(g.label(block), LabelEnum::Block(b) if matches!(b.btype(), BlockType::Assert)),
            "conformance: {side} graph {i}: w's Block(Assert) at index 1"
        );
        let recv = Event::new(c, 1);
        let src = g
            .recv_label(recv)
            .and_then(|r| r.rf())
            .unwrap_or_else(|| panic!("conformance: {side} graph {i}: c's receive reads nothing"));
        assert_eq!(
            g.get_thread_tclab(src.thread).name().as_deref(),
            Some(reads),
            "conformance: {side} graph {i}: c's source"
        );
        assert!(
            g.label(block).stamp() < g.label(recv).stamp(),
            "conformance: {side} graph {i}: w's block (stamp {}) is not before c's receive \
             (stamp {})",
            g.label(block).stamp(),
            g.label(recv).stamp()
        );
        assert!(
            g.unreplayed_events.is_empty(),
            "conformance: {side} graph {i}: unreplayed {:?}",
            g.unreplayed_events
        );
        let (r, sstamp) = (g.label(recv).stamp(), g.label(src).stamp());
        let receive_older = r < sstamp;
        let expected_older = i == 1 && path == Revisit::Backward;
        assert_eq!(
            receive_older, expected_older,
            "conformance: {side} graph {i}: receive stamp {r} vs its source's {sstamp} — not the \
             {path:?} path"
        );
    }
}

/// **Criterion 3, the recorded behaviour (ctx.rs's own worry).** An invisible
/// `Block(Assert)` installed **before** a visible receive is revisited, so it
/// survives into the revisited execution: on the Spec side the run must
/// answer `SpecNotErrorFree`; on the Impl side the pair conforms (`w` is
/// invisible) with notes. Measured; a panic of the completion-gate assertion
/// would be a T-finding. Gate-4 round 01 m1(a): the shape is asserted on the
/// kept graphs of both sides (`assert_block_survives_the_revisit`).
#[test]
fn c03_an_invisible_block_assert_surviving_a_revisit() {
    let v = vis(&["a", "b", "c"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(
        &cc,
        &inv_block_before_revisit(false),
        &inv_block_before_revisit(true),
        true,
    );
    assert_block_survives_the_revisit(&o.kept_spec_graphs, "Spec side", Revisit::Forward);
    assert!(
        !o.spec_errors.is_empty() && o.spec_errors.iter().all(|e| e.0 == "w" && !e.2),
        "conformance: Spec side: {:?}",
        o.spec_errors
    );
    assert_eq!(o.counters.spec_graphs, 2, "conformance: c reads a, then b");
    assert_eq!(
        (o.counters.impl_graphs, o.impl_end),
        (0, SearchEnd::Unknown)
    );

    let o = rw(
        &cc,
        &inv_block_before_revisit(true),
        &inv_block_before_revisit(false),
        true,
    );
    assert_block_survives_the_revisit(&o.kept_impl_graphs, "Impl side", Revisit::Forward);
    assert_counts(
        &o.counters,
        [2, 2, 1, 2, 2, 2, 0, 2, 2, 0, 2, 0],
        "Impl side",
    );
    assert!(
        !o.impl_notes.is_empty(),
        "conformance: the invisible failure is a note"
    );
    let r = run(
        cc,
        &inv_block_before_revisit(true),
        &inv_block_before_revisit(false),
    );
    match &r {
        Ok(ConfVerdict::Conforms(c)) => {
            assert!(
                c.outcome().notes().iter().all(
                    |n| matches!(n, ConfNote::InvisibleThread { thread, .. } if thread == "w")
                ),
                "conformance: notes {:?}",
                c.outcome().notes()
            );
            let s = format!("{}", r.as_ref().unwrap());
            assert!(
                s.contains("note: `w` failed an assertion at"),
                "conformance: {s}"
            );
        }
        other => panic!("conformance: expected Conforms, got {}", class(other)),
    }
}

// =========================================================================
// Criterion 4 — thm:stateful against the Phase 3 morphism
// =========================================================================

/// **Criterion 4 (D4).** On every corpus pair, with `keep_graphs`, the
/// reported Impl graphs are exactly those no Spec graph covers by
/// `matches ∧ statuses_agree`, computed on the same graphs — by completion
/// index and, second, by full canonical form. Excluded (A9): none of the
/// corpus (the NaN fixtures live in criterion 10's test).
#[test]
fn c04_thm_stateful_against_the_phase_3_morphism() {
    let mut pairs = 0;
    let mut reported_pairs = 0;
    let mut silent_pairs = 0;
    let mut failures = Vec::new();
    for p in corpus() {
        let v = &p.visible;
        let cc = built(sb(p.config.clone(), v));
        let o = rw(&cc, &p.imp, &p.spec, true);
        let spec: Vec<_> = o
            .kept_spec_graphs
            .iter()
            .map(|m| {
                let w = wobs(m, v).expect("conformance: wobs");
                let st = statuses(CompleteExecution::assume_finished_at_gate(m), &w, v)
                    .expect("conformance: statuses");
                (m, w, st)
            })
            .collect();
        let reference: Vec<usize> = o
            .kept_impl_graphs
            .iter()
            .enumerate()
            .filter(|(_, g)| {
                let w = wobs(g, v).expect("conformance: wobs");
                let st = statuses(CompleteExecution::assume_finished_at_gate(g), &w, v)
                    .expect("conformance: statuses");
                !spec
                    .iter()
                    .any(|(m, wm, sm)| matches(m, g, wm, &w, v) && statuses_agree(sm, &st))
            })
            .map(|(i, _)| i)
            .collect();
        // Map each report to its completion index (reports are pushed in
        // completion order, so they are a subsequence of the kept graphs).
        let mut by_index = Vec::new();
        let mut j = 0;
        for (i, g) in o.kept_impl_graphs.iter().enumerate() {
            if j < o.reports.len() && o.reports[j].0.to_string() == g.to_string() {
                by_index.push(i);
                j += 1;
            }
        }
        if j != o.reports.len() {
            failures.push(format!("{}: a report is not among the kept graphs", p.name));
        }
        if by_index != reference {
            failures.push(format!(
                "{}: by index {by_index:?} vs reference {reference:?}",
                p.name
            ));
        }
        let ref_keys = sorted(
            reference
                .iter()
                .map(|i| full_key(&o.kept_impl_graphs[*i], v))
                .collect(),
        );
        if report_keys(&o, v) != ref_keys {
            failures.push(format!(
                "{}: canonical report keys differ from the reference",
                p.name
            ));
        }
        if reference.is_empty() {
            silent_pairs += 1;
        } else {
            reported_pairs += 1;
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 4: {failures:#?}"
    );
    assert!(pairs >= 75, "conformance: only {pairs} pairs");
    assert!(
        reported_pairs >= 10 && silent_pairs >= 10,
        "conformance: ({reported_pairs}, {silent_pairs})"
    );
}

// =========================================================================
// Criterion 5 — ex:naive
// =========================================================================

/// **Criterion 5 (D5).** `k = 2..5`: `k!` orders of `k(k+1)` pairs each in one
/// slot; `k!` reports with `k!` distinct canonical keys, every lookup a
/// signature miss with zero containment tests.
#[test]
fn c05_ex_naive_k_2_to_5() {
    for (k, fact) in [(2usize, 2usize), (3, 6), (4, 24), (5, 120)] {
        let v = naive_visible(k);
        let cc = built(sb(cfg(ConsType::Bag), &v));
        let o = rw(&cc, &naive(k, 0), &naive(k, 1), true);
        let what = format!("ex:naive k={k}");
        assert_counts(
            &o.counters,
            [fact, fact, 1, 1, fact, fact, fact, 0, 0, 0, 0, fact],
            &what,
        );
        assert_identities(&o, &what);
        let slot = slot(&o.index, &o.kept_spec_graphs[0], &v).expect("conformance: the one slot");
        assert_eq!(
            slot.len(),
            fact,
            "conformance: {what}: k! orders in the slot"
        );
        assert!(
            slot.iter().all(|q| q.len() == k * (k + 1)),
            "conformance: {what}: each order has C(k+1,2) po pairs + k(k+1)/2 rf pairs"
        );
        // Every Impl order equals the Spec order of the same rf choice: the
        // miss is the signature's (values), not the containment's.
        for g in &o.kept_impl_graphs {
            assert!(
                slot.contains(&summary(g, &v).ord),
                "conformance: {what}: Impl order in Spec slot"
            );
            assert!(
                slot_of_impl_is_absent(&o.index, g, &v),
                "conformance: {what}"
            );
        }
        let keys = report_keys(&o, &v);
        let distinct: BTreeSet<&String> = keys.iter().collect();
        assert_eq!(
            (keys.len(), distinct.len()),
            (fact, fact),
            "conformance: {what}: k! reports, k! distinct keys (multiplicity 1)"
        );
    }
}

fn slot_of_impl_is_absent(
    index: &SigBuckets<BTreeSet<VisOrder>>,
    g: &ExecutionGraph,
    v: &[String],
) -> bool {
    slot(index, g, v).is_none()
}

// =========================================================================
// Criteria 6 and 9 — the Blocking pair, the oracle regression, artefacts
// =========================================================================

fn assert_report_artefacts(v: &Result<ConfVerdict, ConfError>, o: &StatefulOutcome, what: &str) {
    let out = outcome(v);
    assert_eq!(out.reports().len(), o.reports.len(), "conformance: {what}");
    let mut dumps_run: Vec<String> = Vec::new();
    for r in out.reports() {
        assert_eq!(
            *r.cause(),
            ReportCause::NoCover,
            "conformance: {what}: cause"
        );
        assert_eq!(
            r.gate(),
            ReportGate::Completion,
            "conformance: {what}: gate"
        );
        assert_eq!(
            r.tag(),
            ReportTag::CompleteCoverage,
            "conformance: {what}: tag"
        );
        assert!(
            matches!(
                r.diagnostics(),
                Diagnostics::NotProduced {
                    by: Engine::Stateful
                }
            ),
            "conformance: {what}: diagnostics"
        );
        assert!(r.triage().is_none(), "conformance: {what}: triage ran");
        match r.replay_snapshot() {
            ReplaySnapshot::Serialized(s) => {
                assert!(
                    s.starts_with('{') && s.len() > 2,
                    "conformance: {what}: JSON"
                )
            }
            other => panic!("conformance: {what}: snapshot not Serialized: {other:?}"),
        }
        assert!(!r.graph_dump().is_empty());
        let shown = format!("{r}");
        assert!(
            shown.contains(&format!(
                "certifies (CompleteCoverage): {T6_CERTIFIES_STATEFUL}"
            )),
            "conformance: {what}: certificate text: {shown}"
        );
        assert!(
            shown.contains(T6_NOT_PRODUCED),
            "conformance: {what}: NotProduced: {shown}"
        );
        dumps_run.push(r.graph_dump().to_string());
    }
    for (g, snap) in &o.reports {
        assert!(
            matches!(snap, ReplaySnapshot::Serialized(_)),
            "conformance: {what}"
        );
        let dump = g.to_string();
        let r = out
            .reports()
            .iter()
            .find(|r| r.graph_dump() == dump)
            .unwrap_or_else(|| panic!("conformance: {what}: run_with's graph not reported by run"));
        assert_eq!(
            r.events(),
            label_count(g),
            "conformance: {what}: events = label count"
        );
    }
}

/// **Criteria 6 and 9 (D6, D9).** The Blocking pair: one report, a
/// `SigKey` miss on the status, `CompleteCoverage` at `Completion`, a
/// `Serialized` snapshot.
#[test]
fn c06_c09_the_blocking_pair() {
    let v = vis(&["main", "c"]);
    let cc = built(sb(cfg(ConsType::FIFO), &v));
    let o = rw(&cc, &blocking(true), &blocking(false), true);
    assert_counts(
        &o.counters,
        [1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1],
        "blocking",
    );
    let r = run(cc, &blocking(true), &blocking(false));
    assert_eq!(class(&r), "reported:1");
    assert_report_artefacts(&r, &o, "blocking");
}

/// **Criteria 6 and 9 (D6).** Plan §6's oracle regression: `CompleteCoverage`,
/// errored vs done, never `VisibleError`; the Impl visible failure is not a
/// note.
#[test]
fn c06_c09_the_oracle_regression_is_complete_coverage() {
    let v = vis(&["w"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &visible_error(true), &visible_error(false), false);
    assert_counts(
        &o.counters,
        [1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1],
        "oracle regression",
    );
    assert!(
        o.impl_notes.is_empty(),
        "conformance: a visible failure is not a note"
    );
    let r = run(cc, &visible_error(true), &visible_error(false));
    assert_eq!(class(&r), "reported:1");
    assert!(outcome(&r).notes().is_empty());
    assert_report_artefacts(&r, &o, "oracle regression");
}

/// **Criterion 9 (D9)** on a many-report run (`ex:naive` `k = 3`).
#[test]
fn c09_report_artefacts_on_ex_naive() {
    let v = naive_visible(3);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &naive(3, 0), &naive(3, 1), false);
    let r = run(cc, &naive(3, 0), &naive(3, 1));
    assert_eq!(class(&r), "reported:6");
    assert_report_artefacts(&r, &o, "ex:naive k=3");
}

// =========================================================================
// Criterion 7 — several Spec graphs under one signature
// =========================================================================

/// **Criterion 7 (D7).** `Q_A < Q_B`; Impl `ord = Q_A` costs 1 test, Impl
/// `ord = Q_B` costs 2, both covered.
#[test]
fn c07_several_spec_graphs_one_signature() {
    let v = vis(&["a", "b", "c"]);
    let q_a: VisOrder = [
        pair(("a", 0), ("c", 0)),
        pair(("a", 0), ("c", 1)),
        pair(("b", 0), ("c", 1)),
        pair(("c", 0), ("c", 1)),
    ]
    .into_iter()
    .collect();
    let q_b: VisOrder = [
        pair(("a", 0), ("c", 1)),
        pair(("b", 0), ("c", 0)),
        pair(("b", 0), ("c", 1)),
        pair(("c", 0), ("c", 1)),
    ]
    .into_iter()
    .collect();
    assert!(q_a < q_b, "conformance: BTreeSet order");
    for (a_first, ord, tests) in [(true, &q_a, 1usize), (false, &q_b, 2usize)] {
        let cc = built(sb(cfg(ConsType::Bag), &v));
        let o = rw(&cc, &c7_impl(a_first), &c7_spec(), true);
        let what = format!("criterion 7, a_first={a_first}");
        assert_counts(&o.counters, [2, 1, 1, 1, 2, 1, 0, 1, 1, 0, tests, 0], &what);
        assert_eq!(
            &summary(&o.kept_impl_graphs[0], &v).ord,
            ord,
            "conformance: {what}: Impl ord"
        );
        let slot = slot(&o.index, &o.kept_impl_graphs[0], &v).expect("conformance: the slot");
        assert_eq!(
            slot.iter().collect::<Vec<_>>(),
            vec![&q_a, &q_b],
            "conformance: {what}: the slot, in scan order"
        );
        assert_eq!(class(&run(cc, &c7_impl(a_first), &c7_spec())), "conforms");
    }
}

/// **Criterion 7's one-graph fixtures**: `ex:cone`'s Spec and the relay
/// against themselves — one Spec graph, one test, success.
#[test]
fn c07_one_spec_graph_one_test() {
    for (what, p, v) in [
        ("ex:cone", ex_cone_spec(), vis(&["a", "c"])),
        ("relay", relay_spec(), vis(&["a", "c"])),
    ] {
        let cc = built(sb(cfg(ConsType::Bag), &v));
        let o = rw(&cc, &p, &p, false);
        assert_counts(&o.counters, [1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0], what);
    }
}

/// **Criterion 8 (D8).** Signatures that differ only in a value share a
/// `SigKey` bucket: `signatures = 2`, `sig_key_buckets = 1`; the Impl that
/// reads 1 or 2 is covered by the Spec that also does (2 lookups, 2 tests).
#[test]
fn c08_key_buckets_and_signatures_differ_in_general() {
    let v = vis(&["a", "b", "c"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(
        &cc,
        &two_senders(1i32, 2i32),
        &two_senders(1i32, 2i32),
        false,
    );
    assert_counts(
        &o.counters,
        [2, 2, 1, 2, 2, 2, 0, 2, 2, 0, 2, 0],
        "two senders 1/2",
    );
    let o = rw(
        &cc,
        &two_senders(1i32, 2i32),
        &two_senders(1i32, 1i32),
        false,
    );
    // Against `1, 1`: `b` sends 2 on the Impl side, so both Impl signatures
    // miss — behind a `SigKey` hit (same shapes).
    assert_counts(
        &o.counters,
        [2, 2, 1, 1, 2, 2, 2, 0, 0, 0, 0, 2],
        "1/2 vs 1/1",
    );
}

/// **Criterion 8 (D8b, derived after the audit showed the gap, before this
/// test ran).** `orders_held` counts **after** `BTreeSet` deduplication: an
/// invisible `w` reading 1 or 2 gives 2 Spec graphs with one signature and
/// the same `ord = ∅`, so the slot holds 1 order; each Impl lookup tests it
/// once.
#[test]
fn c08_orders_held_is_after_dedup() {
    let v = vis(&["v"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let p = inv_assert_on_revisit(false);
    let o = rw(&cc, &p, &p, false);
    assert_counts(
        &o.counters,
        [2, 2, 1, 1, 1, 2, 0, 2, 2, 0, 2, 0],
        "repeated order",
    );
}

// =========================================================================
// Criterion 10 — A9
// =========================================================================

/// **Criterion 10 (D10).** A NaN pair reports (the lookup fails), and every
/// NaN Spec graph opens a slot of its own.
#[test]
fn c10_a9_nan_reports_and_inflates_the_index() {
    let v = vis(&["a", "c"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &direct_of(f64::NAN), &direct_of(f64::NAN), false);
    assert_counts(
        &o.counters,
        [1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1],
        "NaN direct",
    );
    let vb = vis(&["a", "b", "c"]);
    let ccb = built(sb(cfg(ConsType::Bag), &vb));
    let o = rw(
        &ccb,
        &two_senders(f64::NAN, f64::NAN),
        &two_senders(f64::NAN, f64::NAN),
        false,
    );
    assert_counts(
        &o.counters,
        [2, 2, 1, 2, 2, 2, 2, 0, 0, 0, 0, 2],
        "NaN two senders",
    );
    // Control: the same shape with a reflexive value shares one slot.
    let o = rw(
        &ccb,
        &two_senders(1.0f64, 1.0f64),
        &two_senders(1.0f64, 1.0f64),
        false,
    );
    assert_counts(
        &o.counters,
        [2, 2, 1, 1, 2, 2, 0, 2, 2, 0, 3, 0],
        "1.0 two senders",
    );
}

// =========================================================================
// Criterion 11 — the containment direction
// =========================================================================

/// **Criterion 11 (D11).** `ord(Impl) = ∅` against `ord(Spec) = {(b,a)}`:
/// report; the mirror: silence.
#[test]
fn c11_the_containment_direction() {
    let v = vis(&["a", "b"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &c2_impl(), &c2_spec(), true);
    assert!(
        summary(&o.kept_impl_graphs[0], &v).ord.is_empty(),
        "conformance: ord(Impl) = ∅"
    );
    assert_eq!(
        summary(&o.kept_spec_graphs[0], &v).ord,
        [pair(("b", 0), ("a", 0))].into_iter().collect::<VisOrder>()
    );
    assert_counts(
        &o.counters,
        [1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1],
        "∅ vs {(b,a)}",
    );
    assert_eq!(
        class(&run(cc.clone(), &c2_impl(), &c2_spec())),
        "reported:1"
    );

    let o = rw(&cc, &c2_spec(), &c2_impl(), false);
    assert_counts(&o.counters, [1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0], "mirror");
    assert_eq!(class(&run(cc, &c2_spec(), &c2_impl())), "conforms");
}

// =========================================================================
// Criterion 12 — the engine-only entry point
// =========================================================================

/// **Criterion 12 (D12).** The fields and their types, by exhaustive
/// destructuring (a field added or removed fails to compile); the kept
/// families are empty unless asked for.
#[test]
fn c12_the_entry_point_fields() {
    let v = naive_visible(2);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let StatefulOutcome {
        reports,
        counters,
        index,
        kept_impl_graphs,
        kept_spec_graphs,
        impl_end,
        spec_end,
        spec_errors,
        impl_notes,
        executions,
        max_paper_events,
    } = rw(&cc, &naive(2, 0), &naive(2, 1), false);
    let reports: Vec<(ExecutionGraph, ReplaySnapshot)> = reports;
    let counters: StatefulCounters = counters;
    let index: SigBuckets<BTreeSet<VisOrder>> = index;
    let kept_impl_graphs: Vec<ExecutionGraph> = kept_impl_graphs;
    let kept_spec_graphs: Vec<ExecutionGraph> = kept_spec_graphs;
    let (impl_end, spec_end): (SearchEnd, SearchEnd) = (impl_end, spec_end);
    let spec_errors: Vec<(String, Event, bool)> = spec_errors;
    let impl_notes: Vec<Diagnostic> = impl_notes;
    let (executions, max_paper_events): (usize, usize) = (executions, max_paper_events);
    assert_eq!(reports.len(), 2);
    assert_eq!(counters.reports, 2);
    assert_eq!(index.len(), 1);
    assert!(
        kept_impl_graphs.is_empty() && kept_spec_graphs.is_empty(),
        "conformance: kept without keep_graphs"
    );
    assert_eq!(
        (impl_end, spec_end),
        (
            SearchEnd::StateSpaceExhausted,
            SearchEnd::StateSpaceExhausted
        )
    );
    assert!(spec_errors.is_empty() && impl_notes.is_empty());
    assert_eq!(
        (executions, max_paper_events),
        (2, 5),
        "conformance: L = 2k+1 = 5"
    );
    let kept = rw(&cc, &naive(2, 0), &naive(2, 1), true);
    assert_eq!(
        (kept.kept_impl_graphs.len(), kept.kept_spec_graphs.len()),
        (2, 2)
    );
}

// =========================================================================
// Criterion 13 — selector completeness
// =========================================================================

/// **Criterion 13 (D13).** Under `Ltr`, `FewestEvents` and `Reverse`, every
/// corpus pair gives identical report sets (full canonical form, as
/// multisets), verdicts and family sizes.
#[test]
fn c13_selector_completeness() {
    let mut failures = Vec::new();
    let mut pairs = 0;
    for p in corpus() {
        let runs: Vec<(Vec<String>, String, usize, usize)> =
            [Selector::Ltr, Selector::FewestEvents, Selector::Reverse]
                .iter()
                .map(|s| {
                    let c = with_selector(p.config.clone(), *s);
                    let cc = built(sb(c, &p.visible).selector(*s));
                    let o = rw(&cc, &p.imp, &p.spec, false);
                    let verdict = class(&run(cc, &p.imp, &p.spec));
                    (
                        report_keys(&o, &p.visible),
                        verdict,
                        o.counters.spec_graphs,
                        o.counters.impl_graphs,
                    )
                })
                .collect();
        for (i, s) in ["fewest", "reverse"].iter().enumerate() {
            if runs[i + 1] != runs[0] {
                failures.push(format!(
                    "{}: {s} differs from ltr: ({}, {}, {}) vs ({}, {}, {})",
                    p.name,
                    runs[i + 1].1,
                    runs[i + 1].2,
                    runs[i + 1].3,
                    runs[0].1,
                    runs[0].2,
                    runs[0].3
                ));
            }
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 13: {failures:#?}"
    );
    assert!(pairs >= 75);
}

// =========================================================================
// Criterion 14 — first-report mode
// =========================================================================

/// **Criterion 14 (D14).** `stop_at_first_report`: the Spec enumeration is
/// complete, the Impl side makes exactly one lookup, `StoppedAtFirstReport`,
/// `Reported`, the always-true sentence without "exactly the set", and the
/// truncation text.
#[test]
fn c14_first_report_mode() {
    let v = naive_visible(3);
    let cc = built(sb(cfg(ConsType::Bag), &v).stop_at_first_report(true));
    let o = rw(&cc, &naive(3, 0), &naive(3, 1), false);
    assert_counts(
        &o.counters,
        [6, 1, 1, 1, 6, 1, 1, 0, 0, 0, 0, 1],
        "first report",
    );
    assert_eq!(o.impl_end, SearchEnd::StoppedAtFirstReport);
    assert_eq!(o.spec_end, SearchEnd::StateSpaceExhausted);
    let r = run(cc, &naive(3, 0), &naive(3, 1));
    assert_eq!(class(&r), "reported:1");
    assert_eq!(outcome(&r).end(), SearchEnd::StoppedAtFirstReport);
    let s = format!("{}", r.as_ref().unwrap());
    assert!(s.contains(T6_EACH_UNCOVERED), "conformance: {s}");
    assert!(!s.contains(T6_EXACTLY), "conformance: {s}");
    assert!(s.contains(TRUNC_CONFIG), "conformance: {s}");
}

// =========================================================================
// Criterion 14b — the rendered texts
// =========================================================================

/// The rendering's head: everything before the first report section.
fn head(s: &str) -> &str {
    s.split("\n#0\n").next().unwrap_or(s)
}

/// **Criterion 14b.** A stateful `Conforms` renders exactly the enumerator's
/// baseline with its first silence line replaced by T6's (lines 2–5 are
/// engine-independent by T6).
#[test]
fn c14b_stateful_conforms_rendering() {
    let cc = built(
        ConfBuilder::new()
            .config(Config::builder().with_seed(7).build())
            .visible_threads(vis(&["a", "c"]))
            .engine(Engine::Stateful),
    );
    let r = run(cc, &restart(true), &restart(true));
    assert_eq!(class(&r), "conforms");
    let expected = super::stateful_baseline::ENUMERATOR_CONFORMS_BASELINE.replacen(
        ENUM_SILENCE_LINE,
        T6_CONFORMS_LINE,
        1,
    );
    assert_ne!(
        expected,
        super::stateful_baseline::ENUMERATOR_CONFORMS_BASELINE
    );
    assert_eq!(format!("{}", r.unwrap()), expected);
}

/// **Criterion 14b.** An unbounded stateful `Reported`: the head is exactly
/// the count, both T6 sentences, the two kept lines; none of the enumerator's
/// three claims; no triage caveat; each report shows the stateful certificate
/// and `NotProduced`.
#[test]
fn c14b_stateful_reported_rendering_unbounded() {
    let v = naive_visible(2);
    let cc = built(
        ConfBuilder::new()
            .config(Config::builder().with_seed(7).build())
            .visible_threads(v)
            .engine(Engine::Stateful),
    );
    let r = run(cc, &naive(2, 0), &naive(2, 1));
    assert_eq!(class(&r), "reported:2");
    let s = format!("{}", r.unwrap());
    let expected_head = format!(
        "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)\n\
         conformance: 2 candidate violation(s).\n{T6_EACH_UNCOVERED}\n{T6_EXACTLY}\n\
         {RESIDUAL}\n{ONLY_SILENCE}\n"
    );
    assert_eq!(head(&s), expected_head, "conformance: the head, verbatim");
    for gone in [
        ENUM_SETTLED,
        ENUM_UNSETTLED,
        ENUM_NOT_COMPLETE,
        TRIAGE_CAVEAT,
    ] {
        assert!(
            !s.contains(gone),
            "conformance: {gone:?} rendered under Stateful: {s}"
        );
    }
    assert!(s.contains("\n#1\n"), "conformance: two report sections");
    assert_eq!(
        s.matches(&format!(
            "certifies (CompleteCoverage): {T6_CERTIFIES_STATEFUL}"
        ))
        .count(),
        2
    );
    assert_eq!(s.matches(T6_NOT_PRODUCED).count(), 2);
    assert!(
        !s.contains("lem:coverexact"),
        "conformance: the enumerator's certificate: {s}"
    );
}

/// **Criterion 14b.** The truncated heads (criteria 2 and 14) verbatim.
#[test]
fn c14b_stateful_reported_rendering_truncated() {
    let v = naive_visible(3);
    let bounded = built(sb(
        Config::builder()
            .with_seed(7)
            .with_max_iterations(2)
            .build(),
        &v,
    ));
    let s = format!("{}", run(bounded, &naive(3, 0), &naive(3, 1)).unwrap());
    let expected = format!(
        "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)\n\
         conformance: 2 candidate violation(s).\n{T6_EACH_UNCOVERED}\n{RESIDUAL}\n\
         {ONLY_SILENCE}\n{}\n",
        trunc_bound(2)
    );
    assert_eq!(head(&s), expected, "conformance: bounded head");
    let stopped = built(sb(Config::builder().with_seed(7).build(), &v).stop_at_first_report(true));
    let s = format!("{}", run(stopped, &naive(3, 0), &naive(3, 1)).unwrap());
    let expected = format!(
        "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)\n\
         conformance: 1 candidate violation(s).\n{T6_EACH_UNCOVERED}\n{RESIDUAL}\n\
         {ONLY_SILENCE}\n{TRUNC_CONFIG}\n"
    );
    assert_eq!(head(&s), expected, "conformance: stopped head");
    assert!(!s.contains(TRIAGE_CAVEAT));
}

/// **Criterion 14b / T6.** `triage(true)` under `Stateful`: ignored (no triage
/// outcome), recorded as configured, and still no triage caveat.
#[test]
fn c14b_triage_is_ignored_and_recorded() {
    let v = naive_visible(2);
    for t in [false, true] {
        let cc = built(sb(cfg(ConsType::Bag), &v).triage(t));
        let r = run(cc, &naive(2, 0), &naive(2, 1));
        let o = outcome(&r);
        assert_eq!(
            o.triage_enabled, t,
            "conformance: the configured value is recorded"
        );
        assert!(
            o.reports().iter().all(|r| r.triage().is_none()),
            "conformance: triage ran"
        );
        let s = format!("{}", r.as_ref().unwrap());
        assert!(
            !s.contains("triage is off") && !s.contains("ConfBuilder::triage(true)"),
            "conformance: {s}"
        );
    }
}

/// **Criterion 14b / T6.** `certifies_under` on every (engine, tag),
/// `certifies` unchanged, `NotProduced`'s two strings.
#[test]
fn c14b_certifies_under_and_not_produced() {
    let tags = [
        ReportTag::GrowingExhaustion,
        ReportTag::CompleteCoverage,
        ReportTag::VisibleError,
    ];
    for t in tags {
        assert_eq!(
            t.certifies_under(Engine::Enumerator),
            t.certifies(),
            "conformance: {t:?}"
        );
    }
    assert_eq!(
        ReportTag::CompleteCoverage.certifies_under(Engine::Stateful),
        T6_CERTIFIES_STATEFUL
    );
    for t in [ReportTag::GrowingExhaustion, ReportTag::VisibleError] {
        assert_eq!(
            t.certifies_under(Engine::Stateful),
            t.certifies(),
            "conformance: {t:?}"
        );
    }
    assert_eq!(
        ReportTag::CompleteCoverage.certifies(),
        "no graph of the specification covers the reported complete graph (lem:coverexact (2))",
        "conformance: Part 2's text unchanged"
    );
    let d = Diagnostics::NotProduced {
        by: Engine::Stateful,
    };
    assert_eq!(format!("{d}"), T6_NOT_PRODUCED);
    assert_eq!(
        crate::conformance::diagnose::spec_side_first_mismatch(&d, &ReportCause::NoCover),
        T6_NOT_PRODUCED_MISMATCH
    );
}

/// **T6.** The stateful outcome's own record: engine, counters, the
/// `ConfCounters` fields T6 names, `Checked` whatever the flag; the
/// enumerator's outcome has no stateful counters.
#[test]
fn c14b_outcome_record_by_engine() {
    let v = naive_visible(3);
    for skip in [false, true] {
        let cc = built(sb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(skip));
        let r = run(cc, &naive(3, 0), &naive(3, 1));
        let o = outcome(&r);
        assert_eq!(o.engine(), Engine::Stateful);
        assert_eq!(
            o.spec_err_freedom(),
            SpecErrFreedom::Checked,
            "conformance: skip={skip}"
        );
        assert!(!format!("{}", r.as_ref().unwrap()).contains("assumption recorded"));
        let c = o.counters();
        assert_eq!((c.executions, c.max_paper_events_per_execution), (6, 7));
        assert_eq!(
            c.paper_events_at_first_report, None,
            "conformance: not filled by T6"
        );
    }
    let e = run(
        ConfBuilder::new()
            .config(cfg(ConsType::Bag))
            .visible_threads(v)
            .unlimited()
            .build()
            .unwrap(),
        &naive(3, 0),
        &naive(3, 1),
    );
    let o = outcome(&e);
    assert_eq!(o.engine(), Engine::Enumerator);
    assert!(o.stateful_counters().is_none());
    assert_eq!(Engine::default(), Engine::Enumerator);
}

/// **T6.** A bounded stateful run with no report is `Inconclusive`, rendering
/// only `not_a_certificate` reasons (`BoundedRun`).
#[test]
fn c14b_bounded_silence_is_inconclusive() {
    let v = naive_visible(3);
    let cc = built(sb(
        Config::builder()
            .with_cons_type(ConsType::Bag)
            .with_max_iterations(2)
            .build(),
        &v,
    ));
    let r = run(cc, &naive(3, 1), &naive(3, 1));
    match &r {
        Ok(ConfVerdict::Inconclusive(o)) => {
            // n3 (D-n3): an `Inconclusive` *verdict* (a bounded run) is not
            // `inconclusive()` (an exhausted budget), which no stateful run has.
            assert!(
                !o.inconclusive(),
                "conformance: inconclusive() on a stateful run"
            );
            assert_eq!(
                o.not_a_certificate(),
                vec![NotACertificate::BoundedRun { max_iterations: 2 }]
            );
            let s = format!("{}", r.as_ref().unwrap());
            assert!(
                !s.contains("ran out of budget") && !s.contains(T6_CONFORMS_LINE),
                "conformance: {s}"
            );
        }
        other => panic!("conformance: expected Inconclusive, got {}", class(other)),
    }
}

/// **Round 02 m3(b), D-bwd.** The backward instance of the shape: spawn order
/// `w, a, c, b` under `Ltr`, so `c` reads `a` before `b`'s send exists and
/// `b`'s send revisits `c`'s receive **backward** — measured by stamps on the
/// revisited graph (the receive is older than its source send), through the
/// same helper as the forward fixture. Spec side: `SpecNotErrorFree`'s path;
/// Impl side: conforms with notes; nothing panics.
#[test]
fn c03_an_invisible_block_assert_surviving_a_backward_revisit() {
    let v = vis(&["a", "b", "c"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let order = ["w", "a", "c", "b"];
    let o = rw(
        &cc,
        &race_on_channel(order, false),
        &race_on_channel(order, true),
        true,
    );
    assert_block_survives_the_revisit(&o.kept_spec_graphs, "Spec side", Revisit::Backward);
    assert!(
        !o.spec_errors.is_empty() && o.spec_errors.iter().all(|e| e.0 == "w" && !e.2),
        "conformance: Spec side: {:?}",
        o.spec_errors
    );
    assert_eq!(
        (o.counters.impl_graphs, o.impl_end),
        (0, SearchEnd::Unknown)
    );

    let o = rw(
        &cc,
        &race_on_channel(order, true),
        &race_on_channel(order, false),
        true,
    );
    assert_block_survives_the_revisit(&o.kept_impl_graphs, "Impl side", Revisit::Backward);
    assert_counts(
        &o.counters,
        [2, 2, 1, 2, 2, 2, 0, 2, 2, 0, 2, 0],
        "Impl side",
    );
    assert!(
        !o.impl_notes.is_empty(),
        "conformance: the invisible failure is a note"
    );
    assert_eq!(
        class(&run(
            cc,
            &race_on_channel(order, true),
            &race_on_channel(order, false)
        )),
        "conforms"
    );
}

/// **Round 02 m3(b), D-fail.** The helper's failing direction: spawn order
/// `a, c, b, w` puts `w`'s assertion after `c`'s receive, so the helper must
/// refuse graph 0 on the stamp comparison.
#[test]
fn c03_the_survival_helper_rejects_a_block_after_the_receive() {
    let v = vis(&["a", "b", "c"]);
    let cc = built(sb(cfg(ConsType::Bag), &v));
    let order = ["a", "c", "b", "w"];
    let o = rw(
        &cc,
        &race_on_channel(order, true),
        &race_on_channel(order, false),
        true,
    );
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        assert_block_survives_the_revisit(&o.kept_impl_graphs, "late", Revisit::Backward);
    }));
    let msg = panic_text(r).expect("conformance: the helper accepted a block after the receive");
    assert!(
        msg.contains("late graph 0: w's block") && msg.contains("is not before c's receive"),
        "conformance: the helper refused for another reason: {msg}"
    );
}
