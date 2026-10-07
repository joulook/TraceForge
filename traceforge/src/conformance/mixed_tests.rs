//! P4-MIXED gate 3: the tester's tests for per-operation visibility
//! (criteria `P4-MIXED.md` revision 5.1).
//!
//! Every expected value below was derived from the criteria's engine facts
//! M1–M8 and the paper (`mixed.tex` §10, `appendix.tex`'s "Stability of
//! annotated visibility" and "The audit behind `thm:mixed`") **before** the
//! lead's Part 7 diffs were read; the derivations are in
//! `plan/traceForge/log/dev/P4-MIXED.report.md`, Part 0, under D1..D10, cited
//! on each test. Tests are named by criterion. The fixtures are written here
//! from the criteria's text, independently of `grid.rs`'s registry entries,
//! which criterion 10's test cross-checks against them.
//!
//! Conventions kept because `s5_tests`' source scans read this file: no print
//! macro anywhere, and every panic-family message starts with `conformance:`.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::config::{ConfConfig, GatePolicy, GatedMode};
use crate::conformance::ctx::{
    CompletionSink, ConfMode, Gate, GateAt, GateSink, GateVerdict, ReportKind, SinkVerdict,
};
use crate::conformance::gated::ReportSite;
use crate::conformance::grid::{
    mixed_fixture, mixed_fixtures, row_of, run_grid, Fixture, GridConfig, GridEnd, GridEngine,
    GridRaw, GridResult, Row, Tables,
};
use crate::conformance::grid_oracle::{canon_key, certify, Cause, Claim, Families};
use crate::conformance::morphism::{follows, CompleteExecution, Status};
use crate::conformance::obs::{is_visible, wobs, Obs, Wobs};
use crate::conformance::report::{
    obs_text, ConfOutcome, ConfVerdict, ReplaySnapshot, ReportCause, ReportGate, ReportTag,
    SearchEnd,
};
use crate::conformance::selector::Selector;
use crate::conformance::sig::{ord, Summary, VPosMap};
use crate::conformance::stateful::{enumerate, EnumRun};
use crate::conformance::testing::{executions_begun, reset_executions_begun};
use crate::conformance::{ConfBuilder, ConfError, Engine};
use crate::event::Event;
use crate::event_label::{Annotation, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::must::{Must, MustState};
use crate::thread::ThreadId;
use crate::{thread, CommunicationModel, Config, ConsType, Visibility};

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

fn vis(ns: &[&str]) -> Vec<String> {
    ns.iter().map(|s| (*s).to_string()).collect()
}

/// A p2p (FIFO) channel of `i32`, created by the calling thread.
fn fifo() -> (crate::channel::Sender<i32>, crate::channel::Receiver<i32>) {
    crate::channel::Builder::<i32>::new()
        .with_comm(crate::channel::cons_to_model(ConsType::FIFO))
        .build()
}

/// An `asyn` (Bag) channel of `i32`, created by the calling thread.
fn bag_chan() -> (crate::channel::Sender<i32>, crate::channel::Receiver<i32>) {
    crate::channel::Builder::<i32>::new()
        .with_comm(CommunicationModel::NoOrder)
        .build()
}

const SELECTORS: [Selector; 3] = [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];

/// One engine configuration of the public path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Eng {
    Enum,
    Stateful,
    CFirst,
    Gated(GatedMode, GatePolicy),
}

/// The four engines, the gated one in both modes under `Never`, `Always`,
/// `Budget(1)` (criterion 1's table).
const ENGINES: [Eng; 9] = [
    Eng::Enum,
    Eng::Stateful,
    Eng::CFirst,
    Eng::Gated(GatedMode::Exhaustive, GatePolicy::Never),
    Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
    Eng::Gated(GatedMode::Exhaustive, GatePolicy::Budget(1)),
    Eng::Gated(GatedMode::FirstFailure, GatePolicy::Never),
    Eng::Gated(GatedMode::FirstFailure, GatePolicy::Always),
    Eng::Gated(GatedMode::FirstFailure, GatePolicy::Budget(1)),
];

fn cc(e: Eng, config: Config, visible: &[String], s: Selector, skip: bool) -> ConfConfig {
    let mut b = ConfBuilder::new()
        .config(config)
        .visible_threads(visible.to_vec())
        .selector(s)
        .skip_spec_errfree_check(skip);
    b = match e {
        Eng::Enum => b.engine(Engine::Enumerator),
        Eng::Stateful => b.engine(Engine::Stateful),
        Eng::CFirst => b.engine(Engine::CompleteFirst),
        Eng::Gated(m, p) => b.engine(Engine::Gated).gated_mode(m).gate_policy(p),
    };
    b.build()
        .expect("conformance: the test configuration is in scope")
}

/// The public entry point (`conformance::verify`, its own thread, a panic
/// re-raised with its payload).
fn verify(c: ConfConfig, imp: &Prog, spec: &Prog) -> Result<ConfVerdict, ConfError> {
    let (i, s) = (Arc::clone(imp), Arc::clone(spec));
    crate::conformance::verify(c, move || i(), move || s())
}

fn outcome(v: &Result<ConfVerdict, ConfError>) -> &ConfOutcome {
    match v {
        Ok(ConfVerdict::Conforms(c)) => c.outcome(),
        Ok(ConfVerdict::Reported(o)) | Ok(ConfVerdict::Inconclusive(o)) => o,
        Err(e) => panic!("conformance: expected a verdict, got {e:?}"),
    }
}

fn class(v: &Result<ConfVerdict, ConfError>) -> String {
    match v {
        Ok(ConfVerdict::Conforms(_)) => "conforms".to_string(),
        Ok(ConfVerdict::Reported(o)) => format!("reported:{}", o.reports().len()),
        Ok(ConfVerdict::Inconclusive(_)) => "inconclusive".to_string(),
        Err(e) => format!("error:{e:?}"),
    }
}

fn invisible_ops(v: &Result<ConfVerdict, ConfError>) -> usize {
    outcome(v).counters().invisible_ops_of_visible_threads
}

/// The panic payload's text, if `f` panicked.
fn panic_of<R>(f: impl FnOnce() -> R) -> Option<String> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(_) => None,
        Err(p) => Some(
            p.downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_else(|| "<non-string payload>".to_string()),
        ),
    }
}

/// The innermost message of a payload the runtime may have wrapped.
fn innermost(payload: &str) -> &str {
    payload.rsplit("original panic: ").next().unwrap_or(payload)
}

/// M4's delimited site field: the text between the **last** "(site `" and
/// the "`)" closing it — never a bare substring (round 04 m1).
fn site_field(payload: &str) -> Option<String> {
    let msg = innermost(payload);
    let at = msg.rfind("(site `")?;
    let rest = &msg[at + "(site `".len()..];
    let end = rest.find("`)")?;
    Some(rest[..end].to_string())
}

fn tid(g: &ExecutionGraph, name: &str) -> ThreadId {
    g.thread_ids()
        .into_iter()
        .find(|t| g.get_thread_tclab(*t).name().as_deref() == Some(name))
        .unwrap_or_else(|| panic!("conformance: no thread `{name}` in the graph"))
}

/// The positions of thread `name`'s `SendMsg`/`RecvMsg` labels, in order.
fn comm_events(g: &ExecutionGraph, name: &str) -> Vec<Event> {
    let t = tid(g, name);
    (0..g.thread_size(t) as u32)
        .map(|i| Event::new(t, i))
        .filter(|e| matches!(g.label(*e), LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_)))
        .collect()
}

fn annotation(g: &ExecutionGraph, e: Event) -> Option<Annotation> {
    match g.label(e) {
        LabelEnum::SendMsg(s) => Some(s.annotation()),
        LabelEnum::RecvMsg(r) => Some(r.annotation()),
        _ => None,
    }
}

fn w(g: &ExecutionGraph, v: &[String]) -> Wobs {
    wobs(g, v).expect("conformance: wobs on a fixture graph")
}

/// The word of thread `n`, rendered by the tool's own `obs_text`.
fn word(g: &ExecutionGraph, v: &[String], n: &str) -> Vec<String> {
    w(g, v).of(n).iter().map(|(_, o)| obs_text(o)).collect()
}

/// The word's shape: `s`/`r` per observation, `r⊥` for a receive of ⊥.
fn shape(g: &ExecutionGraph, v: &[String], n: &str) -> String {
    w(g, v)
        .of(n)
        .iter()
        .map(|(_, o)| match o {
            Obs::Send(_) => "s",
            Obs::Recv(Some(_)) => "r",
            Obs::Recv(None) => "r⊥",
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn summary(g: &ExecutionGraph, v: &[String]) -> Summary {
    Summary::of(CompleteExecution::assume_finished_at_gate(g), &w(g, v), v)
        .expect("conformance: summary on a fixture graph")
}

/// `ord(G)` rendered as `"t,i<u,j"` strings.
fn ord_of(g: &ExecutionGraph, v: &[String]) -> BTreeSet<String> {
    ord(g, &w(g, v), v)
        .into_iter()
        .map(|(a, b)| format!("{},{}<{},{}", a.thread, a.index, b.thread, b.index))
        .collect()
}

fn set(xs: &[&str]) -> BTreeSet<String> {
    xs.iter().map(|s| (*s).to_string()).collect()
}

// --- the grid route (graphs and the certification oracle) ----------------

fn ok(end: GridEnd) -> GridResult {
    match end {
        GridEnd::Ok(r) => r,
        GridEnd::Panicked {
            fixture,
            config,
            payload,
        } => panic!(
            "conformance: the engine panicked on `{fixture}` under {}: {payload}",
            config.label()
        ),
        GridEnd::Capped { fixture, .. } => panic!("conformance: `{fixture}` capped"),
    }
}

fn grun(f: &Fixture, c: &GridConfig) -> GridResult {
    ok(run_grid(f, c, None))
}

/// One report of a grid run, engine-independently (Part 6's X3 mapping).
struct Rep<'a> {
    graph: &'a ExecutionGraph,
    tag: ReportTag,
    cause: Cause,
    serialized: bool,
    site: String,
}

fn serialized(s: &ReplaySnapshot) -> bool {
    matches!(s, ReplaySnapshot::Serialized(_))
}

fn reports_of(r: &GridResult) -> Vec<Rep<'_>> {
    match &r.raw {
        GridRaw::Enumerator(o) => o
            .reports
            .iter()
            .map(|rep| {
                let (cause, rc) = match &rep.kind {
                    ReportKind::NoCover => (Cause::NoCover, ReportCause::NoCover),
                    ReportKind::VisibleError { thread, pos } => (
                        Cause::VisibleError {
                            thread: thread.clone(),
                            pos: pos.to_string(),
                        },
                        ReportCause::VisibleError {
                            thread: thread.clone(),
                            pos: pos.to_string(),
                        },
                    ),
                };
                let gate = ReportGate::of(rep.gate);
                Rep {
                    graph: &rep.graph,
                    tag: ReportTag::of(&rc, gate),
                    cause,
                    serialized: serialized(&rep.replay),
                    site: format!("{gate:?}"),
                }
            })
            .collect(),
        GridRaw::Stateful(o) => o
            .reports
            .iter()
            .map(|(g, s)| Rep {
                graph: g,
                tag: ReportTag::CompleteCoverage,
                cause: Cause::NoCover,
                serialized: serialized(s),
                site: "Completion".to_owned(),
            })
            .collect(),
        GridRaw::CompleteFirst(o) => {
            let mut v: Vec<Rep<'_>> = o
                .cut_reports
                .iter()
                .map(|rep| {
                    let ReportKind::VisibleError { thread, pos } = &rep.kind else {
                        panic!("conformance: a cut report that is not a VisibleError")
                    };
                    Rep {
                        graph: &rep.graph,
                        tag: ReportTag::VisibleError,
                        cause: Cause::VisibleError {
                            thread: thread.clone(),
                            pos: pos.to_string(),
                        },
                        serialized: serialized(&rep.replay),
                        site: "NotAGate".to_owned(),
                    }
                })
                .collect();
            v.extend(o.reports.iter().map(|(g, s)| Rep {
                graph: g,
                tag: ReportTag::CompleteCoverage,
                cause: Cause::NoCover,
                serialized: serialized(s),
                site: "Completion".to_owned(),
            }));
            v
        }
        GridRaw::Gated(o) => o
            .reports
            .iter()
            .map(|(g, s, site)| Rep {
                graph: g,
                tag: match site {
                    ReportSite::Completion => ReportTag::CompleteCoverage,
                    ReportSite::Gate(_) => ReportTag::GrowingExhaustion,
                },
                cause: Cause::NoCover,
                serialized: serialized(s),
                site: match site {
                    ReportSite::Completion => "Completion".to_owned(),
                    ReportSite::Gate(g) => format!("{:?}", ReportGate::of(Some(*g))),
                },
            })
            .collect(),
        GridRaw::Verdict(_) => Vec::new(),
    }
}

/// The run's `invisible_ops_of_visible_threads`, from the engine's own record.
fn grid_counter(r: &GridResult) -> usize {
    match &r.raw {
        GridRaw::Enumerator(o) => o.counters.invisible_ops_of_visible_threads,
        GridRaw::Stateful(o) => o.counters.invisible_ops_of_visible_threads,
        GridRaw::CompleteFirst(o) => o.counters.invisible_ops_of_visible_threads,
        GridRaw::Gated(o) => o.counters.invisible_ops_of_visible_threads,
        GridRaw::Verdict(v) => invisible_ops(v),
    }
}

/// The oracle families of a fixture (the stateful run, both families kept).
fn families(f: &Fixture) -> Families {
    let r = grun(f, &GridConfig::new(GridEngine::Stateful));
    let GridRaw::Stateful(o) = &r.raw else {
        unreachable!("conformance: stateful")
    };
    assert!(
        o.spec_errors.is_empty(),
        "conformance: `{}`: Spec errors {:?}",
        f.name,
        o.spec_errors
    );
    Families::new(&o.kept_spec_graphs, &o.kept_impl_graphs, 0, &f.visible)
}

fn certify_all(fam: &Families, r: &GridResult, what: &str) {
    for rep in reports_of(r) {
        certify(
            fam,
            &Claim {
                graph: rep.graph,
                tag: rep.tag,
                cause: rep.cause.clone(),
                serialized: rep.serialized,
            },
        )
        .unwrap_or_else(|e| panic!("conformance: {what}: the oracle rejects a report: {e}"));
    }
}

/// The grid configurations matching [`ENGINES`] under `s` (the sweeping
/// engines through `run_with`, the precheck skipped; the enumerator's raw
/// route at the default budget).
fn grid_engines(s: Selector) -> Vec<(Eng, GridConfig)> {
    ENGINES
        .iter()
        .map(|e| {
            let c = match e {
                Eng::Enum => GridConfig::new(GridEngine::Enumerator),
                Eng::Stateful => GridConfig::new(GridEngine::Stateful),
                Eng::CFirst => GridConfig::new(GridEngine::CompleteFirst),
                Eng::Gated(m, p) => GridConfig::new(GridEngine::Gated).gated(*m, *p),
            };
            (*e, c.selector(s))
        })
        .collect()
}

// =========================================================================
// Fixtures, from the criteria's text
// =========================================================================

/// `ex:server`'s Impl (criterion 1; D1): `K: send(S,1); x := recv^b() ‖ S:
/// y := recv^b(); send(D,1); z := recv^b(); send(K, reply) ‖ D: w :=
/// recv^b(); send(S,1)`; FIFO channels `main` creates; spawned `d, s, k`.
/// With `annotated`, exactly S's two storage operations are `Invisible`.
fn server_impl(annotated: bool, reply: i32) -> Prog {
    prog(move || {
        let (tx_k, rx_k) = fifo();
        let (tx_s, rx_s) = fifo();
        let (tx_d, rx_d) = fifo();
        let ts = tx_s.clone();
        let _d = named("d", move || {
            let _w: i32 = rx_d.recv_msg_block();
            ts.send_msg(1);
        });
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            if annotated {
                tx_d.send_msg_as(Visibility::Invisible, 1);
                let _z: i32 = rx_s.recv_msg_block_as(Visibility::Invisible);
            } else {
                tx_d.send_msg(1);
                let _z: i32 = rx_s.recv_msg_block();
            }
            tx_k.send_msg(reply);
        });
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
    })
}

/// `ex:server`'s Spec: `K: send(S,1); x := recv^b() ‖ S: y := recv^b();
/// send(K,2)`; spawned `s, k`.
fn server_spec() -> Prog {
    prog(|| {
        let (tx_k, rx_k) = fifo();
        let (tx_s, rx_s) = fifo();
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            tx_k.send_msg(2);
        });
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
    })
}

/// `ex:serverblock`'s Impl′ (criterion 2; D2).
fn serverblock_impl() -> Prog {
    prog(|| {
        let (tx_k, rx_k) = fifo();
        let (tx_s, rx_s) = fifo();
        let (tx_d, rx_d) = fifo();
        let _d = named("d", move || {
            let _w: i32 = rx_d.recv_msg_block();
        });
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            tx_k.send_msg(2);
            tx_d.send_msg_as(Visibility::Invisible, 1);
            let _z: i32 = rx_s.recv_msg_block_as(Visibility::Invisible);
        });
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
    })
}

/// Criterion 3 (D3): Impl `A: send^i(D,0); send(C,0) ‖ C: x := recv^b() ‖
/// D: skip`; Spec without the `i` send and without `D`. Spawned `d, c, a`
/// (Impl) and `c, a` (Spec); every mailbox a channel `main` creates.
fn vpos_pair(imp: bool) -> Prog {
    prog(move || {
        let (tx_c, rx_c) = bag_chan();
        let (tx_d, _rx_d) = bag_chan();
        if imp {
            let _d = named("d", || {});
        }
        let _c = named("c", move || {
            let _x: i32 = rx_c.recv_msg_block();
        });
        let _a = named("a", move || {
            if imp {
                tx_d.send_msg_as(Visibility::Invisible, 0);
            }
            tx_c.send_msg(0);
        });
    })
}

/// Criterion 4's two programs (D4): `K: send(S,1) ‖ S: ill` where `ill` is
/// `skip`, `send_as(Visible)(K,2)` or `send_as(Invisible)(K,2)`; `Tvis = {k}`.
#[derive(Clone, Copy)]
enum SOp {
    Skip,
    SendVisible,
    SendInvisible,
}

fn wf_prog(op: SOp) -> Prog {
    prog(move || {
        let (tx_k, _rx_k) = fifo();
        let (tx_s, _rx_s) = fifo();
        let _k = named("k", move || tx_s.send_msg(1));
        let _s = named("s", move || match op {
            SOp::Skip => {}
            SOp::SendVisible => tx_k.send_msg_as(Visibility::Visible, 2),
            SOp::SendInvisible => tx_k.send_msg_as(Visibility::Invisible, 2),
        });
    })
}

/// Criterion 5 (D5): `A: n := nondet(); if n then send^v(C,1) else
/// send^i(C,1) ‖ C: x := recv_msg()` (non-blocking); spawned `a, c`.
fn branch() -> Prog {
    prog(|| {
        let (tx_c, rx_c) = bag_chan();
        let _a = named("a", move || {
            if crate::nondet() {
                tx_c.send_msg_as(Visibility::Visible, 1);
            } else {
                tx_c.send_msg_as(Visibility::Invisible, 1);
            }
        });
        let _c = named("c", move || {
            let _x: Option<i32> = rx_c.recv_msg();
        });
    })
}

/// Criterion 6 (D6): spawned `d` (skip), `a: send(C,1)`, `c: x := recv^b();
/// if x = 1 then send^v(D,0) else send^i(D,0)`, `b: send(C,2)`; Bag.
fn survivor() -> Prog {
    prog(|| {
        let (tx_c, rx_c) = bag_chan();
        let (tx_d, _rx_d) = bag_chan();
        let _d = named("d", || {});
        let ta = tx_c.clone();
        let _a = named("a", move || ta.send_msg(1));
        let _c = named("c", move || {
            let x: i32 = rx_c.recv_msg_block();
            if x == 1 {
                tx_d.send_msg_as(Visibility::Visible, 0);
            } else {
                tx_d.send_msg_as(Visibility::Invisible, 0);
            }
        });
        let _b = named("b", move || tx_c.send_msg(2));
    })
}

/// Criterion 7′ (D7′): `main` creates `X`'s mailbox (read by nobody), spawns
/// `x: skip` then `v: send^i(X,1); assert(false)` (Impl) / `v: send^i(X,1)`
/// (Spec); with `control`, also `w: skip` (declared instead of `v`).
fn cut_prog(fails: bool, control: bool) -> Prog {
    prog(move || {
        let (tx_x, _rx_x) = fifo();
        let _x = named("x", || {});
        let _v = named("v", move || {
            tx_x.send_msg_as(Visibility::Invisible, 1);
            if fails {
                crate::assert(false);
            }
        });
        if control {
            let _w = named("w", || {});
        }
    })
}

fn fx(name: &str, config: Config, visible: Vec<String>, imp: Prog, spec: Prog) -> Fixture {
    mixed_fixture(
        name.to_string(),
        "mixed_tests.rs (tester)",
        config,
        visible,
        imp,
        spec,
    )
}

// =========================================================================
// Criterion 1 — the server pair
// =========================================================================

/// Expected `(tag, gate, gates_inert)` of the unannotated server pair (D1).
fn c01a_expected(e: Eng) -> (ReportTag, ReportGate, Option<usize>) {
    match e {
        Eng::Enum => (ReportTag::GrowingExhaustion, ReportGate::FreshSend, None),
        Eng::Stateful | Eng::CFirst => (ReportTag::CompleteCoverage, ReportGate::Completion, None),
        Eng::Gated(GatedMode::Exhaustive, _)
        | Eng::Gated(GatedMode::FirstFailure, GatePolicy::Never) => {
            (ReportTag::CompleteCoverage, ReportGate::Completion, Some(2))
        }
        Eng::Gated(GatedMode::FirstFailure, _) => {
            (ReportTag::GrowingExhaustion, ReportGate::FreshSend, Some(0))
        }
    }
}

/// **Criterion 1 (a)** (D1): the unannotated server pair reports exactly once
/// on every engine, mode, policy and selector, at the derived gate with the
/// derived tag; the enumerator's F42 skip is 0, the gated `gates_inert` is 2
/// or 0 as the run reaches completion or prunes; the counter is 0.
#[test]
fn c01a_the_unannotated_server_pair_reports_once_everywhere() {
    let v = vis(&["k", "s"]);
    let (imp, spec) = (server_impl(false, 2), server_spec());
    let mut bad = Vec::new();
    for s in SELECTORS {
        for e in ENGINES {
            let what = format!("{e:?} {s:?}");
            let r = verify(cc(e, cfg(ConsType::FIFO), &v, s, false), &imp, &spec);
            if class(&r) != "reported:1" {
                bad.push(format!("{what}: {}", class(&r)));
                continue;
            }
            let o = outcome(&r);
            let (tag, gate, inert) = c01a_expected(e);
            let rep = &o.reports()[0];
            if (rep.tag(), rep.gate()) != (tag, gate) {
                bad.push(format!("{what}: {:?}@{:?}", rep.tag(), rep.gate()));
            }
            if invisible_ops(&r) != 0 {
                bad.push(format!("{what}: counter {}", invisible_ops(&r)));
            }
            if e == Eng::Enum && o.counters().gate_skipped_inert != 0 {
                bad.push(format!(
                    "{what}: F42 skip {}",
                    o.counters().gate_skipped_inert
                ));
            }
            if let Some(n) = inert {
                let g = o.gated_counters().expect("conformance: gated counters");
                if g.gates_inert != n {
                    bad.push(format!(
                        "{what}: gates_inert {} (expected {n})",
                        g.gates_inert
                    ));
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 1(a):\n  {}",
        bad.join("\n  ")
    );
}

/// **Criterion 1 (b)** (D1): with S's two storage operations `Invisible`,
/// every engine, mode, policy and selector conforms with zero reports and an
/// exhausted state space; `gates_inert = 4` (gated) and `gate_skipped_inert
/// = 4` (enumerator); the counter is 2 on all four engines. Mutant "annotation
/// treated as per-thread" makes every run report.
#[test]
fn c01b_the_annotated_server_pair_conforms_everywhere() {
    let v = vis(&["k", "s"]);
    let (imp, spec) = (server_impl(true, 2), server_spec());
    let mut bad = Vec::new();
    for s in SELECTORS {
        for e in ENGINES {
            let what = format!("{e:?} {s:?}");
            let r = verify(cc(e, cfg(ConsType::FIFO), &v, s, false), &imp, &spec);
            if class(&r) != "conforms" {
                bad.push(format!("{what}: {}", class(&r)));
                continue;
            }
            let o = outcome(&r);
            if o.end() != SearchEnd::StateSpaceExhausted || !o.reports().is_empty() {
                bad.push(format!("{what}: end {:?}", o.end()));
            }
            if invisible_ops(&r) != 2 {
                bad.push(format!(
                    "{what}: counter {} (expected 2)",
                    invisible_ops(&r)
                ));
            }
            if e == Eng::Enum && o.counters().gate_skipped_inert != 4 {
                bad.push(format!(
                    "{what}: F42 skip {}",
                    o.counters().gate_skipped_inert
                ));
            }
            if let Eng::Gated(..) = e {
                let g = o.gated_counters().expect("conformance: gated counters");
                if g.gates_inert != 4 {
                    bad.push(format!("{what}: gates_inert {}", g.gates_inert));
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 1(b):\n  {}",
        bad.join("\n  ")
    );
}

/// **Criterion 1, words and order** (D1): one graph per side in both
/// variants; (a) S's Impl word is `⟨rcv,1⟩⟨snd,1⟩⟨rcv,1⟩⟨snd,2⟩` against
/// Spec's `⟨rcv,1⟩⟨snd,2⟩`; (b) the words agree (`k` = send 1, receive 2;
/// `s` = receive 1, send 2) and `ord` on both sides is the closure of the
/// chain `K.s → S.r → S.s₂ → K.r`; S's storage operations carry
/// `Explicit(Invisible)` and are not visible, D's are not visible.
#[test]
fn c01_words_and_visible_order_of_the_server_pair() {
    let v = vis(&["k", "s"]);
    let one = |imp: Prog| {
        let f = fx("c01", cfg(ConsType::FIFO), v.clone(), imp, server_spec());
        let r = grun(&f, &GridConfig::new(GridEngine::Stateful));
        let GridRaw::Stateful(o) = r.raw else {
            unreachable!("conformance: stateful")
        };
        assert_eq!(o.kept_impl_graphs.len(), 1, "conformance: one Impl graph");
        assert_eq!(o.kept_spec_graphs.len(), 1, "conformance: one Spec graph");
        (o.kept_impl_graphs[0].clone(), o.kept_spec_graphs[0].clone())
    };
    let (ia, sa) = one(server_impl(false, 2));
    let send = |x: i32| obs_text(&Obs::Send(crate::msg::Val::new(x)));
    let recv = |x: i32| obs_text(&Obs::Recv(Some(crate::msg::Val::new(x))));
    assert_eq!(
        word(&ia, &v, "s"),
        vec![recv(1), send(1), recv(1), send(2)],
        "conformance: (a) Impl's S word"
    );
    assert_eq!(
        word(&sa, &v, "s"),
        vec![recv(1), send(2)],
        "conformance: Spec's S word"
    );
    assert_ne!(
        summary(&ia, &v).sig,
        summary(&sa, &v).sig,
        "conformance: (a) sigs differ"
    );

    let (ib, sb) = one(server_impl(true, 2));
    for (side, g) in [("Impl", &ib), ("Spec", &sb)] {
        assert_eq!(
            word(g, &v, "k"),
            vec![send(1), recv(2)],
            "conformance: {side} K word"
        );
        assert_eq!(
            word(g, &v, "s"),
            vec![recv(1), send(2)],
            "conformance: {side} S word"
        );
        assert_eq!(
            ord_of(g, &v),
            set(&["k,0<k,1", "k,0<s,0", "k,0<s,1", "s,0<s,1", "s,0<k,1", "s,1<k,1"]),
            "conformance: {side}: ord is the chain K.s → S.r → S.s₂ → K.r"
        );
    }
    assert_eq!(
        summary(&ib, &v).sig,
        summary(&sb, &v).sig,
        "conformance: (b) sigs agree"
    );
    let s = comm_events(&ib, "s");
    assert_eq!(s.len(), 4, "conformance: S has four communication events");
    let flags: Vec<(Option<Annotation>, bool)> = s
        .iter()
        .map(|e| (annotation(&ib, *e), is_visible(&ib, *e, &v)))
        .collect();
    assert_eq!(
        flags,
        vec![
            (Some(Annotation::Default), true),
            (Some(Annotation::Explicit(Visibility::Invisible)), false),
            (Some(Annotation::Explicit(Visibility::Invisible)), false),
            (Some(Annotation::Default), true),
        ],
        "conformance: S's recorded annotations and visibility"
    );
    for e in comm_events(&ib, "d") {
        assert!(!is_visible(&ib, e, &v), "conformance: D is undeclared");
    }
}

// =========================================================================
// Criterion 2 — status through an invisible block
// =========================================================================

/// **Criterion 2** (D2): one report on every engine, mode, policy and
/// selector, `CompleteCoverage` at `Completion`; the rendering names `s` as
/// blocked; the counter is 1. Words and order agree, statuses differ (S
/// `Blocked` vs `Done`). Mutant "statuses only of threads whose last send or
/// receive is visible" removes the report.
#[test]
fn c02_status_through_an_invisible_block() {
    let v = vis(&["k", "s"]);
    let (imp, spec) = (serverblock_impl(), server_spec());
    let mut bad = Vec::new();
    for s in SELECTORS {
        for e in ENGINES {
            let what = format!("{e:?} {s:?}");
            let r = verify(cc(e, cfg(ConsType::FIFO), &v, s, false), &imp, &spec);
            if class(&r) != "reported:1" {
                bad.push(format!("{what}: {}", class(&r)));
                continue;
            }
            let rep = &outcome(&r).reports()[0];
            if (rep.tag(), rep.gate()) != (ReportTag::CompleteCoverage, ReportGate::Completion) {
                bad.push(format!("{what}: {:?}@{:?}", rep.tag(), rep.gate()));
            }
            // Only the enumerator renders statuses (its diagnostics); the
            // sweeping engines' rendering is pinned by closed tests and shows
            // the graph, where S ends at its `BLK Value` (T-finding T2).
            let shown = format!("{}", r.as_ref().unwrap());
            let named = if e == Eng::Enum {
                shown.contains("blocked") && shown.contains("`s`")
            } else {
                rep.graph_dump().contains("thread \"s\"") && rep.graph_dump().contains("BLK Value")
            };
            if !named {
                bad.push(format!(
                    "{what}: rendering does not name `s` blocked:\n{shown}"
                ));
            }
            if invisible_ops(&r) != 1 {
                bad.push(format!(
                    "{what}: counter {} (expected 1)",
                    invisible_ops(&r)
                ));
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 2:\n  {}",
        bad.join("\n  ")
    );

    let f = fx(
        "c02",
        cfg(ConsType::FIFO),
        v.clone(),
        serverblock_impl(),
        server_spec(),
    );
    let r = grun(&f, &GridConfig::new(GridEngine::Stateful));
    let GridRaw::Stateful(o) = &r.raw else {
        unreachable!("conformance: stateful")
    };
    let (i, sp) = (&o.kept_impl_graphs[0], &o.kept_spec_graphs[0]);
    let (si, ss) = (summary(i, &v), summary(sp, &v));
    for n in ["k", "s"] {
        assert_eq!(
            si.sig.word(n),
            ss.sig.word(n),
            "conformance: {n}'s words agree"
        );
    }
    assert_eq!(si.ord, ss.ord, "conformance: the visible order agrees");
    assert_eq!(
        si.sig.status("s"),
        Some(Status::Blocked),
        "conformance: Impl′'s S"
    );
    assert_eq!(
        ss.sig.status("s"),
        Some(Status::Done),
        "conformance: Spec's S"
    );
    assert_eq!(si.sig.status("k"), Some(Status::Done));
    // The terminal label of S is the `Block{Value}` of the blocked `i` receive.
    let t = tid(i, "s");
    let last = (0..i.thread_size(t) as u32)
        .map(|k| Event::new(t, k))
        .rev()
        .find(|e| !matches!(i.label(*e), LabelEnum::End(_)))
        .expect("conformance: S has labels");
    assert!(
        matches!(i.label(last), LabelEnum::Block(_)),
        "conformance: S's terminal label is a Block: {}",
        i.label(last)
    );
}

// =========================================================================
// Criterion 3 — vpos under mixed visibility
// =========================================================================

/// **Criterion 3** (D3): conformance with no report on every engine; on the
/// Impl graph `vpos(A's v send) = (a,0)`, A's `i` send has no `vpos`; `ord`
/// is `{((a,0),(c,0))}` on both sides. Mutant "count all sends and receives of
/// visible threads in `vpos`" — a false report on stateful, complete-first
/// and gated (or `VPosMap::of`'s converse check panics).
#[test]
fn c03_vpos_under_mixed_visibility() {
    let v = vis(&["a", "c"]);
    let (imp, spec) = (vpos_pair(true), vpos_pair(false));
    let mut bad = Vec::new();
    for e in ENGINES {
        let r = verify(
            cc(e, cfg(ConsType::Bag), &v, Selector::Ltr, false),
            &imp,
            &spec,
        );
        if class(&r) != "conforms" {
            bad.push(format!("{e:?}: {}", class(&r)));
        } else if invisible_ops(&r) != 1 {
            bad.push(format!("{e:?}: counter {} (expected 1)", invisible_ops(&r)));
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 3:\n  {}",
        bad.join("\n  ")
    );

    let f = fx("c03", cfg(ConsType::Bag), v.clone(), imp, spec);
    let r = grun(&f, &GridConfig::new(GridEngine::Stateful));
    let GridRaw::Stateful(o) = &r.raw else {
        unreachable!("conformance: stateful")
    };
    assert_eq!(o.kept_impl_graphs.len(), 1, "conformance: one Impl graph");
    assert_eq!(o.kept_spec_graphs.len(), 1, "conformance: one Spec graph");
    let g = &o.kept_impl_graphs[0];
    let a = comm_events(g, "a");
    assert_eq!(a.len(), 2, "conformance: A's two sends");
    let vp = VPosMap::of(g, &w(g, &v), &v);
    assert!(
        vp.get(a[0]).is_none(),
        "conformance: the `i` send has no vpos"
    );
    let p = vp.get(a[1]).expect("conformance: the `v` send has a vpos");
    assert_eq!(
        (p.thread.as_str(), p.index),
        ("a", 0),
        "conformance: vpos of A's v send"
    );
    for (side, g) in [("Impl", g), ("Spec", &o.kept_spec_graphs[0])] {
        assert_eq!(
            ord_of(g, &v),
            set(&["a,0<c,0"]),
            "conformance: {side}'s ord"
        );
    }
}

// =========================================================================
// Criterion 4 — well-formedness
// =========================================================================

/// The site field of the panic `verify` raises, or `None` if it returned.
fn wf_site(e: Eng, imp: &Prog, spec: &Prog, skip: bool) -> (Option<String>, String) {
    let v = vis(&["k"]);
    let c = cc(e, cfg(ConsType::FIFO), &v, Selector::Ltr, skip);
    match panic_of(|| verify(c, imp, spec)) {
        None => (None, "returned".to_string()),
        Some(p) => (site_field(&p), innermost(&p).to_string()),
    }
}

fn wf_engines() -> [Eng; 5] {
    [
        Eng::Enum,
        Eng::Stateful,
        Eng::CFirst,
        Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
        Eng::Gated(GatedMode::FirstFailure, GatePolicy::Always),
    ]
}

/// **Criterion 4** (D4): an `Explicit(Visible)` on undeclared `s` panics
/// through the entry point with M4's message, its delimited site field
/// exactly (a) `conformance`/`stateful`/`complete-first`/`gated` on the Impl
/// side; (b) `precheck` (enumerator, complete-first, gated) and `stateful`
/// under the default configuration on the Spec side; (c) `inner search`,
/// `stateful`, `complete-first sweep`, `gated sweep` with the precheck
/// skipped. The message names the thread `s`. Mutant "site (i) only": (c) on
/// the enumerator returns.
#[test]
fn c04_an_undeclared_visible_operation_panics_naming_its_site() {
    let ill = wf_prog(SOp::SendVisible);
    let good = wf_prog(SOp::Skip);
    let mut bad = Vec::new();
    let expect = |case: &str, e: Eng| -> &'static str {
        match (case, e) {
            ("a", Eng::Enum) => "conformance",
            ("a", Eng::Stateful) | ("b", Eng::Stateful) | ("c", Eng::Stateful) => "stateful",
            ("a", Eng::CFirst) => "complete-first",
            ("a", Eng::Gated(..)) => "gated",
            ("b", _) => "precheck",
            ("c", Eng::Enum) => "inner search",
            ("c", Eng::CFirst) => "complete-first sweep",
            ("c", Eng::Gated(..)) => "gated sweep",
            _ => unreachable!("conformance: three cases"),
        }
    };
    for (case, imp, spec, skip) in [
        ("a", &ill, &good, false),
        ("b", &good, &ill, false),
        ("c", &good, &ill, true),
    ] {
        for e in wf_engines() {
            let (site, msg) = wf_site(e, imp, spec, skip);
            let want = expect(case, e);
            if site.as_deref() != Some(want) {
                bad.push(format!(
                    "({case}) {e:?}: site {site:?}, expected {want:?}: {msg}"
                ));
                continue;
            }
            if !msg.starts_with("conformance: ") || !msg.contains("undeclared thread `s`") {
                bad.push(format!("({case}) {e:?}: message {msg}"));
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 4:\n  {}",
        bad.join("\n  ")
    );
}

/// **Criterion 4, the accepted cases** (D4): an `Explicit(Invisible)` on the
/// undeclared thread is accepted on every engine, both sides, with and without
/// the precheck (the pair conforms: S is undeclared either way); the
/// ill-formed program under `crate::verify` runs normally.
#[test]
fn c04_an_undeclared_invisible_operation_is_accepted() {
    let v = vis(&["k"]);
    let inv = wf_prog(SOp::SendInvisible);
    let skip = wf_prog(SOp::Skip);
    let mut bad = Vec::new();
    for (imp, spec) in [(&inv, &skip), (&skip, &inv), (&inv, &inv)] {
        for e in wf_engines() {
            for sk in [false, true] {
                let r = verify(cc(e, cfg(ConsType::FIFO), &v, Selector::Ltr, sk), imp, spec);
                if class(&r) != "conforms" {
                    bad.push(format!("{e:?} skip={sk}: {}", class(&r)));
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 4:\n  {}",
        bad.join("\n  ")
    );
    let ill = wf_prog(SOp::SendVisible);
    let stats = crate::verify(cfg(ConsType::FIFO), move || ill());
    assert_eq!(
        stats.execs, 1,
        "conformance: outside conformance the annotation is ignored"
    );
}

// =========================================================================
// Criterion 5 — branch-dependent visibility
// =========================================================================

/// **Criterion 5** (D5): four kept Impl graphs; `A = [Begin, CToss, send]`;
/// for each value C reads, the `n = 0`/`n = 1` graphs disagree on
/// `is_visible((a,2))` and on `sig`; words as derived; the four canonical
/// keys are distinct; the self-conformance pair conforms on every engine.
/// Mutant "visibility by position, cached across graphs" fails the flag
/// assertion.
#[test]
fn c05_branch_dependent_visibility() {
    let v = vis(&["a", "c"]);
    let p = branch();
    let mut bad = Vec::new();
    for e in ENGINES {
        let r = verify(cc(e, cfg(ConsType::Bag), &v, Selector::Ltr, false), &p, &p);
        if class(&r) != "conforms" {
            bad.push(format!("{e:?}: {}", class(&r)));
        } else if invisible_ops(&r) != 1 {
            bad.push(format!("{e:?}: counter {} (expected 1)", invisible_ops(&r)));
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 5:\n  {}",
        bad.join("\n  ")
    );

    let f = fx("c05", cfg(ConsType::Bag), v.clone(), branch(), branch());
    let r = grun(&f, &GridConfig::new(GridEngine::Stateful));
    let GridRaw::Stateful(o) = &r.raw else {
        unreachable!("conformance: stateful")
    };
    let gs = &o.kept_impl_graphs;
    assert_eq!(gs.len(), 4, "conformance: four complete Impl graphs");
    // (n, C reads something, is_visible((a,2)), a's word shape, c's word shape, sig)
    let mut rows = Vec::new();
    for g in gs {
        let a = tid(g, "a");
        assert!(
            matches!(g.label(Event::new(a, 0)), LabelEnum::Begin(_)),
            "conformance: (a,0)"
        );
        let LabelEnum::CToss(t) = g.label(Event::new(a, 1)) else {
            panic!(
                "conformance: (a,1) is the CToss: {}",
                g.label(Event::new(a, 1))
            )
        };
        let n = t.result();
        let snd = Event::new(a, 2);
        assert!(
            matches!(g.label(snd), LabelEnum::SendMsg(_)),
            "conformance: (a,2)"
        );
        let expect = Annotation::Explicit(if n {
            Visibility::Visible
        } else {
            Visibility::Invisible
        });
        assert_eq!(
            annotation(g, snd),
            Some(expect),
            "conformance: (a,2)'s annotation, n = {n}"
        );
        let c_reads = match g.label(comm_events(g, "c")[0]) {
            LabelEnum::RecvMsg(r) => r.rf().is_some(),
            other => panic!("conformance: C's receive: {other}"),
        };
        rows.push((
            n,
            c_reads,
            is_visible(g, snd, &v),
            shape(g, &v, "a"),
            shape(g, &v, "c"),
            summary(g, &v).sig,
        ));
    }
    for reads in [true, false] {
        let pair: Vec<_> = rows.iter().filter(|r| r.1 == reads).collect();
        assert_eq!(pair.len(), 2, "conformance: two graphs read {reads}");
        let (one, zero) = if pair[0].0 {
            (pair[0], pair[1])
        } else {
            (pair[1], pair[0])
        };
        assert!(one.0 && !zero.0, "conformance: one graph per nondet value");
        assert!(one.2, "conformance: n = 1: (a,2) is visible");
        assert!(!zero.2, "conformance: n = 0: (a,2) is not visible");
        assert_eq!(
            (one.3.as_str(), zero.3.as_str()),
            ("s", ""),
            "conformance: a's words"
        );
        let c = if reads { "r" } else { "r⊥" };
        assert_eq!(
            (one.4.as_str(), zero.4.as_str()),
            (c, c),
            "conformance: c's words"
        );
        assert_ne!(
            one.5, zero.5,
            "conformance: the sigs differ (C reads {reads})"
        );
    }
    let keys: BTreeSet<String> = gs.iter().map(|g| canon_key(g, &v)).collect();
    assert_eq!(keys.len(), 4, "conformance: four distinct canonical keys");
}

// =========================================================================
// Criterion 6 — revisit survivor visibility
// =========================================================================

type Seen = Rc<RefCell<Vec<ExecutionGraph>>>;

/// **Criterion 6** (D6): under `GatedOuter` with a gate sink, B's backward
/// `RevisitApply` of C's receive has a `g1` with no send of C (C's
/// `send^v(D,0)` is not a survivor) and C's receive reading B's 2; the next
/// execution's completion carries C's re-installed send `Explicit(Invisible)`;
/// every survivor's recorded annotation equals the re-created label's; the
/// pair conforms with itself on every engine.
#[test]
fn c06_revisit_survivors_keep_their_annotations() {
    let v = vis(&["a", "b", "c"]);
    let revisits: Seen = Default::default();
    let completions: Seen = Default::default();
    let gate_sink: GateSink = {
        let revisits = Rc::clone(&revisits);
        Box::new(
            move |gate: Gate, _at: &GateAt, g: &ExecutionGraph, _st: &MustState| {
                if gate == Gate::RevisitApply {
                    revisits.borrow_mut().push(g.clone());
                }
                GateVerdict::Continue
            },
        )
    };
    let sink: CompletionSink = {
        let completions = Rc::clone(&completions);
        Box::new(move |g: &ExecutionGraph, _: &MustState| {
            completions.borrow_mut().push(g.clone());
            SinkVerdict::Continue
        })
    };
    let e = enumerate(
        EnumRun {
            config: cfg(ConsType::Bag),
            visible: v.clone(),
            mode: ConfMode::GatedOuter,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: Some(gate_sink),
        },
        &survivor(),
    );
    assert_eq!(
        e.end,
        SearchEnd::StateSpaceExhausted,
        "conformance: exhausted"
    );
    let revisits = revisits.borrow();
    let completions = completions.borrow();
    assert_eq!(revisits.len(), 1, "conformance: one backward RevisitApply");
    assert_eq!(
        completions.len(),
        2,
        "conformance: two complete graphs (x = 1, x = 2)"
    );
    let g1 = &revisits[0];
    let c = comm_events(g1, "c");
    assert_eq!(
        c.len(),
        1,
        "conformance: g1 holds C's receive and no send of C: {g1}"
    );
    let LabelEnum::RecvMsg(r) = g1.label(c[0]) else {
        unreachable!("conformance: C's receive")
    };
    let b_send = comm_events(g1, "b")[0];
    assert_eq!(
        r.rf(),
        Some(b_send),
        "conformance: the revisited receive reads B's send"
    );

    // The completions in order: x = 1 first (before the revisit), then x = 2.
    let flags: Vec<Option<Annotation>> = completions
        .iter()
        .map(|g| annotation(g, comm_events(g, "c")[1]))
        .collect();
    assert_eq!(
        flags,
        vec![
            Some(Annotation::Explicit(Visibility::Visible)),
            Some(Annotation::Explicit(Visibility::Invisible)),
        ],
        "conformance: C's send per execution"
    );
    let after = &completions[1];
    assert!(
        !is_visible(after, comm_events(after, "c")[1], &v),
        "conformance: the re-installed send is not visible"
    );
    // Every survivor's annotation equals the next execution's label there.
    for t in g1.thread_ids() {
        for i in 0..g1.thread_size(t) as u32 {
            let e = Event::new(t, i);
            if let Some(a) = annotation(g1, e) {
                assert_eq!(annotation(after, e), Some(a), "conformance: survivor {e}");
            }
        }
    }

    let p = survivor();
    let mut bad = Vec::new();
    for e in ENGINES {
        let r = verify(cc(e, cfg(ConsType::Bag), &v, Selector::Ltr, false), &p, &p);
        if class(&r) != "conforms" {
            bad.push(format!("{e:?}: {}", class(&r)));
        } else if invisible_ops(&r) != 1 {
            bad.push(format!("{e:?}: counter {} (expected 1)", invisible_ops(&r)));
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 6:\n  {}",
        bad.join("\n  ")
    );
}

// =========================================================================
// Criterion 7 — the annotated `send(K,3)` variant
// =========================================================================

/// **Criterion 7** (D7): the annotated server with `S: send(K,3)` is
/// reported on every engine, mode, policy and selector, each report
/// certified by Part 6's oracle; the enumerator and gated first-failure
/// under `Always` (and `Budget(1)`) report the growing graph at S's reply
/// (`FreshSend`); every other run one `CompleteCoverage` at completion. The
/// counter is 2 where the Impl graph completes, 0 where the run prunes first.
#[test]
fn c07_the_annotated_reply3_variant_is_reported_and_certified() {
    let v = vis(&["k", "s"]);
    let f = fx(
        "c07",
        cfg(ConsType::FIFO),
        v,
        server_impl(true, 3),
        server_spec(),
    );
    let fam = families(&f);
    assert!(fam.some_impl_uncovered(), "conformance: a violation exists");
    let mut bad = Vec::new();
    for s in SELECTORS {
        for (e, c) in grid_engines(s) {
            let what = format!("{e:?} {s:?}");
            let r = grun(&f, &c);
            let reps = reports_of(&r);
            let growing = matches!(
                e,
                Eng::Enum
                    | Eng::Gated(GatedMode::FirstFailure, GatePolicy::Always)
                    | Eng::Gated(GatedMode::FirstFailure, GatePolicy::Budget(1))
            );
            let want = if growing {
                (ReportTag::GrowingExhaustion, "FreshSend", 0)
            } else {
                (ReportTag::CompleteCoverage, "Completion", 2)
            };
            if reps.len() != 1 || (reps[0].tag, reps[0].site.as_str()) != (want.0, want.1) {
                let got: Vec<String> = reps
                    .iter()
                    .map(|r| format!("{:?}@{}", r.tag, r.site))
                    .collect();
                bad.push(format!("{what}: {got:?}"));
                continue;
            }
            if growing {
                let g = reps[0].graph;
                if word(g, &f.visible, "s").len() != 2 {
                    bad.push(format!("{what}: the report is not at S's reply"));
                }
            }
            if grid_counter(&r) != want.2 {
                bad.push(format!(
                    "{what}: counter {} (expected {})",
                    grid_counter(&r),
                    want.2
                ));
            }
            certify_all(&fam, &r, &what);
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 7:\n  {}",
        bad.join("\n  ")
    );
}

// =========================================================================
// Criterion 7′ — the early-error cut under mixed visibility
// =========================================================================

/// The configurations of criterion 7′: the four engines, the gated one in
/// both modes, and complete-first with the cut on.
fn c07p_configs() -> Vec<(&'static str, GridConfig)> {
    let mut cut = GridConfig::new(GridEngine::CompleteFirst);
    cut.early_error_cut = true;
    vec![
        ("enumerator", GridConfig::new(GridEngine::Enumerator)),
        ("stateful", GridConfig::new(GridEngine::Stateful)),
        ("cfirst", GridConfig::new(GridEngine::CompleteFirst)),
        ("cfirst+cut", cut),
        (
            "gated exh",
            GridConfig::new(GridEngine::Gated).gated(GatedMode::Exhaustive, GatePolicy::Always),
        ),
        (
            "gated ff never",
            GridConfig::new(GridEngine::Gated).gated(GatedMode::FirstFailure, GatePolicy::Never),
        ),
        (
            "gated ff always",
            GridConfig::new(GridEngine::Gated).gated(GatedMode::FirstFailure, GatePolicy::Always),
        ),
    ]
}

/// The notes a raw run carries (invisible-thread failures).
fn raw_notes(r: &GridResult) -> Vec<String> {
    let ds = match &r.raw {
        GridRaw::Enumerator(o) => &o.diagnostics,
        GridRaw::Stateful(o) => &o.impl_notes,
        GridRaw::CompleteFirst(o) => &o.impl_notes,
        GridRaw::Gated(o) => &o.impl_notes,
        GridRaw::Verdict(_) => return Vec::new(),
    };
    ds.iter()
        .map(|d| format!("{:?}@{}", d.reason, d.thread))
        .collect()
}

/// **Criterion 7′** (D7′): the enumerator `VisibleError` at `NotAGate`;
/// stateful, gated (both modes) and complete-first with the cut off one
/// `CompleteCoverage` at completion; complete-first with the cut on one cut
/// report (`cut_reports = 1`); every report certified; **no notes** on any
/// unmutated run. The public path agrees (tags, `cut_reports`, empty notes).
/// The mutant "cut keyed on the visibility of the thread's last send or
/// receive" is killed by every run here.
#[test]
fn c07p_the_early_error_cut_is_thread_keyed() {
    let v = vis(&["v"]);
    let f = fx(
        "c07p",
        cfg(ConsType::FIFO),
        v.clone(),
        cut_prog(true, false),
        cut_prog(false, false),
    );
    let fam = families(&f);
    let mut bad = Vec::new();
    for (name, c) in c07p_configs() {
        let r = grun(&f, &c);
        let reps = reports_of(&r);
        let want: (ReportTag, &str, usize) = match name {
            "enumerator" => (ReportTag::VisibleError, "NotAGate", 0),
            "cfirst+cut" => (ReportTag::VisibleError, "NotAGate", 0),
            _ => (ReportTag::CompleteCoverage, "Completion", 1),
        };
        let got: Vec<String> = reps
            .iter()
            .map(|r| format!("{:?}@{}", r.tag, r.site))
            .collect();
        if got != vec![format!("{:?}@{}", want.0, want.1)] {
            bad.push(format!("{name}: {got:?}"));
        }
        if !raw_notes(&r).is_empty() {
            bad.push(format!("{name}: notes {:?}", raw_notes(&r)));
        }
        if grid_counter(&r) != want.2 {
            bad.push(format!(
                "{name}: counter {} (expected {})",
                grid_counter(&r),
                want.2
            ));
        }
        if let GridRaw::CompleteFirst(o) = &r.raw {
            let n = if name == "cfirst+cut" { 1 } else { 0 };
            if o.counters.cut_reports != n {
                bad.push(format!("{name}: cut_reports {}", o.counters.cut_reports));
            }
        }
        certify_all(&fam, &r, name);
    }
    // The public path.
    let (imp, spec) = (cut_prog(true, false), cut_prog(false, false));
    for e in ENGINES {
        let r = verify(
            cc(e, cfg(ConsType::FIFO), &v, Selector::Ltr, false),
            &imp,
            &spec,
        );
        let o = outcome(&r);
        let want = if e == Eng::Enum {
            (ReportTag::VisibleError, ReportGate::NotAGate)
        } else {
            (ReportTag::CompleteCoverage, ReportGate::Completion)
        };
        let got: Vec<_> = o.reports().iter().map(|r| (r.tag(), r.gate())).collect();
        if got != vec![want] || !o.notes().is_empty() {
            bad.push(format!("public {e:?}: {got:?} notes {:?}", o.notes()));
        }
    }
    let c = ConfBuilder::new()
        .config(cfg(ConsType::FIFO))
        .visible_threads(v.clone())
        .engine(Engine::CompleteFirst)
        .early_error_cut(true)
        .build()
        .expect("conformance: in scope");
    let r = verify(c, &imp, &spec);
    let o = outcome(&r);
    let got: Vec<_> = o.reports().iter().map(|r| (r.tag(), r.gate())).collect();
    if got != vec![(ReportTag::VisibleError, ReportGate::NotAGate)]
        || o.cfirst_counters().map(|c| c.cut_reports) != Some(1)
        || !o.notes().is_empty()
    {
        bad.push(format!("public cfirst+cut: {got:?} {:?}", o.notes()));
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 7′:\n  {}",
        bad.join("\n  ")
    );
}

/// **Criterion 7′, the control** (D7′): `v` undeclared, `w: skip` declared —
/// no report, an `InvisibleThread` note naming `v`, on every engine.
#[test]
fn c07p_the_control_takes_the_invisible_path() {
    let v = vis(&["w"]);
    let (imp, spec) = (cut_prog(true, true), cut_prog(false, true));
    let mut bad = Vec::new();
    for e in ENGINES {
        let r = verify(
            cc(e, cfg(ConsType::FIFO), &v, Selector::Ltr, false),
            &imp,
            &spec,
        );
        if class(&r) != "conforms" {
            bad.push(format!("{e:?}: {}", class(&r)));
            continue;
        }
        let notes = outcome(&r).notes();
        let named_v = notes
            .iter()
            .filter(|n| matches!(n, crate::conformance::report::ConfNote::InvisibleThread { thread, .. } if thread == "v"))
            .count();
        if named_v != 1 {
            bad.push(format!("{e:?}: notes {notes:?}"));
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 7′ control:\n  {}",
        bad.join("\n  ")
    );
}

// =========================================================================
// Criterion 8 — the embedding regression (serde clauses; the grid elsewhere)
// =========================================================================

/// **Criterion 8, serde** (D8): an unannotated label's JSON carries no
/// annotation key, and a `ReplaySnapshot` of an unannotated report holds none;
/// an annotated label round-trips with its annotation; a JSON without the
/// field loads as `Default`.
#[test]
fn c08_serde_of_the_annotation() {
    let v = vis(&["k", "s"]);
    let f = fx(
        "c08",
        cfg(ConsType::FIFO),
        v,
        server_impl(true, 2),
        server_spec(),
    );
    let r = grun(&f, &GridConfig::new(GridEngine::Stateful));
    let GridRaw::Stateful(o) = &r.raw else {
        unreachable!("conformance: stateful")
    };
    let g = &o.kept_impl_graphs[0];
    let s = comm_events(g, "s");
    // s[0]: Default receive; s[1]: Explicit(Invisible) send; s[2]: receive.
    for (e, annotated) in [(s[0], false), (s[1], true), (s[2], true), (s[3], false)] {
        let label = g.label(e).clone();
        let json = serde_json::to_string(&label).expect("conformance: serialize a label");
        assert_eq!(
            json.contains("annotation"),
            annotated,
            "conformance: {e}: annotation key present iff annotated: {json}"
        );
        let back: LabelEnum = serde_json::from_str(&json).expect("conformance: deserialize");
        assert_eq!(
            label_annotation(&back),
            annotation(g, e),
            "conformance: {e}: round trip"
        );
        if annotated {
            let stripped = strip_annotation(&json);
            assert!(
                !stripped.contains("annotation"),
                "conformance: stripped: {stripped}"
            );
            let old: LabelEnum =
                serde_json::from_str(&stripped).expect("conformance: an old label loads");
            assert_eq!(
                label_annotation(&old),
                Some(Annotation::Default),
                "conformance: a JSON without the field loads as Default"
            );
        }
    }
    // A snapshot of an unannotated report: no annotation key anywhere.
    let f = fx(
        "c08u",
        cfg(ConsType::FIFO),
        vis(&["k", "s"]),
        server_impl(false, 2),
        server_spec(),
    );
    let r = grun(&f, &GridConfig::new(GridEngine::Stateful));
    let GridRaw::Stateful(o) = &r.raw else {
        unreachable!("conformance: stateful")
    };
    assert_eq!(o.reports.len(), 1, "conformance: one report");
    match &o.reports[0].1 {
        ReplaySnapshot::Serialized(j) => {
            assert!(
                j.contains("SendMsg"),
                "conformance: the snapshot holds sends"
            );
            assert!(
                !j.contains("annotation"),
                "conformance: an unannotated snapshot"
            );
        }
        other => panic!("conformance: snapshot {other:?}"),
    }
}

fn label_annotation(l: &LabelEnum) -> Option<Annotation> {
    match l {
        LabelEnum::SendMsg(s) => Some(s.annotation()),
        LabelEnum::RecvMsg(r) => Some(r.annotation()),
        _ => None,
    }
}

/// The JSON with its `"annotation":…` member removed (the pre-Part-7 form).
fn strip_annotation(json: &str) -> String {
    let mut v: serde_json::Value = serde_json::from_str(json).expect("conformance: JSON");
    fn strip(v: &mut serde_json::Value) {
        match v {
            serde_json::Value::Object(m) => {
                m.remove("annotation");
                m.values_mut().for_each(strip);
            }
            serde_json::Value::Array(a) => a.iter_mut().for_each(strip),
            _ => {}
        }
    }
    strip(&mut v);
    v.to_string()
}

// =========================================================================
// Criterion 9 — candidate visibility without replay
// =========================================================================

/// Criterion 9's program (D9): spawned `s`, `a`, `d`; `A: send(S,1) ‖ D:
/// send(D,1) ‖ S: y := recv()` (non-blocking; with `invisible`, annotated
/// `Invisible`).
fn c09_prog(invisible: bool) -> impl Fn() + Send + Sync + Clone + 'static {
    move || {
        let s = named("s", move || {
            let _y: Option<i32> = if invisible {
                crate::recv_msg_as(Visibility::Invisible)
            } else {
                crate::recv_msg()
            };
        });
        let sid = s.thread().id();
        let _a = named("a", move || crate::send_msg(sid, 1));
        let _d = named("d", || {
            let me = thread::current().id();
            crate::send_msg(me, 1)
        });
    }
}

/// The parent (both sends installed, consistent), S's receive offer on it,
/// and the two sends.
fn c09_parent(
    invisible: bool,
) -> (
    ExecutionGraph,
    crate::conformance::probe::Offer,
    Event,
    Event,
) {
    use crate::conformance::prober::{install, probe_from};
    let config = cfg(ConsType::Bag);
    let p = c09_prog(invisible);
    let first = probe_from(config.clone(), ExecutionGraph::default(), p.clone());
    let (offers, mut g) = first.into_parts();
    for o in offers.iter().filter(|o| o.kind() == "send") {
        g = install(config.clone(), g, o);
    }
    let second = probe_from(config, g, p);
    let (offers, parent) = second.into_parts();
    let recv = offers
        .into_iter()
        .find(|o| o.kind() == "recv")
        .expect("conformance: S's receive is offered");
    let a = comm_events(&parent, "a")[0];
    let d = comm_events(&parent, "d")[0];
    (parent, recv, a, d)
}

/// The candidate built with `Must::with_initial_graph` + `probe_install` +
/// `probe_set_rf`, bypassing `install_recv`.
fn c09_candidate(
    parent: &ExecutionGraph,
    offer: &crate::conformance::probe::Offer,
    src: Event,
) -> ExecutionGraph {
    let mut m = Must::with_initial_graph(cfg(ConsType::Bag), parent.clone());
    let pos = m.probe_install(offer.label().clone());
    m.probe_set_rf(pos, Some(src));
    m.take_graph()
}

/// **Criterion 9** (D9): the candidate (S reads D's send, which is not
/// among the offered sources) follows the outer graph (S reads A's 1); no
/// execution begins during the evaluation; existing labels keep the parent's
/// annotations; the new receive is visible. The variant (`Invisible`): not
/// visible, S's word empty, `follows` true. Mutant "flag from the proposed
/// source's thread" fails the flag assertion.
#[test]
fn c09_candidate_visibility_without_replay() {
    use crate::conformance::prober::install_recv;
    let v = vis(&["a", "s"]);
    for invisible in [false, true] {
        let (parent, offer, a, d) = c09_parent(invisible);
        assert_eq!(
            offer.sources(),
            &[a],
            "conformance: the consistent sources are A's send"
        );
        let outer = install_recv(cfg(ConsType::Bag), parent.clone(), &offer, Some(a));
        reset_executions_begun();
        let cand = c09_candidate(&parent, &offer, d);
        let r = comm_events(&cand, "s")[0];
        let (wc, wo) = (w(&cand, &v), w(&outer, &v));
        let follows_now = follows(&cand, &outer, &wc, &wo, &v);
        let flag = is_visible(&cand, r, &v);
        let s_word = shape(&cand, &v, "s");
        let a_word = shape(&cand, &v, "a");
        assert_eq!(
            executions_begun(),
            0,
            "conformance: the evaluation began an execution"
        );
        assert!(
            follows_now,
            "conformance: follows on the candidate ({invisible})"
        );
        assert_eq!(a_word, "s", "conformance: A's word");
        match cand.label(r) {
            LabelEnum::RecvMsg(l) => assert_eq!(l.rf(), Some(d), "conformance: rf = D's send"),
            other => panic!("conformance: {other}"),
        }
        if invisible {
            assert!(!flag, "conformance: the Invisible receive is not visible");
            assert_eq!(s_word, "", "conformance: S's word is ε");
        } else {
            assert!(
                flag,
                "conformance: the new receive is visible (its issuing operation's)"
            );
            assert_eq!(s_word, "r", "conformance: S's word is one receive");
            assert_eq!(
                word(&cand, &v, "s"),
                word(&outer, &v, "s"),
                "conformance: of 1"
            );
        }
        for t in parent.thread_ids() {
            for i in 0..parent.thread_size(t) as u32 {
                let e = Event::new(t, i);
                assert_eq!(
                    annotation(&cand, e),
                    annotation(&parent, e),
                    "conformance: {e}"
                );
            }
        }
    }
    // The counter counts: a probe begins one execution.
    reset_executions_begun();
    let _ = c09_parent(false);
    assert!(
        executions_begun() >= 2,
        "conformance: the counter sees probes"
    );
}

/// **Criterion 9, the consistency guard**: `install_recv` refuses D's send.
#[test]
#[should_panic(expected = "is not among the sources offered")]
fn c09_install_recv_refuses_the_inconsistent_source() {
    let (parent, offer, _a, d) = c09_parent(false);
    let _ = crate::conformance::prober::install_recv(cfg(ConsType::Bag), parent, &offer, Some(d));
}

// =========================================================================
// Criterion 10 — benchmarks and the counter
// =========================================================================

/// The tester's two corpus picks (criterion 10): mixed variants of the
/// generator's `InvisibleRefactor` shape (conforming) and `VisibleMutation`
/// shape (violating). In each, `main` — visible — performs a storage
/// round-trip `send^i(R, v); y := recv^{b,i}()` through an invisible relay
/// `r` before its visible `send(C, v)`; the Spec sends directly (`v = 1`;
/// the mutation's Spec sends `v + 1`). FIFO, `Tvis = {main, c}`.
fn corpus_mixed(spec_value: Option<i32>) -> (Prog, Prog) {
    let imp = prog(|| {
        let c = named("c", || {
            let _x: i32 = crate::recv_msg_block();
        });
        let cid = c.thread().id();
        let me = thread::current().id();
        let r = named("r", move || {
            let x: i32 = crate::recv_msg_block();
            crate::send_msg(me, x);
        });
        crate::send_msg_as(r.thread().id(), Visibility::Invisible, 1);
        let y: i32 = crate::recv_msg_block_as(Visibility::Invisible);
        crate::send_msg(cid, y);
    });
    let w = spec_value.unwrap_or(1);
    let spec = prog(move || {
        let c = named("c", || {
            let _x: i32 = crate::recv_msg_block();
        });
        // The relay is spawned on the Spec side too so both sides share
        // `Tid_v`'s spawn prologue; it never runs a communication.
        let _r = named("r", || {});
        crate::send_msg(c.thread().id(), w);
    });
    (imp, spec)
}

fn tester_corpus_picks() -> Vec<Fixture> {
    let mc = vis(&["main", "c"]);
    let (ci, cs) = corpus_mixed(None);
    let (vi, vs) = corpus_mixed(Some(2));
    vec![
        fx(
            "mixed/corpus/InvisibleRefactor",
            cfg(ConsType::FIFO),
            mc.clone(),
            ci,
            cs,
        ),
        fx(
            "mixed/corpus/VisibleMutation",
            cfg(ConsType::FIFO),
            mc,
            vi,
            vs,
        ),
    ]
}

/// Criterion 10's expected `(violation, counter on a completing run)` per
/// fixture name (D10).
fn c10_expected(name: &str) -> (bool, usize) {
    match name {
        n if n.ends_with("/annotated") => (false, 2 * rounds_of(n)),
        n if n.ends_with("/unannotated") => (true, 0),
        n if n.ends_with("/reply3") => (true, 2 * rounds_of(n)),
        "mixed/serverblock" => (true, 1),
        "mixed/branch" => (false, 1),
        "mixed/cut" => (true, 1),
        "mixed/corpus/InvisibleRefactor" => (false, 2),
        "mixed/corpus/VisibleMutation" => (true, 2),
        other => panic!("conformance: unknown fixture {other}"),
    }
}

fn rounds_of(name: &str) -> usize {
    let r = name
        .split('/')
        .find(|p| p.starts_with('r') && p[1..].parse::<usize>().is_ok())
        .expect("conformance: a server fixture names its rounds");
    r[1..].parse().expect("conformance: rounds")
}

fn c10_configs() -> Vec<GridConfig> {
    vec![
        GridConfig::new(GridEngine::Enumerator)
            .memo(true)
            .instrumented(true)
            .budget(crate::conformance::grid::Budget::Unlimited),
        GridConfig::new(GridEngine::Stateful),
        GridConfig::new(GridEngine::CompleteFirst),
        GridConfig::new(GridEngine::Gated).gated(GatedMode::Exhaustive, GatePolicy::Always),
        GridConfig::new(GridEngine::Gated).gated(GatedMode::FirstFailure, GatePolicy::Always),
    ]
}

/// Does the run complete the Impl graph without a prune before completion?
fn completes(c: &GridConfig, name: &str) -> bool {
    let (violation, _) = c10_expected(name);
    match c.engine {
        GridEngine::Stateful | GridEngine::CompleteFirst => true,
        // First-failure prunes only at a growing gate report; serverblock's
        // and the cut pair's reports are at completion.
        GridEngine::Gated => {
            c.gated_mode == GatedMode::Exhaustive
                || !violation
                || name == "mixed/serverblock"
                || name == "mixed/cut"
        }
        // The enumerator prunes at its report unless the report is at
        // completion (serverblock's statuses; the conforming pairs).
        _ => !violation || name == "mixed/serverblock",
    }
}

/// **Criterion 10** (D10): the lead's fourteen `mixed_fixtures()` (the
/// tester's two corpus picks among them), each under the five configurations of
/// [`c10_configs`]: the verdict equals the oracle family's, every report is
/// certified, and `invisible_ops_of_visible_threads` is the derived value —
/// `2r` on the annotated server family where the graph completes, 0 where the
/// run prunes first, 1 on serverblock/branch/cut. With `P4_DIFF_TABLES` set,
/// the rows (Part 6's columns, the counter appended) are written there.
#[test]
fn c10_mixed_benchmarks_and_the_counter() {
    let fixtures = mixed_fixtures();
    // 3 rounds × 3 variants + serverblock + branch + cut + the tester's two
    // corpus picks, registered by the lead (follow-up to T1) = 14.
    assert_eq!(
        fixtures.len(),
        14,
        "conformance: the lead's registry entries"
    );
    let mut bad = Vec::new();
    let mut rows: Vec<Row> = Vec::new();
    for f in &fixtures {
        let fam = families(f);
        let (violation, n) = c10_expected(&f.name);
        if fam.some_impl_uncovered() != violation {
            bad.push(format!(
                "{}: oracle violation = {}",
                f.name,
                fam.some_impl_uncovered()
            ));
        }
        for c in c10_configs() {
            let what = format!("{} {}", f.name, c.label());
            let r = grun(f, &c);
            let reported = !reports_of(&r).is_empty();
            if reported != violation {
                bad.push(format!("{what}: reported = {reported}"));
            }
            let want = if completes(&c, &f.name) { n } else { 0 };
            if grid_counter(&r) != want {
                bad.push(format!(
                    "{what}: counter {} (expected {want})",
                    grid_counter(&r)
                ));
            }
            certify_all(&fam, &r, &what);
            let mut row = row_of(&r);
            row.push((
                "invisible_ops_of_visible_threads",
                grid_counter(&r).to_string(),
            ));
            rows.push(row);
        }
    }
    if std::env::var_os("P4_DIFF_TABLES").is_some() {
        let mut t = Tables::open();
        t.table(
            "P4-MIXED criterion 10: the mixed benchmarks and the counter",
            &rows,
        );
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 10:\n  {}",
        bad.join("\n  ")
    );
}

/// **Criterion 10, the registry against the criteria**: each of the lead's
/// fixtures is checked against this file's independent copy where one exists
/// — the same canonical Impl and Spec families (the server family at
/// `r = 1`, serverblock, branch, cut, and the two corpus picks against
/// this file's `corpus_mixed`).
#[test]
fn c10_the_registry_matches_the_criteria_fixtures() {
    let lead = mixed_fixtures();
    let by = |n: &str| {
        lead.iter()
            .find(|f| f.name == n)
            .unwrap_or_else(|| panic!("conformance: no `{n}` in mixed_fixtures()"))
    };
    let fam_keys = |f: &Fixture| -> (BTreeSet<String>, BTreeSet<String>) {
        let r = grun(f, &GridConfig::new(GridEngine::Stateful));
        let GridRaw::Stateful(o) = &r.raw else {
            unreachable!("conformance: stateful")
        };
        (
            o.kept_impl_graphs
                .iter()
                .map(|g| canon_key(g, &f.visible))
                .collect(),
            o.kept_spec_graphs
                .iter()
                .map(|g| canon_key(g, &f.visible))
                .collect(),
        )
    };
    let ks = vis(&["k", "s"]);
    let mine = [
        (
            "mixed/server/r1/annotated",
            fx(
                "m",
                cfg(ConsType::FIFO),
                ks.clone(),
                server_impl(true, 2),
                server_spec(),
            ),
        ),
        (
            "mixed/server/r1/unannotated",
            fx(
                "m",
                cfg(ConsType::FIFO),
                ks.clone(),
                server_impl(false, 2),
                server_spec(),
            ),
        ),
        (
            "mixed/server/r1/reply3",
            fx(
                "m",
                cfg(ConsType::FIFO),
                ks.clone(),
                server_impl(true, 3),
                server_spec(),
            ),
        ),
        (
            "mixed/serverblock",
            fx(
                "m",
                cfg(ConsType::FIFO),
                ks,
                serverblock_impl(),
                server_spec(),
            ),
        ),
        (
            "mixed/branch",
            fx(
                "m",
                cfg(ConsType::Bag),
                vis(&["a", "c"]),
                branch(),
                branch(),
            ),
        ),
        (
            "mixed/cut",
            fx(
                "m",
                cfg(ConsType::FIFO),
                vis(&["v"]),
                cut_prog(true, false),
                cut_prog(false, false),
            ),
        ),
    ];
    let picks = tester_corpus_picks();
    let mine: Vec<(&str, Fixture)> = mine
        .into_iter()
        .chain(picks.into_iter().map(|f| {
            let n: &str = if f.name.ends_with("InvisibleRefactor") {
                "mixed/corpus/InvisibleRefactor"
            } else {
                "mixed/corpus/VisibleMutation"
            };
            (n, f)
        }))
        .collect();
    for (name, f) in mine {
        let l = by(name);
        assert_eq!(l.visible, f.visible, "conformance: {name}: visible set");
        assert_eq!(
            fam_keys(l),
            fam_keys(&f),
            "conformance: {name}: families differ"
        );
    }
}

// =========================================================================
// M3 — the closed API surface records its annotation (every twin)
// =========================================================================

/// **M3** (criterion 12's `lib.rs`/`channel.rs` entries): each of the 18
/// `lib.rs` and 13 `channel.rs` `_as` twins records `Explicit(α)` on its label
/// — a twin that forwarded `Default`, or a fixed `α`, fails here. `s` issues
/// the six `lib.rs` sends (to `r`'s mailbox) and the six `Sender` sends (to
/// `X`) annotated `Invisible`, then six plain sends to `Y`; `r` issues the six
/// `lib.rs` receives, the seven `Receiver` receives on `X` and the six selects
/// on `Y`, all `Invisible`. One execution (`testing::run_once`, no
/// conformance context).
#[test]
fn m3_every_twin_records_its_annotation() {
    use crate::Visibility::Invisible as I;
    let p = || {
        let (tx_x, rx_x) = bag_chan();
        let (tx_y, rx_y) = bag_chan();
        let r = named("r", move || {
            let any2 = |_: ThreadId, _: Option<u32>| true;
            let anyv = |_: ThreadId, _: Option<Vec<u32>>| true;
            let _: Option<i32> = crate::recv_msg_as(I);
            let _: Option<i32> = crate::recv_tagged_msg_as(I, any2);
            let _: Option<i32> = crate::recv_vec_tagged_msg_as(I, anyv);
            let _: i32 = crate::recv_msg_block_as(I);
            let _: i32 = crate::recv_tagged_msg_block_as(I, any2);
            let _: i32 = crate::recv_vec_tagged_msg_block_as(I, anyv);
            let _ = rx_x.recv_msg_as(I);
            let _ = rx_x.recv_tagged_msg_as(I, |_| true);
            let _ = rx_x.recv_vec_tagged_msg_as(I, |_| true);
            let _ = rx_x.recv_msg_block_as(I);
            let _ = rx_x.recv_tagged_msg_block_as(I, |_| true);
            let _ = rx_x.recv_vec_tagged_msg_block_as(I, |_| true);
            let _ = rx_x.try_recv_as(I);
            let ys = [&rx_y];
            let m = CommunicationModel::NoOrder;
            let _ = crate::select_msg_as(I, ys.iter(), m);
            let _ = crate::select_tagged_msg_as(I, ys.iter(), m, any2);
            let _ = crate::select_vec_tagged_msg_as(I, ys.iter(), m, anyv);
            let _ = crate::select_msg_block_as(I, ys.iter(), m);
            let _ = crate::select_tagged_msg_block_as(I, ys.iter(), m, any2);
            let _ = crate::select_vec_tagged_msg_block_as(I, ys.iter(), m, anyv);
        });
        let rid = r.thread().id();
        let _s = named("s", move || {
            crate::send_msg_as(rid, I, 1);
            crate::send_lossy_msg_as(rid, I, 2);
            crate::send_tagged_msg_as(rid, I, 7, 3);
            crate::send_tagged_lossy_msg_as(rid, I, 7, 4);
            crate::send_vec_tagged_msg_as(rid, I, vec![7], 5);
            crate::send_vec_tagged_lossy_msg_as(rid, I, vec![7], 6);
            tx_x.send_msg_as(I, 1);
            tx_x.send_lossy_msg_as(I, 2);
            tx_x.send_tagged_msg_as(I, 7, 3);
            tx_x.send_tagged_lossy_msg_as(I, 7, 4);
            tx_x.send_vec_tagged_msg_as(I, vec![7], 5);
            tx_x.send_vec_tagged_lossy_msg_as(I, vec![7], 6);
            for k in 0..6 {
                tx_y.send_msg(k);
            }
        });
    };
    let g = crate::conformance::testing::run_once(cfg(ConsType::Bag), p);
    let inv = Some(Annotation::Explicit(Visibility::Invisible));
    let s: Vec<_> = comm_events(&g, "s")
        .iter()
        .map(|e| annotation(&g, *e))
        .collect();
    let mut want_s = vec![inv; 12];
    want_s.extend(vec![Some(Annotation::Default); 6]);
    assert_eq!(
        s, want_s,
        "conformance: the 12 annotated sends, then 6 plain ones"
    );
    let r: Vec<_> = comm_events(&g, "r")
        .iter()
        .map(|e| annotation(&g, *e))
        .collect();
    assert_eq!(
        r,
        vec![inv; 19],
        "conformance: the 19 annotated receives: {g}"
    );
}

/// **M1** (round 01 m1): an `Explicit(Visible)` on an undeclared thread reads
/// false through the predicate even where M4's check is absent (outside
/// conformance); `Default` on a declared thread reads true; nondet labels
/// read false.
#[test]
fn m1_the_predicate_is_the_conjunction() {
    let g = crate::conformance::testing::run_once(cfg(ConsType::FIFO), || {
        let (tx, _rx) = fifo();
        let t2 = tx.clone();
        let _u = named("u", move || tx.send_msg_as(Visibility::Visible, 1));
        let _k = named("k", move || {
            let _ = crate::nondet();
            t2.send_msg(2)
        });
    });
    let v = vis(&["k"]);
    let u = comm_events(&g, "u")[0];
    assert_eq!(
        annotation(&g, u),
        Some(Annotation::Explicit(Visibility::Visible))
    );
    assert!(
        !is_visible(&g, u, &v),
        "conformance: Visible on an undeclared thread"
    );
    let k = tid(&g, "k");
    assert!(matches!(g.label(Event::new(k, 1)), LabelEnum::CToss(_)));
    assert!(
        !is_visible(&g, Event::new(k, 1), &v),
        "conformance: a nondet label"
    );
    assert!(
        is_visible(&g, Event::new(k, 2), &v),
        "conformance: Default on a declared thread"
    );
    assert!(!is_visible(&g, Event::new(k, 0), &v), "conformance: Begin");
}

/// **Criterion 4, receives and an unnamed thread** (D4; L12): an
/// `Explicit(Visible)` non-blocking receive on undeclared `s` panics with the
/// same sites as the send, the Spec-side enumerator case through site (ii);
/// on an unnamed thread the message names its id.
#[test]
fn c04_an_undeclared_visible_receive_and_an_unnamed_thread() {
    let recv = prog(|| {
        let (tx_s, _rx_s) = fifo();
        let (_tx_x, rx_x) = fifo();
        let _k = named("k", move || tx_s.send_msg(1));
        let _s = named("s", move || {
            let _: Option<i32> = rx_x.recv_msg_as(Visibility::Visible);
        });
    });
    let good = wf_prog(SOp::Skip);
    let mut bad = Vec::new();
    for (case, imp, spec, skip) in [
        ("a", &recv, &good, false),
        ("b", &good, &recv, false),
        ("c", &good, &recv, true),
    ] {
        for e in wf_engines() {
            let (site, msg) = wf_site(e, imp, spec, skip);
            let want = match (case, e) {
                (_, Eng::Stateful) => "stateful",
                ("a", Eng::Enum) => "conformance",
                ("a", Eng::CFirst) => "complete-first",
                ("a", _) => "gated",
                ("b", _) => "precheck",
                ("c", Eng::Enum) => "inner search",
                ("c", Eng::CFirst) => "complete-first sweep",
                _ => "gated sweep",
            };
            if site.as_deref() != Some(want) || !msg.contains("undeclared thread `s`") {
                bad.push(format!(
                    "({case}) {e:?}: site {site:?}, expected {want:?}: {msg}"
                ));
            }
        }
    }
    let unnamed = prog(|| {
        let (tx_k, _rx_k) = fifo();
        let (tx_s, _rx_s) = fifo();
        let _k = named("k", move || tx_s.send_msg(1));
        let _u = thread::spawn(move || tx_k.send_msg_as(Visibility::Visible, 2));
    });
    let (site, msg) = wf_site(Eng::Enum, &unnamed, &good, false);
    let id = msg
        .split("undeclared thread `")
        .nth(1)
        .and_then(|r| r.split('`').next())
        .unwrap_or("")
        .to_string();
    if site.as_deref() != Some("conformance")
        || !id.starts_with('t')
        || !id[1..].chars().all(|c| c.is_ascii_digit())
    {
        bad.push(format!("unnamed: site {site:?}, thread `{id}`: {msg}"));
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 4:\n  {}",
        bad.join("\n  ")
    );
}

/// **D11, the recorded gap, measured** (M4: "a blocking receive with no
/// source is installed and overwritten by `Block{Value}` inside the probe and
/// never returned as an `Offer`"): an undeclared Spec thread's sourceless
/// `recv_msg_block_as(Visible)` escapes the enumerator with the precheck
/// skipped (the pair conforms: `s` is undeclared), while every other route
/// panics at site (i).
#[test]
fn d11_a_sourceless_blocking_visible_receive_escapes_the_probe_path_only() {
    let spec = prog(|| {
        let (tx_s, _rx_s) = fifo();
        let (_tx_x, rx_x) = fifo();
        let _k = named("k", move || tx_s.send_msg(1));
        let _s = named("s", move || {
            let _: i32 = rx_x.recv_msg_block_as(Visibility::Visible);
        });
    });
    let imp = wf_prog(SOp::Skip);
    let (site, msg) = wf_site(Eng::Enum, &imp, &spec, true);
    assert_eq!(site, None, "conformance: D11's gap is closed? {msg}");
    let v = vis(&["k"]);
    let r = verify(
        cc(Eng::Enum, cfg(ConsType::FIFO), &v, Selector::Ltr, true),
        &imp,
        &spec,
    );
    assert_eq!(
        class(&r),
        "conforms",
        "conformance: the escaped run's verdict"
    );
    for (e, skip, want) in [
        (Eng::Enum, false, "precheck"),
        (Eng::Stateful, true, "stateful"),
        (Eng::CFirst, true, "complete-first sweep"),
        (
            Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
            true,
            "gated sweep",
        ),
    ] {
        let (site, msg) = wf_site(e, &imp, &spec, skip);
        assert_eq!(site.as_deref(), Some(want), "conformance: {e:?}: {msg}");
    }
}

static L7_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// **L7 / M5**: a program that annotates a *replayed* send differently in a
/// later execution (its annotation chosen from a global counter, outside
/// `nondet()`) is rejected by the replay validation as a determinism error
/// naming the annotations — under `crate::verify` and under conformance.
#[test]
fn l7_a_replayed_label_with_a_different_annotation_is_a_determinism_error() {
    let p = || {
        let (tx, rx) = bag_chan();
        let ta = tx.clone();
        let _a = named("a", move || {
            let first = L7_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst) == 0;
            let alpha = if first {
                Visibility::Visible
            } else {
                Visibility::Invisible
            };
            ta.send_msg_as(alpha, 1)
        });
        let _c = named("c", move || {
            let _: i32 = rx.recv_msg_block();
        });
        let _b = named("b", move || tx.send_msg(2));
    };
    L7_CALLS.store(0, std::sync::atomic::Ordering::SeqCst);
    let plain = panic_of(|| crate::verify(cfg(ConsType::Bag), p));
    let plain = plain.expect("conformance: the varying annotation went undetected (crate::verify)");
    assert!(
        innermost(&plain).contains("annotated"),
        "conformance: the determinism error names the annotation: {plain}"
    );
    L7_CALLS.store(0, std::sync::atomic::Ordering::SeqCst);
    let v = vis(&["a", "b", "c"]);
    let pp = prog(p);
    let c = cc(Eng::Stateful, cfg(ConsType::Bag), &v, Selector::Ltr, false);
    let conf = panic_of(|| verify(c, &pp, &pp))
        .expect("conformance: the varying annotation went undetected (conformance)");
    assert!(
        innermost(&conf).contains("annotated"),
        "conformance: {conf}"
    );
}

/// **Criterion 8, the counter on the unannotated corpus** (D8): Part 6's
/// full-grid fixtures (`ex:naive` k ≤ 4 with E2, the paper pairs, `ndk`
/// without `bad_A`, 2PC at N ≤ 3, `corpus(7, 10)`) — no annotation anywhere —
/// read `invisible_ops_of_visible_threads = 0` on every engine (`Ltr`; the
/// enumerator unlimited with memo, stateful, complete-first, gated
/// exhaustive `Always`). `c08`'s tables do not carry the field (`row_of` is
/// Part 6's), so this is where criterion 8's "0 everywhere" is measured.
/// Ignored (heavy): 18.9 s measured, one process, `--test-threads=1`.
#[test]
#[ignore]
fn c08_the_counter_is_zero_on_the_unannotated_corpus() {
    let fixtures: Vec<Fixture> = crate::conformance::grid::registry(2..=4, 3, 10)
        .into_iter()
        .filter(|f| f.name != "ndk3/bad_A")
        .collect();
    let configs = [
        GridConfig::new(GridEngine::Enumerator)
            .memo(true)
            .budget(crate::conformance::grid::Budget::Unlimited),
        GridConfig::new(GridEngine::Stateful),
        GridConfig::new(GridEngine::CompleteFirst),
        GridConfig::new(GridEngine::Gated),
    ];
    let mut bad = Vec::new();
    let mut runs = 0;
    for f in &fixtures {
        for c in &configs {
            let r = grun(f, c);
            runs += 1;
            if grid_counter(&r) != 0 {
                bad.push(format!("{} {}: {}", f.name, c.label(), grid_counter(&r)));
            }
        }
    }
    assert_eq!(runs, fixtures.len() * 4, "conformance: every run counted");
    assert!(
        fixtures.len() >= 100,
        "conformance: {} fixtures",
        fixtures.len()
    );
    assert!(
        bad.is_empty(),
        "conformance: criterion 8, non-zero counters:\n  {}",
        bad.join("\n  ")
    );
}
