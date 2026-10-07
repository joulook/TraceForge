//! P4-CFIRST gate 3: the tester's tests for `CVerify`, the complete-first
//! checker (criteria `P4-CFIRST.md` revision 2.1).
//!
//! Every expected value below was derived from the criteria's engine facts
//! C1–C7 and the paper (`alg.tex` §8.1, §8.2 `lem:sig`, §8.5 `alg:cfirst`,
//! `lem:inert`, `thm:cfirst`, `ex:nogate`, §8.8) **before** `cfirst.rs` or the
//! diffs were read; the derivations are written out in
//! `plan/traceForge/log/dev/P4-CFIRST.report.md`, Part 0, under the labels
//! `D1`..`D14` cited on each test. Tests are named by criterion. Expected
//! rendered texts are transcribed from the criteria, not copied from the
//! module's constants.
//!
//! Conventions this file keeps because `s5_tests`' source scans read it: no
//! print macro anywhere, and every panic-family message starts with
//! `conformance:`.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::conformance::canon::CanonicalGraph;
use crate::conformance::cfirst::{run_with, CFirstOutcome, SweepEnd};
use crate::conformance::config::ConfConfig;
use crate::conformance::ctx::{Diagnostic, DiagnosticReason, Report, ReportKind};
use crate::conformance::morphism::{matches, statuses, statuses_agree, CompleteExecution, Status};
use crate::conformance::obs::{wobs, Obs};
use crate::conformance::selector::Selector;
use crate::conformance::sig::{covered, Summary};
use crate::conformance::stateful::{run_with as stateful_run_with, StatefulOutcome};
use crate::conformance::witness::WitnessCache;
use crate::conformance::{
    CFirstCounters, ConfBuilder, ConfError, ConfNote, ConfOutcome, ConfVerdict, Diagnostics,
    Engine, NotACertificate, ReplaySnapshot, ReportCause, ReportGate, ReportTag, ScopeField,
    SearchEnd, SpecErrFreedom,
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

fn bounded(n: u64) -> Config {
    Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .with_max_iterations(n)
        .build()
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

/// A complete-first `ConfBuilder`: `engine(CompleteFirst)`, nothing else set.
fn cb(config: Config, visible: &[String]) -> ConfBuilder {
    ConfBuilder::new()
        .config(config)
        .visible_threads(visible.to_vec())
        .engine(Engine::CompleteFirst)
}

/// The same configuration under the stateful engine.
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

/// The engine-only entry point (criterion 11).
fn rw(cc: &ConfConfig, imp: &Prog, spec: &Prog, keep: bool) -> CFirstOutcome {
    run_with(cc, imp, spec, keep)
}

fn srw(cc: &ConfConfig, imp: &Prog, spec: &Prog) -> StatefulOutcome {
    stateful_run_with(cc, imp, spec, true)
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

fn counters_of(v: &Result<ConfVerdict, ConfError>) -> CFirstCounters {
    outcome(v)
        .cfirst_counters()
        .expect("conformance: a complete-first outcome without counters")
        .clone()
}

/// The full canonical form (values included): plan §6's report key.
fn full_key(g: &ExecutionGraph, visible: &[String]) -> String {
    match CanonicalGraph::of(g, visible) {
        Ok(c) => format!("{c:?}"),
        Err(e) => format!("ERR {e:?}"),
    }
}

fn keys(gs: &[ExecutionGraph], visible: &[String]) -> Vec<String> {
    let mut v: Vec<String> = gs.iter().map(|g| full_key(g, visible)).collect();
    v.sort();
    v
}

fn report_keys(o: &CFirstOutcome, visible: &[String]) -> Vec<String> {
    let gs: Vec<ExecutionGraph> = o.reports.iter().map(|(g, _)| g.clone()).collect();
    keys(&gs, visible)
}

fn stateful_report_keys(o: &StatefulOutcome, visible: &[String]) -> Vec<String> {
    let gs: Vec<ExecutionGraph> = o.reports.iter().map(|(g, _)| g.clone()).collect();
    keys(&gs, visible)
}

fn label_count(g: &ExecutionGraph) -> usize {
    g.thread_ids().into_iter().map(|t| g.thread_size(t)).sum()
}

fn summary(g: &ExecutionGraph, v: &[String]) -> Summary {
    let w = wobs(g, v).expect("conformance: wobs on a fixture graph");
    Summary::of(CompleteExecution::assume_finished_at_gate(g), &w, v)
        .expect("conformance: summary on a fixture graph")
}

fn ev(t: u32, i: u32) -> Event {
    Event::new(construct_thread_id(t), i)
}

/// Criterion 9's counters as a comparable row (wall times and the vector
/// out): `[impl_graphs, cache_probes, cache_hits, cache_tests, sweeps,
/// successful, failing, aborted, sweep_graphs, witnesses, duplicates,
/// reports, cut_reports]`.
fn row(c: &CFirstCounters) -> [usize; 13] {
    [
        c.impl_graphs,
        c.cache_probes,
        c.cache_hits,
        c.cache_tests,
        c.sweeps,
        c.sweeps_successful,
        c.sweeps_failing,
        c.sweeps_aborted,
        c.sweep_graphs,
        c.witnesses,
        c.witness_duplicates,
        c.reports,
        c.cut_reports,
    ]
}

fn assert_counts(c: &CFirstCounters, expected: [usize; 13], what: &str) {
    assert_eq!(
        row(c),
        expected,
        "conformance: {what}: [impl, probes, hits, cache_tests, sweeps, succ, fail, aborted, \
         sweep_graphs, witnesses, dups, reports, cut_reports]"
    );
}

/// Criterion 9's identities on a run that is neither stopped nor aborted
/// nor cut (D1); with `keep_graphs`, a re-simulation of `alg:cfirst`'s
/// `Covered` over the kept graphs, independent of the engine's bookkeeping.
fn assert_identities(o: &CFirstOutcome, visible: &[String], kept: bool, what: &str) {
    let c = &o.counters;
    assert_eq!(c.cache_probes, c.impl_graphs, "conformance: {what}: probes");
    assert_eq!(
        c.impl_graphs,
        c.cache_hits + c.sweeps,
        "conformance: {what}: impl = hits + sweeps: {c:?}"
    );
    assert_eq!(
        c.sweeps,
        c.sweeps_successful + c.sweeps_failing + c.sweeps_aborted,
        "conformance: {what}: sweeps split: {c:?}"
    );
    assert_eq!(c.sweeps_aborted, 0, "conformance: {what}: aborted");
    assert_eq!(c.sweep_sizes.len(), c.sweeps, "conformance: {what}");
    assert_eq!(
        c.sweep_graphs,
        c.sweep_sizes.iter().sum::<usize>(),
        "conformance: {what}: sweep_graphs = sum of sizes"
    );
    assert_eq!(
        c.sweep_graphs_max,
        c.sweep_sizes.iter().copied().max().unwrap_or(0),
        "conformance: {what}: max"
    );
    assert_eq!(
        c.witnesses + c.witness_duplicates,
        c.sweeps_successful,
        "conformance: {what}: witnesses + dups = successful"
    );
    assert_eq!(c.witness_duplicates, 0, "conformance: {what}: duplicates");
    assert_eq!(
        c.witnesses,
        o.witnesses.len(),
        "conformance: {what}: W.len()"
    );
    assert_eq!(
        c.reports, c.sweeps_failing,
        "conformance: {what}: reports = failing"
    );
    assert_eq!(c.reports, o.reports.len(), "conformance: {what}: list");
    assert_eq!(c.cut_reports, 0, "conformance: {what}: cut off");
    assert!(o.cut_reports.is_empty(), "conformance: {what}: cut off");
    assert!(
        c.cache_tests >= c.cache_hits && c.cache_tests <= c.cache_probes * c.witnesses,
        "conformance: {what}: cache_tests bounds: {c:?}"
    );
    assert_eq!(o.sweep_ends.len(), c.sweeps, "conformance: {what}: ends");
    let count = |e: SweepEnd| o.sweep_ends.iter().filter(|x| **x == e).count();
    assert_eq!(
        count(SweepEnd::Witness),
        c.sweeps_successful,
        "conformance: {what}"
    );
    assert_eq!(
        count(SweepEnd::Exhausted),
        c.sweeps_failing,
        "conformance: {what}"
    );
    assert!(
        !o.aborted && o.spec_errors.is_empty(),
        "conformance: {what}"
    );
    assert_eq!(
        o.executions, c.impl_graphs,
        "conformance: {what}: executions"
    );
    assert_eq!(
        o.impl_end,
        SearchEnd::StateSpaceExhausted,
        "conformance: {what}: impl_end"
    );
    assert!(
        !c.precheck_ran && c.precheck_wall_time_ms == 0,
        "conformance: {what}"
    );
    if !kept {
        assert!(o.kept_impl_graphs.is_empty() && o.kept_spec_graphs.is_empty());
        return;
    }
    assert_eq!(
        o.kept_impl_graphs.len(),
        c.impl_graphs,
        "conformance: {what}"
    );
    assert_eq!(o.kept_spec_graphs.len(), c.sweeps, "conformance: {what}");
    for (i, s) in o.kept_spec_graphs.iter().enumerate() {
        assert_eq!(s.len(), c.sweep_sizes[i], "conformance: {what}: sweep {i}");
    }
    // Re-simulate `Covered` (`ln:ccache`, `ln:csweep`, `ln:cfound`) from the
    // kept graphs alone.
    let mut w_sim: Vec<Summary> = Vec::new();
    let mut w_keys: Vec<String> = Vec::new();
    let (mut s, mut hits, mut tests, mut rep) = (0usize, 0usize, 0usize, 0usize);
    for (gi, g) in o.kept_impl_graphs.iter().enumerate() {
        let sg = summary(g, visible);
        match w_sim.iter().position(|m| covered(&sg, m)) {
            Some(p) => {
                hits += 1;
                tests += p + 1;
                continue;
            }
            None => tests += w_sim.len(),
        }
        assert!(
            s < c.sweeps,
            "conformance: {what}: Impl graph {gi} has no sweep"
        );
        let swept = &o.kept_spec_graphs[s];
        let first = swept
            .iter()
            .position(|m| covered(&sg, &summary(m, visible)));
        match o.sweep_ends[s] {
            SweepEnd::Witness => {
                assert_eq!(
                    first,
                    Some(swept.len() - 1),
                    "conformance: {what}: sweep {s} must stop at its first covering graph"
                );
                let m = swept.last().unwrap();
                w_sim.push(summary(m, visible));
                w_keys.push(full_key(m, visible));
            }
            SweepEnd::Exhausted => {
                assert_eq!(first, None, "conformance: {what}: a failing sweep covered");
                assert_eq!(
                    full_key(&o.reports[rep].0, visible),
                    full_key(g, visible),
                    "conformance: {what}: report {rep} is not Impl graph {gi}"
                );
                rep += 1;
            }
            SweepEnd::Aborted => panic!("conformance: {what}: an aborted sweep"),
            SweepEnd::Budgeted => panic!(
                "conformance: {what}: a budgeted sweep; the complete-first engine never budgets one"
            ),
        }
        s += 1;
    }
    assert_eq!(
        (s, hits, tests, rep),
        (c.sweeps, c.cache_hits, c.cache_tests, c.reports),
        "conformance: {what}: (sweeps, hits, cache_tests, reports) re-simulated"
    );
    let held: Vec<String> = o
        .witnesses
        .entries()
        .iter()
        .map(|m| full_key(m.graph(), visible))
        .collect();
    assert_eq!(held, w_keys, "conformance: {what}: W in admission order");
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

/// The innermost message of a payload the runtime may have wrapped as
/// "A panic was detected\noriginal panic: <message>".
fn innermost(payload: &str) -> &str {
    payload.rsplit("original panic: ").next().unwrap_or(payload)
}

// =========================================================================
// Texts, transcribed from the criteria (C4, C7) and the pre-existing engine
// =========================================================================

const C7_EACH_UNCOVERED: &str = "Every complete graph in this list is an uncovered complete \
     graph of the implementation: at its completion no cached witness covered it, and an \
     unpruned sweep of the specification found no graph with its signature whose order is \
     contained in its own (lem:sig).";

const C7_EXACTLY: &str = "The list is exactly the set of such graphs (thm:cfirst): the outer \
     exploration reached the end of its state space, no early-error cut fired, and every \
     failing sweep reached the end of the specification's.";

const C7_CUT_LINE: &str = "Reports raised by the early-error cut are prefixes of the \
     implementation: every completion of every extension of each is uncovered (the \
     certificate of §8.1); the cut skips the subtree below each, which may contain other \
     uncovered graphs that are not listed.";

const C7_CONFORMS_LINE: &str = "conformance: silence. Every complete graph of the \
     implementation is covered by one of the specification — by a cached witness or by a \
     sweep (thm:cfirst) — and the outer exploration reached the end of its state space.";

const C7_NOT_PRODUCED: &str = "the complete-first engine computes no inner-search \
     diagnostics; this report is a failed coverage test at completion (lem:sig)";

const C7_NOT_PRODUCED_MISMATCH: &str =
    "not produced: the complete-first engine computes no inner-search diagnostics";

const C7_CERTIFIES: &str = "no graph of the specification covers the reported complete \
     graph: no cached witness did, and an exhaustive unpruned sweep of the specification \
     found none (lem:sig, thm:cfirst)";

/// C4's tail, one text for three engines.
const C4_TAIL: &str = "Either fix the specification, or — on the enumerator — accept the \
     assumption with `ConfBuilder::skip_spec_errfree_check(true)`, which records it in the \
     verdict. Under `Engine::CompleteFirst` that flag skips only the precheck: a sweep that \
     meets a specification assertion failure still aborts the run. Under `Engine::Gated`, as \
     under `CompleteFirst`. Under `Engine::Stateful` it has no effect and the only remedy is \
     fixing the specification.";

/// C4's `detail` body after its leading article.
fn c4_detail(visibility: &str, thread: &str, pos: &str, nth: usize) -> String {
    format!(
        "{visibility} thread `{thread}` failed an assertion at {pos} during a complete-first \
         sweep of the specification (the sweep for complete implementation graph number {nth})"
    )
}

// The other engines' texts that the complete-first arm must not print.
const ENUM_SETTLED: &str = "What this report establishes (Lemma gate";
const ENUM_UNSETTLED: &str = "What this report does not establish";
const ENUM_NOT_COMPLETE: &str = "This list is not a complete set of violations";
const ENUM_SILENCE_LINE: &str = "conformance: silence. No candidate violation, no exhausted \
     search budget, and the outer loop reached the end of its state space.";
const STATEFUL_EACH: &str = "each was looked up in an index";
const STATEFUL_EXACTLY: &str = "(thm:stateful)";
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

/// The rendering's head: everything before the first report section.
fn head(s: &str) -> &str {
    s.split("\n#0\n").next().unwrap_or(s)
}

// =========================================================================
// Fixtures
// =========================================================================

/// `ex:naive` (Part 3 criterion 5's encoding, `naive_d(k, v, true, None)`):
/// `main` (undeclared) creates `c`'s and `a`'s mailboxes as channels, then
/// spawns `c, b1..bk, a`. `c` sends `v` to `a`, then receives `k` times; each
/// `b_i` sends `1` to `c`; `a` skips.
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

/// `ex:nogate` (criterion 3): every mailbox a channel `main` creates before
/// any spawn; `main` spawns `u, w, i, a, b, c`. `u: send(a,9) ‖ w: send(b,7)
/// ‖ i: x := recv^nb(); if x = 1 then send(c,8) ‖ a: recv^nb() ‖ b: recv^b();
/// send(i,1) ‖ c: recv^b()`. Visible: `a, b, c`.
fn nogate() -> Prog {
    prog(|| {
        let (tx_a, rx_a) = chan();
        let (tx_b, rx_b) = chan();
        let (tx_c, rx_c) = chan();
        let (tx_i, rx_i) = chan();
        let _u = named("u", move || tx_a.send_msg(9));
        let _w = named("w", move || tx_b.send_msg(7));
        let _i = named("i", move || {
            let x: Option<i32> = rx_i.recv_msg();
            if x == Some(1) {
                tx_c.send_msg(8);
            }
        });
        let _a = named("a", move || {
            let _x: Option<i32> = rx_a.recv_msg();
        });
        let _b = named("b", move || {
            let _y: i32 = rx_b.recv_msg_block();
            tx_i.send_msg(1);
        });
        let _c = named("c", move || {
            let _z: i32 = rx_c.recv_msg_block();
        });
    })
}

/// Criterion 4's Impl (= Part 3 criterion 7's Spec): `c: recv; recv ‖ a:
/// send(c,1) ‖ b: send(c,1)`, one channel, spawned `c, a, b`.
fn c4_impl() -> Prog {
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

/// Criterion 4's positive Spec: `a`, `b` send 1 to a channel nobody reads;
/// `c` receives twice from a channel only the invisible `d` writes (twice).
fn c4_spec_positive() -> Prog {
    prog(|| {
        let (tx_x, _rx_x) = chan();
        let (tx_c, rx_c) = chan();
        let _c = named("c", move || {
            let _x: i32 = rx_c.recv_msg_block();
            let _y: i32 = rx_c.recv_msg_block();
        });
        let ta = tx_x.clone();
        let _a = named("a", move || ta.send_msg(1));
        let _b = named("b", move || tx_x.send_msg(1));
        let _d = named("d", move || {
            tx_c.send_msg(1);
            tx_c.send_msg(1);
        });
    })
}

/// Criterion 4's negative Spec: the Impl plus an invisible `d: send(c,1)`
/// spawned last.
fn c4_spec_negative() -> Prog {
    prog(|| {
        let (tx, rx) = chan();
        let _c = named("c", move || {
            let _x: i32 = rx.recv_msg_block();
            let _y: i32 = rx.recv_msg_block();
        });
        let ta = tx.clone();
        let _a = named("a", move || ta.send_msg(1));
        let tb = tx.clone();
        let _b = named("b", move || tb.send_msg(1));
        let _d = named("d", move || tx.send_msg(1));
    })
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

/// Plan §6's growing regression: `a: assert(false) ‖ b: send(B,0)` (Impl) vs
/// `a: skip ‖ b: send(B,0)`; `a` spawned first; `b`'s mailbox a channel
/// nobody reads.
fn growing(fails: bool) -> Prog {
    prog(move || {
        let (tx, _rx) = chan();
        let _a = named("a", move || {
            if fails {
                crate::assert(false);
            }
        });
        let _b = named("b", move || tx.send_msg(0));
    })
}

/// A27's witness 1: `b: x := recv_msg() ‖ a: assert(false) ‖ c: send(b,1)`,
/// all visible, spawned `b, a, c`; the Spec has `a: skip`.
fn a27(fails: bool) -> Prog {
    prog(move || {
        let b = named("b", || {
            let _x: Option<i32> = crate::recv_msg();
        });
        let bid = b.thread().id();
        let _a = named("a", move || {
            if fails {
                crate::assert(false);
            }
        });
        let _c = named("c", move || send_msg(bid, 1i32));
    })
}

/// Round 02 m4's list-order fixture: Impl `b: send(A,1) ‖ a: x :=
/// recv_msg(); if x.is_none() { assert(false) }`; Spec `b: send(A,2) ‖ a: x
/// := recv_msg()`. `a`'s mailbox a channel `main` creates; spawned `b, a`.
fn list_order(spec: bool) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let _b = named("b", move || tx.send_msg(if spec { 2 } else { 1 }));
        let _a = named("a", move || {
            let x: Option<i32> = rx.recv_msg();
            if !spec && x.is_none() {
                crate::assert(false);
            }
        });
    })
}

/// Two visible threads that both fail an assertion, `a` first (L2).
fn two_failures() -> Prog {
    prog(|| {
        let _a = named("a", || crate::assert(false));
        let _b = named("b", || crate::assert(false));
    })
}

/// D7 (invisible): `main` spawns `v` (visible, skip) then `w` (invisible),
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

/// D7 (i′): `v` visible skip; invisible `w` receives once from a channel two
/// invisible senders (`s1` sends 1, `s2` sends 2) write; `w` fails on 2 —
/// only in the execution the revisit produces (Spec execution 2 under `Ltr`).
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

/// A per-channel `TotalOrder` (mailbox) channel, sent on.
fn total_order_channel() -> Prog {
    prog(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new()
            .with_comm(CommunicationModel::TotalOrder)
            .build();
        let _w = named("w", move || tx.send_msg(1));
    })
}

/// An implementation that must never run (criterion 7 (i)).
fn never_runs() -> Prog {
    prog(|| panic!("conformance: the outer run executed the implementation"))
}

// --- the corpus of criteria 1, 5 and 12 (Part 3's, copied) -----------------

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

fn c2_spec() -> Prog {
    prog(|| {
        let a = named("a", || {
            let _x: i32 = recv_msg_block();
        });
        let aid = a.thread().id();
        let _b = named("b", move || send_msg(aid, 1i32));
    })
}

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

fn ex_cone_spec() -> Prog {
    prog(|| {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, 9i32));
    })
}

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

/// Admissible pairs only (A9 excluded: no NaN anywhere): Part 3's corpus,
/// plus this part's own fixtures.
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
        let mut add = |n: &str, v: &Vec<String>, i: Prog, s: Prog| {
            out.push(pr(&format!("{n}/{m}"), c(), v.clone(), i, s));
        };
        add("relay/direct", &mc, pe_p2_relay(), pe_p1_direct(1));
        add("direct/relay", &mc, pe_p1_direct(1), pe_p2_relay());
        add("relay/two", &mc, pe_p2_relay(), pe_p1_direct(2));
        add("blocking", &mc, blocking(true), blocking(false));
        add("blocking/rev", &mc, blocking(false), blocking(true));
        add(
            "verr",
            &vis(&["w"]),
            visible_error(true),
            visible_error(false),
        );
        add("traces/self", &abc, traces_prog(false), traces_prog(false));
        add("traces/assume", &abc, traces_prog(false), traces_prog(true));
        add(
            "traces/joined",
            &abc,
            traces_prog(false),
            pe_sends_ordered_by_join(),
        );
        add(
            "joined/traces",
            &abc,
            pe_sends_ordered_by_join(),
            traces_prog(false),
        );
        add("c7/a", &abc, c7_impl(true), c4_impl());
        add("c7/b", &abc, c7_impl(false), c4_impl());
        add("c7/rev", &abc, c4_impl(), c7_impl(true));
        add("clause2", &vis(&["a", "b"]), c2_impl(), c2_spec());
        add("clause2/mirror", &vis(&["a", "b"]), c2_spec(), c2_impl());
        add(
            "cone/relay",
            &vis(&["a", "c"]),
            relay_spec(),
            ex_cone_spec(),
        );
        add(
            "cone/self",
            &vis(&["a", "c"]),
            ex_cone_spec(),
            ex_cone_spec(),
        );
        add(
            "two/12-11",
            &abc,
            two_senders(1i32, 2i32),
            two_senders(1i32, 1i32),
        );
        add(
            "inv-block-revisit",
            &abc,
            inv_block_before_revisit(false),
            inv_block_before_revisit(false),
        );
        add("c4/positive", &abc, c4_impl(), c4_spec_positive());
        add("c4/negative", &abc, c4_impl(), c4_spec_negative());
        add("c4/neg-rev", &abc, c4_spec_negative(), c4_impl());
        add("nogate/self", &abc, nogate(), nogate());
        add("a27", &abc, a27(true), a27(false));
        add("a27/self", &abc, a27(false), a27(false));
        add(
            "list-order",
            &vis(&["a", "b"]),
            list_order(false),
            list_order(true),
        );
        add("growing", &vis(&["a", "b"]), growing(true), growing(false));
    }
    for k in [2usize, 3] {
        let bag = || cfg(ConsType::Bag);
        out.push(pr(
            &format!("naive{k}/impl-spec"),
            bag(),
            naive_visible(k),
            naive(k, 0),
            naive(k, 1),
        ));
        out.push(pr(
            &format!("naive{k}/spec-spec"),
            bag(),
            naive_visible(k),
            naive(k, 1),
            naive(k, 1),
        ));
        out.push(pr(
            &format!("naive{k}/spec-impl"),
            bag(),
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
        "inv-assert/impl",
        cfg(ConsType::Bag),
        vis(&["v"]),
        inv_assert(true),
        inv_assert(false),
    ));
    for (n, i, s) in [
        ("restart", restart(false), restart(true)),
        ("restart/rev", restart(true), restart(false)),
        ("restart/both", restart(true), restart(true)),
    ] {
        out.push(pr(n, cfg(ConsType::FIFO), vis(&["a", "c"]), i, s));
    }
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
// Criteria 1 and 9 — the uncut outer run, the identities
// =========================================================================

/// **Criteria 1 and 9 (D1).** On every corpus pair: the multiset of complete
/// Impl graphs the sink sees equals the stateful checker's, by full
/// canonical form; the identities and the `Covered` re-simulation hold; the
/// public path records the same row, the precheck, and no inner search.
#[test]
fn c01_the_outer_run_is_musts_uncut_exploration_of_impl() {
    let mut failures = Vec::new();
    let mut pairs = 0;
    for p in corpus() {
        let v = &p.visible;
        let cc = built(cb(p.config.clone(), v));
        let o = rw(&cc, &p.imp, &p.spec, true);
        assert_identities(&o, v, true, &p.name);
        let s = srw(&built(sb(p.config.clone(), v)), &p.imp, &p.spec);
        if keys(&o.kept_impl_graphs, v) != keys(&s.kept_impl_graphs, v) {
            failures.push(format!(
                "{}: kept Impl multisets differ ({} vs {})",
                p.name,
                o.kept_impl_graphs.len(),
                s.kept_impl_graphs.len()
            ));
        }
        if o.max_paper_events != s.max_paper_events {
            failures.push(format!("{}: max_paper_events", p.name));
        }
        let unkept = rw(&cc, &p.imp, &p.spec, false);
        assert_identities(&unkept, v, false, &p.name);
        assert_eq!(
            row(&unkept.counters),
            row(&o.counters),
            "conformance: {}",
            p.name
        );
        assert_eq!(unkept.counters.sweep_sizes, o.counters.sweep_sizes);

        let r = run(cc, &p.imp, &p.spec);
        let out = outcome(&r);
        assert_eq!(
            out.engine(),
            Engine::CompleteFirst,
            "conformance: {}",
            p.name
        );
        assert!(out.stateful_counters().is_none());
        let pc = counters_of(&r);
        assert_eq!(
            row(&pc),
            row(&o.counters),
            "conformance: {}: run vs run_with",
            p.name
        );
        assert_eq!(pc.sweep_sizes, o.counters.sweep_sizes);
        assert!(
            pc.precheck_ran,
            "conformance: {}: the precheck is on by default",
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
        assert_eq!(c.executions, pc.impl_graphs, "conformance: {}", p.name);
        assert_eq!(
            c.max_paper_events_per_execution, o.max_paper_events,
            "conformance: {}",
            p.name
        );
        assert!(out.exhaustions().is_empty() && !out.inconclusive());
        assert_eq!(out.spec_err_freedom(), SpecErrFreedom::Checked);
        assert_eq!(out.end(), SearchEnd::StateSpaceExhausted);
        assert_eq!(out.reports().len(), o.reports.len());
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 1: {failures:#?}"
    );
    assert!(pairs >= 90, "conformance: only {pairs} pairs");
}

// =========================================================================
// Criterion 2 — admissible inputs, the bound on the outer run only
// =========================================================================

/// **Criterion 2 (D2).** `ex:naive` `k = 3`, `max_iterations = 2`: two
/// completions, `MaxIterations(2)`, each of the two sweeps tested all six Spec
/// graphs and ended exhausted; `BoundedRun`; reports among the unbounded six.
#[test]
fn c02_max_iterations_bounds_the_outer_run_only() {
    let v = naive_visible(3);
    let cc = built(cb(bounded(2), &v));
    let o = rw(&cc, &naive(3, 0), &naive(3, 1), true);
    assert_counts(
        &o.counters,
        [2, 2, 0, 0, 2, 0, 2, 0, 12, 0, 0, 2, 0],
        "bounded",
    );
    assert_eq!(o.counters.sweep_sizes, vec![6, 6]);
    assert_eq!(o.counters.sweep_graphs_max, 6);
    assert_eq!(o.sweep_ends, vec![SweepEnd::Exhausted, SweepEnd::Exhausted]);
    assert_eq!(o.impl_end, SearchEnd::MaxIterations(2));
    assert_eq!(o.max_paper_events, 7, "conformance: 2k+1");
    let un = rw(
        &built(cb(cfg(ConsType::Bag), &v)),
        &naive(3, 0),
        &naive(3, 1),
        false,
    );
    assert_counts(
        &un.counters,
        [6, 6, 0, 0, 6, 0, 6, 0, 36, 0, 0, 6, 0],
        "unbounded",
    );
    let all: BTreeSet<String> = report_keys(&un, &v).into_iter().collect();
    let some = report_keys(&o, &v);
    assert_eq!(some.len(), 2);
    assert!(some.iter().all(|k| all.contains(k)), "conformance: subset");

    let r = run(cc, &naive(3, 0), &naive(3, 1));
    match &r {
        Ok(ConfVerdict::Reported(out)) => {
            assert_eq!(out.end(), SearchEnd::MaxIterations(2));
            assert!(out
                .not_a_certificate()
                .contains(&NotACertificate::BoundedRun { max_iterations: 2 }));
            let s = format!("{}", r.as_ref().unwrap());
            assert!(s.contains(C7_EACH_UNCOVERED), "conformance: {s}");
            assert!(!s.contains(C7_EXACTLY), "conformance: {s}");
            assert!(s.contains(&trunc_bound(2)), "conformance: {s}");
            assert!(counters_of(&r).precheck_ran);
        }
        other => panic!("conformance: expected Reported, got {}", class(other)),
    }
}

/// **Criterion 2.** `mbox` is refused at `build` under this engine.
#[test]
fn c02_mailbox_is_refused_at_build() {
    let e = cb(cfg(ConsType::Mailbox), &vis(&["w"]))
        .build()
        .err()
        .expect("conformance: a Mailbox configuration was accepted");
    assert_eq!(e.field(), ScopeField::ConsType);
}

/// **Criterion 2 (D2, round 01 m8).** A per-channel `TotalOrder` panics
/// naming the engine that met it: on Impl "complete-first"; on Spec with the
/// precheck on "precheck"; on Spec with the precheck skipped, and through
/// `run_with`, "complete-first sweep".
#[test]
fn c02_a_total_order_channel_panics_naming_the_engine_that_met_it() {
    let v = vis(&["w"]);
    let refusal = "`a TotalOrder (mailbox) send` is outside conformance scope";
    type Case = (&'static str, Prog, Prog, bool, bool, &'static str);
    let cases: [Case; 5] = [
        (
            "impl/run",
            total_order_channel(),
            visible_error(false),
            false,
            false,
            "complete-first",
        ),
        (
            "impl/run_with",
            total_order_channel(),
            visible_error(false),
            true,
            false,
            "complete-first",
        ),
        (
            "spec/precheck",
            visible_error(false),
            total_order_channel(),
            false,
            false,
            "precheck",
        ),
        (
            "spec/skipped",
            visible_error(false),
            total_order_channel(),
            false,
            true,
            "complete-first sweep",
        ),
        (
            "spec/run_with",
            visible_error(false),
            total_order_channel(),
            true,
            false,
            "complete-first sweep",
        ),
    ];
    for (what, imp, spec, engine_only, skip, label) in cases {
        let cc = built(cb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(skip));
        let payload = panic_text(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || {
                if engine_only {
                    let _ = rw(&cc, &imp, &spec, false);
                } else {
                    let _ = run(cc.clone(), &imp, &spec);
                }
            },
        )))
        .unwrap_or_else(|| panic!("conformance: {what}: a TotalOrder channel ran"));
        let original = innermost(&payload);
        assert!(
            original.starts_with(&format!("{label}: {refusal}")),
            "conformance: {what}: expected a refusal naming {label:?}: {payload:?}"
        );
    }
}

// =========================================================================
// Criterion 3 — ex:nogate
// =========================================================================

fn word<'a>(s: &'a Summary, t: &str) -> &'a [Obs] {
    s.sig.word(t)
}

/// `G`: `a` reads a value (9), `c` done having read (8).
fn is_paper_g(s: &Summary) -> bool {
    matches!(word(s, "a"), [Obs::Recv(Some(_))])
        && matches!(word(s, "c"), [Obs::Recv(Some(_))])
        && s.sig.status("c") == Some(Status::Done)
}

/// The first completion: `a` reads ⊥, `b` reads and sends, `c` blocked.
fn is_first_completion(s: &Summary) -> bool {
    matches!(word(s, "a"), [Obs::Recv(None)])
        && matches!(word(s, "b"), [Obs::Recv(Some(_)), Obs::Send(_)])
        && word(s, "c").is_empty()
        && s.sig.status("c") == Some(Status::Blocked)
}

/// **Criterion 3 (D3).** `ex:nogate`, Impl = Spec: no report, `Conforms`,
/// `sweeps_failing = 0`; four graphs with pairwise distinct signatures, so
/// every sweep stops at its completion's twin (`sweep_sizes = [1, 2, 3, 4]`);
/// (i) `G` is kept; (ii) its sweep ends `Witness` at `G`'s twin and
/// `covered(G, witness)`; (iii) its sweep's first graph is (`i` ⊥, `a` ⊥,
/// `b` 7, `c` blocked), the first Impl completion.
#[test]
fn c03_ex_nogate_no_pruning() {
    let v = vis(&["a", "b", "c"]);
    let cc = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &nogate(), &nogate(), true);
    assert_identities(&o, &v, true, "ex:nogate");
    assert_counts(
        &o.counters,
        [4, 4, 0, 6, 4, 4, 0, 0, 10, 4, 0, 0, 0],
        "ex:nogate",
    );
    assert_eq!(o.counters.sweep_sizes, vec![1, 2, 3, 4], "conformance: (α)");
    let sums: Vec<Summary> = o.kept_impl_graphs.iter().map(|g| summary(g, &v)).collect();
    let distinct: BTreeSet<String> = sums.iter().map(|s| format!("{:?}", s.sig)).collect();
    assert_eq!(distinct.len(), 4, "conformance: four distinct signatures");
    assert!(
        is_first_completion(&sums[0]),
        "conformance: Impl_1 {:?}",
        sums[0].sig
    );
    // (i)
    let gi = sums
        .iter()
        .position(is_paper_g)
        .expect("conformance: (i) the paper's G is not among the Impl graphs");
    let g = &o.kept_impl_graphs[gi];
    // No cache hit, so completion `gi` owns sweep `gi`.
    let swept = &o.kept_spec_graphs[gi];
    // (ii)
    assert_eq!(o.sweep_ends[gi], SweepEnd::Witness, "conformance: (ii)");
    let witness = o.witnesses.entries()[gi].graph();
    assert_eq!(
        full_key(witness, &v),
        full_key(g, &v),
        "conformance: (ii) twin"
    );
    assert_eq!(
        full_key(swept.last().unwrap(), &v),
        full_key(g, &v),
        "conformance: (ii) the sweep stopped at the twin"
    );
    assert!(
        covered(&sums[gi], &summary(witness, &v)),
        "conformance: (ii) covered"
    );
    // (iii)
    assert_eq!(
        full_key(&swept[0], &v),
        full_key(&o.kept_impl_graphs[0], &v),
        "conformance: (iii) the first swept graph"
    );
    assert!(
        is_first_completion(&summary(&swept[0], &v)),
        "conformance: (iii)"
    );
    // Measured (D3's LIFO derivation): `G` is the third completion.
    assert_eq!(gi, 2, "conformance: G's position (derived under LIFO)");

    let r = run(cc, &nogate(), &nogate());
    assert_eq!(class(&r), "conforms");
    assert_eq!(counters_of(&r).sweeps_failing, 0);
}

// =========================================================================
// Criterion 4 — W fed only at ln:cfound, probed first
// =========================================================================

/// **Criterion 4 (D4), positive fixture.** The first swept graph covers both
/// Impl graphs: one sweep, one hit, one cache test.
#[test]
fn c04_w_positive_fixture_is_a_provable_hit() {
    let v = vis(&["a", "b", "c"]);
    let cc = built(cb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(true));
    let o = rw(&cc, &c4_impl(), &c4_spec_positive(), true);
    assert_identities(&o, &v, true, "c4 positive");
    assert_counts(
        &o.counters,
        [2, 2, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0],
        "c4 positive",
    );
    assert_eq!(o.counters.sweep_sizes, vec![1]);
    let w = summary(o.witnesses.entries()[0].graph(), &v);
    for g in &o.kept_impl_graphs {
        assert!(covered(&summary(g, &v), &w), "conformance: covers both");
    }
    assert_eq!(class(&run(cc, &c4_impl(), &c4_spec_positive())), "conforms");
}

/// **Criterion 4 (D4), negative fixture (E1's measured miss).** The first
/// sweep's witness covers only `Q_A`'s graph; `Q_B`'s completion misses.
#[test]
fn c04_w_negative_fixture_misses() {
    let v = vis(&["a", "b", "c"]);
    let cc = built(cb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(true));
    let o = rw(&cc, &c4_impl(), &c4_spec_negative(), true);
    assert_identities(&o, &v, true, "c4 negative");
    let c = &o.counters;
    assert_eq!(
        (c.impl_graphs, c.cache_probes, c.cache_hits, c.cache_tests),
        (2, 2, 0, 1),
        "conformance: {c:?}"
    );
    assert_eq!(
        (c.sweeps, c.sweeps_successful, c.witnesses, c.reports),
        (2, 2, 2, 0)
    );
    assert_eq!(
        c.sweep_sizes[0], 1,
        "conformance: M_1 is Impl_1 + d's unread send"
    );
    assert!(c.sweep_sizes[1] >= 2);
    let w1 = summary(o.witnesses.entries()[0].graph(), &v);
    let g2 = summary(&o.kept_impl_graphs[1], &v);
    assert!(!covered(&g2, &w1), "conformance: Q_A ⊄ Q_B");
    assert_eq!(class(&run(cc, &c4_impl(), &c4_spec_negative())), "conforms");
}

// =========================================================================
// Criterion 5 — thm:cfirst against the stateful checker and Phase 3
// =========================================================================

/// **Criterion 5 (D5).** On every corpus pair: equal report sets (full
/// canonical form) and verdicts; the reports equal the Phase 3 reference over
/// the stateful run's exhaustive Spec family; (a) every swept graph and
/// witness is in that family; (b) every failing sweep's kept set *is* it.
#[test]
fn c05_thm_cfirst_against_stateful_and_the_morphism() {
    let mut failures = Vec::new();
    let (mut pairs, mut reported, mut silent, mut failing_sweeps) = (0, 0, 0, 0);
    for p in corpus() {
        let v = &p.visible;
        let cc = built(cb(p.config.clone(), v));
        let scc = built(sb(p.config.clone(), v));
        let o = rw(&cc, &p.imp, &p.spec, true);
        let s = srw(&scc, &p.imp, &p.spec);
        assert_eq!(
            s.spec_end,
            SearchEnd::StateSpaceExhausted,
            "conformance: {}",
            p.name
        );
        assert!(s.spec_errors.is_empty(), "conformance: {}", p.name);
        if report_keys(&o, v) != stateful_report_keys(&s, v) {
            failures.push(format!("{}: report sets differ", p.name));
        }
        let (cv, sv) = (
            class(&run(cc, &p.imp, &p.spec)),
            class(&run(scc, &p.imp, &p.spec)),
        );
        if cv != sv {
            failures.push(format!("{}: verdicts {cv} vs {sv}", p.name));
        }
        // The reference on cfirst's own Impl graphs against the exhaustive
        // family.
        let family: Vec<_> = s
            .kept_spec_graphs
            .iter()
            .map(|m| {
                let w = wobs(m, v).expect("conformance: wobs");
                let st = statuses(CompleteExecution::assume_finished_at_gate(m), &w, v)
                    .expect("conformance: statuses");
                (m, w, st)
            })
            .collect();
        let reference: Vec<ExecutionGraph> = o
            .kept_impl_graphs
            .iter()
            .filter(|g| {
                let w = wobs(g, v).expect("conformance: wobs");
                let st = statuses(CompleteExecution::assume_finished_at_gate(g), &w, v)
                    .expect("conformance: statuses");
                !family
                    .iter()
                    .any(|(m, wm, sm)| matches(m, g, wm, &w, v) && statuses_agree(sm, &st))
            })
            .cloned()
            .collect();
        if keys(&reference, v) != report_keys(&o, v) {
            failures.push(format!(
                "{}: reports differ from the morphism reference",
                p.name
            ));
        }
        let fam: BTreeSet<String> = s.kept_spec_graphs.iter().map(|m| full_key(m, v)).collect();
        // (a)
        for (i, swept) in o.kept_spec_graphs.iter().enumerate() {
            if swept.iter().any(|m| !fam.contains(&full_key(m, v))) {
                failures.push(format!("{}: (a) sweep {i} left the family", p.name));
            }
        }
        if o.witnesses
            .entries()
            .iter()
            .any(|m| !fam.contains(&full_key(m.graph(), v)))
        {
            failures.push(format!("{}: (a) a witness outside the family", p.name));
        }
        // (b)
        for (i, swept) in o.kept_spec_graphs.iter().enumerate() {
            if o.sweep_ends[i] == SweepEnd::Exhausted {
                failing_sweeps += 1;
                let got: BTreeSet<String> = swept.iter().map(|m| full_key(m, v)).collect();
                if got != fam || swept.len() != s.kept_spec_graphs.len() {
                    failures.push(format!(
                        "{}: (b) failing sweep {i}: {} graphs vs family {}",
                        p.name,
                        swept.len(),
                        s.kept_spec_graphs.len()
                    ));
                }
            }
        }
        if o.reports.is_empty() {
            silent += 1;
        } else {
            reported += 1;
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 5: {failures:#?}"
    );
    assert!(pairs >= 90, "conformance: only {pairs} pairs");
    assert!(
        reported >= 10 && silent >= 10 && failing_sweeps >= 20,
        "conformance: ({reported}, {silent}, {failing_sweeps})"
    );
}

// =========================================================================
// Criteria 6 and 10 — report shapes, the cut, the list order, stop
// =========================================================================

/// Criterion 10's artefacts on every completion report; returns the run's
/// outcome for further checks.
fn assert_completion_artefacts(r: &Result<ConfVerdict, ConfError>, o: &CFirstOutcome, what: &str) {
    let out = outcome(r);
    let completion: Vec<_> = out
        .reports()
        .iter()
        .filter(|r| r.tag() == ReportTag::CompleteCoverage)
        .collect();
    assert_eq!(completion.len(), o.reports.len(), "conformance: {what}");
    for r in completion {
        assert_eq!(*r.cause(), ReportCause::NoCover, "conformance: {what}");
        assert_eq!(r.gate(), ReportGate::Completion, "conformance: {what}");
        assert!(
            matches!(
                r.diagnostics(),
                Diagnostics::NotProduced {
                    by: Engine::CompleteFirst
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
            shown.contains(&format!("certifies (CompleteCoverage): {C7_CERTIFIES}")),
            "conformance: {what}: certificate text: {shown}"
        );
        assert!(
            shown.contains(C7_NOT_PRODUCED),
            "conformance: {what}: {shown}"
        );
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
            .unwrap_or_else(|| panic!("conformance: {what}: run_with's graph not reported"));
        assert_eq!(r.events(), label_count(g), "conformance: {what}: events");
    }
}

/// The one cut report's artefacts (C5, L5).
fn assert_cut_artefacts(r: &Result<ConfVerdict, ConfError>, o: &CFirstOutcome, what: &str) {
    let out = outcome(r);
    let cut: Vec<_> = out
        .reports()
        .iter()
        .filter(|r| r.tag() == ReportTag::VisibleError)
        .collect();
    assert_eq!(cut.len(), o.cut_reports.len(), "conformance: {what}");
    for (r, raw) in cut.iter().zip(&o.cut_reports) {
        assert!(
            matches!(r.cause(), ReportCause::VisibleError { .. }),
            "conformance: {what}: cause"
        );
        assert!(matches!(raw.kind, ReportKind::VisibleError { .. }));
        assert_eq!(r.gate(), ReportGate::NotAGate, "conformance: {what}: gate");
        assert!(
            matches!(r.diagnostics(), Diagnostics::NotApplicable),
            "conformance: {what}: diagnostics"
        );
        assert!(
            matches!(r.replay_snapshot(), ReplaySnapshot::Serialized(_)),
            "conformance: {what}: {:?}",
            r.replay_snapshot()
        );
        assert!(matches!(raw.replay, ReplaySnapshot::Serialized(_)));
        assert_eq!(r.events(), raw.events, "conformance: {what}: L5 events");
        let shown = format!("{r}");
        assert!(
            shown.contains(ReportTag::VisibleError.certifies()),
            "conformance: {what}: {shown}"
        );
    }
}

fn rendering(r: &Result<ConfVerdict, ConfError>) -> String {
    format!("{}", r.as_ref().expect("conformance: a verdict"))
}

/// **Criteria 6 and 10 (D6).** The Blocking pair: one report, `blocked` vs
/// `done`, `CompleteCoverage` at `Completion`, `Serialized`.
#[test]
fn c06_c10_the_blocking_pair() {
    let v = vis(&["main", "c"]);
    let cc = built(cb(cfg(ConsType::FIFO), &v));
    let o = rw(&cc, &blocking(true), &blocking(false), true);
    assert_identities(&o, &v, true, "blocking");
    assert_counts(
        &o.counters,
        [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
        "blocking",
    );
    assert_eq!(
        summary(&o.reports[0].0, &v).sig.status("c"),
        Some(Status::Blocked)
    );
    let r = run(cc, &blocking(true), &blocking(false));
    assert_eq!(class(&r), "reported:1");
    assert_completion_artefacts(&r, &o, "blocking");
}

/// **Criterion 6 (D6).** Plan §6's oracle regression, cut off: one
/// `CompleteCoverage` report, `w` errored; cut on: one `VisibleError` at
/// `NotAGate`, `NotApplicable`, `impl_graphs = 0`, `executions = 1`, the cut
/// line and not "exactly".
#[test]
fn c06_the_oracle_regression_cut_off_and_on() {
    let v = vis(&["w"]);
    let (imp, spec) = (visible_error(true), visible_error(false));
    let off = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&off, &imp, &spec, true);
    assert_identities(&o, &v, true, "oracle/off");
    assert_counts(
        &o.counters,
        [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
        "oracle/off",
    );
    assert_eq!(
        summary(&o.reports[0].0, &v).sig.status("w"),
        Some(Status::Errored)
    );
    assert!(
        o.impl_notes.is_empty(),
        "conformance: a visible failure is not a note"
    );
    let r = run(off, &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    assert!(outcome(&r)
        .reports()
        .iter()
        .all(|r| r.tag() == ReportTag::CompleteCoverage));
    assert_completion_artefacts(&r, &o, "oracle/off");
    let s = rendering(&r);
    assert!(
        s.contains(C7_EXACTLY) && !s.contains(C7_CUT_LINE),
        "conformance: {s}"
    );

    let on = built(cb(cfg(ConsType::Bag), &v).early_error_cut(true));
    let o = rw(&on, &imp, &spec, true);
    assert_counts(
        &o.counters,
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        "oracle/on",
    );
    assert!(o.reports.is_empty() && o.kept_impl_graphs.is_empty());
    assert_eq!(o.cut_reports.len(), 1);
    assert_eq!(
        o.executions, 1,
        "conformance: the pruned execution is counted"
    );
    assert_eq!(o.impl_end, SearchEnd::StateSpaceExhausted);
    match &o.cut_reports[0].kind {
        ReportKind::VisibleError { thread, pos } => {
            assert_eq!(
                (thread.as_str(), *pos),
                ("w", ev(1, 1)),
                "conformance: the cut"
            )
        }
        other => panic!("conformance: {other:?}"),
    }
    let r = run(on, &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    assert_eq!(outcome(&r).reports()[0].tag(), ReportTag::VisibleError);
    assert_eq!(outcome(&r).counters().executions, 1);
    assert_eq!(counters_of(&r).impl_graphs, 0);
    assert_cut_artefacts(&r, &o, "oracle/on");
    let s = rendering(&r);
    assert!(s.contains(C7_CUT_LINE), "conformance: the cut line: {s}");
    assert!(
        !s.contains(C7_EXACTLY),
        "conformance: exactly with a cut: {s}"
    );
    assert!(s.contains(C7_EACH_UNCOVERED), "conformance: {s}");
}

/// **Criterion 6 (D6, n2).** The growing regression: cut off exactly one
/// completion report; cut on exactly one `VisibleError` and no completion
/// report.
#[test]
fn c06_the_growing_regression_cut_off_and_on() {
    let v = vis(&["a", "b"]);
    let (imp, spec) = (growing(true), growing(false));
    let off = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&off, &imp, &spec, true);
    assert_identities(&o, &v, true, "growing/off");
    assert_counts(
        &o.counters,
        [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0],
        "growing/off",
    );
    let r = run(off, &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    assert_eq!(outcome(&r).reports()[0].tag(), ReportTag::CompleteCoverage);

    let on = built(cb(cfg(ConsType::Bag), &v).early_error_cut(true));
    let o = rw(&on, &imp, &spec, true);
    assert_counts(
        &o.counters,
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        "growing/on",
    );
    assert_eq!(o.executions, 1);
    let r = run(on, &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    assert_eq!(outcome(&r).reports()[0].tag(), ReportTag::VisibleError);
    assert_cut_artefacts(&r, &o, "growing/on");
}

/// **Criterion 6 (D6, A27 witness 1).** Cut off: two completion reports (`b`
/// reads ⊥ and 1, `a` errored). Cut on: one prefix report, and the graph in
/// which `b` reads 1 appears nowhere.
#[test]
fn c06_a27_the_cut_loses_an_uncovered_graph() {
    let v = vis(&["a", "b", "c"]);
    let (imp, spec) = (a27(true), a27(false));
    let off = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&off, &imp, &spec, true);
    assert_identities(&o, &v, true, "a27/off");
    assert_counts(
        &o.counters,
        [2, 2, 0, 0, 2, 0, 2, 0, 4, 0, 0, 2, 0],
        "a27/off",
    );
    let words: BTreeSet<String> = o
        .reports
        .iter()
        .map(|(g, _)| {
            let s = summary(g, &v);
            assert_eq!(
                s.sig.status("a"),
                Some(Status::Errored),
                "conformance: a errored"
            );
            format!("{:?}", word(&s, "b"))
        })
        .collect();
    assert_eq!(words.len(), 2, "conformance: b reads ⊥ and 1: {words:?}");
    let reads_one: Vec<&ExecutionGraph> = o
        .reports
        .iter()
        .map(|(g, _)| g)
        .filter(|g| matches!(word(&summary(g, &v), "b"), [Obs::Recv(Some(_))]))
        .collect();
    assert_eq!(reads_one.len(), 1);
    let lost = full_key(reads_one[0], &v);
    let r = run(off, &imp, &spec);
    assert_eq!(class(&r), "reported:2");
    assert!(outcome(&r)
        .reports()
        .iter()
        .all(|r| r.tag() == ReportTag::CompleteCoverage));

    let on = built(cb(cfg(ConsType::Bag), &v).early_error_cut(true));
    let o = rw(&on, &imp, &spec, true);
    assert_counts(
        &o.counters,
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        "a27/on",
    );
    assert_eq!(o.cut_reports.len(), 1);
    let everywhere: Vec<String> = o
        .reports
        .iter()
        .map(|(g, _)| full_key(g, &v))
        .chain(o.cut_reports.iter().map(|r| full_key(&r.graph, &v)))
        .chain(o.kept_impl_graphs.iter().map(|g| full_key(g, &v)))
        .collect();
    assert!(
        !everywhere.contains(&lost),
        "conformance: the lost graph surfaced"
    );
    let r = run(on, &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    assert_cut_artefacts(&r, &o, "a27/on");
    let s = rendering(&r);
    assert!(
        s.contains(C7_CUT_LINE) && !s.contains(C7_EXACTLY),
        "conformance: {s}"
    );
}

/// **Criterion 6 (D6, round 02 m4).** The list order under the cut: raised
/// `[cut, completion]`, listed `[completion, cut]`; `impl_graphs = 1`,
/// `executions = 2`; cut off: two completion reports.
#[test]
fn c06_the_list_order_completion_reports_then_cut_reports() {
    let v = vis(&["a", "b"]);
    let (imp, spec) = (list_order(false), list_order(true));
    let on = built(cb(cfg(ConsType::Bag), &v).early_error_cut(true));
    let o = rw(&on, &imp, &spec, true);
    assert_counts(
        &o.counters,
        [1, 1, 0, 0, 1, 0, 1, 0, 2, 0, 0, 1, 1],
        "list/on",
    );
    assert_eq!(o.executions, 2);
    assert_eq!(o.impl_end, SearchEnd::StateSpaceExhausted);
    assert!(matches!(
        word(&summary(&o.reports[0].0, &v), "a"),
        [Obs::Recv(Some(_))]
    ));
    let r = run(on, &imp, &spec);
    let tags: Vec<ReportTag> = outcome(&r).reports().iter().map(|r| r.tag()).collect();
    assert_eq!(
        tags,
        vec![ReportTag::CompleteCoverage, ReportTag::VisibleError],
        "conformance: C5's list order"
    );
    assert_eq!(outcome(&r).counters().executions, 2);
    assert_completion_artefacts(&r, &o, "list/on");
    assert_cut_artefacts(&r, &o, "list/on");
    let s = rendering(&r);
    assert!(
        s.contains(C7_CUT_LINE) && !s.contains(C7_EXACTLY),
        "conformance: {s}"
    );

    let off = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&off, &imp, &spec, true);
    assert_identities(&o, &v, true, "list/off");
    assert_counts(
        &o.counters,
        [2, 2, 0, 0, 2, 0, 2, 0, 4, 0, 0, 2, 0],
        "list/off",
    );
    let r = run(off, &imp, &spec);
    assert_eq!(class(&r), "reported:2");
    assert!(outcome(&r)
        .reports()
        .iter()
        .all(|r| r.tag() == ReportTag::CompleteCoverage));
}

/// **Criterion 6 (D6, round 01 M4).** Stop under the cut: one report,
/// `StoppedAtFirstReport`, `Reported` with the truncation text — on the
/// oracle and the growing regressions; the A27 and list-order fixtures stop
/// at the first raised report too.
#[test]
fn c06_stop_under_the_cut() {
    for (what, v, imp, spec, impl_graphs) in [
        (
            "oracle",
            vis(&["w"]),
            visible_error(true),
            visible_error(false),
            0usize,
        ),
        (
            "growing",
            vis(&["a", "b"]),
            growing(true),
            growing(false),
            0,
        ),
        (
            "list-order",
            vis(&["a", "b"]),
            list_order(false),
            list_order(true),
            0,
        ),
    ] {
        let cc = built(
            cb(cfg(ConsType::Bag), &v)
                .early_error_cut(true)
                .stop_at_first_report(true),
        );
        let o = rw(&cc, &imp, &spec, false);
        assert_eq!(
            o.impl_end,
            SearchEnd::StoppedAtFirstReport,
            "conformance: {what}"
        );
        assert_eq!(o.cut_reports.len(), 1, "conformance: {what}");
        assert_eq!(o.counters.impl_graphs, impl_graphs, "conformance: {what}");
        assert_eq!(o.executions, 1, "conformance: {what}");
        let r = run(cc, &imp, &spec);
        assert_eq!(class(&r), "reported:1", "conformance: {what}");
        assert_eq!(outcome(&r).end(), SearchEnd::StoppedAtFirstReport);
        assert!(outcome(&r)
            .not_a_certificate()
            .contains(&NotACertificate::StoppedAtFirstReport));
        let s = rendering(&r);
        assert!(s.contains(TRUNC_CONFIG), "conformance: {what}: {s}");
        assert!(
            s.contains(C7_CUT_LINE) && !s.contains(C7_EXACTLY),
            "conformance: {s}"
        );
    }
}

/// **L2 (C7's notes).** An Impl invisible-thread failure becomes a
/// `ConfNote` and does not report. With the cut on, a failure on a *second*
/// thread after the prune is never reached (`conf_prune` stops the other
/// threads), but a second failure on the *same* thread is (gate-4 round 01
/// M1): it is recorded `AfterPrune` and rendered as a note.
#[test]
fn c06_l2_impl_notes() {
    let v = vis(&["v"]);
    let cc = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &inv_assert(true), &inv_assert(false), false);
    assert_eq!(o.impl_notes.len(), 1, "conformance: {:?}", o.impl_notes);
    assert_eq!(
        (o.impl_notes[0].thread.as_str(), o.impl_notes[0].pos),
        ("w", ev(2, 1))
    );
    let r = run(cc, &inv_assert(true), &inv_assert(false));
    assert_eq!(class(&r), "conforms");
    match outcome(&r).notes() {
        [ConfNote::InvisibleThread { thread, at }] => {
            assert_eq!((thread.as_str(), at.as_str()), ("w", "(t2, 1)"))
        }
        other => panic!("conformance: notes {other:?}"),
    }
    let v = vis(&["a", "b"]);
    let cc = built(cb(cfg(ConsType::Bag), &v).early_error_cut(true));
    let o = rw(&cc, &two_failures(), &growing(false), false);
    assert_eq!(o.cut_reports.len(), 1, "conformance: one prune, one report");
    assert!(
        o.impl_notes.is_empty(),
        "conformance: AfterPrune arose: {:?}",
        o.impl_notes
    );

    // Gate-4 round 01 M1: one thread failing twice. `traceforge::assert`
    // installs without yielding, so after the cut prunes on `a`'s first
    // failure `a` runs on, and its second failed assertion meets the prune
    // latch: recorded `AfterPrune`, rendered as a note, never a report.
    let v = vis(&["a"]);
    let cc = built(cb(cfg(ConsType::Bag), &v).early_error_cut(true));
    let o = rw(&cc, &fails_twice(true), &fails_twice(false), false);
    assert_eq!(o.cut_reports.len(), 1, "conformance: M1: one cut report");
    assert_eq!(o.counters.impl_graphs, 0, "conformance: M1: pruned");
    assert_eq!(
        o.impl_notes
            .iter()
            .map(|d| (d.thread.as_str(), d.reason))
            .collect::<Vec<_>>(),
        vec![("a", DiagnosticReason::AfterPrune)],
        "conformance: M1: impl_notes"
    );
    assert_eq!(
        o.impl_notes[0].pos,
        ev(1, 2),
        "conformance: M1: would-be position"
    );
    let r = run(cc, &fails_twice(true), &fails_twice(false));
    assert_eq!(class(&r), "reported:1");
    assert_eq!(outcome(&r).reports()[0].tag(), ReportTag::VisibleError);
    let after: Vec<&ConfNote> = outcome(&r)
        .notes()
        .iter()
        .filter(|n| matches!(n, ConfNote::AfterPrune { thread, .. } if thread == "a"))
        .collect();
    assert_eq!(after.len(), 1, "conformance: M1: {:?}", outcome(&r).notes());
    assert_eq!(
        outcome(&r).notes().len(),
        1,
        "conformance: M1: only that note"
    );
    let s = rendering(&r);
    assert!(
        s.contains("notes (1)") && s.contains(&format!("{}", after[0])),
        "conformance: M1: the note is not rendered: {s}"
    );
    assert!(
        s.contains("a further assertion failed after this execution was pruned, on `a`"),
        "conformance: M1: {s}"
    );
}

/// Gate-4 round 01 M1: a visible `a` that fails an assertion twice (Impl), or
/// skips (Spec).
fn fails_twice(fails: bool) -> Prog {
    prog(move || {
        let _a = named("a", move || {
            if fails {
                crate::assert(false);
                crate::assert(false);
            }
        });
    })
}

// =========================================================================
// Criterion 7 — Spec assertion-safety
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

/// **Criterion 7 (i), (i′) (D7).** With the precheck on, a reachable Spec
/// failure is the precheck's error, before any outer execution; and it still
/// is under `max_iterations = 1` when the failure lies in Spec execution 2.
#[test]
fn c07_the_precheck_answers_first_and_unbounded() {
    let v = vis(&["v"]);
    let cc = built(cb(cfg(ConsType::Bag), &v));
    let r = run(cc, &never_runs(), &inv_assert(true));
    let detail = spec_not_error_free(&r);
    assert!(
        detail.contains("The thread `w` failed an assertion at (t2, 1) during the precheck run"),
        "conformance: (i): {detail}"
    );
    let shown = format!("{}", r.unwrap_err());
    assert!(shown.contains(C4_TAIL), "conformance: the tail: {shown}");

    let cc = built(cb(bounded(1), &v));
    let r = run(
        cc,
        &inv_assert_on_revisit(false),
        &inv_assert_on_revisit(true),
    );
    let detail = spec_not_error_free(&r);
    assert!(
        detail.contains("The thread `w` failed an assertion at (t2, 2) during the precheck run"),
        "conformance: (i′): {detail}"
    );
}

/// **Criterion 7 (ii) (D7).** With the precheck skipped, a sweep that meets
/// a Spec failure aborts: `run` returns this engine's wording; `run_with`
/// records one aborted sweep, nothing reported or admitted, and the outer run
/// stopped. On an invisible thread (the swept graph covers: stored *and*
/// erroring) and a visible one (nothing covers).
#[test]
fn c07_a_sweep_that_meets_a_failure_aborts() {
    type Case = (&'static str, Prog, Prog, Vec<String>, Event, bool);
    let cases: [Case; 2] = [
        (
            "invisible",
            inv_assert(false),
            inv_assert(true),
            vis(&["v"]),
            ev(2, 1),
            false,
        ),
        (
            "visible",
            visible_error(false),
            visible_error(true),
            vis(&["w"]),
            ev(1, 1),
            true,
        ),
    ];
    for (what, imp, spec, v, pos, visible) in cases {
        let cc = built(cb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(true));
        let o = rw(&cc, &imp, &spec, true);
        let c = &o.counters;
        assert_eq!(
            (
                c.sweeps,
                c.sweeps_aborted,
                c.sweeps_successful,
                c.sweeps_failing
            ),
            (1, 1, 0, 0),
            "conformance: {what}: {c:?}"
        );
        assert_eq!(o.sweep_ends, vec![SweepEnd::Aborted], "conformance: {what}");
        assert!(o.aborted, "conformance: {what}");
        assert!(
            o.reports.is_empty() && o.cut_reports.is_empty(),
            "conformance: {what}"
        );
        assert_eq!(
            (c.witnesses, o.witnesses.len(), c.reports),
            (0, 0, 0),
            "conformance: {what}"
        );
        assert_eq!(
            o.impl_end,
            SearchEnd::StoppedAtFirstReport,
            "conformance: {what}"
        );
        assert_eq!(c.impl_graphs, 1, "conformance: {what}");
        assert_eq!(
            o.spec_errors,
            vec![("w".to_string(), pos, visible)],
            "conformance: {what}"
        );
        let r = run(cc, &imp, &spec);
        let detail = spec_not_error_free(&r);
        let body = c4_detail(what, "w", &pos.to_string(), 1);
        assert!(
            detail.contains(&body),
            "conformance: {what}: {detail:?} lacks {body:?}"
        );
        assert!(
            !detail.contains("precheck run"),
            "conformance: {what}: {detail}"
        );
        let shown = format!("{}", r.unwrap_err());
        assert!(
            shown.contains(C4_TAIL),
            "conformance: {what}: the tail: {shown}"
        );
    }
}

// =========================================================================
// Criterion 8 — first-report mode
// =========================================================================

/// **Criterion 8 (D8).** `ex:naive` `k = 2, 3`, stopped at the first report,
/// precheck skipped and on: one completed graph of `2k+1` events, one
/// failing sweep of all `k!` graphs, one report.
#[test]
fn c08_first_report_mode() {
    for (k, fact) in [(2usize, 2usize), (3, 6)] {
        let v = naive_visible(k);
        for skip in [true, false] {
            let what = format!("k={k} skip={skip}");
            let cc = built(
                cb(cfg(ConsType::Bag), &v)
                    .stop_at_first_report(true)
                    .skip_spec_errfree_check(skip),
            );
            let o = rw(&cc, &naive(k, 0), &naive(k, 1), false);
            assert_counts(
                &o.counters,
                [1, 1, 0, 0, 1, 0, 1, 0, fact, 0, 0, 1, 0],
                &what,
            );
            assert_eq!(o.counters.sweep_sizes, vec![fact]);
            assert_eq!(o.max_paper_events, 2 * k + 1, "conformance: {what}");
            assert_eq!(o.impl_end, SearchEnd::StoppedAtFirstReport);
            let r = run(cc, &naive(k, 0), &naive(k, 1));
            assert_eq!(class(&r), "reported:1", "conformance: {what}");
            let pc = counters_of(&r);
            assert_eq!(row(&pc), row(&o.counters), "conformance: {what}");
            assert_eq!(pc.precheck_ran, !skip, "conformance: {what}");
            if skip {
                assert_eq!(pc.precheck_wall_time_ms, 0);
            }
            let s = rendering(&r);
            assert!(s.contains(C7_EACH_UNCOVERED), "conformance: {s}");
            assert!(!s.contains(C7_EXACTLY), "conformance: {s}");
            assert!(s.contains(TRUNC_CONFIG), "conformance: {s}");
        }
    }
}

// =========================================================================
// Criterion 9 — the cost dial
// =========================================================================

/// **Criterion 9 (D9).** `ex:naive` against itself, `k = 2, 3`, precheck
/// skipped: `Conforms`, no cache hit, `k!` successful sweeps, and the vector
/// `sweep_sizes = [1, 2, …, k!]` — the `i`-th sweep stops at the `i`-th Spec
/// completion, the `i`-th Impl completion's twin.
#[test]
fn c09_the_cost_dial_on_ex_naive_against_itself() {
    for (k, fact) in [(2usize, 2usize), (3, 6)] {
        let v = naive_visible(k);
        let cc = built(cb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(true));
        let o = rw(&cc, &naive(k, 0), &naive(k, 0), true);
        let what = format!("cost dial k={k}");
        assert_identities(&o, &v, true, &what);
        assert_counts(
            &o.counters,
            [
                fact,
                fact,
                0,
                fact * (fact - 1) / 2,
                fact,
                fact,
                0,
                0,
                fact * (fact + 1) / 2,
                fact,
                0,
                0,
                0,
            ],
            &what,
        );
        let expected: Vec<usize> = (1..=fact).collect();
        assert_eq!(o.counters.sweep_sizes, expected, "conformance: {what}: (α)");
        assert_eq!(o.counters.sweep_graphs_max, fact);
        for (i, g) in o.kept_impl_graphs.iter().enumerate() {
            assert_eq!(
                full_key(o.witnesses.entries()[i].graph(), &v),
                full_key(g, &v),
                "conformance: {what}: witness {i} is Impl_{i}'s twin"
            );
        }
        let r = run(cc, &naive(k, 0), &naive(k, 0));
        assert_eq!(class(&r), "conforms");
        let pc = counters_of(&r);
        assert_eq!(pc.sweep_sizes, expected);
        assert!(!pc.precheck_ran && pc.precheck_wall_time_ms == 0);
    }
}

// =========================================================================
// Criteria 10 and 11 — artefacts and the entry point
// =========================================================================

/// **Criterion 10 (D10).** Report artefacts on a many-report run.
#[test]
fn c10_report_artefacts_on_ex_naive() {
    let v = naive_visible(3);
    let cc = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &naive(3, 0), &naive(3, 1), false);
    let r = run(cc, &naive(3, 0), &naive(3, 1));
    assert_eq!(class(&r), "reported:6");
    assert_completion_artefacts(&r, &o, "ex:naive k=3");
    let distinct: BTreeSet<String> = report_keys(&o, &v).into_iter().collect();
    assert_eq!(distinct.len(), 6, "conformance: six distinct report keys");
}

/// **Criterion 11 (D11, L4).** `CFirstOutcome` destructured without `..`,
/// every field's type ascribed.
#[test]
fn c11_the_entry_point_fields() {
    let v = naive_visible(2);
    let cc = built(cb(cfg(ConsType::Bag), &v));
    let CFirstOutcome {
        reports,
        cut_reports,
        counters,
        witnesses,
        kept_impl_graphs,
        kept_spec_graphs,
        sweep_ends,
        aborted,
        impl_end,
        spec_errors,
        impl_notes,
        executions,
        max_paper_events,
    } = rw(&cc, &naive(2, 0), &naive(2, 1), false);
    let reports: Vec<(ExecutionGraph, ReplaySnapshot)> = reports;
    let cut_reports: Vec<Report> = cut_reports;
    let counters: CFirstCounters = counters;
    let witnesses: WitnessCache = witnesses;
    let kept_impl_graphs: Vec<ExecutionGraph> = kept_impl_graphs;
    let kept_spec_graphs: Vec<Vec<ExecutionGraph>> = kept_spec_graphs;
    let sweep_ends: Vec<SweepEnd> = sweep_ends;
    let aborted: bool = aborted;
    let impl_end: SearchEnd = impl_end;
    let spec_errors: Vec<(String, Event, bool)> = spec_errors;
    let impl_notes: Vec<Diagnostic> = impl_notes;
    let (executions, max_paper_events): (usize, usize) = (executions, max_paper_events);
    assert_eq!((reports.len(), counters.reports), (2, 2));
    assert!(cut_reports.is_empty() && witnesses.is_empty() && !aborted);
    assert!(kept_impl_graphs.is_empty() && kept_spec_graphs.is_empty());
    assert_eq!(sweep_ends, vec![SweepEnd::Exhausted, SweepEnd::Exhausted]);
    assert_eq!(impl_end, SearchEnd::StateSpaceExhausted);
    assert!(spec_errors.is_empty() && impl_notes.is_empty());
    assert_eq!(
        (executions, max_paper_events),
        (2, 5),
        "conformance: L = 2k+1"
    );
}

// =========================================================================
// Criterion 12 — selector completeness
// =========================================================================

/// **Criterion 12 (D12).** Cut off, under `Ltr`, `FewestEvents`, `Reverse`:
/// identical report sets (multisets of full canonical keys), verdicts and
/// `impl_graphs` on every corpus pair; `sweep_graphs` may differ.
#[test]
fn c12_selector_completeness() {
    let mut failures = Vec::new();
    let mut pairs = 0;
    let mut sweep_graphs_differ = 0;
    for p in corpus() {
        let runs: Vec<(Vec<String>, String, usize, usize)> =
            [Selector::Ltr, Selector::FewestEvents, Selector::Reverse]
                .iter()
                .map(|s| {
                    let c = with_selector(p.config.clone(), *s);
                    let cc = built(cb(c, &p.visible).selector(*s));
                    let o = rw(&cc, &p.imp, &p.spec, false);
                    assert_identities(&o, &p.visible, false, &p.name);
                    (
                        report_keys(&o, &p.visible),
                        class(&run(cc, &p.imp, &p.spec)),
                        o.counters.impl_graphs,
                        o.counters.sweep_graphs,
                    )
                })
                .collect();
        for (i, s) in ["fewest", "reverse"].iter().enumerate() {
            let (a, b) = (&runs[i + 1], &runs[0]);
            if (&a.0, &a.1, a.2) != (&b.0, &b.1, b.2) {
                failures.push(format!(
                    "{}: {s} differs from ltr: ({}, {}) vs ({}, {})",
                    p.name, a.1, a.2, b.1, b.2
                ));
            }
            if a.3 != b.3 {
                sweep_graphs_differ += 1;
            }
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 12: {failures:#?}"
    );
    assert!(pairs >= 90);
    // Gate-4 round 01 m1: measured 0 on this corpus — no pair's
    // `sweep_graphs` depends on the selector, so the count cannot show that
    // knob A took effect; `c12_the_selector_reaches_the_outer_run_and_the_sweeps`
    // pins that by insertion order instead.
    assert_eq!(
        sweep_graphs_differ, 0,
        "conformance: recorded figure changed: sweep_graphs_differ = {sweep_graphs_differ}"
    );
}

/// The stamp of the `i`-th event of the thread named `n` (Must's insertion
/// order, which the canonical form deliberately omits).
fn stamp_of(g: &ExecutionGraph, n: &str, i: u32) -> usize {
    let t = g
        .thread_ids()
        .into_iter()
        .find(|t| g.get_thread_tclab(*t).name().as_deref() == Some(n))
        .unwrap_or_else(|| panic!("conformance: no thread named {n}"));
    g.label(Event::new(t, i)).stamp()
}

/// **Criterion 12, non-vacuity (gate-4 round 01 m1, rev 2.2).** Knob A
/// reaches the outer run and every sweep. Rev 2.2's fixture (`ex:naive`
/// `k = 3` against itself) cannot show it: measured, both selectors complete
/// the six graphs in the same canonical order *and* install the sends in the
/// same order — `main` spawns `b1` first and, under `Reverse`, the newest
/// thread runs at once, so `b1` sends before `b2` exists (see the report).
/// The discriminating fixture is `P4-SELECTOR`'s `c3_prog`: under every
/// selector both receivers (`r1`, `r2`) block before `s` sends, `s` sends
/// both and ends, and the receives are then installed by `unblock_ready`,
/// whose selector pick is `r1` under `Ltr` (least origination vector) and
/// `r2` under `Reverse` (greatest); see
/// `selector_tests::c03_the_pick_at_unblock_ready_decides`. (Gate-4 round 02
/// m1 corrected an earlier wording here.) Measured by stamps on the kept Impl
/// graph and on the swept graph;
/// the rev 2.2 `ex:naive` facts that do hold (same family, `sweep_sizes =
/// [1..6]` per selector) are kept.
#[test]
fn c12_the_selector_reaches_the_outer_run_and_the_sweeps() {
    let v = vis(&["r1", "r2", "s"]);
    for (what, s, r1_first) in [
        ("ltr", Selector::Ltr, true),
        ("reverse", Selector::Reverse, false),
    ] {
        let c = with_selector(cfg(ConsType::Bag), s);
        let cc = built(cb(c, &v).selector(s).skip_spec_errfree_check(true));
        let o = rw(&cc, &c3_prog(), &c3_prog(), true);
        assert_eq!(o.counters.sweep_sizes, vec![1], "conformance: {what}");
        let order = |g: &ExecutionGraph| stamp_of(g, "r1", 1) < stamp_of(g, "r2", 1);
        let impl_graph = &o.kept_impl_graphs[0];
        assert_eq!(
            order(impl_graph),
            r1_first,
            "conformance: {what}: the outer run ignored the selector"
        );
        assert_eq!(
            order(&o.kept_spec_graphs[0][0]),
            r1_first,
            "conformance: {what}: the sweep ignored the selector"
        );
        let nv = naive_visible(3);
        let c = with_selector(cfg(ConsType::Bag), s);
        let cc = built(cb(c, &nv).selector(s).skip_spec_errfree_check(true));
        let o = rw(&cc, &naive(3, 0), &naive(3, 0), true);
        assert_eq!(
            o.counters.sweep_sizes,
            vec![1, 2, 3, 4, 5, 6],
            "conformance: {what}: ex:naive (α) per selector"
        );
    }
}

// =========================================================================
// Criterion 13 — A9
// =========================================================================

/// **Criterion 13 (D13).** A NaN pair reports against itself; `W` never
/// admits a witness.
#[test]
fn c13_a9_nan_reports() {
    let v = vis(&["a", "c"]);
    let cc = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &direct_of(f64::NAN), &direct_of(f64::NAN), true);
    assert_counts(&o.counters, [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0], "A9");
    assert!(o.witnesses.is_empty());
    let o = rw(
        &cc,
        &two_senders(f64::NAN, f64::NAN),
        &two_senders(f64::NAN, f64::NAN),
        false,
    );
    assert_eq!(
        (
            o.counters.witnesses,
            o.counters.reports,
            o.counters.impl_graphs
        ),
        (0, 2, 2),
        "conformance: A9 two senders"
    );
}

// =========================================================================
// Criterion 14 — the rendered texts
// =========================================================================

/// **Criterion 14.** A complete-first `Conforms` renders exactly the
/// enumerator's baseline with its first silence line replaced by C7's.
#[test]
fn c14_conforms_rendering() {
    let cc = built(
        ConfBuilder::new()
            .config(Config::builder().with_seed(7).build())
            .visible_threads(vis(&["a", "c"]))
            .engine(Engine::CompleteFirst),
    );
    let r = run(cc, &restart(true), &restart(true));
    assert_eq!(class(&r), "conforms");
    let expected = super::stateful_baseline::ENUMERATOR_CONFORMS_BASELINE.replacen(
        ENUM_SILENCE_LINE,
        C7_CONFORMS_LINE,
        1,
    );
    assert_ne!(
        expected,
        super::stateful_baseline::ENUMERATOR_CONFORMS_BASELINE
    );
    assert_eq!(rendering(&r), expected);
}

/// **Criterion 14.** An unbounded `Reported`: the head verbatim; none of the
/// enumerator's or the stateful engine's sentences; no triage caveat.
#[test]
fn c14_reported_rendering_unbounded() {
    let v = naive_visible(2);
    let cc = built(
        ConfBuilder::new()
            .config(Config::builder().with_seed(7).build())
            .visible_threads(v)
            .engine(Engine::CompleteFirst),
    );
    let r = run(cc, &naive(2, 0), &naive(2, 1));
    assert_eq!(class(&r), "reported:2");
    let s = rendering(&r);
    let expected_head = format!(
        "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)\n\
         conformance: 2 candidate violation(s).\n{C7_EACH_UNCOVERED}\n{C7_EXACTLY}\n\
         {RESIDUAL}\n{ONLY_SILENCE}\n"
    );
    assert_eq!(head(&s), expected_head, "conformance: the head, verbatim");
    for gone in [
        ENUM_SETTLED,
        ENUM_UNSETTLED,
        ENUM_NOT_COMPLETE,
        STATEFUL_EACH,
        STATEFUL_EXACTLY,
        TRIAGE_CAVEAT,
        C7_CUT_LINE,
    ] {
        assert!(!s.contains(gone), "conformance: {gone:?} rendered: {s}");
    }
    assert_eq!(
        s.matches(&format!("certifies (CompleteCoverage): {C7_CERTIFIES}"))
            .count(),
        2
    );
    assert_eq!(s.matches(C7_NOT_PRODUCED).count(), 2);
    assert!(!s.contains("lem:coverexact"), "conformance: {s}");
}

/// **Criterion 14.** The truncated heads (criteria 2 and 8) verbatim.
#[test]
fn c14_reported_rendering_truncated() {
    let v = naive_visible(3);
    let bounded = built(cb(
        Config::builder()
            .with_seed(7)
            .with_max_iterations(2)
            .build(),
        &v,
    ));
    let s = rendering(&run(bounded, &naive(3, 0), &naive(3, 1)));
    let expected = format!(
        "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)\n\
         conformance: 2 candidate violation(s).\n{C7_EACH_UNCOVERED}\n{RESIDUAL}\n\
         {ONLY_SILENCE}\n{}\n",
        trunc_bound(2)
    );
    assert_eq!(head(&s), expected, "conformance: bounded head");
    let stopped = built(cb(Config::builder().with_seed(7).build(), &v).stop_at_first_report(true));
    let s = rendering(&run(stopped, &naive(3, 0), &naive(3, 1)));
    let expected = format!(
        "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)\n\
         conformance: 1 candidate violation(s).\n{C7_EACH_UNCOVERED}\n{RESIDUAL}\n\
         {ONLY_SILENCE}\n{TRUNC_CONFIG}\n"
    );
    assert_eq!(head(&s), expected, "conformance: stopped head");
    assert!(!s.contains(TRIAGE_CAVEAT));
}

/// **Criterion 14 (M1).** With a cut report and a completion report on an
/// exhausted run, the head is: count, always-true sentence, the cut line,
/// and no "exactly".
#[test]
fn c14_cut_rendering_head() {
    let v = vis(&["a", "b"]);
    let cc = built(cb(Config::builder().with_seed(7).build(), &v).early_error_cut(true));
    let s = rendering(&run(cc, &list_order(false), &list_order(true)));
    let expected = format!(
        "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)\n\
         conformance: 2 candidate violation(s).\n{C7_EACH_UNCOVERED}\n{C7_CUT_LINE}\n\
         {RESIDUAL}\n{ONLY_SILENCE}\n"
    );
    assert_eq!(head(&s), expected, "conformance: the cut head");
}

/// **Criterion 14 / C7.** `triage`, `search_budget`, `inner_order` and
/// `memo` are ignored; `triage_enabled` records the configured value; no
/// triage caveat.
#[test]
fn c14_ignored_knobs() {
    let v = naive_visible(2);
    let base = rw(
        &built(cb(cfg(ConsType::Bag), &v)),
        &naive(2, 0),
        &naive(2, 1),
        false,
    );
    for t in [false, true] {
        let cc = built(
            cb(cfg(ConsType::Bag), &v)
                .triage(t)
                .search_budget(1)
                .memo(!t)
                .inner_order(crate::conformance::InnerOrder::Reverse),
        );
        let o = rw(&cc, &naive(2, 0), &naive(2, 1), false);
        assert_eq!(
            row(&o.counters),
            row(&base.counters),
            "conformance: triage={t}"
        );
        let r = run(cc, &naive(2, 0), &naive(2, 1));
        let out = outcome(&r);
        assert_eq!(out.triage_enabled, t);
        assert!(out.reports().iter().all(|r| r.triage().is_none()));
        assert!(!out.inconclusive());
        let s = rendering(&r);
        assert!(
            !s.contains("triage is off") && !s.contains("ConfBuilder::triage(true)"),
            "conformance: {s}"
        );
    }
}

/// **Criterion 14 / C7.** `certifies_under(CompleteFirst, _)`, `NotProduced`'s
/// two strings, and the other engines' texts unchanged.
#[test]
fn c14_certifies_under_and_not_produced() {
    assert_eq!(
        ReportTag::CompleteCoverage.certifies_under(Engine::CompleteFirst),
        C7_CERTIFIES
    );
    for t in [ReportTag::GrowingExhaustion, ReportTag::VisibleError] {
        assert_eq!(
            t.certifies_under(Engine::CompleteFirst),
            t.certifies(),
            "conformance: {t:?}"
        );
    }
    assert_ne!(
        ReportTag::CompleteCoverage.certifies_under(Engine::Stateful),
        C7_CERTIFIES
    );
    let d = Diagnostics::NotProduced {
        by: Engine::CompleteFirst,
    };
    assert_eq!(format!("{d}"), C7_NOT_PRODUCED);
    assert_eq!(
        crate::conformance::diagnose::spec_side_first_mismatch(&d, &ReportCause::NoCover),
        C7_NOT_PRODUCED_MISMATCH
    );
}

/// **Criterion 14 / C7.** The outcome's record: engine, counters, the
/// `ConfCounters` fields C7 names; `Assumed` under the skip; the other
/// engines carry no complete-first counters.
#[test]
fn c14_outcome_record_by_engine() {
    let v = naive_visible(3);
    for skip in [false, true] {
        let cc = built(cb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(skip));
        let r = run(cc, &naive(3, 0), &naive(3, 1));
        let o = outcome(&r);
        assert_eq!(o.engine(), Engine::CompleteFirst);
        assert_eq!(
            o.spec_err_freedom(),
            if skip {
                SpecErrFreedom::Assumed
            } else {
                SpecErrFreedom::Checked
            }
        );
        let c = o.counters();
        assert_eq!((c.executions, c.max_paper_events_per_execution), (6, 7));
        assert_eq!(c.paper_events_at_first_report, None);
        assert_eq!((c.cover_calls, c.spec_visit_calls, c.memo_hits), (0, 0, 0));
    }
    for e in [Engine::Enumerator, Engine::Stateful] {
        let cc = ConfBuilder::new()
            .config(cfg(ConsType::Bag))
            .visible_threads(v.clone())
            .engine(e)
            .unlimited()
            .build()
            .unwrap();
        let r = run(cc, &naive(3, 0), &naive(3, 1));
        assert!(
            outcome(&r).cfirst_counters().is_none(),
            "conformance: {e:?}"
        );
    }
}

/// **Criterion 14 / C7.** A bounded silent run is `Inconclusive` by
/// `BoundedRun`, and `inconclusive()` (an exhausted budget) is false.
#[test]
fn c14_bounded_silence_is_inconclusive() {
    let v = naive_visible(3);
    let cc = built(cb(bounded(2), &v));
    let r = run(cc, &naive(3, 1), &naive(3, 1));
    match &r {
        Ok(ConfVerdict::Inconclusive(o)) => {
            assert!(!o.inconclusive());
            assert_eq!(
                o.not_a_certificate(),
                vec![NotACertificate::BoundedRun { max_iterations: 2 }]
            );
            assert!(!rendering(&r).contains(C7_CONFORMS_LINE));
        }
        other => panic!("conformance: expected Inconclusive, got {}", class(other)),
    }
}

// =========================================================================
// Adversarial additions (beyond the named criteria)
// =========================================================================

/// `c` receives one value from `a` (1) or `b` (2) and forwards it to the
/// invisible `w`; with `bad = Some(n)`, `w` fails an assertion when it reads
/// `n`. `main` spawns `c, w, a, b` (t1..t4). Visible: `a, b, c`.
fn forward_to_checker(bad: Option<i32>) -> Prog {
    prog(move || {
        let (tx_c, rx_c) = chan();
        let (tx_w, rx_w) = chan();
        let _c = named("c", move || {
            let x: i32 = rx_c.recv_msg_block();
            tx_w.send_msg(x);
        });
        let _w = named("w", move || {
            let y: i32 = rx_w.recv_msg_block();
            if Some(y) == bad {
                crate::assert(false);
            }
        });
        let ta = tx_c.clone();
        let _a = named("a", move || ta.send_msg(1));
        let _b = named("b", move || tx_c.send_msg(2));
    })
}

/// **Criterion 7 (ii), L3.** An abort at the *n*-th completion. `bad = 2`:
/// completion 1 (`c` reads 1) is covered by Spec graph 1 and admitted;
/// completion 2 (`c` reads 2) misses the cache, and its sweep's covering
/// graph is the erroring one ⇒ `[Witness, Aborted]`, "number 2". `bad = 1`: the
/// first sweep aborts, and the stop leaves the second Impl graph unvisited.
/// The cut does not reach the sweeps: both cut settings agree.
#[test]
fn c07_an_abort_at_the_nth_completion() {
    let v = vis(&["a", "b", "c"]);
    let imp = forward_to_checker(None);
    for cut in [false, true] {
        let cc = built(
            cb(cfg(ConsType::Bag), &v)
                .skip_spec_errfree_check(true)
                .early_error_cut(cut),
        );
        let spec = forward_to_checker(Some(2));
        let o = rw(&cc, &imp, &spec, true);
        let what = format!("bad=2 cut={cut}");
        assert_counts(&o.counters, [2, 2, 0, 1, 2, 1, 0, 1, 3, 1, 0, 0, 0], &what);
        assert_eq!(o.counters.sweep_sizes, vec![1, 2], "conformance: {what}");
        assert_eq!(o.sweep_ends, vec![SweepEnd::Witness, SweepEnd::Aborted]);
        assert_eq!(
            o.impl_end,
            SearchEnd::StoppedAtFirstReport,
            "conformance: {what}"
        );
        assert_eq!(o.spec_errors, vec![("w".to_string(), ev(2, 2), false)]);
        let detail = spec_not_error_free(&run(cc.clone(), &imp, &spec));
        let body = c4_detail("invisible", "w", "(t2, 2)", 2);
        assert!(detail.contains(&body), "conformance: {what}: {detail:?}");

        let spec = forward_to_checker(Some(1));
        let o = rw(&cc, &imp, &spec, true);
        let what = format!("bad=1 cut={cut}");
        assert_counts(&o.counters, [1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], &what);
        assert_eq!(
            o.kept_impl_graphs.len(),
            1,
            "conformance: {what}: the run stopped"
        );
        assert_eq!(o.impl_end, SearchEnd::StoppedAtFirstReport);
        let detail = spec_not_error_free(&run(cc, &imp, &spec));
        assert!(
            detail.contains(&c4_detail("invisible", "w", "(t2, 2)", 1)),
            "conformance: {what}: {detail:?}"
        );
    }
    // With the precheck on, the precheck answers first, unbounded.
    let cc = built(cb(bounded(1), &v));
    let detail = spec_not_error_free(&run(cc, &imp, &forward_to_checker(Some(2))));
    assert!(
        detail.contains("during the precheck run"),
        "conformance: {detail}"
    );
}

/// **C5 / D1 of round 02 ("the cut decides").** On every corpus pair, the
/// cut-on run is silent iff the cut-off run is; when no cut fires it is the
/// cut-off run (same row, same report keys); when one fires, every
/// completion report it lists is one the uncut run lists too, and every cut
/// report names a declared visible thread.
#[test]
fn c06_the_cut_decides_on_the_corpus() {
    let mut failures = Vec::new();
    let mut fired = 0;
    for p in corpus() {
        let v = &p.visible;
        let off = rw(&built(cb(p.config.clone(), v)), &p.imp, &p.spec, false);
        let on = rw(
            &built(cb(p.config.clone(), v).early_error_cut(true)),
            &p.imp,
            &p.spec,
            false,
        );
        let silent_off = off.reports.is_empty();
        let silent_on = on.reports.is_empty() && on.cut_reports.is_empty();
        if silent_off != silent_on {
            failures.push(format!("{}: silence differs", p.name));
        }
        if on.cut_reports.is_empty() {
            if row(&on.counters) != row(&off.counters)
                || report_keys(&on, v) != report_keys(&off, v)
            {
                failures.push(format!("{}: no cut fired, yet the runs differ", p.name));
            }
        } else {
            fired += 1;
            let all: BTreeSet<String> = report_keys(&off, v).into_iter().collect();
            if report_keys(&on, v).iter().any(|k| !all.contains(k)) {
                failures.push(format!("{}: a cut-run completion report is new", p.name));
            }
            for r in &on.cut_reports {
                match &r.kind {
                    ReportKind::VisibleError { thread, .. } if v.contains(thread) => {}
                    other => failures.push(format!("{}: cut report {other:?}", p.name)),
                }
            }
            if on.counters.cut_reports != on.cut_reports.len() {
                failures.push(format!("{}: cut_reports counter", p.name));
            }
        }
    }
    assert!(failures.is_empty(), "conformance: {failures:#?}");
    assert!(
        fired >= 9,
        "conformance: the cut fired on only {fired} pairs"
    );
}

/// A Spec whose thread panics with its own message (not an assertion).
fn spec_panics() -> Prog {
    prog(|| {
        let _w = named("w", || {
            panic!("conformance: fixture: the specification panicked")
        });
    })
}

/// **C2.** A panic inside a sweep arrives on the caller as itself (joined,
/// `resume_unwind`), and the calling OS thread runs a correct complete-first
/// check afterwards (no stale state from the interrupted outer run).
#[test]
fn c02_a_sweep_panic_arrives_as_itself_and_the_thread_recovers() {
    let v = vis(&["w"]);
    let cc = built(cb(cfg(ConsType::Bag), &v).skip_spec_errfree_check(true));
    let payload = panic_text(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || {
            let _ = rw(&cc, &visible_error(false), &spec_panics(), false);
        },
    )))
    .expect("conformance: the sweep's panic was swallowed");
    assert!(
        payload.contains("conformance: fixture: the specification panicked"),
        "conformance: payload {payload:?}"
    );
    let v = naive_visible(2);
    let cc = built(cb(cfg(ConsType::Bag), &v));
    let o = rw(&cc, &naive(2, 0), &naive(2, 0), false);
    assert_eq!(
        o.counters.sweep_sizes,
        vec![1, 2],
        "conformance: after the panic"
    );
    assert_eq!(class(&run(cc, &naive(2, 0), &naive(2, 0))), "conforms");
}

/// **C7.** `verify` (the public, threaded entry point) dispatches to this
/// engine.
#[test]
fn c14_verify_dispatches_to_complete_first() {
    let v = naive_visible(2);
    let (imp, spec) = (naive(2, 0), naive(2, 1));
    let r = crate::conformance::verify(
        built(cb(cfg(ConsType::Bag), &v)),
        move || imp(),
        move || spec(),
    );
    assert_eq!(class(&r), "reported:2");
    let o = outcome(&r);
    assert_eq!(o.engine(), Engine::CompleteFirst);
    assert_eq!(counters_of(&r).sweep_sizes, vec![2, 2]);
}
