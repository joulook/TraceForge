//! P4-GATED gate 3: the tester's tests for `GVerify`, the gated checker
//! (criteria `P4-GATED.md` revision 3.1).
//!
//! Every expected value below was derived from the criteria's engine facts
//! G1–G6 and the paper (`alg.tex` §8.1 `def:ext`, §8.4 `def:cone`,
//! `cor:absence`, §8.6 `alg:gated`, `thm:gated`, §8.8) **before** `gated.rs`
//! or the diffs were read; the derivations are written out in
//! `plan/traceForge/log/dev/P4-GATED.report.md`, Part 0, under the labels
//! D1..D8 cited on each test. Tests are named by criterion. Expected rendered
//! texts are transcribed from the criteria, not copied from the module's
//! constants. The fixtures of the corpus are `cfirst_tests.rs`'s, copied
//! (that file exports none).
//!
//! Conventions this file keeps because `s5_tests`' source scans read it: no
//! print macro anywhere, and every panic-family message starts with
//! `conformance:`.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::conformance::canon::CanonicalGraph;
use crate::conformance::cert::Certificate;
use crate::conformance::cfirst::{run_with as cfirst_run_with, CFirstOutcome, SweepEnd};
use crate::conformance::config::ConfConfig;
use crate::conformance::ctx::{
    CompletionSink, ConfMode, Diagnostic, Gate, GateAt, GateSink, GateVerdict, SinkVerdict,
};
use crate::conformance::gated::{run_with as gated_run_with, GatedOutcome, ReportSite};
use crate::conformance::morphism::{matches, statuses, statuses_agree, CompleteExecution};
use crate::conformance::obs::wobs;
use crate::conformance::report::replay_snapshot;
use crate::conformance::selector::Selector;
use crate::conformance::sig::{cone, covered, Summary};
use crate::conformance::stateful::{
    enumerate, run_with as stateful_run_with, EnumRun, StatefulOutcome,
};
use crate::conformance::witness::WitnessCache;
use crate::conformance::{
    ConfBuilder, ConfError, ConfOutcome, ConfVerdict, Diagnostics, Engine, GatePolicy,
    GatedCounters, GatedMode, NotACertificate, ReplaySnapshot, ReportCause, ReportGate, ReportTag,
    ScopeField, SearchEnd, SpecErrFreedom,
};
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;
use crate::must::MustState;
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

fn bag() -> Config {
    cfg(ConsType::Bag)
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

/// A gated `ConfBuilder` under `ltr`, the given policy and mode.
fn gb(config: Config, visible: &[String], policy: GatePolicy, mode: GatedMode) -> ConfBuilder {
    ConfBuilder::new()
        .config(config)
        .visible_threads(visible.to_vec())
        .engine(Engine::Gated)
        .gate_policy(policy)
        .gated_mode(mode)
}

fn built(b: ConfBuilder) -> ConfConfig {
    b.build()
        .expect("conformance: the test configuration is in scope")
}

fn gcc(config: Config, visible: &[String], policy: GatePolicy, mode: GatedMode) -> ConfConfig {
    built(gb(config, visible, policy, mode))
}

/// Exhaustive, `Always`, `ltr` — the criteria's default fixture setting.
fn always(config: Config, visible: &[String]) -> ConfConfig {
    gcc(config, visible, GatePolicy::Always, GatedMode::Exhaustive)
}

fn ff(config: Config, visible: &[String], policy: GatePolicy) -> ConfConfig {
    gcc(config, visible, policy, GatedMode::FirstFailure)
}

fn with_sel(cc: &ConfConfig, s: Selector) -> ConfConfig {
    let mut c = cc.clone();
    c.config.selector = s;
    c
}

/// The engine-only entry point (criterion 11).
fn grw(cc: &ConfConfig, imp: &Prog, spec: &Prog, keep: bool) -> GatedOutcome {
    gated_run_with(cc, imp, spec, keep)
}

fn cb(config: Config, visible: &[String]) -> ConfConfig {
    built(
        ConfBuilder::new()
            .config(config)
            .visible_threads(visible.to_vec())
            .engine(Engine::CompleteFirst),
    )
}

fn sb(config: Config, visible: &[String]) -> ConfConfig {
    built(
        ConfBuilder::new()
            .config(config)
            .visible_threads(visible.to_vec())
            .engine(Engine::Stateful),
    )
}

fn crw(cc: &ConfConfig, imp: &Prog, spec: &Prog) -> CFirstOutcome {
    cfirst_run_with(cc, imp, spec, true)
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

fn gated_counters_of(v: &Result<ConfVerdict, ConfError>) -> GatedCounters {
    outcome(v)
        .gated_counters()
        .expect("conformance: a gated outcome without counters")
        .clone()
}

fn rendering(r: &Result<ConfVerdict, ConfError>) -> String {
    format!("{}", r.as_ref().expect("conformance: a verdict"))
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

fn report_keys(o: &GatedOutcome, visible: &[String]) -> Vec<String> {
    let gs: Vec<ExecutionGraph> = o.reports.iter().map(|(g, _, _)| g.clone()).collect();
    keys(&gs, visible)
}

fn cfirst_report_keys(o: &CFirstOutcome, visible: &[String]) -> Vec<String> {
    let gs: Vec<ExecutionGraph> = o.reports.iter().map(|(g, _)| g.clone()).collect();
    keys(&gs, visible)
}

fn stateful_report_keys(o: &StatefulOutcome, visible: &[String]) -> Vec<String> {
    let gs: Vec<ExecutionGraph> = o.reports.iter().map(|(g, _)| g.clone()).collect();
    keys(&gs, visible)
}

fn summary(g: &ExecutionGraph, v: &[String]) -> Summary {
    let w = wobs(g, v).expect("conformance: wobs on a fixture graph");
    Summary::of(CompleteExecution::assume_finished_at_gate(g), &w, v)
        .expect("conformance: summary on a fixture graph")
}

fn label_count(g: &ExecutionGraph) -> usize {
    g.thread_ids().into_iter().map(|t| g.thread_size(t)).sum()
}

/// The word of thread `n` in `g`, rendered (`wobs`), for narrative checks.
fn word_of(g: &ExecutionGraph, v: &[String], n: &str) -> String {
    let w = wobs(g, v).expect("conformance: wobs on a fixture graph");
    let obs: Vec<String> = w.of(n).iter().map(|(_, o)| format!("{o:?}")).collect();
    obs.join(" ")
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
// Counter rows (criterion 9)
// =========================================================================

/// The gate family as a comparable row: `[gates, inert, skipped_replay,
/// skipped_certified, declined, c1_carried, carried_hits, c1_cache,
/// gate_cache_hits, c1_sweep, gate_sweeps, succ, fail, budgeted, aborted,
/// certificates_set, certificate_resets, states_pushed,
/// certified_states_revisited, reports_certified,
/// reports_by_completion_test]`.
fn grow(c: &GatedCounters) -> [usize; 21] {
    [
        c.gates,
        c.gates_inert,
        c.gates_skipped_replay,
        c.gates_skipped_certified,
        c.gates_declined,
        c.c1_tests_carried,
        c.carried_hits,
        c.c1_tests_cache,
        c.gate_cache_hits,
        c.c1_tests_sweep,
        c.gate_sweeps,
        c.gate_sweeps_successful,
        c.gate_sweeps_failing,
        c.gate_sweeps_budgeted,
        c.gate_sweeps_aborted,
        c.certificates_set,
        c.certificate_resets,
        c.states_pushed,
        c.certified_states_revisited,
        c.reports_certified,
        c.reports_by_completion_test,
    ]
}

/// The completion family: `[impl_graphs, probes, cache_hits, cache_tests,
/// sweeps, succ, fail, aborted, witnesses, duplicates, reports]`.
fn crow(c: &GatedCounters) -> [usize; 11] {
    [
        c.impl_graphs,
        c.completion_probes,
        c.completion_cache_hits,
        c.completion_cache_tests,
        c.completion_sweeps,
        c.completion_sweeps_successful,
        c.completion_sweeps_failing,
        c.completion_sweeps_aborted,
        c.witnesses,
        c.witness_duplicates,
        c.reports,
    ]
}

const GROW: &str = "[gates, inert, replay, certified, declined, c1_carried, carried_hits, \
     c1_cache, cache_hits, c1_sweep, gate_sweeps, succ, fail, budgeted, aborted, certs, resets, \
     pushed, certified_revisited, rep_certified, rep_by_test]";
const CROW: &str =
    "[impl, probes, hits, cache_tests, sweeps, succ, fail, aborted, witnesses, dups, reports]";

fn assert_rows(c: &GatedCounters, g: [usize; 21], k: [usize; 11], what: &str) {
    assert_eq!(grow(c), g, "conformance: {what}: gate row {GROW}");
    assert_eq!(crow(c), k, "conformance: {what}: completion row {CROW}");
}

/// Criterion 9's identities, on every fixture; the policy- and
/// mode-specific consequences of G3–G5; and, with `keep`, the kept graphs'
/// agreement with the counters and `W`'s admission order.
fn identities(o: &GatedOutcome, v: &[String], first_failure: bool, policy: GatePolicy, what: &str) {
    let c = &o.counters;
    assert_eq!(
        c.gates,
        c.gates_skipped_certified
            + c.gates_declined
            + c.carried_hits
            + c.gate_cache_hits
            + c.gate_sweeps,
        "conformance: {what}: gates identity: {c:?}"
    );
    assert_eq!(
        c.gate_sweeps,
        c.gate_sweeps_successful
            + c.gate_sweeps_failing
            + c.gate_sweeps_budgeted
            + c.gate_sweeps_aborted,
        "conformance: {what}: gate sweeps split"
    );
    assert_eq!(
        c.gate_sweep_sizes.len(),
        c.gate_sweeps,
        "conformance: {what}"
    );
    assert_eq!(
        c.c1_tests_sweep,
        c.gate_sweep_sizes.iter().sum::<usize>(),
        "conformance: {what}: c1_tests_sweep = sum of gate sweep sizes"
    );
    assert_eq!(
        c.certificates_set, c.gate_sweeps_failing,
        "conformance: {what}: certificates = failing gate sweeps"
    );
    assert!(
        c.carried_hits <= c.c1_tests_carried && c.gate_cache_hits <= c.c1_tests_cache,
        "conformance: {what}: hits exceed tests: {c:?}"
    );
    assert!(
        c.certified_states_revisited <= c.states_pushed,
        "conformance: {what}"
    );
    assert_eq!(
        c.completion_sweeps,
        c.completion_sweeps_successful + c.completion_sweeps_failing + c.completion_sweeps_aborted,
        "conformance: {what}: completion sweeps split"
    );
    assert_eq!(
        c.completion_sweep_sizes.len(),
        c.completion_sweeps,
        "conformance: {what}"
    );
    assert_eq!(c.witness_duplicates, 0, "conformance: {what}: duplicates");
    assert_eq!(
        c.witnesses,
        c.gate_sweeps_successful + c.completion_sweeps_successful,
        "conformance: {what}: witnesses = successful sweeps"
    );
    assert_eq!(c.witnesses, o.witnesses.len(), "conformance: {what}: W");
    assert_eq!(c.reports, o.reports.len(), "conformance: {what}: list");
    assert_eq!(
        c.reports_by_completion_test, c.completion_sweeps_failing,
        "conformance: {what}"
    );
    let gate_reports = o
        .reports
        .iter()
        .filter(|r| matches!(r.2, ReportSite::Gate(_)))
        .count();
    if first_failure {
        assert!(c.reports <= 1, "conformance: {what}: first-failure reports");
        assert_eq!(
            c.reports,
            c.reports_certified + c.reports_by_completion_test + gate_reports,
            "conformance: {what}"
        );
    } else {
        assert_eq!(
            gate_reports, 0,
            "conformance: {what}: exhaustive gate report"
        );
        assert_eq!(
            c.reports,
            c.reports_certified + c.reports_by_completion_test,
            "conformance: {what}: reports identity"
        );
    }
    assert_eq!(
        c.impl_graphs,
        c.completion_cache_hits + c.completion_sweeps + c.reports_certified,
        "conformance: {what}: impl_graphs identity: {c:?}"
    );
    assert_eq!(
        c.completion_probes + c.reports_certified,
        c.impl_graphs,
        "conformance: {what}: one probe per uncertified completion"
    );
    assert_eq!(
        o.sweep_ends.len(),
        c.gate_sweeps + c.completion_sweeps,
        "conformance: {what}: ends"
    );
    let count = |e: SweepEnd| o.sweep_ends.iter().filter(|x| **x == e).count();
    assert_eq!(
        (
            count(SweepEnd::Witness),
            count(SweepEnd::Exhausted),
            count(SweepEnd::Budgeted),
            count(SweepEnd::Aborted)
        ),
        (
            c.gate_sweeps_successful + c.completion_sweeps_successful,
            c.gate_sweeps_failing + c.completion_sweeps_failing,
            c.gate_sweeps_budgeted,
            c.gate_sweeps_aborted + c.completion_sweeps_aborted
        ),
        "conformance: {what}: ends by kind"
    );
    assert_eq!(
        o.aborted,
        c.gate_sweeps_aborted + c.completion_sweeps_aborted > 0,
        "conformance: {what}: aborted"
    );
    assert!(
        c.gate_sweeps_aborted + c.completion_sweeps_aborted <= 1,
        "conformance: {what}: more than one abort"
    );
    assert_eq!(
        c.paper_events_at_first_report.is_some(),
        c.reports > 0,
        "conformance: {what}: paper events at first report"
    );
    assert_eq!(c.first_failure_mode, first_failure, "conformance: {what}");
    assert!(o.executions >= c.impl_graphs, "conformance: {what}");
    assert!(
        !c.precheck_ran && c.precheck_wall_time_ms == 0,
        "conformance: {what}"
    );
    match policy {
        GatePolicy::Never => {
            assert_eq!(
                (
                    c.c1_tests_carried,
                    c.carried_hits,
                    c.c1_tests_cache,
                    c.gate_cache_hits,
                    c.gate_sweeps,
                    c.gates_skipped_certified,
                    c.certificates_set,
                    c.certificate_resets,
                    c.reports_certified
                ),
                (0, 0, 0, 0, 0, 0, 0, 0, 0),
                "conformance: {what}: Never runs no cone test and sets no certificate"
            );
            assert_eq!(c.gates, c.gates_declined, "conformance: {what}: Never");
        }
        GatePolicy::Always => assert_eq!(
            (c.gates_declined, c.gate_sweeps_budgeted),
            (0, 0),
            "conformance: {what}: Always"
        ),
        GatePolicy::Budget(b) => {
            assert_eq!(c.gates_declined, 0, "conformance: {what}: Budget");
            for (i, s) in c.gate_sweep_sizes.iter().enumerate() {
                assert!(
                    *s <= b,
                    "conformance: {what}: gate sweep {i} tested {s} > {b}"
                );
            }
        }
    }
    if !matches!(policy, GatePolicy::Budget(_)) {
        assert_eq!(c.gate_sweeps_budgeted, 0, "conformance: {what}");
    }
    if o.kept_impl_graphs.is_empty() && o.kept_spec_graphs.is_empty() {
        return;
    }
    assert_eq!(
        o.kept_impl_graphs.len(),
        c.impl_graphs,
        "conformance: {what}: kept impl"
    );
    assert_eq!(
        o.kept_spec_graphs.len(),
        o.sweep_ends.len(),
        "conformance: {what}: kept spec per sweep"
    );
    // Interleaved gate and completion sweeps, matched against the two size
    // vectors in order, by kind: a sweep that is the gate's is one whose
    // sizes queue matches. The total must agree whatever the interleaving.
    let kept_total: usize = o.kept_spec_graphs.iter().map(Vec::len).sum();
    assert_eq!(
        kept_total,
        c.c1_tests_sweep + c.completion_sweep_sizes.iter().sum::<usize>(),
        "conformance: {what}: kept spec graphs = tested graphs"
    );
    // `W` in admission order: the last kept graph of every successful sweep.
    let admitted: Vec<String> = o
        .sweep_ends
        .iter()
        .zip(&o.kept_spec_graphs)
        .filter(|(e, _)| **e == SweepEnd::Witness)
        .map(|(_, s)| {
            full_key(
                s.last()
                    .expect("conformance: a successful sweep kept no graph"),
                v,
            )
        })
        .collect();
    let held: Vec<String> = o
        .witnesses
        .entries()
        .iter()
        .map(|m| full_key(m.graph(), v))
        .collect();
    assert_eq!(held, admitted, "conformance: {what}: W in admission order");
}

/// The morphism reference of Part 4 criterion 5: the members of `graphs`
/// that no graph of `family` covers (`matches` plus agreeing statuses).
fn reference(graphs: &[ExecutionGraph], family: &[ExecutionGraph], v: &[String]) -> Vec<String> {
    let fam: Vec<_> = family
        .iter()
        .map(|m| {
            let w = wobs(m, v).expect("conformance: wobs");
            let st = statuses(CompleteExecution::assume_finished_at_gate(m), &w, v)
                .expect("conformance: statuses");
            (m, w, st)
        })
        .collect();
    let out: Vec<ExecutionGraph> = graphs
        .iter()
        .filter(|g| {
            let w = wobs(g, v).expect("conformance: wobs");
            let st = statuses(CompleteExecution::assume_finished_at_gate(g), &w, v)
                .expect("conformance: statuses");
            !fam.iter()
                .any(|(m, wm, sm)| matches(m, g, wm, &w, v) && statuses_agree(sm, &st))
        })
        .cloned()
        .collect();
    keys(&out, v)
}

const POLICIES: [GatePolicy; 4] = [
    GatePolicy::Never,
    GatePolicy::Always,
    GatePolicy::Budget(1),
    GatePolicy::Budget(2),
];

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
// This part's own fixtures
// =========================================================================

/// `ex:naive` in both `P4-SELECTOR` criterion 6 encodings: `c_first` is
/// encoding 1 (spawn `c, b1..bk, a`), otherwise encoding 2 (spawn `b1..bk,
/// a, c`). `c` sends `v` to `a`'s channel, then receives `k` times; each
/// `b_i` sends 1 to `c`'s channel; `a` skips.
fn naive_enc(k: usize, v: i32, c_first: bool) -> Prog {
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

/// Criterion 5's revisit fixture (E2): encoding 2's threads, `main` spawning
/// `b1, c, b2..bk, a`.
fn naive_e2(k: usize, v: i32) -> Prog {
    prog(move || {
        let (tx_a, _rx_a) = chan();
        let (tx_c, rx_c) = chan();
        let t1 = tx_c.clone();
        let _b1 = named("b1", move || t1.send_msg(1));
        let _c = named("c", move || {
            tx_a.send_msg(v);
            for _ in 0..k {
                let _x: i32 = rx_c.recv_msg_block();
            }
        });
        for i in 2..=k {
            let t = tx_c.clone();
            let _b = named(&format!("b{i}"), move || t.send_msg(1));
        }
        let _a = named("a", || {});
    })
}

/// Plan §5.3 / §5.1's three-thread program: `a` sends 1 (tag 1), `b` sends 2
/// (tag 2), both to one channel `main` creates; `c` receives once — any
/// message, or (`only = Some(t)`) only tag `t`, the paper's guarded receive.
/// `order` is the spawn order, e.g. `"acb"`.
fn abc(order: &'static str, only: Option<u32>) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let mut rx = Some(rx);
        for ch in order.chars() {
            match ch {
                'a' => {
                    let t = tx.clone();
                    let _a = named("a", move || t.send_tagged_msg(1, 1));
                }
                'b' => {
                    let t = tx.clone();
                    let _b = named("b", move || t.send_tagged_msg(2, 2));
                }
                'c' => {
                    let r = rx.take().expect("conformance: one receiver");
                    let _c = named("c", move || {
                        let _x: i32 = match only {
                            Some(tag) => r.recv_tagged_msg_block(move |t| t == Some(tag)),
                            None => r.recv_msg_block(),
                        };
                    });
                }
                _ => unreachable!("conformance: a spawn order names a, b, c only"),
            }
        }
    })
}

/// Criterion 12's pair (round 01 M6): `a: send(c,1) ‖ b: send(c,2) ‖ c: x :=
/// recv(); send(d, 2 | x)` — Impl sends 2, Spec forwards `x`; `d` is an
/// undeclared thread that never receives, its mailbox a channel. `main`
/// spawns `a, b, c, d`.
fn forward_pair(spec: bool) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let (tx_d, _rx_d) = chan();
        let ta = tx.clone();
        let _a = named("a", move || ta.send_tagged_msg(1, 1));
        let _b = named("b", move || tx.send_tagged_msg(2, 2));
        let _c = named("c", move || {
            let x: i32 = rx.recv_msg_block();
            tx_d.send_msg(if spec { x } else { 2 });
        });
        let _d = named("d", || {});
    })
}

/// Visible senders, an invisible receiver: `a` sends 1, `b` sends 2 to the
/// channel the invisible `r` receives from once. `order` is the spawn order
/// (`"arb"`: a backward revisit of `r` by the visible `b`; `"abr"`: a
/// forward pop at the invisible `r`). Self-conformance, `Tvis = {a, b}`.
fn inv_recv(order: &'static str) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let mut rx = Some(rx);
        for ch in order.chars() {
            match ch {
                'a' => {
                    let t = tx.clone();
                    let _a = named("a", move || t.send_msg(1));
                }
                'b' => {
                    let t = tx.clone();
                    let _b = named("b", move || t.send_msg(2));
                }
                'r' => {
                    let r = rx.take().expect("conformance: one receiver");
                    let _r = named("r", move || {
                        let _x: i32 = r.recv_msg_block();
                    });
                }
                _ => unreachable!("conformance: a spawn order names a, b, r only"),
            }
        }
    })
}

/// Criterion 8's gate-abort pair: `a: skip | assert(false) ‖ b: send(B,0);
/// send(B,1)`; `b`'s mailbox a channel nobody reads; spawned `a, b`.
fn growing2(fails: bool) -> Prog {
    prog(move || {
        let (tx, _rx) = chan();
        let _a = named("a", move || {
            if fails {
                crate::assert(false);
            }
        });
        let _b = named("b", move || {
            tx.send_msg(0);
            tx.send_msg(1);
        });
    })
}

fn fact(k: usize) -> usize {
    (1..=k).product()
}

/// `Σ_{i=1}^{k} k!/(k−i)!`: the receive installations of Must's tree on
/// `ex:naive` (round 02 M2): 4 at `k = 2`, 15 at `k = 3`.
fn sigma(k: usize) -> usize {
    (1..=k).map(|i| fact(k) / fact(k - i)).sum()
}

const ABC: [&str; 3] = ["a", "b", "c"];

// =========================================================================
// Criterion 1 — `Never` is complete-first plus the gates' bookkeeping
// =========================================================================

/// **Criterion 1 (D8).** On every corpus pair, `Engine::Gated` under `Never`
/// and `Engine::CompleteFirst`: equal report keys (multisets), verdicts,
/// kept Impl multisets, completion-sweep counters and ends, executions and
/// `L`; `gate_sweeps = 0` and `gates = gates_declined`.
#[test]
fn c01_never_is_complete_first_plus_bookkeeping() {
    let mut failures = Vec::new();
    let mut pairs = 0;
    let mut declined_total = 0;
    for p in corpus() {
        let v = &p.visible;
        let gc = gcc(
            p.config.clone(),
            v,
            GatePolicy::Never,
            GatedMode::Exhaustive,
        );
        let o = grw(&gc, &p.imp, &p.spec, true);
        identities(&o, v, false, GatePolicy::Never, &p.name);
        let cc = cb(p.config.clone(), v);
        let c = crw(&cc, &p.imp, &p.spec);
        if report_keys(&o, v) != cfirst_report_keys(&c, v) {
            failures.push(format!("{}: report keys", p.name));
        }
        if keys(&o.kept_impl_graphs, v) != keys(&c.kept_impl_graphs, v) {
            failures.push(format!("{}: kept impl multisets", p.name));
        }
        let g = &o.counters;
        let f = &c.counters;
        let got = (
            g.impl_graphs,
            g.completion_probes,
            g.completion_cache_hits,
            g.completion_cache_tests,
            g.completion_sweeps,
            g.completion_sweeps_successful,
            g.completion_sweeps_failing,
            g.completion_sweeps_aborted,
            g.completion_sweep_sizes.clone(),
            g.witnesses,
            g.reports,
        );
        let want = (
            f.impl_graphs,
            f.cache_probes,
            f.cache_hits,
            f.cache_tests,
            f.sweeps,
            f.sweeps_successful,
            f.sweeps_failing,
            f.sweeps_aborted,
            f.sweep_sizes.clone(),
            f.witnesses,
            f.reports,
        );
        if got != want {
            failures.push(format!(
                "{}: completion counters {got:?} vs {want:?}",
                p.name
            ));
        }
        if o.sweep_ends != c.sweep_ends {
            failures.push(format!("{}: sweep ends", p.name));
        }
        let ks: Vec<Vec<String>> = o.kept_spec_graphs.iter().map(|s| keys(s, v)).collect();
        let kc: Vec<Vec<String>> = c.kept_spec_graphs.iter().map(|s| keys(s, v)).collect();
        if ks != kc {
            failures.push(format!("{}: swept graphs", p.name));
        }
        if (o.executions, o.max_paper_events, o.impl_end)
            != (c.executions, c.max_paper_events, c.impl_end)
        {
            failures.push(format!("{}: executions/L/end", p.name));
        }
        if (g.gate_sweeps, g.gates) != (0, g.gates_declined) {
            failures.push(format!("{}: gate work under Never: {g:?}", p.name));
        }
        declined_total += g.gates_declined;
        let (gv, cv) = (
            class(&run(gc, &p.imp, &p.spec)),
            class(&run(cc, &p.imp, &p.spec)),
        );
        if gv != cv {
            failures.push(format!("{}: verdicts {gv} vs {cv}", p.name));
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 1: {failures:#?}"
    );
    assert!(pairs >= 90, "conformance: only {pairs} pairs");
    assert!(
        declined_total > 100,
        "conformance: the corpus declined only {declined_total} gates: vacuous"
    );
}

// =========================================================================
// Criterion 2 — `thm:gated`, exhaustive, every policy
// =========================================================================

/// **Criterion 2 (D8).** Under `Never`, `Always`, `Budget(1)`, `Budget(2)`
/// (and, adversarially, `Budget(0)`), on every corpus pair: the report keys
/// equal the stateful checker's and the morphism reference over the stateful
/// family; every swept graph and every witness is a member of the family;
/// every failing sweep — gate or completion — swept the whole family (what
/// a certificate rests on); every budgeted sweep tested exactly `B`.
#[test]
fn c02_thm_gated_exhaustive_every_policy() {
    let mut failures = Vec::new();
    let (mut pairs, mut certs, mut certified, mut budgeted, mut gate_hits) = (0, 0, 0, 0, 0);
    for p in corpus() {
        let v = &p.visible;
        let s = srw(&sb(p.config.clone(), v), &p.imp, &p.spec);
        assert_eq!(
            s.spec_end,
            SearchEnd::StateSpaceExhausted,
            "conformance: {}",
            p.name
        );
        let want = stateful_report_keys(&s, v);
        let fam: BTreeSet<String> = s.kept_spec_graphs.iter().map(|m| full_key(m, v)).collect();
        let mut policies = POLICIES.to_vec();
        policies.push(GatePolicy::Budget(0));
        for policy in policies {
            let what = format!("{} {policy:?}", p.name);
            let gc = gcc(p.config.clone(), v, policy, GatedMode::Exhaustive);
            let o = grw(&gc, &p.imp, &p.spec, true);
            identities(&o, v, false, policy, &what);
            assert_eq!(
                o.impl_end,
                SearchEnd::StateSpaceExhausted,
                "conformance: {what}"
            );
            if report_keys(&o, v) != want {
                failures.push(format!("{what}: report keys differ from the stateful run"));
            }
            if reference(&o.kept_impl_graphs, &s.kept_spec_graphs, v) != report_keys(&o, v) {
                failures.push(format!("{what}: report keys differ from the reference"));
            }
            for (i, (end, swept)) in o.sweep_ends.iter().zip(&o.kept_spec_graphs).enumerate() {
                if swept.iter().any(|m| !fam.contains(&full_key(m, v))) {
                    failures.push(format!("{what}: sweep {i} left the family"));
                }
                if *end == SweepEnd::Exhausted {
                    let got: BTreeSet<String> = swept.iter().map(|m| full_key(m, v)).collect();
                    if got != fam || swept.len() != s.kept_spec_graphs.len() {
                        failures.push(format!("{what}: failing sweep {i} is not the family"));
                    }
                }
                if *end == SweepEnd::Budgeted {
                    budgeted += 1;
                    if let GatePolicy::Budget(b) = policy {
                        if swept.len() != b || b >= s.kept_spec_graphs.len() {
                            failures.push(format!(
                                "{what}: budgeted sweep {i} tested {} of {}",
                                swept.len(),
                                s.kept_spec_graphs.len()
                            ));
                        }
                    }
                }
            }
            if o.witnesses
                .entries()
                .iter()
                .any(|m| !fam.contains(&full_key(m.graph(), v)))
            {
                failures.push(format!("{what}: a witness outside the family"));
            }
            certs += o.counters.certificates_set;
            certified += o.counters.reports_certified;
            gate_hits += o.counters.gate_cache_hits + o.counters.carried_hits;
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 2: {failures:#?}"
    );
    assert!(pairs >= 90, "conformance: only {pairs} pairs");
    assert!(
        certs >= 20 && certified >= 20 && budgeted >= 20 && gate_hits >= 50,
        "conformance: vacuity: certs {certs}, certified {certified}, budgeted {budgeted}, \
         gate hits {gate_hits}"
    );
}

// =========================================================================
// Criterion 3 — first-failure decides
// =========================================================================

/// **Criterion 3 (D8, m7).** On every corpus pair, under each policy: the
/// first-failure run is silent iff the exhaustive run is; a reporting run
/// has exactly one report, end `StoppedAtFirstReport`, `executions >= 1`; a
/// gate report (tag `GrowingExhaustion`) passes `cone` against no graph of
/// the stateful family, and every kept exhaustive Impl graph it certifies
/// (`valid_at`) is uncovered, at least one existing; a completion report
/// fails `covered` against the whole family. The public path agrees on the
/// tag and the site.
#[test]
fn c03_first_failure_decides_on_the_corpus() {
    let mut failures = Vec::new();
    let (mut pairs, mut gate_reports, mut completion_reports) = (0, 0, 0);
    for p in corpus() {
        let v = &p.visible;
        let s = srw(&sb(p.config.clone(), v), &p.imp, &p.spec);
        let fam: Vec<(ExecutionGraph, Summary)> = s
            .kept_spec_graphs
            .iter()
            .map(|m| (m.clone(), summary(m, v)))
            .collect();
        for policy in POLICIES {
            let what = format!("{} {policy:?}", p.name);
            let ex = grw(
                &gcc(p.config.clone(), v, policy, GatedMode::Exhaustive),
                &p.imp,
                &p.spec,
                true,
            );
            let fc = ff(p.config.clone(), v, policy);
            let o = grw(&fc, &p.imp, &p.spec, false);
            identities(&o, v, true, policy, &what);
            if o.reports.is_empty() != ex.reports.is_empty() {
                failures.push(format!("{what}: silent iff exhaustive silent"));
                continue;
            }
            if o.reports.is_empty() {
                if o.impl_end != SearchEnd::StateSpaceExhausted {
                    failures.push(format!("{what}: silent but {:?}", o.impl_end));
                }
                continue;
            }
            if o.reports.len() != 1
                || o.impl_end != SearchEnd::StoppedAtFirstReport
                || o.executions < 1
            {
                failures.push(format!(
                    "{what}: {} reports, {:?}, {} executions",
                    o.reports.len(),
                    o.impl_end,
                    o.executions
                ));
                continue;
            }
            let (g, _, site) = &o.reports[0];
            let pub_r = run(fc.clone().with_skip(), &p.imp, &p.spec);
            let pr0 = &outcome(&pub_r).reports()[0];
            match site {
                ReportSite::Gate(gate) => {
                    gate_reports += 1;
                    if pr0.tag() != ReportTag::GrowingExhaustion
                        || pr0.gate() != ReportGate::of(Some(*gate))
                    {
                        failures.push(format!("{what}: public tag/gate {:?}", pr0.gate()));
                    }
                    let gw = wobs(g, v).expect("conformance: wobs");
                    for (m, _) in &fam {
                        let mw = wobs(m, v).expect("conformance: wobs");
                        if cone(g, &gw, m, &mw, v) {
                            failures.push(format!("{what}: a family graph passes cone"));
                        }
                    }
                    let cert = Certificate::absence_established(g, v)
                        .expect("conformance: the report's canonical form");
                    let ext: Vec<&ExecutionGraph> = ex
                        .kept_impl_graphs
                        .iter()
                        .filter(|k| cert.valid_at(k, v).expect("conformance: valid_at"))
                        .collect();
                    if ext.is_empty() {
                        failures.push(format!("{what}: no kept completion extends the report"));
                    }
                    for k in ext {
                        let ks = summary(k, v);
                        if fam.iter().any(|(_, ms)| covered(&ks, ms)) {
                            failures.push(format!("{what}: a certified completion is covered"));
                        }
                    }
                }
                ReportSite::Completion => {
                    completion_reports += 1;
                    if pr0.tag() != ReportTag::CompleteCoverage
                        || pr0.gate() != ReportGate::Completion
                    {
                        failures.push(format!("{what}: public tag {:?}", pr0.tag()));
                    }
                    let gs = summary(g, v);
                    if fam.iter().any(|(_, ms)| covered(&gs, ms)) {
                        failures.push(format!("{what}: a covered completion reported"));
                    }
                }
            }
        }
        pairs += 1;
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 3: {failures:#?}"
    );
    assert!(pairs >= 90, "conformance: only {pairs} pairs");
    assert!(
        gate_reports >= 20 && completion_reports >= 10,
        "conformance: vacuity: {gate_reports} gate, {completion_reports} completion reports"
    );
}

trait WithSkip {
    fn with_skip(self) -> Self;
}

impl WithSkip for ConfConfig {
    /// The precheck skipped on the public path (the corpus is admissible;
    /// criteria 3–7 skip it).
    fn with_skip(mut self) -> Self {
        self.skip_spec_errfree_check = true;
        self
    }
}

/// **Criterion 3 (a) (D3).** First-failure report at a **forward**
/// `RevisitApply`: one report, `GrowingExhaustion`, `StoppedAtFirstReport`,
/// `executions = 1`, `impl_graphs = 1`; the reported graph is `c` reading
/// 2. Exhaustive: report set {c reads 2}, under the certificate.
#[test]
fn c03_a_first_failure_report_at_a_forward_pop() {
    let v = vis(&ABC);
    let (imp, spec) = (abc("abc", None), abc("abc", Some(1)));
    let o = grw(&ff(bag(), &v, GatePolicy::Always), &imp, &spec, true);
    identities(&o, &v, true, GatePolicy::Always, "3a ff");
    assert_rows(
        &o.counters,
        [
            4, 0, 0, 0, 0, 3, 2, 1, 0, 2, 2, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0,
        ],
        [1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1],
        "3a ff",
    );
    assert_eq!(o.counters.gate_sweep_sizes, vec![1, 1]);
    assert_eq!(o.reports.len(), 1);
    assert_eq!(o.reports[0].2, ReportSite::Gate(Gate::RevisitApply));
    // The reported graph is `c` reading `b`'s 2: not the completed graph's
    // word for `c`.
    assert_ne!(
        word_of(&o.reports[0].0, &v, "c"),
        word_of(&o.kept_impl_graphs[0], &v, "c")
    );
    assert_eq!(
        (o.executions, o.impl_end),
        (1, SearchEnd::StoppedAtFirstReport)
    );
    assert_eq!(o.counters.paper_events_at_first_report, Some(3));
    let r = run(ff(bag(), &v, GatePolicy::Always).with_skip(), &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    let rep = &outcome(&r).reports()[0];
    assert_eq!(
        (rep.tag(), rep.gate(), outcome(&r).end()),
        (
            ReportTag::GrowingExhaustion,
            ReportGate::RevisitApply,
            SearchEnd::StoppedAtFirstReport
        )
    );
    let ex = grw(&always(bag(), &v), &imp, &spec, true);
    identities(&ex, &v, false, GatePolicy::Always, "3a ex");
    assert_rows(
        &ex.counters,
        [
            4, 0, 0, 0, 0, 3, 2, 1, 0, 2, 2, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0,
        ],
        [2, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1],
        "3a ex",
    );
    // The exhaustive report is the forward pop's completion: `c` reads `b`'s
    // 2, and it extends the first-failure report.
    assert_eq!(ex.reports.len(), 1);
    let cert = Certificate::absence_established(&o.reports[0].0, &v).unwrap();
    assert!(cert.valid_at(&ex.reports[0].0, &v).unwrap());
    let s = srw(&sb(bag(), &v), &imp, &spec);
    assert_eq!(report_keys(&ex, &v), stateful_report_keys(&s, &v));
}

/// **Criterion 3 (b) (D3).** First-failure report at a **backward**
/// `RevisitApply`: `states_pushed = 1`, `executions = 1`, `impl_graphs = 1`.
#[test]
fn c03_b_first_failure_report_at_a_backward_pop() {
    let v = vis(&ABC);
    let (imp, spec) = (abc("acb", None), abc("acb", Some(1)));
    let o = grw(&ff(bag(), &v, GatePolicy::Always), &imp, &spec, false);
    identities(&o, &v, true, GatePolicy::Always, "3b ff");
    assert_rows(
        &o.counters,
        [
            4, 0, 0, 0, 0, 2, 2, 1, 0, 2, 2, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0,
        ],
        [1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1],
        "3b ff",
    );
    assert_eq!(o.reports[0].2, ReportSite::Gate(Gate::RevisitApply));
    assert_eq!(
        (o.executions, o.impl_end),
        (1, SearchEnd::StoppedAtFirstReport)
    );
    let r = run(ff(bag(), &v, GatePolicy::Always).with_skip(), &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    assert_eq!(outcome(&r).end(), SearchEnd::StoppedAtFirstReport);
    assert_eq!(outcome(&r).reports()[0].gate(), ReportGate::RevisitApply);
    let ex = grw(&always(bag(), &v), &imp, &spec, true);
    identities(&ex, &v, false, GatePolicy::Always, "3b ex");
    assert_rows(
        &ex.counters,
        [
            4, 0, 0, 0, 0, 2, 2, 1, 0, 2, 2, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0,
        ],
        [2, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1],
        "3b ex",
    );
    let s = srw(&sb(bag(), &v), &imp, &spec);
    assert_eq!(report_keys(&ex, &v), stateful_report_keys(&s, &v));
    assert_eq!(ex.impl_end, SearchEnd::StateSpaceExhausted);
}

// =========================================================================
// Criterion 4 — plan §5.3's certificate-reset pair
// =========================================================================

/// **Criterion 4 (D2), exhaustive.** Report set exactly {c reads 1}, under
/// the certificate; every counter as derived gate by gate.
#[test]
fn c04_the_reset_pair_exhaustive() {
    let v = vis(&ABC);
    let (imp, spec) = (abc("acb", None), abc("acb", Some(2)));
    let o = grw(&always(bag(), &v), &imp, &spec, true);
    let s = srw(&sb(bag(), &v), &imp, &spec);
    assert_eq!(report_keys(&o, &v), stateful_report_keys(&s, &v));
    assert_eq!(o.reports.len(), 1);
    assert_eq!(o.reports[0].2, ReportSite::Completion);
    // c reads a's 1: the graph that is not covered.
    let k = &o.reports[0].0;
    assert_eq!(full_key(k, &v), full_key(&o.kept_impl_graphs[0], &v));
    identities(&o, &v, false, GatePolicy::Always, "c4");
    assert_rows(
        &o.counters,
        [
            4, 0, 0, 1, 0, 1, 0, 2, 1, 2, 2, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0,
        ],
        [2, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1],
        "c4",
    );
    assert_eq!(o.counters.gate_sweep_sizes, vec![1, 1]);
    assert_eq!(o.executions, 2);
    let r = run(always(bag(), &v).with_skip(), &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    let pc = gated_counters_of(&r);
    assert_eq!(grow(&pc), grow(&o.counters), "conformance: run vs run_with");
    assert_eq!(crow(&pc), crow(&o.counters), "conformance: run vs run_with");
}

/// **Criterion 4 (D2), first-failure.** One report, the growing graph
/// `{a0, c0←a0}` at gate 2 (`FreshRecv`), `GrowingExhaustion`, the
/// `cor:absence` text, `StoppedAtFirstReport`, `impl_graphs = 0`,
/// `executions = 1`.
#[test]
fn c04_the_reset_pair_first_failure() {
    let v = vis(&ABC);
    let (imp, spec) = (abc("acb", None), abc("acb", Some(2)));
    let o = grw(&ff(bag(), &v, GatePolicy::Always), &imp, &spec, false);
    identities(&o, &v, true, GatePolicy::Always, "c4 ff");
    assert_rows(
        &o.counters,
        [
            2, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0,
        ],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
        "c4 ff",
    );
    assert_eq!(o.reports[0].2, ReportSite::Gate(Gate::FreshRecv));
    assert_eq!(
        (o.executions, o.impl_end),
        (1, SearchEnd::StoppedAtFirstReport)
    );
    // `{a0, c0←a0}`: b has not run.
    let g = &o.reports[0].0;
    assert_eq!(word_of(g, &v, "b"), "", "conformance: b has no event");
    assert_eq!(o.counters.paper_events_at_first_report, Some(2));
    let r = run(ff(bag(), &v, GatePolicy::Always).with_skip(), &imp, &spec);
    assert_eq!(class(&r), "reported:1");
    let rep = &outcome(&r).reports()[0];
    assert_eq!(rep.tag(), ReportTag::GrowingExhaustion);
    assert_eq!(rep.gate(), ReportGate::FreshRecv);
    assert_eq!(
        rep.tag().certifies_under(Engine::Gated),
        ReportTag::GrowingExhaustion.certifies()
    );
    assert!(format!("{rep}").contains(ReportTag::GrowingExhaustion.certifies()));
    assert_eq!(outcome(&r).end(), SearchEnd::StoppedAtFirstReport);
    assert_eq!(gated_counters_of(&r).impl_graphs, 0);
    assert_eq!(outcome(&r).counters().executions, 1);
}

// =========================================================================
// Criterion 5 — `ex:naive`, exhaustive, `Always`
// =========================================================================

/// **Criterion 5 (D4).** Both encodings, `k = 2, 3`, under `ltr` (exact,
/// encoding 1's F49 split as derived by reading in round 02) and `reverse`
/// (sweep figures exact; the F49 split measured, the invariant asserted).
#[test]
fn c05_ex_naive_accounting_both_encodings_both_selectors() {
    for k in [2usize, 3] {
        let (f, sg) = (fact(k), sigma(k));
        let v = naive_visible(k);
        for c_first in [true, false] {
            for sel in [Selector::Ltr, Selector::Reverse] {
                let what = format!("k={k} enc={} {sel:?}", if c_first { 1 } else { 2 });
                let cc = with_sel(&always(bag(), &v), sel);
                let imp = naive_enc(k, 0, c_first);
                let spec = naive_enc(k, 1, c_first);
                let o = grw(&cc, &imp, &spec, false);
                identities(&o, &v, false, GatePolicy::Always, &what);
                let c = &o.counters;
                let skipped = c.gates_skipped_certified + c.gates_skipped_replay;
                if c_first {
                    assert_eq!(c.gate_sweep_sizes, vec![f], "conformance: {what}");
                    assert_eq!(
                        (
                            c.gate_sweeps_successful,
                            c.carried_hits,
                            c.c1_tests_carried,
                            c.c1_tests_cache
                        ),
                        (0, 0, 0, 0),
                        "conformance: {what}"
                    );
                    assert_eq!(skipped, k + sg, "conformance: {what}: certified + replay");
                } else {
                    assert_eq!(c.gate_sweep_sizes, vec![1, f], "conformance: {what}");
                    assert_eq!(
                        (
                            c.gate_sweeps_successful,
                            c.carried_hits,
                            c.c1_tests_carried,
                            c.c1_tests_cache
                        ),
                        (1, k - 1, k, 1),
                        "conformance: {what}"
                    );
                    assert_eq!(skipped, sg, "conformance: {what}: certified + replay");
                }
                assert_eq!(
                    (
                        c.certificates_set,
                        c.gate_sweeps_failing,
                        c.reports_certified,
                        c.reports_by_completion_test,
                        c.completion_sweeps,
                        c.completion_probes,
                        c.certificate_resets,
                        c.states_pushed,
                        c.gates_inert,
                        c.impl_graphs,
                        o.reports.len()
                    ),
                    (1, 1, f, 0, 0, 0, 0, 0, 0, f, f),
                    "conformance: {what}"
                );
                if sel == Selector::Ltr {
                    if c_first {
                        let replay = sg - k - (f - 1);
                        assert_eq!(
                            (c.gates_skipped_certified, c.gates_skipped_replay, c.gates),
                            (2 * k + f - 1, replay, 2 * k + f),
                            "conformance: {what}: round 02's split (5/1/6, 11/7/12)"
                        );
                    } else {
                        assert_eq!(
                            (c.gates_skipped_certified, c.gates_skipped_replay, c.gates),
                            (sg, 0, k + 1 + sg),
                            "conformance: {what}: exact (4/0/7, 15/0/19)"
                        );
                    }
                }
                let s = srw(&sb(cc.config.clone(), &v), &imp, &spec);
                assert_eq!(
                    report_keys(&o, &v),
                    stateful_report_keys(&s, &v),
                    "conformance: {what}"
                );
            }
        }
    }
}

/// **Criterion 5, the revisit fixture (E2, D4).** Spawn `b1, c, b2..bk, a`,
/// `reverse`: every backward pop's fresh slot pays one failing sweep;
/// `gate_sweeps_failing = 1 + states_pushed`, `certified_states_revisited =
/// states_pushed`, sizes `[1, k!, k!, …]`, `k!` reports. `k = 2` exact:
/// `states_pushed = 1`; `k = 3` measured (recorded below).
#[test]
fn c05_the_revisit_fixture() {
    for (k, pushed) in [(2usize, Some(1usize)), (3, None)] {
        let f = fact(k);
        let v = naive_visible(k);
        let what = format!("E2 k={k}");
        let cc = with_sel(&always(bag(), &v), Selector::Reverse);
        let (imp, spec) = (naive_e2(k, 0), naive_e2(k, 1));
        let o = grw(&cc, &imp, &spec, true);
        identities(&o, &v, false, GatePolicy::Always, &what);
        let c = &o.counters;
        assert!(
            c.states_pushed >= 1,
            "conformance: {what}: no backward revisit"
        );
        if let Some(p) = pushed {
            assert_eq!(c.states_pushed, p, "conformance: {what}");
        }
        assert_eq!(
            c.gate_sweeps_failing,
            1 + c.states_pushed,
            "conformance: {what}: one failing sweep per revisit"
        );
        assert_eq!(
            c.certified_states_revisited, c.states_pushed,
            "conformance: {what}"
        );
        let mut sizes = vec![1, f];
        sizes.extend(vec![f; c.states_pushed]);
        assert_eq!(c.gate_sweep_sizes, sizes, "conformance: {what}");
        assert_eq!(
            (
                c.gate_sweeps_successful,
                c.reports_certified,
                o.reports.len(),
                c.completion_sweeps
            ),
            (1, f, f, 0),
            "conformance: {what}"
        );
        assert_eq!(c.certificate_resets, 0, "conformance: {what}");
        let s = srw(&sb(cc.config.clone(), &v), &imp, &spec);
        assert_eq!(report_keys(&o, &v), stateful_report_keys(&s, &v));
        if k == 3 {
            // Measured on this tree, not derived (see the report): recorded so
            // that a change is noticed.
            assert_eq!(
                c.states_pushed, 3,
                "conformance: {what}: recorded states_pushed"
            );
        }
    }
}

// =========================================================================
// Criterion 6 — `ex:naive` first-failure
// =========================================================================

/// **Criterion 6 (D5).** `Always`, `k = 2, 3`, both selectors: encoding 2
/// reports at `c`'s send after `k + 1` paper events with sizes `[1, k!]`;
/// encoding 1 at its first gate, 1 paper event, `[k!]`; both one report,
/// `GrowingExhaustion`, `impl_graphs = 0`, `executions = 1`.
#[test]
fn c06_ex_naive_first_failure() {
    for k in [2usize, 3] {
        let f = fact(k);
        let v = naive_visible(k);
        for c_first in [true, false] {
            for sel in [Selector::Ltr, Selector::Reverse] {
                let what = format!("k={k} enc={} {sel:?}", if c_first { 1 } else { 2 });
                let cc = with_sel(&ff(bag(), &v, GatePolicy::Always), sel);
                let (imp, spec) = (naive_enc(k, 0, c_first), naive_enc(k, 1, c_first));
                let o = grw(&cc, &imp, &spec, false);
                identities(&o, &v, true, GatePolicy::Always, &what);
                let c = &o.counters;
                let (sizes, succ, events) = if c_first {
                    (vec![f], 0, 1)
                } else {
                    (vec![1, f], 1, k + 1)
                };
                assert_eq!(c.gate_sweep_sizes, sizes, "conformance: {what}");
                assert_eq!(c.gate_sweeps_successful, succ, "conformance: {what}");
                assert_eq!(
                    c.paper_events_at_first_report,
                    Some(events),
                    "conformance: {what}"
                );
                assert_eq!(
                    c.gates,
                    if c_first { 1 } else { k + 1 },
                    "conformance: {what}"
                );
                assert_eq!(
                    (o.reports.len(), c.impl_graphs, o.executions, o.impl_end),
                    (1, 0, 1, SearchEnd::StoppedAtFirstReport),
                    "conformance: {what}"
                );
                assert_eq!(o.reports[0].2, ReportSite::Gate(Gate::FreshSend));
                let r = run(cc.clone().with_skip(), &imp, &spec);
                assert_eq!(class(&r), "reported:1", "conformance: {what}");
                assert_eq!(outcome(&r).reports()[0].tag(), ReportTag::GrowingExhaustion);
                assert_eq!(
                    gated_counters_of(&r).paper_events_at_first_report,
                    Some(events)
                );
                // m6: the public `ConfCounters` carries the engine's figure too.
                assert_eq!(
                    outcome(&r).counters().paper_events_at_first_report,
                    Some(events),
                    "conformance: {what}: ConfCounters"
                );
            }
        }
    }
}

// =========================================================================
// Criterion 7 — the policies
// =========================================================================

/// **Criterion 7 (D6).** Encoding 2, exhaustive, `ltr` exact at `k = 2, 3`:
/// `Never` (Part 4's completion figures; every gate declined), `Budget(B)`
/// for `B = 1` and `B = k! − 1` (budgeted, `1 + Σ` budgeted sweeps), and
/// `B = k!` (criterion 5's row: failing, certificate).
#[test]
fn c07_policies_on_encoding_2_ltr() {
    for k in [2usize, 3] {
        let (f, sg) = (fact(k), sigma(k));
        let v = naive_visible(k);
        let (imp, spec) = (naive_enc(k, 0, false), naive_enc(k, 1, false));
        let gates = k + 1 + sg;

        let o = grw(
            &gcc(bag(), &v, GatePolicy::Never, GatedMode::Exhaustive),
            &imp,
            &spec,
            false,
        );
        identities(&o, &v, false, GatePolicy::Never, "Never");
        let mut g = [0usize; 21];
        g[0] = gates;
        g[4] = gates;
        g[20] = f;
        assert_rows(
            &o.counters,
            g,
            [f, f, 0, 0, f, 0, f, 0, 0, 0, f],
            &format!("Never k={k}"),
        );
        assert_eq!(o.counters.completion_sweep_sizes, vec![f; f]);

        let mut budgets = vec![1usize, f - 1];
        budgets.dedup();
        for b in budgets {
            let what = format!("Budget({b}) k={k}");
            let o = grw(
                &gcc(bag(), &v, GatePolicy::Budget(b), GatedMode::Exhaustive),
                &imp,
                &spec,
                false,
            );
            identities(&o, &v, false, GatePolicy::Budget(b), &what);
            let budgeted = 1 + sg;
            assert_rows(
                &o.counters,
                [
                    gates,
                    0,
                    0,
                    0,
                    0,
                    k,
                    k - 1,
                    1 + sg,
                    0,
                    1 + b * budgeted,
                    1 + budgeted,
                    1,
                    0,
                    budgeted,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    f,
                ],
                [f, f, 0, f, f, 0, f, 0, 1, 0, f],
                &what,
            );
            let mut sizes = vec![1];
            sizes.extend(vec![b; budgeted]);
            assert_eq!(o.counters.gate_sweep_sizes, sizes, "conformance: {what}");
        }

        let what = format!("Budget(k!) k={k}");
        let o = grw(
            &gcc(bag(), &v, GatePolicy::Budget(f), GatedMode::Exhaustive),
            &imp,
            &spec,
            false,
        );
        identities(&o, &v, false, GatePolicy::Budget(f), &what);
        let a = grw(&always(bag(), &v), &imp, &spec, false);
        assert_eq!(
            grow(&o.counters),
            grow(&a.counters),
            "conformance: {what} = Always"
        );
        assert_eq!(
            crow(&o.counters),
            crow(&a.counters),
            "conformance: {what} = Always"
        );
        assert_eq!(o.counters.gate_sweep_sizes, vec![1, f]);
        assert_eq!(
            o.counters.gate_sweeps_failing, 1,
            "conformance: {what}: test, then limit"
        );
    }
}

/// **Criterion 7 (D6), `reverse`.** Encoding 2, `k = 3`: the
/// selector-independent figures; F49-dependent terms measured through the
/// invariants (`Never`: fired + replay-skipped = `k + 1 + Σ`; `Budget(1)`:
/// every fired gate after `c`'s send a budgeted sweep).
#[test]
fn c07_policies_on_encoding_2_reverse() {
    let k = 3;
    let (f, sg) = (fact(k), sigma(k));
    let v = naive_visible(k);
    let (imp, spec) = (naive_enc(k, 0, false), naive_enc(k, 1, false));
    let never = with_sel(
        &gcc(bag(), &v, GatePolicy::Never, GatedMode::Exhaustive),
        Selector::Reverse,
    );
    let o = grw(&never, &imp, &spec, false);
    identities(&o, &v, false, GatePolicy::Never, "Never reverse");
    let c = &o.counters;
    assert_eq!(
        c.gates + c.gates_skipped_replay,
        k + 1 + sg,
        "conformance: Never reverse"
    );
    assert_eq!(
        (c.completion_sweeps_failing, c.reports_by_completion_test),
        (f, f)
    );
    let b1 = with_sel(
        &gcc(bag(), &v, GatePolicy::Budget(1), GatedMode::Exhaustive),
        Selector::Reverse,
    );
    let o = grw(&b1, &imp, &spec, false);
    identities(&o, &v, false, GatePolicy::Budget(1), "Budget(1) reverse");
    let c = &o.counters;
    assert_eq!(c.gates + c.gates_skipped_replay, k + 1 + sg);
    assert_eq!(
        (
            c.gate_sweeps_successful,
            c.carried_hits,
            c.c1_tests_carried,
            c.certificates_set
        ),
        (1, k - 1, k, 0)
    );
    assert_eq!(
        c.gate_sweeps_budgeted,
        c.gates - k,
        "conformance: every later gate budgeted"
    );
    assert_eq!(c.c1_tests_cache, c.gate_sweeps_budgeted);
    assert_eq!(c.reports_by_completion_test, f);
}

/// **Criterion 7, "`W` probes do not count toward `B`" (round 03 m2, D1).**
/// Criterion 12's pair under `Budget(2)`: `c1_tests_carried = 4`,
/// `carried_hits = 3`, successful 2, failing 1, budgeted 0,
/// `certificate_resets = 1`, `reports_certified = 1`; the second witness at
/// position 2 of the pop gate's sweep.
#[test]
fn c07_w_probes_do_not_count_toward_b() {
    let v = vis(&ABC);
    let (imp, spec) = (forward_pair(false), forward_pair(true));
    let o = grw(
        &gcc(bag(), &v, GatePolicy::Budget(2), GatedMode::Exhaustive),
        &imp,
        &spec,
        true,
    );
    identities(&o, &v, false, GatePolicy::Budget(2), "W fixture");
    assert_rows(
        &o.counters,
        [
            6, 0, 0, 0, 0, 4, 3, 2, 0, 5, 3, 2, 1, 0, 0, 1, 1, 0, 0, 1, 0,
        ],
        [2, 1, 1, 2, 0, 0, 0, 0, 2, 0, 1],
        "W fixture",
    );
    assert_eq!(o.counters.gate_sweep_sizes, vec![1, 2, 2]);
    assert_eq!(
        o.sweep_ends,
        vec![SweepEnd::Witness, SweepEnd::Exhausted, SweepEnd::Witness]
    );
}

// =========================================================================
// Criterion 8 — admissible inputs, labels, aborts
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

/// C4's tail, one text for four engines (criterion 15).
const TAIL: &str = "Either fix the specification, or — on the enumerator — accept the \
     assumption with `ConfBuilder::skip_spec_errfree_check(true)`, which records it in the \
     verdict. Under `Engine::CompleteFirst` that flag skips only the precheck: a sweep that \
     meets a specification assertion failure still aborts the run. Under `Engine::Gated`, as \
     under `CompleteFirst`. Under `Engine::Stateful` it has no effect and the only remedy is \
     fixing the specification.";

/// **Criterion 8 (D7), a gate-sweep abort.** `b`'s first send gates and its
/// sweep meets `a`'s assertion: `gate_sweeps_aborted = 1`, `Stop` is a prune
/// (`b`'s second send is never installed: `L = 1`), no later gate reaches
/// the sink, the completion sink never runs, `StoppedAtFirstReport`; `run`
/// returns `SpecNotErrorFree` in this engine's words.
#[test]
fn c08_a_gate_sweep_abort() {
    let v = vis(&["a", "b"]);
    for mode in [GatedMode::Exhaustive, GatedMode::FirstFailure] {
        let what = format!("{mode:?}");
        let cc = gcc(bag(), &v, GatePolicy::Always, mode).with_skip();
        let o = grw(&cc, &growing2(false), &growing2(true), true);
        identities(
            &o,
            &v,
            mode == GatedMode::FirstFailure,
            GatePolicy::Always,
            &what,
        );
        let c = &o.counters;
        assert_eq!(
            (
                c.gates,
                c.gate_sweeps,
                c.gate_sweeps_aborted,
                c.impl_graphs,
                c.reports
            ),
            (1, 1, 1, 0, 0),
            "conformance: {what}: {c:?}"
        );
        assert_eq!(o.sweep_ends, vec![SweepEnd::Aborted]);
        assert!(o.aborted && o.reports.is_empty());
        assert_eq!(
            (o.executions, o.max_paper_events, o.impl_end),
            (1, 1, SearchEnd::StoppedAtFirstReport),
            "conformance: {what}: the aborting execution was pruned at its gate"
        );
        assert_eq!(
            o.spec_errors,
            vec![(
                "a".to_string(),
                Event::new(crate::thread::construct_thread_id(1), 1),
                true
            )]
        );
        assert_eq!(
            o.abort_gate_at,
            Some(Event::new(crate::thread::construct_thread_id(2), 1)),
            "conformance: {what}: the gated event"
        );
        let r = run(cc, &growing2(false), &growing2(true));
        let detail = spec_not_error_free(&r);
        // Criterion 8 (rev 3.2, T2 resolved): the position of the
        // implementation's visible event whose gate swept: `b`'s first send,
        // `b` the second spawned thread, index 1 after its `Begin`.
        assert_eq!(
            detail,
            "The visible thread `a` failed an assertion at (t1, 1) during a gated sweep of the \
             specification (the gate after the implementation's visible event at (t2, 1)).",
            "conformance: {what}: the wording"
        );
        let shown = format!("{}", r.unwrap_err());
        assert!(
            shown.contains(TAIL),
            "conformance: {what}: the tail: {shown}"
        );
    }
}

/// The reset pair's shape with a Spec whose `c` fails an assertion when it
/// reads `b`'s 2 — reachable only in the Spec graph a backward revisit
/// builds. Spawned `a, c, b`; any-message receive.
fn abc_assert_on_two() -> Prog {
    prog(|| {
        let (tx, rx) = chan();
        let ta = tx.clone();
        let _a = named("a", move || ta.send_tagged_msg(1, 1));
        let _c = named("c", move || {
            let x: i32 = rx.recv_msg_block();
            if x == 2 {
                crate::assert(false);
            }
        });
        let _b = named("b", move || tx.send_tagged_msg(2, 2));
    })
}

/// **Criterion 8 (m3), a gate-sweep abort at a backward `RevisitApply`.**
/// Derived (`ltr`, `Always`, precheck skipped): `a` sends — the sweep's first
/// Spec graph `M1` (`c` reads 1, no assertion) is a witness and stops it;
/// `c` reads 1 and `b` sends 2 are carried hits; the completion is a cache
/// hit. `b`'s backward revisit of `c` gates (the send's thread `b` visible)
/// on a fresh slot: the probe fails on `c`'s 2, the sweep tests `M1`, then
/// builds the graph where `c` reads 2 and fails its assertion — abort.
/// `abort_gate_at` is the revisiting **send** `b0` = (t3, 1), not the
/// receive (t2, 1); the Spec failure is `c`'s at (t2, 2).
#[test]
fn c08_a_gate_sweep_abort_at_a_backward_pop() {
    let v = vis(&ABC);
    let cc = always(bag(), &v).with_skip();
    let (imp, spec) = (abc("acb", None), abc_assert_on_two());
    let o = grw(&cc, &imp, &spec, false);
    identities(&o, &v, false, GatePolicy::Always, "backward abort");
    let c = &o.counters;
    assert_eq!(
        (
            c.gates,
            c.gate_sweeps,
            c.gate_sweeps_successful,
            c.gate_sweeps_aborted,
            c.carried_hits,
            c.states_pushed,
            c.impl_graphs,
            c.completion_cache_hits
        ),
        (4, 2, 1, 1, 2, 1, 1, 1),
        "conformance: backward abort: {c:?}"
    );
    assert_eq!(o.sweep_ends, vec![SweepEnd::Witness, SweepEnd::Aborted]);
    assert_eq!(
        (o.executions, o.impl_end),
        (1, SearchEnd::StoppedAtFirstReport),
        "conformance: backward abort: the revisit is abandoned"
    );
    assert_eq!(
        o.spec_errors,
        vec![(
            "c".to_string(),
            Event::new(crate::thread::construct_thread_id(2), 2),
            true
        )],
        "conformance: backward abort: spec error"
    );
    assert_eq!(
        o.abort_gate_at,
        Some(Event::new(crate::thread::construct_thread_id(3), 1)),
        "conformance: backward abort: the revisiting send, not the receive"
    );
    let r = run(cc, &imp, &spec);
    assert_eq!(
        spec_not_error_free(&r),
        "The visible thread `c` failed an assertion at (t2, 2) during a gated sweep of the \
         specification (the gate after the implementation's visible event at (t3, 1)).",
        "conformance: backward abort: the wording"
    );
}

/// **Criterion 8 (D7), a completion-sweep abort.** No visible send or
/// receive, so no gate: the completion sweep aborts; "number 1".
#[test]
fn c08_a_completion_sweep_abort() {
    let v = vis(&["w"]);
    let cc = always(bag(), &v).with_skip();
    let o = grw(&cc, &visible_error(false), &visible_error(true), false);
    identities(&o, &v, false, GatePolicy::Always, "completion abort");
    let c = &o.counters;
    assert_eq!(
        (
            c.gates,
            c.gates_inert,
            c.completion_sweeps_aborted,
            c.impl_graphs,
            c.reports
        ),
        (0, 0, 1, 1, 0)
    );
    assert_eq!(o.impl_end, SearchEnd::StoppedAtFirstReport);
    assert_eq!(
        o.abort_gate_at, None,
        "conformance: a completion-sweep abort"
    );
    let r = run(cc, &visible_error(false), &visible_error(true));
    assert_eq!(
        spec_not_error_free(&r),
        "The visible thread `w` failed an assertion at (t1, 1) during a gated sweep of the \
         specification (the sweep for complete implementation graph number 1)."
    );
}

/// **Criterion 8.** `mbox` is refused at build; a `TotalOrder` channel
/// panics naming the engine that met it: "gated" on Impl, "precheck" on Spec
/// with the precheck on, "gated sweep" with it skipped.
#[test]
fn c08_labels_and_scope() {
    let e = gb(
        cfg(ConsType::Mailbox),
        &vis(&["w"]),
        GatePolicy::Always,
        GatedMode::Exhaustive,
    )
    .build()
    .err()
    .expect("conformance: a Mailbox configuration was accepted");
    assert_eq!(e.field(), ScopeField::ConsType);
    assert_eq!(ConfMode::GatedOuter.engine_label(), "gated");
    assert_eq!(ConfMode::GatedSweep.engine_label(), "gated sweep");
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
            "gated",
        ),
        (
            "impl/run_with",
            total_order_channel(),
            visible_error(false),
            true,
            false,
            "gated",
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
            "gated sweep",
        ),
        (
            "spec/run_with",
            visible_error(false),
            total_order_channel(),
            true,
            false,
            "gated sweep",
        ),
    ];
    for (what, imp, spec, engine_only, skip, label) in cases {
        let mut cc = always(bag(), &v);
        cc.skip_spec_errfree_check = skip;
        let payload = panic_text(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || {
                if engine_only {
                    let _ = grw(&cc, &imp, &spec, false);
                } else {
                    let _ = run(cc.clone(), &imp, &spec);
                }
            },
        )))
        .unwrap_or_else(|| panic!("conformance: {what}: a TotalOrder channel ran"));
        assert!(
            innermost(&payload).starts_with(&format!("{label}: {refusal}")),
            "conformance: {what}: expected a refusal naming {label:?}: {payload:?}"
        );
    }
}

/// **Criterion 8.** The precheck answers first, unbounded, under the gated
/// engine too.
#[test]
fn c08_the_precheck_answers_first() {
    let v = vis(&["a", "b"]);
    let r = run(always(bag(), &v), &growing2(false), &growing2(true));
    let detail = spec_not_error_free(&r);
    assert!(
        detail.contains("during the precheck run"),
        "conformance: {detail}"
    );
    assert!(format!("{}", r.unwrap_err()).contains(TAIL));
}

// =========================================================================
// Criterion 9 — the gate's visibility test, inertness, `states_pushed`
// =========================================================================

/// **Criterion 9 / G1 (adversarial).** An invisible receiver: its fresh
/// receive and a forward pop at it are inert; a backward revisit of it by
/// the visible `b` fires (the send's thread decides) and is counted in
/// `states_pushed`. Self-conformance, no reports.
#[test]
fn c09_inert_and_firing_pops_at_an_invisible_receive() {
    let v = vis(&["a", "b"]);
    // Backward: a sends (sweep), r reads a (inert), b sends (carried hit),
    // completion (cache hit); b revisits r (fires; fresh slot; W hit);
    // completion (cache hit).
    let o = grw(&always(bag(), &v), &inv_recv("arb"), &inv_recv("arb"), true);
    identities(&o, &v, false, GatePolicy::Always, "arb");
    assert_rows(
        &o.counters,
        [
            3, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
        ],
        [2, 2, 2, 2, 0, 0, 0, 0, 1, 0, 0],
        "arb",
    );
    // Forward: a sends (sweep), b sends (carried hit), r reads a (inert,
    // alternative pushed), completion (hit); the pop at r is inert;
    // completion (hit).
    let o = grw(&always(bag(), &v), &inv_recv("abr"), &inv_recv("abr"), true);
    identities(&o, &v, false, GatePolicy::Always, "abr");
    assert_rows(
        &o.counters,
        [
            2, 2, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ],
        [2, 2, 2, 2, 0, 0, 0, 0, 1, 0, 0],
        "abr",
    );
}

/// **Criterion 9 (adversarial).** A backward revisit by an **invisible**
/// send is inert and still counted in `states_pushed` (before the
/// inertness test).
#[test]
fn c09_states_pushed_counts_an_inert_backward_revisit() {
    // `v` visible (skip); invisible `s1` sends 1, `w` receives it, `s2` sends
    // 2 and backward-revisits `w`. Spawned `v, s1, w, s2`; `ltr`.
    let p = prog(|| {
        let (tx, rx) = chan();
        let _v = named("v", || {});
        let t1 = tx.clone();
        let _s1 = named("s1", move || t1.send_msg(1));
        let _w = named("w", move || {
            let _x: i32 = rx.recv_msg_block();
        });
        let _s2 = named("s2", move || tx.send_msg(2));
    });
    let v = vis(&["v"]);
    let o = grw(&always(bag(), &v), &p, &p, false);
    identities(&o, &v, false, GatePolicy::Always, "inert backward");
    let c = &o.counters;
    // Fresh: s1's send, w's receive, s2's send (inert); the backward pop
    // (inert: s2 invisible) — counted in `states_pushed` all the same.
    assert_eq!(
        (
            c.gates,
            c.gates_inert,
            c.states_pushed,
            c.certified_states_revisited
        ),
        (0, 4, 1, 0),
        "conformance: {c:?}"
    );
    assert!(o.reports.is_empty());
}

/// **Criterion 9.** The identities on every corpus pair, under every
/// policy, both modes, three selectors: a broad net for counting drift.
#[test]
fn c09_identities_on_the_corpus_every_setting() {
    let mut n = 0;
    for p in corpus() {
        for policy in POLICIES {
            for mode in [GatedMode::Exhaustive, GatedMode::FirstFailure] {
                for sel in [Selector::Ltr, Selector::FewestEvents, Selector::Reverse] {
                    let cc = with_sel(&gcc(p.config.clone(), &p.visible, policy, mode), sel);
                    let o = grw(&cc, &p.imp, &p.spec, true);
                    identities(
                        &o,
                        &p.visible,
                        mode == GatedMode::FirstFailure,
                        policy,
                        &format!("{} {policy:?} {mode:?} {sel:?}", p.name),
                    );
                    n += 1;
                }
            }
        }
    }
    assert!(n >= 90 * 24, "conformance: only {n} runs");
}

// =========================================================================
// Criterion 10 — report artefacts
// =========================================================================

const GATED_CERTIFIES: &str = "no graph of the specification covers the reported complete \
     graph: it was reported under an absence certificate set at a gate above it \
     (cor:absence), or no cached witness and no graph of an exhaustive unpruned sweep covered \
     it (lem:sig, thm:gated)";
const GATED_NOT_PRODUCED: &str = "the gated engine computes no inner-search diagnostics; \
     this report is an absence certificate set at a gate (cor:absence) or a failed coverage \
     test at completion (lem:sig)";
const GATED_NOT_PRODUCED_MISMATCH: &str =
    "not produced: the gated engine computes no inner-search diagnostics";

/// Returns the snapshot defects (criterion 10's `Serialized`, taken before
/// the prune) rather than panicking on the first, so the other artefacts are
/// checked on every report; the caller asserts the list empty.
fn assert_artefacts(
    r: &Result<ConfVerdict, ConfError>,
    o: &GatedOutcome,
    what: &str,
) -> Vec<String> {
    let mut bad = Vec::new();
    let out = outcome(r);
    assert_eq!(out.reports().len(), o.reports.len(), "conformance: {what}");
    for (rep, (g, snap, site)) in out.reports().iter().zip(&o.reports) {
        assert_eq!(*rep.cause(), ReportCause::NoCover, "conformance: {what}");
        assert!(
            matches!(
                rep.diagnostics(),
                Diagnostics::NotProduced { by: Engine::Gated }
            ),
            "conformance: {what}: diagnostics"
        );
        assert!(rep.triage().is_none(), "conformance: {what}");
        for (which, s) in [("ConfOutcome", rep.replay_snapshot()), ("run_with", snap)] {
            match s {
                ReplaySnapshot::Serialized(j) => {
                    assert!(j.starts_with('{'), "conformance: {what}: JSON");
                    assert!(
                        !j.contains("ConfPrune"),
                        "conformance: {what}: a snapshot taken after the prune"
                    );
                }
                other => bad.push(format!("{what}: {site:?}: {which}: {other:?}")),
            }
        }
        assert_eq!(
            rep.graph_dump(),
            g.to_string(),
            "conformance: {what}: order"
        );
        assert_eq!(rep.events(), label_count(g), "conformance: {what}: events");
        let shown = format!("{rep}");
        assert!(
            shown.contains(GATED_NOT_PRODUCED),
            "conformance: {what}: {shown}"
        );
        match site {
            ReportSite::Completion => {
                assert_eq!(
                    rep.tag(),
                    ReportTag::CompleteCoverage,
                    "conformance: {what}"
                );
                assert_eq!(rep.gate(), ReportGate::Completion, "conformance: {what}");
                assert!(
                    shown.contains(&format!("certifies (CompleteCoverage): {GATED_CERTIFIES}")),
                    "conformance: {what}: {shown}"
                );
            }
            ReportSite::Gate(gate) => {
                assert!(
                    matches!(gate, Gate::FreshSend | Gate::FreshRecv | Gate::RevisitApply),
                    "conformance: {what}"
                );
                assert_eq!(
                    rep.tag(),
                    ReportTag::GrowingExhaustion,
                    "conformance: {what}"
                );
                assert_eq!(
                    rep.gate(),
                    ReportGate::of(Some(*gate)),
                    "conformance: {what}"
                );
                assert!(
                    shown.contains(ReportTag::GrowingExhaustion.certifies()),
                    "conformance: {what}: {shown}"
                );
            }
        }
    }
    bad
}

/// **Criterion 10.** Completion reports on `ex:naive` (exhaustive, certified
/// and by completion test) and gate reports at each of the three gates
/// (first-failure): kinds, tags, gates, `Serialized` snapshots taken before
/// the prune, `NotProduced { by: Gated }`.
#[test]
fn c10_report_artefacts() {
    let mut bad: Vec<String> = Vec::new();
    let v = naive_visible(3);
    let (imp, spec) = (naive_enc(3, 0, false), naive_enc(3, 1, false));
    for policy in [GatePolicy::Always, GatePolicy::Never] {
        let cc = gcc(bag(), &v, policy, GatedMode::Exhaustive).with_skip();
        let o = grw(&cc, &imp, &spec, false);
        let r = run(cc, &imp, &spec);
        assert_eq!(class(&r), "reported:6");
        bad.extend(assert_artefacts(&r, &o, &format!("ex:naive {policy:?}")));
    }
    let abc_v = vis(&ABC);
    type Case = (&'static str, Prog, Prog, Vec<String>, Gate);
    let cases: [Case; 3] = [
        (
            "send",
            naive_enc(2, 0, true),
            naive_enc(2, 1, true),
            naive_visible(2),
            Gate::FreshSend,
        ),
        (
            "recv",
            abc("acb", None),
            abc("acb", Some(2)),
            abc_v.clone(),
            Gate::FreshRecv,
        ),
        (
            "pop",
            abc("abc", None),
            abc("abc", Some(1)),
            abc_v,
            Gate::RevisitApply,
        ),
    ];
    for (what, imp, spec, v, gate) in cases {
        let cc = ff(bag(), &v, GatePolicy::Always).with_skip();
        let o = grw(&cc, &imp, &spec, false);
        assert_eq!(
            o.reports[0].2,
            ReportSite::Gate(gate),
            "conformance: {what}"
        );
        let r = run(cc, &imp, &spec);
        bad.extend(assert_artefacts(&r, &o, what));
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 10: report snapshots not Serialized:\n  {}",
        bad.join("\n  ")
    );
}

/// A snapshot's JSON with every array under a `labels` key sorted:
/// `replay.rs`'s `SortedGraph` serializes `labels`, a `HashSet<Event>`, in
/// hash order, so two snapshots of one graph and state differ byte-wise
/// (measured; see L2 in the report).
fn normalised_snapshot(s: &ReplaySnapshot) -> serde_json::Value {
    fn norm(v: &mut serde_json::Value) {
        match v {
            serde_json::Value::Object(m) => {
                for (k, x) in m.iter_mut() {
                    if k == "labels" {
                        if let serde_json::Value::Array(a) = x {
                            a.sort_by_key(|e| e.to_string());
                        }
                    }
                    norm(x);
                }
            }
            serde_json::Value::Array(a) => a.iter_mut().for_each(norm),
            _ => {}
        }
    }
    let ReplaySnapshot::Serialized(j) = s else {
        panic!("conformance: snapshot not Serialized: {s:?}");
    };
    let mut v: serde_json::Value =
        serde_json::from_str(j).expect("conformance: a snapshot is JSON");
    norm(&mut v);
    v
}

/// **L2.** The context's own gate report (pushed by `ConfCtx` with its
/// snapshot) agrees with the snapshot the sink takes of the same graph and
/// state, at a fresh gate and at a backward `RevisitApply`; a `Stop` is a
/// prune without a report; each ends the run `StoppedAtFirstReport`.
#[test]
fn l2_the_contexts_gate_report_matches_the_sinks() {
    type Seen = std::rc::Rc<std::cell::RefCell<Vec<(String, ReplaySnapshot)>>>;
    let v = vis(&ABC);
    for (what, order, at, verdict) in [
        (
            "fresh recv",
            "acb",
            Some(Gate::FreshRecv),
            GateVerdict::Report,
        ),
        (
            "backward pop",
            "acb",
            Some(Gate::RevisitApply),
            GateVerdict::Report,
        ),
        ("stop", "acb", Some(Gate::FreshRecv), GateVerdict::Stop),
    ] {
        let seen: Seen = Default::default();
        let config = bag();
        let gate_sink: GateSink = {
            let seen = std::rc::Rc::clone(&seen);
            let config = config.clone();
            Box::new(
                move |gate: Gate, _site: &GateAt, g: &ExecutionGraph, st: &MustState| {
                    if Some(gate) != at {
                        return GateVerdict::Continue;
                    }
                    seen.borrow_mut()
                        .push((g.to_string(), replay_snapshot(g, st, &config, None)));
                    verdict
                },
            )
        };
        let sink: CompletionSink =
            Box::new(|_: &ExecutionGraph, _: &MustState| SinkVerdict::Continue);
        let e = enumerate(
            EnumRun {
                config,
                visible: v.clone(),
                mode: ConfMode::GatedOuter,
                sink,
                cut: false,
                stop_at_first_report: false,
                gate_sink: Some(gate_sink),
            },
            &abc(order, None),
        );
        let seen = seen.borrow();
        assert_eq!(
            seen.len(),
            1,
            "conformance: {what}: one call reached the sink"
        );
        assert_eq!(
            e.end,
            SearchEnd::StoppedAtFirstReport,
            "conformance: {what}"
        );
        if verdict == GateVerdict::Stop {
            assert!(e.reports.is_empty(), "conformance: {what}: Stop reported");
            assert_eq!(e.executions, 1, "conformance: {what}");
            continue;
        }
        assert_eq!(e.reports.len(), 1, "conformance: {what}");
        let rep = &e.reports[0];
        assert_eq!(
            rep.graph.to_string(),
            seen[0].0,
            "conformance: {what}: graph"
        );
        assert_eq!(
            normalised_snapshot(&rep.replay),
            normalised_snapshot(&seen[0].1),
            "conformance: {what}: snapshot (modulo the `labels` set's order)"
        );
        assert_eq!(rep.gate, at, "conformance: {what}");
        match &rep.replay {
            ReplaySnapshot::Serialized(j) => assert!(
                !j.contains("ConfPrune"),
                "conformance: {what}: a snapshot taken after the prune"
            ),
            other => panic!("conformance: {what}: {other:?}"),
        }
        assert_eq!(e.executions, 1, "conformance: {what}: executions");
    }
}

// =========================================================================
// Criterion 11 — the engine-only entry point
// =========================================================================

/// **Criterion 11 (L6).** `GatedOutcome` destructured without `..`, every
/// field's type ascribed; `sweep_ends` and `kept_spec_graphs` interleave
/// gate and completion sweeps in order (criterion 12's pair: gate, gate,
/// gate, then two cache hits at completion — and `Never` on the same pair:
/// completion sweeps only).
#[test]
fn c11_the_entry_point_fields() {
    let v = vis(&ABC);
    let GatedOutcome {
        reports,
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
        abort_gate_at,
    } = grw(
        &always(bag(), &v),
        &forward_pair(false),
        &forward_pair(true),
        true,
    );
    let reports: Vec<(ExecutionGraph, ReplaySnapshot, ReportSite)> = reports;
    let counters: GatedCounters = counters;
    let witnesses: WitnessCache = witnesses;
    let kept_impl_graphs: Vec<ExecutionGraph> = kept_impl_graphs;
    let kept_spec_graphs: Vec<Vec<ExecutionGraph>> = kept_spec_graphs;
    let sweep_ends: Vec<SweepEnd> = sweep_ends;
    let aborted: bool = aborted;
    let impl_end: SearchEnd = impl_end;
    let spec_errors: Vec<(String, Event, bool)> = spec_errors;
    let impl_notes: Vec<Diagnostic> = impl_notes;
    let (executions, max_paper_events): (usize, usize) = (executions, max_paper_events);
    let abort_gate_at: Option<Event> = abort_gate_at;
    assert_eq!(abort_gate_at, None, "conformance: no abort, no gated event");
    assert_eq!((reports.len(), counters.reports), (1, 1));
    assert_eq!(witnesses.len(), 2);
    assert_eq!(kept_impl_graphs.len(), 2);
    assert_eq!(
        kept_spec_graphs.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![1, 2, 2]
    );
    assert_eq!(
        sweep_ends,
        vec![SweepEnd::Witness, SweepEnd::Exhausted, SweepEnd::Witness]
    );
    assert!(!aborted && spec_errors.is_empty() && impl_notes.is_empty());
    assert_eq!(impl_end, SearchEnd::StateSpaceExhausted);
    assert_eq!((executions, max_paper_events), (2, 4));
    // Gate and completion sweeps interleave in order: `Budget(1)` on
    // ex:naive k = 2, encoding 2 — gate sweeps, then a completion sweep,
    // then (after the forward pop) gate sweeps again.
    let v2 = naive_visible(2);
    let o = grw(
        &gcc(bag(), &v2, GatePolicy::Budget(1), GatedMode::Exhaustive),
        &naive_enc(2, 0, false),
        &naive_enc(2, 1, false),
        true,
    );
    identities(&o, &v2, false, GatePolicy::Budget(1), "interleave");
    // b1 (W), c's send (B), r1 (B), r2 (B), completion (X), pop (B), r2 (B),
    // completion (X).
    assert_eq!(
        o.sweep_ends,
        vec![
            SweepEnd::Witness,
            SweepEnd::Budgeted,
            SweepEnd::Budgeted,
            SweepEnd::Budgeted,
            SweepEnd::Exhausted,
            SweepEnd::Budgeted,
            SweepEnd::Budgeted,
            SweepEnd::Exhausted
        ]
    );
    assert_eq!(
        o.kept_spec_graphs.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![1, 1, 1, 1, 2, 1, 1, 2]
    );
}

// =========================================================================
// Criterion 12 — validity at use on a forward pop
// =========================================================================

/// **Criterion 12 (D1).** The certificate set at `c`'s send is dropped at
/// the forward pop (`valid_at` false, `def:ext` (iii)): report set exactly
/// {c reads 1, sends 2}; `certificate_resets = 1`, `states_pushed = 0`;
/// every counter as derived.
#[test]
fn c12_validity_at_use_on_a_forward_pop() {
    let v = vis(&ABC);
    let (imp, spec) = (forward_pair(false), forward_pair(true));
    let o = grw(&always(bag(), &v), &imp, &spec, true);
    let s = srw(&sb(bag(), &v), &imp, &spec);
    assert_eq!(report_keys(&o, &v), stateful_report_keys(&s, &v));
    assert_eq!(o.reports.len(), 1);
    assert_eq!(
        full_key(&o.reports[0].0, &v),
        full_key(&o.kept_impl_graphs[0], &v),
        "conformance: the reported graph is the first completion (c reads 1)"
    );
    identities(&o, &v, false, GatePolicy::Always, "c12");
    assert_rows(
        &o.counters,
        [
            6, 0, 0, 0, 0, 4, 3, 2, 0, 5, 3, 2, 1, 0, 0, 1, 1, 0, 0, 1, 0,
        ],
        [2, 1, 1, 2, 0, 0, 0, 0, 2, 0, 1],
        "c12",
    );
    assert_eq!(o.counters.gate_sweep_sizes, vec![1, 2, 2]);
}

// =========================================================================
// Criterion 13 — selector completeness
// =========================================================================

/// **Criterion 13.** Under `Never` and `Always`, exhaustive: identical report
/// sets and verdicts across `ltr`, `fewest-events`, `reverse` on every
/// corpus pair; gate counters may differ (recorded: how many differ).
#[test]
fn c13_selector_completeness() {
    let mut failures = Vec::new();
    let mut gate_rows_differ = 0;
    for p in corpus() {
        for policy in [GatePolicy::Never, GatePolicy::Always] {
            let runs: Vec<(Vec<String>, String, [usize; 21])> =
                [Selector::Ltr, Selector::FewestEvents, Selector::Reverse]
                    .iter()
                    .map(|s| {
                        let cc = with_sel(
                            &gcc(p.config.clone(), &p.visible, policy, GatedMode::Exhaustive),
                            *s,
                        );
                        let o = grw(&cc, &p.imp, &p.spec, false);
                        (
                            report_keys(&o, &p.visible),
                            class(&run(cc.with_skip(), &p.imp, &p.spec)),
                            grow(&o.counters),
                        )
                    })
                    .collect();
            for (i, s) in ["fewest", "reverse"].iter().enumerate() {
                let (a, b) = (&runs[i + 1], &runs[0]);
                if (&a.0, &a.1) != (&b.0, &b.1) {
                    failures.push(format!("{} {policy:?}: {s} differs from ltr", p.name));
                }
                if a.2 != b.2 {
                    gate_rows_differ += 1;
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "conformance: criterion 13: {failures:#?}"
    );
    assert!(
        gate_rows_differ > 0,
        "conformance: no gate row depends on the selector: knob A never reached the gates"
    );
}

// =========================================================================
// Criterion 14 — A9
// =========================================================================

/// **Criterion 14.** A NaN pair reports (no witness covers it); a
/// certificate is set at its first visible send (`⟨snd,NaN⟩` is no prefix
/// of itself); recorded, excluded from criteria 1–3 and 13.
#[test]
fn c14_a9_nan_reports() {
    let v = vis(&["a", "c"]);
    let o = grw(
        &always(bag(), &v),
        &direct_of(f64::NAN),
        &direct_of(f64::NAN),
        false,
    );
    identities(&o, &v, false, GatePolicy::Always, "A9");
    assert_eq!(
        (o.reports.len(), o.counters.witnesses),
        (1, 0),
        "conformance: A9: {:?}",
        o.counters
    );
    // Measured and recorded (criterion 14): the certificate set at `a`'s
    // send is dropped at `c`'s receive — `valid_at` compares labels, and the
    // set point's NaN is not equal to itself — so the receive re-sweeps and
    // re-certifies, the completion drops it again, and the report comes from
    // a completion sweep: two certificates, two resets, no certified report.
    assert_rows(
        &o.counters,
        [
            2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 0, 0, 1,
        ],
        [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1],
        "A9 measured",
    );
    let o = grw(
        &always(bag(), &v),
        &two_senders(f64::NAN, f64::NAN),
        &two_senders(f64::NAN, f64::NAN),
        false,
    );
    assert_eq!(o.reports.len(), 2, "conformance: A9 two senders");
}

// =========================================================================
// Criterion 15 — the rendered texts
// =========================================================================

const SEED7: &str =
    "conformance: run seed 7 (reproduce with the same `Config` plus `.with_seed(7)`)";
const EACH: &str = "Every graph in this list is an uncovered complete graph of the \
     implementation: it was reported under an absence certificate set at a gate above it \
     (cor:absence), or no cached witness covered it and an unpruned sweep of the specification \
     found none (lem:sig).";
const EXACTLY: &str = "The list is exactly the set of such graphs (thm:gated, exhaustive \
     mode): the outer exploration reached the end of its state space and every failing sweep \
     reached the end of the specification's.";
const FIRST_FAILURE: &str = "This run was gated in first-failure mode and stopped at its first \
     report (thm:gated): the reported graph is either a partial implementation graph with a \
     completion, every completion of every extension of which is uncovered (cor:absence), or a \
     complete graph that no specification graph covers (lem:sig).";
const CONFORMS_LINE: &str = "conformance: silence. Every complete graph of the \
     implementation is covered by one of the specification — by a cached witness or by a \
     sweep (thm:gated) — and the outer exploration reached the end of its state space.";
const ENUM_SILENCE_LINE: &str = "conformance: silence. No candidate violation, no exhausted \
     search budget, and the outer loop reached the end of its state space.";
const RESIDUAL: &str = "\"Candidate\" has two named sources: (i) single-cover is sufficient \
     but not necessary for trace inclusion, so a union of specification graphs may still cover \
     these traces; (ii) the lemmas this rests on carry the open A4 transport gap.";
const ONLY_SILENCE: &str = "Only silence is a verdict: a run that produced no report, hit no \
     search budget and reached the end of its state space is the certificate, and nothing \
     else is.";
const TRUNC_CONFIG: &str = "**This list is truncated by configuration.** \
     `stop_at_first_report` was set, so the outer loop stopped at the report below and looked \
     for no others. There may be more; this run did not ask.";
/// Criteria rev 3.3 G6 (m5): a gated first-failure run names the mode, not
/// the knob the user did not set.
const TRUNC_FIRST_FAILURE: &str = "**This list is truncated by configuration.** \
     `GatedMode::FirstFailure` implies `stop_at_first_report`, so the search stopped at the \
     report below and looked for no others. There may be more; this run did not ask.";
const TRIAGE_CAVEAT: &str = "triage is off (the default)";
const OTHER_ENGINES: [&str; 6] = [
    "What this report establishes (Lemma gate",
    "What this report does not establish",
    "This list is not a complete set of violations",
    "each was looked up in an index",
    "(thm:cfirst)",
    "(thm:stateful)",
];

fn seeded(visible: &[String], policy: GatePolicy, mode: GatedMode) -> ConfBuilder {
    gb(
        Config::builder().with_seed(7).build(),
        visible,
        policy,
        mode,
    )
}

fn head(s: &str) -> &str {
    s.split("\n#0\n").next().unwrap_or(s)
}

/// **Criterion 15.** `Conforms` in both modes renders the enumerator's
/// baseline with its first silence line replaced by G6's.
#[test]
fn c15_conforms_rendering_both_modes() {
    for mode in [GatedMode::Exhaustive, GatedMode::FirstFailure] {
        let cc = built(seeded(&vis(&["a", "c"]), GatePolicy::Always, mode));
        let r = run(cc, &restart(true), &restart(true));
        assert_eq!(class(&r), "conforms", "conformance: {mode:?}");
        let expected = super::stateful_baseline::ENUMERATOR_CONFORMS_BASELINE.replacen(
            ENUM_SILENCE_LINE,
            CONFORMS_LINE,
            1,
        );
        assert_ne!(
            expected,
            super::stateful_baseline::ENUMERATOR_CONFORMS_BASELINE
        );
        assert_eq!(rendering(&r), expected, "conformance: {mode:?}");
    }
}

/// **Criterion 15.** Exhaustive `Reported`: exhausted (with "exactly"),
/// bounded and stopped (without); first-failure `Reported`; no triage
/// caveat and none of the other engines' sentences.
#[test]
fn c15_reported_rendering() {
    let v = naive_visible(2);
    let (imp, spec) = (naive_enc(2, 0, true), naive_enc(2, 1, true));
    let ex = built(seeded(&v, GatePolicy::Always, GatedMode::Exhaustive));
    let s = rendering(&run(ex, &imp, &spec));
    assert_eq!(
        head(&s),
        format!(
            "{SEED7}\nconformance: 2 candidate violation(s).\n{EACH}\n{EXACTLY}\n{RESIDUAL}\n\
             {ONLY_SILENCE}\n"
        ),
        "conformance: exhausted head"
    );
    assert_eq!(
        s.matches(&format!("certifies (CompleteCoverage): {GATED_CERTIFIES}"))
            .count(),
        2
    );
    assert_eq!(s.matches(GATED_NOT_PRODUCED).count(), 2);
    for gone in OTHER_ENGINES.iter().chain([TRIAGE_CAVEAT].iter()) {
        assert!(!s.contains(gone), "conformance: {gone:?} rendered: {s}");
    }

    let v3 = naive_visible(3);
    let (imp3, spec3) = (naive_enc(3, 0, true), naive_enc(3, 1, true));
    let bounded = built(gb(
        Config::builder()
            .with_seed(7)
            .with_max_iterations(2)
            .build(),
        &v3,
        GatePolicy::Always,
        GatedMode::Exhaustive,
    ));
    let s = rendering(&run(bounded, &imp3, &spec3));
    let bound = "**This list is truncated by a bound you set.** `Config::max_iterations` was 2, \
                 so the outer loop stopped after counting that many endings rather than after \
                 seeing them all. There may be more reports; this run did not look.";
    assert_eq!(
        head(&s),
        format!(
            "{SEED7}\nconformance: 2 candidate violation(s).\n{EACH}\n{RESIDUAL}\n{ONLY_SILENCE}\n\
             {bound}\n"
        ),
        "conformance: bounded head"
    );
    let stopped =
        built(seeded(&v3, GatePolicy::Always, GatedMode::Exhaustive).stop_at_first_report(true));
    let r = run(stopped, &imp3, &spec3);
    let s = rendering(&r);
    assert_eq!(
        head(&s),
        format!(
            "{SEED7}\nconformance: 1 candidate violation(s).\n{EACH}\n{RESIDUAL}\n{ONLY_SILENCE}\n\
             {TRUNC_CONFIG}\n"
        ),
        "conformance: stopped head"
    );
    // Exhaustive mode with the user's stop: the first *completion* report
    // stops; gates never report.
    assert_eq!(outcome(&r).reports()[0].gate(), ReportGate::Completion);
    assert!(!gated_counters_of(&r).first_failure_mode);

    let first = built(seeded(&v3, GatePolicy::Always, GatedMode::FirstFailure));
    let r = run(first, &imp3, &spec3);
    let s = rendering(&r);
    assert_eq!(
        head(&s),
        format!(
            "{SEED7}\nconformance: 1 candidate violation(s).\n{FIRST_FAILURE}\n{RESIDUAL}\n\
             {ONLY_SILENCE}\n{TRUNC_FIRST_FAILURE}\n"
        ),
        "conformance: first-failure head"
    );
    assert!(gated_counters_of(&r).first_failure_mode);
    for gone in OTHER_ENGINES
        .iter()
        .chain([TRIAGE_CAVEAT, EACH, EXACTLY].iter())
    {
        assert!(!s.contains(gone), "conformance: {gone:?} rendered: {s}");
    }
    assert!(!outcome(&r).inconclusive());
}

/// **Criterion 15.** `certifies_under(Gated, ·)`, `NotProduced`'s two
/// strings, and the other engines' texts not the gated one.
#[test]
fn c15_certifies_under_and_not_produced() {
    assert_eq!(
        ReportTag::CompleteCoverage.certifies_under(Engine::Gated),
        GATED_CERTIFIES
    );
    for t in [ReportTag::GrowingExhaustion, ReportTag::VisibleError] {
        assert_eq!(
            t.certifies_under(Engine::Gated),
            t.certifies(),
            "conformance: {t:?}"
        );
    }
    for e in [Engine::Enumerator, Engine::Stateful, Engine::CompleteFirst] {
        assert_ne!(
            ReportTag::CompleteCoverage.certifies_under(e),
            GATED_CERTIFIES
        );
    }
    let d = Diagnostics::NotProduced { by: Engine::Gated };
    assert_eq!(format!("{d}"), GATED_NOT_PRODUCED);
    assert_eq!(
        crate::conformance::diagnose::spec_side_first_mismatch(&d, &ReportCause::NoCover),
        GATED_NOT_PRODUCED_MISMATCH
    );
}

/// **Criterion 15 / G5–G6.** The outcome's record: engine, `Assumed` under
/// the skip, ignored knobs (`triage`, `search_budget`, `memo`,
/// `inner_order`, `early_error_cut`) change nothing, `inconclusive()` never
/// true, a bounded silent run `Inconclusive` by `BoundedRun`.
#[test]
fn c15_outcome_record_and_ignored_knobs() {
    let v = naive_visible(2);
    let (imp, spec) = (naive_enc(2, 0, false), naive_enc(2, 1, false));
    let base = grw(&always(bag(), &v), &imp, &spec, false);
    for t in [false, true] {
        let cc = built(
            gb(bag(), &v, GatePolicy::Always, GatedMode::Exhaustive)
                .triage(t)
                .search_budget(1)
                .memo(!t)
                .early_error_cut(true)
                .inner_order(crate::conformance::InnerOrder::Reverse)
                .skip_spec_errfree_check(t),
        );
        let o = grw(&cc, &imp, &spec, false);
        assert_eq!(
            grow(&o.counters),
            grow(&base.counters),
            "conformance: triage={t}"
        );
        assert_eq!(
            crow(&o.counters),
            crow(&base.counters),
            "conformance: triage={t}"
        );
        let r = run(cc, &imp, &spec);
        let out = outcome(&r);
        assert_eq!(out.engine(), Engine::Gated);
        assert_eq!(out.triage_enabled, t);
        assert!(out.reports().iter().all(|r| r.triage().is_none()));
        assert!(!out.inconclusive() && out.exhaustions().is_empty());
        assert_eq!(
            out.spec_err_freedom(),
            if t {
                SpecErrFreedom::Assumed
            } else {
                SpecErrFreedom::Checked
            }
        );
        assert!(out.stateful_counters().is_none() && out.cfirst_counters().is_none());
        assert_eq!(gated_counters_of(&r).precheck_ran, !t);
        let c = out.counters();
        assert_eq!((c.cover_calls, c.spec_visit_calls, c.memo_hits), (0, 0, 0));
        assert_eq!(c.executions, base.executions);
        assert!(!rendering(&r).contains(TRIAGE_CAVEAT));
    }
    let r = run(
        built(gb(
            Config::builder()
                .with_cons_type(ConsType::Bag)
                .with_max_iterations(2)
                .build(),
            &naive_visible(3),
            GatePolicy::Always,
            GatedMode::Exhaustive,
        )),
        &naive_enc(3, 1, true),
        &naive_enc(3, 1, true),
    );
    match &r {
        Ok(ConfVerdict::Inconclusive(o)) => {
            assert!(!o.inconclusive());
            assert_eq!(
                o.not_a_certificate(),
                vec![NotACertificate::BoundedRun { max_iterations: 2 }]
            );
            assert!(!rendering(&r).contains(CONFORMS_LINE));
        }
        other => panic!("conformance: expected Inconclusive, got {}", class(other)),
    }
}

// =========================================================================
// Adversarial additions
// =========================================================================

/// The same run twice gives the same counters and report keys (the gate
/// sink's `Rc` state is per run; `W` does not leak across runs).
#[test]
fn adv_runs_are_independent_and_deterministic() {
    let v = vis(&ABC);
    let cc = always(bag(), &v);
    let a = grw(&cc, &forward_pair(false), &forward_pair(true), false);
    let b = grw(&cc, &forward_pair(false), &forward_pair(true), false);
    assert_eq!(grow(&a.counters), grow(&b.counters));
    assert_eq!(crow(&a.counters), crow(&b.counters));
    assert_eq!(report_keys(&a, &v), report_keys(&b, &v));
}

/// `Budget(0)`: every sweep is budgeted before testing anything, no
/// certificate, no witness from a gate; the run is complete-first plus probes
/// and its report set is still exact (criterion 2 runs it on the corpus).
#[test]
fn adv_budget_zero_degenerates_to_complete_first() {
    let v = vis(&ABC);
    let (imp, spec) = (abc("acb", None), abc("acb", Some(2)));
    let o = grw(
        &gcc(bag(), &v, GatePolicy::Budget(0), GatedMode::Exhaustive),
        &imp,
        &spec,
        true,
    );
    identities(&o, &v, false, GatePolicy::Budget(0), "Budget(0)");
    let c = &o.counters;
    assert_eq!(
        (
            c.gate_sweeps_successful,
            c.gate_sweeps_failing,
            c.c1_tests_sweep
        ),
        (0, 0, 0)
    );
    assert_eq!(c.gate_sweeps, c.gate_sweeps_budgeted);
    let s = srw(&sb(bag(), &v), &imp, &spec);
    assert_eq!(report_keys(&o, &v), stateful_report_keys(&s, &v));
}

/// First-failure under `Never`: no gate ever reports, so the one report is
/// a completion report (`CompleteCoverage`), and the run is complete-first's
/// stop-at-first-report run.
#[test]
fn adv_first_failure_under_never_reports_at_completion() {
    let v = naive_visible(2);
    let (imp, spec) = (naive_enc(2, 0, false), naive_enc(2, 1, false));
    let o = grw(&ff(bag(), &v, GatePolicy::Never), &imp, &spec, false);
    identities(&o, &v, true, GatePolicy::Never, "ff Never");
    assert_eq!(o.reports.len(), 1);
    assert_eq!(o.reports[0].2, ReportSite::Completion);
    assert_eq!(
        (
            o.counters.impl_graphs,
            o.counters.reports_by_completion_test,
            o.impl_end
        ),
        (1, 1, SearchEnd::StoppedAtFirstReport)
    );
    assert_eq!(o.counters.paper_events_at_first_report, Some(2 * 2 + 1));
}
