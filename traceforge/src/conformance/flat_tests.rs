//! P4-FLAT gate 3: the tester's tests for `FlatCover` and the
//! communication-flat eligibility scan (criteria `P4-FLAT.md` revision 6.1,
//! gate-2 notes G2-1/G2-2).
//!
//! Every expected value below was derived from the criteria's engine facts
//! F1–F7 and the paper (`flat.tex` §9, `appendix.tex`'s proof of `thm:flat`,
//! `mixed.tex` `cor:mixedflat`, `alg.tex` `ex:naive`) **before** the lead's
//! Part 8 diffs were read; the derivations are in
//! `plan/traceForge/log/dev/P4-FLAT.report.md`, Part 0, under D1..D9, cited on
//! each test. Tests are named by criterion (`cNN_…`) or by the lead's finding
//! they answer (`lNN_…`). Fixtures are written here from the criteria's text;
//! `ex:naive` and the registry come from Part 6's `grid.rs` (copies of closed
//! test fixtures).
//!
//! Conventions kept because `s5_tests`' source scans read this file: no print
//! macro anywhere, no `Display` impl, and every panic-family message starts
//! with `conformance:`.

use std::collections::BTreeSet;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::cfirst::{self, CFirstOutcome};
use crate::conformance::config::{CompletionCover, ConfConfig, GatePolicy, GatedMode};
use crate::conformance::flat;
use crate::conformance::gated::{self, GatedOutcome};
use crate::conformance::grid::{
    corpus_fixtures, mixed_fixtures, naive_d, naive_visible, ndk_fixtures, paper_fixtures,
    registry, row_of_end, run_grid, two_pc_fixtures, Budget, Fixture, GridConfig, GridEnd,
    GridEngine, GridRaw, Row, Tables,
};
use crate::conformance::grid_oracle::canon_key;
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{is_visible, wobs};
use crate::conformance::precheck;
use crate::conformance::report::{
    CFirstCounters, ConfOutcome, ConfVerdict, GatedCounters, ReportGate, ReportTag, SearchEnd,
};
use crate::conformance::selector::Selector;
use crate::conformance::sig::{covered, Summary};
use crate::conformance::stateful;
use crate::conformance::{ConfBuilder, ConfError, Engine, FlatCounters, FlatEligibility};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::thread::ThreadId;
use crate::{thread, CommunicationModel, Config, ConsType, Nondet, Visibility};

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

impl Eng {
    /// `Flat` is a `KnobConflict` on the enumerator and the stateful engine.
    fn flat_capable(self) -> bool {
        matches!(self, Eng::CFirst | Eng::Gated(..))
    }
}

/// The engines of criterion 1's and 2's tables: the enumerator and the
/// stateful engine (under `Sweep`), complete-first, and the gated engine in
/// both modes under `Never`, `Always`, `Budget(1)` and `Budget(2)`.
fn table_engines() -> Vec<Eng> {
    let mut v = vec![Eng::Enum, Eng::Stateful, Eng::CFirst];
    for m in [GatedMode::Exhaustive, GatedMode::FirstFailure] {
        for p in [
            GatePolicy::Never,
            GatePolicy::Always,
            GatePolicy::Budget(1),
            GatePolicy::Budget(2),
        ] {
            v.push(Eng::Gated(m, p));
        }
    }
    v
}

fn builder(
    e: Eng,
    config: Config,
    visible: &[String],
    s: Selector,
    cover: CompletionCover,
) -> ConfBuilder {
    let b = ConfBuilder::new()
        .config(config)
        .visible_threads(visible.to_vec())
        .selector(s)
        .completion_cover(cover);
    match e {
        Eng::Enum => b.engine(Engine::Enumerator),
        Eng::Stateful => b.engine(Engine::Stateful),
        Eng::CFirst => b.engine(Engine::CompleteFirst),
        Eng::Gated(m, p) => b.engine(Engine::Gated).gated_mode(m).gate_policy(p),
    }
}

/// The public configuration, the precheck on (D13).
fn cc(
    e: Eng,
    config: Config,
    visible: &[String],
    s: Selector,
    cover: CompletionCover,
) -> ConfConfig {
    builder(e, config, visible, s, cover)
        .build()
        .expect("conformance: the test configuration is in scope")
}

/// `Flat` where the engine takes it, `Sweep` otherwise.
fn cover_for(e: Eng) -> CompletionCover {
    if e.flat_capable() {
        CompletionCover::Flat
    } else {
        CompletionCover::Sweep
    }
}

/// The public entry point (`conformance::verify`, its own thread).
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

/// `FlatCounters` without `wall_time_ms` (criterion 6: compare fields).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct F {
    calls: usize,
    visits: usize,
    nd: usize,
    src: usize,
    rec: usize,
    sk: usize,
    slk: usize,
    srk: usize,
    dk: usize,
    w: usize,
    md: usize,
}

fn f_of(c: &FlatCounters) -> F {
    F {
        calls: c.calls,
        visits: c.visits,
        nd: c.nd_branches,
        src: c.source_branches,
        rec: c.source_recursions,
        sk: c.send_kills,
        slk: c.slot_kills,
        srk: c.source_kills,
        dk: c.done_kills,
        w: c.witnesses,
        md: c.max_depth,
    }
}

fn flat_of(o: &ConfOutcome) -> F {
    f_of(
        o.flat_counters()
            .expect("conformance: a Flat run carries FlatCounters (F6)"),
    )
}

/// F6's per-engine identities on one complete-first `Flat` run's counters,
/// cut off (criterion 7; L7).
fn identity_cfirst(c: &CFirstCounters, what: &str) -> Vec<String> {
    let mut bad = Vec::new();
    let Some(fc) = c.flat.as_ref() else {
        return vec![format!("{what}: CFirstCounters.flat is None under Flat")];
    };
    let mut chk = |ok: bool, s: String| {
        if !ok {
            bad.push(format!("{what}: {s}"));
        }
    };
    chk(
        fc.calls == c.cache_probes - c.cache_hits,
        format!(
            "calls {} != cache_probes {} - cache_hits {}",
            fc.calls, c.cache_probes, c.cache_hits
        ),
    );
    chk(
        c.impl_graphs == c.cache_hits + fc.calls,
        format!(
            "impl_graphs {} != cache_hits {} + calls {}",
            c.impl_graphs, c.cache_hits, fc.calls
        ),
    );
    chk(
        c.witnesses + c.witness_duplicates == fc.witnesses,
        format!(
            "witnesses {} + duplicates {} != flat.witnesses {}",
            c.witnesses, c.witness_duplicates, fc.witnesses
        ),
    );
    chk(
        c.reports == fc.calls - fc.witnesses,
        format!(
            "reports {} != calls {} - witnesses {}",
            c.reports, fc.calls, fc.witnesses
        ),
    );
    chk(
        c.sweeps == 0
            && c.sweeps_successful == 0
            && c.sweeps_failing == 0
            && c.sweep_sizes.is_empty(),
        format!(
            "a completion sweep ran under Flat: {} {:?}",
            c.sweeps, c.sweep_sizes
        ),
    );
    bad
}

/// F6's per-engine identities on one gated `Flat` run's counters.
fn identity_gated(c: &GatedCounters, what: &str) -> Vec<String> {
    let mut bad = Vec::new();
    let Some(fc) = c.flat.as_ref() else {
        return vec![format!("{what}: GatedCounters.flat is None under Flat")];
    };
    let mut chk = |ok: bool, s: String| {
        if !ok {
            bad.push(format!("{what}: {s}"));
        }
    };
    chk(
        fc.calls == c.completion_probes - c.completion_cache_hits,
        format!(
            "calls {} != completion_probes {} - completion_cache_hits {}",
            fc.calls, c.completion_probes, c.completion_cache_hits
        ),
    );
    chk(
        c.impl_graphs == c.completion_cache_hits + c.reports_certified + fc.calls,
        format!(
            "impl_graphs {} != completion_cache_hits {} + reports_certified {} + calls {}",
            c.impl_graphs, c.completion_cache_hits, c.reports_certified, fc.calls
        ),
    );
    chk(
        c.reports_by_completion_test == fc.calls - fc.witnesses,
        format!(
            "reports_by_completion_test {} != calls {} - witnesses {}",
            c.reports_by_completion_test, fc.calls, fc.witnesses
        ),
    );
    chk(
        c.first_failure_mode || c.reports == c.reports_certified + c.reports_by_completion_test,
        format!(
            "reports {} != certified {} + by completion test {}",
            c.reports, c.reports_certified, c.reports_by_completion_test
        ),
    );
    chk(
        c.completion_sweeps == 0
            && c.completion_sweeps_successful == 0
            && c.completion_sweeps_failing == 0
            && c.completion_sweep_sizes.is_empty(),
        format!("a completion sweep ran under Flat: {}", c.completion_sweeps),
    );
    bad
}

/// The identity on a public `Flat` outcome; also that `flat_counters` is the
/// engine record's.
fn identity(o: &ConfOutcome, what: &str) -> Vec<String> {
    let fc = o.flat_counters().cloned();
    if let Some(c) = o.cfirst_counters() {
        let mut bad = identity_cfirst(c, what);
        if c.flat != fc {
            bad.push(format!(
                "{what}: ConfOutcome.flat_counters is not CFirstCounters.flat"
            ));
        }
        bad
    } else if let Some(c) = o.gated_counters() {
        let mut bad = identity_gated(c, what);
        if c.flat != fc {
            bad.push(format!(
                "{what}: ConfOutcome.flat_counters is not GatedCounters.flat"
            ));
        }
        bad
    } else {
        vec![format!("{what}: a Flat outcome with neither engine record")]
    }
}

fn fail_if(bad: Vec<String>, what: &str) {
    assert!(
        bad.is_empty(),
        "conformance: {what}:\n  {}",
        bad.join("\n  ")
    );
}

fn tid(g: &ExecutionGraph, name: &str) -> ThreadId {
    g.thread_ids()
        .into_iter()
        .find(|t| g.get_thread_tclab(*t).name().as_deref() == Some(name))
        .unwrap_or_else(|| panic!("conformance: no thread `{name}` in the graph"))
}

fn summary(g: &ExecutionGraph, v: &[String]) -> Summary {
    let w = wobs(g, v).expect("conformance: wobs on a fixture graph");
    Summary::of(CompleteExecution::assume_finished_at_gate(g), &w, v)
        .expect("conformance: summary on a fixture graph")
}

/// Both families, kept, from the stateful engine (the oracle route).
fn families(
    config: &Config,
    visible: &[String],
    imp: &Prog,
    spec: &Prog,
) -> (Vec<ExecutionGraph>, Vec<ExecutionGraph>) {
    let c = cc(
        Eng::Stateful,
        config.clone(),
        visible,
        Selector::Ltr,
        CompletionCover::Sweep,
    );
    let o = stateful::run_with(&c, imp, spec, true);
    assert!(
        o.spec_errors.is_empty(),
        "conformance: Spec errors {:?}",
        o.spec_errors
    );
    (o.kept_impl_graphs, o.kept_spec_graphs)
}

fn keys(gs: &[ExecutionGraph], v: &[String]) -> BTreeSet<String> {
    gs.iter().map(|g| canon_key(g, v)).collect()
}

fn cfirst_raw(c: &ConfConfig, imp: &Prog, spec: &Prog) -> CFirstOutcome {
    cfirst::run_with(c, imp, spec, true)
}

fn gated_raw(c: &ConfConfig, imp: &Prog, spec: &Prog) -> GatedOutcome {
    gated::run_with(c, imp, spec, true)
}

/// Report keys of a raw complete-first outcome (completion reports only;
/// the cut is off on every run here).
fn cfirst_keys(o: &CFirstOutcome, v: &[String]) -> BTreeSet<String> {
    assert!(o.cut_reports.is_empty(), "conformance: the cut is off");
    o.reports.iter().map(|(g, _)| canon_key(g, v)).collect()
}

fn gated_keys(o: &GatedOutcome, v: &[String]) -> BTreeSet<String> {
    o.reports.iter().map(|(g, _, _)| canon_key(g, v)).collect()
}

/// The rendered verdict with the `Flat` block's timing removed (the
/// `FlatCover: …` line carries `wall_time_ms`).
fn rendered(v: &Result<ConfVerdict, ConfError>) -> String {
    match v {
        Ok(verdict) => format!("{verdict}"),
        Err(e) => format!("{e}"),
    }
}

// =========================================================================
// Fixtures, from the criteria's text
// =========================================================================

/// `P4-MIXED` 1(b)'s annotated server (test 7's Impl; D1): `K: send(S,1); x
/// := recv^b() ‖ S: y := recv^b(); send^i(D,1); z := recv^{b,i}(); send(K,
/// reply) ‖ D: w := recv^b(); send(S,1)`; FIFO channels `main` creates;
/// spawned `d, s, k`. With `annotated = false`, P4-MIXED 1(a)'s Impl.
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

/// Test 7's Spec (criterion 1; D1): `K: send(S,1); x := recv^b() ‖ S: y :=
/// recv^b(); send(K,2) ‖ Z: n := nondet({0,1}); assume(n = 0)`, spawned
/// `k, s, z`; without `Z` (`with_z = false`) the control of criterion 1.
/// `undeclared_blocked`: also an undeclared `x` whose blocking receive never
/// has a source (a `Block{Value}`, no event — the performable-operations
/// boundary of F1).
fn t7_spec(with_z: bool, undeclared_blocked: bool) -> Prog {
    prog(move || {
        let (tx_k, rx_k) = fifo();
        let (tx_s, rx_s) = fifo();
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            tx_k.send_msg(2);
        });
        if with_z {
            let _z = named("z", || {
                let n = (0..=1usize).nondet();
                crate::assume!(n == 0);
            });
        }
        if undeclared_blocked {
            let (_tx_x, rx_x) = fifo();
            let _x = named("x", move || {
                let _v: i32 = rx_x.recv_msg_block();
            });
        }
    })
}

fn ks() -> Vec<String> {
    vis(&["k", "s"])
}

/// Criterion 3(a) (D3): `A: send(A,1); x := recv^b()`.
fn self_send() -> Prog {
    prog(|| {
        let _a = named("a", || {
            crate::send_msg(thread::current().id(), 1i32);
            let _x: i32 = crate::recv_msg_block();
        });
    })
}

/// Criterion 3(b) (D3): `A: send(B,1) ‖ B: x := recv_msg()` (non-blocking);
/// spawned `b, a`.
fn nb_bottom() -> Prog {
    prog(|| {
        let b = named("b", || {
            let _x: Option<i32> = crate::recv_msg();
        });
        let bid = b.thread().id();
        let _a = named("a", move || crate::send_msg(bid, 1i32));
    })
}

/// Criterion 3(c) (D3): `A: skip ‖ B: x := recv^b()` (`receives = true`) or
/// `A: skip ‖ B: skip`; spawned `a, b`.
fn blocked_b(receives: bool) -> Prog {
    prog(move || {
        let _a = named("a", || {});
        let _b = named("b", move || {
            if receives {
                let _x: i32 = crate::recv_msg_block();
            }
        });
    })
}

/// Criterion 4's mutation fixture (D4): `A: n := nondet(); if n = v_on then
/// send^v(C,1) else send^i(D,1) ‖ C: recv_msg() ‖ D: recv_msg_block()`;
/// spawned `a, c, d`; Bag channels `main` creates. `v_on = true` is the
/// criterion's orientation, `false` the other.
fn branchy(v_on: bool) -> Prog {
    prog(move || {
        let (tx_c, rx_c) = bag_chan();
        let (tx_d, rx_d) = bag_chan();
        let _a = named("a", move || {
            if crate::nondet() == v_on {
                tx_c.send_msg_as(Visibility::Visible, 1);
            } else {
                tx_d.send_msg_as(Visibility::Invisible, 1);
            }
        });
        let _c = named("c", move || {
            let _x: Option<i32> = rx_c.recv_msg();
        });
        let _d = named("d", move || {
            let _y: i32 = rx_d.recv_msg_block();
        });
    })
}

/// F3's tie (D-tie, the tester's addition for the tie-break mutation): `M:
/// send(W,1) ‖ W: x := recv^b(); send(X,1) ‖ X: y := recv_msg()`
/// (non-blocking), spawned **`x, w, m`** — so `x` has the smaller `ThreadId`
/// and `w` the smaller name. In the graph where `X` reads ⊥ its receive and
/// `W`'s are unordered by `ord`, a tie broken by name: `w` first. Then `W`'s
/// send to `X` is saturated before `X`'s slot, whose options are `W`'s send
/// (fails: ⟨rcv,1⟩ vs ⟨rcv,⊥⟩) then ⊥: 2 options. In the graph where `X`
/// reads 1, `W`'s receive precedes by `ord`: 1 option per slot. Run totals
/// self-conformance: `calls 2, visits 10, src 5, rec 4, w 2, md 5`. Broken
/// by `ThreadId` or by reversed name, `x` first: its slot has no send yet,
/// only ⊥ — `src 4`.
fn tie() -> Prog {
    prog(|| {
        let (tx_w, rx_w) = bag_chan();
        let (tx_x, rx_x) = bag_chan();
        let _x = named("x", move || {
            let _y: Option<i32> = rx_x.recv_msg();
        });
        let _w = named("w", move || {
            let _v: i32 = rx_w.recv_msg_block();
            tx_x.send_msg(1);
        });
        let _m = named("m", move || tx_w.send_msg(1));
    })
}

/// `ex:naive`'s pair at `k`, encoding 1 (`c_first`) or 2.
fn naive_pair(k: usize, c_first: bool) -> (Prog, Prog) {
    (naive_d(k, 0, c_first, None), naive_d(k, 1, c_first, None))
}

/// `ex:naive`'s self-conformance pair (criterion 6(b)).
fn naive_self(k: usize, c_first: bool) -> Prog {
    naive_d(k, 1, c_first, None)
}

fn factorial(k: usize) -> usize {
    (1..=k).product()
}

// =========================================================================
// Criterion 1 — test 7, conforming (D1)
// =========================================================================

/// D1's flat figures on a run that called `FlatCover` once.
const T7_CONFORMS: F = F {
    calls: 1,
    visits: 6,
    nd: 1,
    src: 2,
    rec: 2,
    sk: 0,
    slk: 0,
    srk: 0,
    dk: 0,
    w: 1,
    md: 6,
};

/// The (probes, hits) pair of criterion 1's table and the flat figures.
fn c01_expected(e: Eng) -> ((usize, usize), F) {
    match e {
        Eng::CFirst | Eng::Gated(_, GatePolicy::Never) => ((1, 0), T7_CONFORMS),
        Eng::Gated(_, _) => ((1, 1), F::default()),
        _ => unreachable!("conformance: only the sweeping engines take Flat"),
    }
}

fn probes_hits(o: &ConfOutcome) -> (usize, usize) {
    if let Some(c) = o.cfirst_counters() {
        (c.cache_probes, c.cache_hits)
    } else if let Some(c) = o.gated_counters() {
        (c.completion_probes, c.completion_cache_hits)
    } else {
        panic!("conformance: no sweeping-engine record")
    }
}

/// **Criterion 1 (D1).** Test 7 conforms on every engine × selector: zero
/// reports, `StateSpaceExhausted`; the eligibility record `{true, false, 2,
/// None}` on every `Flat` run; criterion 1's counter table per engine × mode
/// × policy (complete-first and gated `Never`: probes 1, hits 0, `calls 1,
/// visits 6, nd 1, src 2, w 1`; gated `Always`/`Budget(n ≥ 1)`: probes 1, hits
/// 1, every flat count 0); F6's identity on every `Flat` run. The same
/// engines under `Sweep` conform too (verdicts equal across engines).
#[test]
fn c01_test7_conforms_everywhere_with_the_counter_table() {
    let (imp, spec) = (server_impl(true, 2), t7_spec(true, false));
    let mut bad = Vec::new();
    for s in SELECTORS {
        for e in table_engines() {
            let covers: Vec<CompletionCover> = if e.flat_capable() {
                vec![CompletionCover::Flat, CompletionCover::Sweep]
            } else {
                vec![CompletionCover::Sweep]
            };
            for cover in covers {
                let what = format!("{e:?} {s:?} {cover:?}");
                let v = verify(cc(e, cfg(ConsType::FIFO), &ks(), s, cover), &imp, &spec);
                if class(&v) != "conforms" {
                    bad.push(format!("{what}: {}", class(&v)));
                    continue;
                }
                let o = outcome(&v);
                if o.end() != SearchEnd::StateSpaceExhausted {
                    bad.push(format!("{what}: end {:?}", o.end()));
                }
                if cover == CompletionCover::Sweep {
                    if o.flat_counters().is_some() || o.flat_eligibility().is_some() {
                        bad.push(format!("{what}: Flat records under Sweep"));
                    }
                    continue;
                }
                let want_e = FlatEligibility {
                    communication_flat: true,
                    thread_flat: false,
                    spec_graphs_scanned: 2,
                    first_invisible: None,
                };
                if o.flat_eligibility() != Some(&want_e) {
                    bad.push(format!("{what}: eligibility {:?}", o.flat_eligibility()));
                }
                let (ph, f) = c01_expected(e);
                if probes_hits(o) != ph {
                    bad.push(format!(
                        "{what}: probes/hits {:?}, expected {ph:?}",
                        probes_hits(o)
                    ));
                }
                if flat_of(o) != f {
                    bad.push(format!("{what}: flat {:?}, expected {f:?}", flat_of(o)));
                }
                bad.extend(identity(o, &what));
            }
        }
    }
    fail_if(bad, "criterion 1");
}

/// **Criterion 1's control (m1; D1).** The same Spec without `Z`: both
/// Booleans true, one graph. And F1's boundary: an undeclared thread whose
/// only receive never has a source (a `Block{Value}`, no event, no slot) does
/// not make the Spec ineligible — it performs no send or receive — while it
/// does make it not thread-flat.
#[test]
fn c01_the_eligibility_control() {
    let imp = server_impl(true, 2);
    for (spec, want) in [
        (
            t7_spec(false, false),
            FlatEligibility {
                communication_flat: true,
                thread_flat: true,
                spec_graphs_scanned: 1,
                first_invisible: None,
            },
        ),
        (
            t7_spec(true, true),
            FlatEligibility {
                communication_flat: true,
                thread_flat: false,
                spec_graphs_scanned: 2,
                first_invisible: None,
            },
        ),
    ] {
        for e in [
            Eng::CFirst,
            Eng::Gated(GatedMode::Exhaustive, GatePolicy::Never),
        ] {
            let v = verify(
                cc(
                    e,
                    cfg(ConsType::FIFO),
                    &ks(),
                    Selector::Ltr,
                    CompletionCover::Flat,
                ),
                &imp,
                &spec,
            );
            assert_eq!(class(&v), "conforms", "conformance: control {e:?}");
            assert_eq!(
                outcome(&v).flat_eligibility(),
                Some(&want),
                "conformance: control {e:?}"
            );
            fail_if(identity(outcome(&v), "control"), "criterion 1 control");
        }
    }
}

/// **Criterion 1, the mutation's target.** "Eligibility requires every thread
/// visible" (`thread_flat` read in place of `communication_flat`) refuses
/// the flat engine on test 7; this test asserts it is **not** refused, on
/// both engines that read the knob, through `verify` and through
/// `cfirst::run`/`gated::run` directly (the grid's route).
#[test]
fn c01_the_flat_engine_is_not_refused_on_test7() {
    let (imp, spec) = (server_impl(true, 2), t7_spec(true, false));
    for e in [
        Eng::CFirst,
        Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
    ] {
        let c = cc(
            e,
            cfg(ConsType::FIFO),
            &ks(),
            Selector::Ltr,
            CompletionCover::Flat,
        );
        let v = verify(c.clone(), &imp, &spec);
        assert_eq!(class(&v), "conforms", "conformance: {e:?} through verify");
        let direct = match e {
            Eng::CFirst => cfirst::run(c, Arc::clone(&imp), Arc::clone(&spec)),
            _ => gated::run(c, Arc::clone(&imp), Arc::clone(&spec)),
        };
        assert_eq!(class(&direct), "conforms", "conformance: {e:?} through run");
    }
}

/// **Criterion 1, the pinned `Conforms` rendering (round 03 M1; D1, D8).**
/// The complete-first `Flat` rendering is the `Sweep` rendering with "a
/// sweep (thm:cfirst)" replaced by "`FlatCover` (thm:cfirst with thm:flat,
/// cor:mixedflat)", followed by the eligibility line and the counters, and
/// with the two `Flat` assumptions in the certificate's list.
#[test]
fn c01_the_pinned_conforms_rendering() {
    let (imp, spec) = (server_impl(true, 2), t7_spec(true, false));
    let flat = verify(
        cc(
            Eng::CFirst,
            cfg(ConsType::FIFO),
            &ks(),
            Selector::Ltr,
            CompletionCover::Flat,
        ),
        &imp,
        &spec,
    );
    let sweep = verify(
        cc(
            Eng::CFirst,
            cfg(ConsType::FIFO),
            &ks(),
            Selector::Ltr,
            CompletionCover::Sweep,
        ),
        &imp,
        &spec,
    );
    let (tf, ts) = (rendered(&flat), rendered(&sweep));
    let line = "conformance: silence. Every complete graph of the implementation is covered by \
                one of the specification \u{2014} by a cached witness or by `FlatCover` \
                (thm:cfirst with thm:flat, cor:mixedflat) \u{2014} and the outer exploration \
                reached the end of its state space.";
    assert!(
        tf.lines().any(|l| l == line),
        "conformance: the coverage line:\n{tf}"
    );
    assert!(
        tf.lines()
            .any(|l| l == "the specification is communication-flat: 2 graphs scanned"),
        "conformance: the eligibility line:\n{tf}"
    );
    let Ok(ConfVerdict::Conforms(c)) = &flat else {
        panic!("conformance: Flat conforms")
    };
    let a = c.assumptions();
    // Criterion 8's two `Flat` entries, verbatim (gate-4 round 01 n2).
    assert!(
        a.iter()
            .any(|x| *x
                == "eligibility decided from the precheck's enumeration of `Graphs(Spec)` (D12)"),
        "conformance: the D12 assumption: {a:?}"
    );
    assert!(
        a.iter()
            .any(|x| *x == "saturation order-independent under F79's premise"),
        "conformance: the F79 assumption: {a:?}"
    );
    let Ok(ConfVerdict::Conforms(cs)) = &sweep else {
        panic!("conformance: Sweep conforms")
    };
    assert_eq!(
        a.len(),
        cs.assumptions().len() + 2,
        "conformance: exactly two Flat entries"
    );
    // Substitution: the Flat text minus its Flat-only lines equals the Sweep
    // text under criterion 8's substitution.
    assert_eq!(
        strip_flat_only(&tf, &a, cs.assumptions().as_slice()),
        subst_sweep(&ts),
        "conformance: criterion 8's substitution"
    );
}

/// Criterion 8's substitutions applied to a `Sweep` rendering (D8), every one
/// written from the criteria's text.
fn subst_sweep(s: &str) -> String {
    let pairs: [(&str, &str); 9] = [
        // The `Conforms` coverage lines.
        (
            "a sweep (thm:cfirst)",
            "`FlatCover` (thm:cfirst with thm:flat, cor:mixedflat)",
        ),
        (
            "a sweep (thm:gated)",
            "`FlatCover` (thm:gated with thm:flat, cor:mixedflat)",
        ),
        // CFIRST_EACH_UNCOVERED's sweep clause.
        (
            "an unpruned sweep of the specification found no graph with its signature whose order \
             is contained in its own (lem:sig).",
            "`FlatCover` found no covering graph (thm:flat).",
        ),
        // GATED_EACH_UNCOVERED's (round 06 n1).
        (
            "an unpruned sweep of the specification found none (lem:sig).",
            "`FlatCover` found no covering graph (thm:flat).",
        ),
        // CFIRST_EXACTLY_THE_SET's last clause.
        (
            "no early-error cut fired, and every failing sweep reached the end of the \
             specification's.",
            "no early-error cut fired, and `FlatCover` is exact for this communication-flat \
             specification (thm:flat, cor:mixedflat).",
        ),
        // GATED_EXACTLY_THE_SET's: the gate-sweep clause stays (round 04 m3).
        (
            "state space and every failing sweep reached the end of the specification's.",
            "state space, every failing gate sweep reached the end of the specification's, and \
             `FlatCover` is exact for this communication-flat specification (thm:flat, \
             cor:mixedflat).",
        ),
        // GATED_FIRST_FAILURE's completion clause.
        (
            "a complete graph that no specification graph covers (lem:sig).",
            "a complete graph that no specification graph covers (thm:flat).",
        ),
        // The per-report `certifies` lines (round 04 M1, round 06 n1).
        (
            "an exhaustive unpruned sweep of the specification found none (lem:sig, thm:cfirst)",
            "`FlatCover` found no covering graph of this communication-flat specification \
             (thm:flat, cor:mixedflat, thm:cfirst)",
        ),
        (
            "no cached witness and no graph of an exhaustive unpruned sweep covered it (lem:sig, \
             thm:gated)",
            "no cached witness covered it and `FlatCover` found no covering graph of it \
             (thm:flat, cor:mixedflat, thm:gated)",
        ),
    ];
    let mut out = s.to_string();
    for (a, b) in pairs {
        out = out.replace(a, b);
    }
    out
}

/// A `Flat` rendering with its `Flat`-only lines removed: the eligibility
/// line, the `Flat` block's sentence, the counters line, and the two extra
/// assumptions (those of `flat_assumptions` not in `sweep_assumptions`).
fn strip_flat_only(s: &str, flat_assumptions: &[&str], sweep_assumptions: &[&str]) -> String {
    let extra: Vec<String> = flat_assumptions
        .iter()
        .filter(|a| !sweep_assumptions.contains(a))
        .map(|a| format!("  - {a}"))
        .collect();
    let mut out = String::new();
    for l in s.split_inclusive('\n') {
        let t = l.trim_end_matches('\n');
        if t.starts_with("the specification is communication-flat: ")
            || t.starts_with("completion reports not raised under an absence certificate are")
            || t.starts_with("FlatCover: ")
            || extra.iter().any(|x| x == t)
        {
            continue;
        }
        out.push_str(l);
    }
    out
}

// =========================================================================
// Criterion 2 — test 7, violating (D2)
// =========================================================================

/// D2's flat figures on a run that called `FlatCover` once on the violating
/// completion.
const T7_VIOLATES: F = F {
    calls: 1,
    visits: 6,
    nd: 2,
    src: 2,
    rec: 2,
    sk: 2,
    slk: 0,
    srk: 0,
    dk: 0,
    w: 0,
    md: 4,
};

/// Criterion 2's expectation per engine: (tag, gate, flat figures if `Flat`).
fn c02_expected(e: Eng) -> (ReportTag, ReportGate, Option<F>) {
    use GatePolicy::*;
    use GatedMode::*;
    let cc_ = (ReportTag::CompleteCoverage, ReportGate::Completion);
    let ge = (ReportTag::GrowingExhaustion, ReportGate::FreshSend);
    match e {
        Eng::Enum => (ge.0, ge.1, None),
        Eng::Stateful => (cc_.0, cc_.1, None),
        Eng::CFirst => (cc_.0, cc_.1, Some(T7_VIOLATES)),
        Eng::Gated(Exhaustive, Always | Budget(2)) => (cc_.0, cc_.1, Some(F::default())),
        Eng::Gated(Exhaustive, Never | Budget(1)) => (cc_.0, cc_.1, Some(T7_VIOLATES)),
        Eng::Gated(FirstFailure, Always | Budget(2)) => (ge.0, ge.1, Some(F::default())),
        Eng::Gated(FirstFailure, Never | Budget(1)) => (cc_.0, cc_.1, Some(T7_VIOLATES)),
        Eng::Gated(_, Budget(_)) => unreachable!("conformance: Budget(1) and Budget(2) only"),
    }
}

/// **Criterion 2 (D2).** `S` replies 3: one report on every engine × selector,
/// tag and gate per mode and policy; under `Flat` the counters (`calls 1,
/// visits 6, send_kills 2, nd 2, src 2, w 0` where `FlatCover` runs; `calls 0`
/// under `Always`/`Budget(2)`); gated exhaustive `Always`/`Budget(2)` report
/// through `reports_certified` with `completion_probes = 0`; the run ends
/// `StateSpaceExhausted` on the exhaustive engines; F6's identity.
#[test]
fn c02_test7_violating_per_engine_mode_and_policy() {
    let (imp, spec) = (server_impl(true, 3), t7_spec(true, false));
    let mut bad = Vec::new();
    for s in SELECTORS {
        for e in table_engines() {
            let what = format!("{e:?} {s:?}");
            let v = verify(
                cc(e, cfg(ConsType::FIFO), &ks(), s, cover_for(e)),
                &imp,
                &spec,
            );
            if class(&v) != "reported:1" {
                bad.push(format!("{what}: {}", class(&v)));
                continue;
            }
            let o = outcome(&v);
            let r = &o.reports()[0];
            let (tag, gate, f) = c02_expected(e);
            if (r.tag(), r.gate()) != (tag, gate) {
                bad.push(format!(
                    "{what}: {:?}@{:?}, expected {tag:?}@{gate:?}",
                    r.tag(),
                    r.gate()
                ));
            }
            let first_failure = matches!(e, Eng::Gated(GatedMode::FirstFailure, _));
            let want_end = if first_failure {
                SearchEnd::StoppedAtFirstReport
            } else {
                SearchEnd::StateSpaceExhausted
            };
            if o.end() != want_end {
                bad.push(format!("{what}: end {:?}", o.end()));
            }
            let Some(f) = f else { continue };
            if flat_of(o) != f {
                bad.push(format!("{what}: flat {:?}, expected {f:?}", flat_of(o)));
            }
            bad.extend(identity(o, &what));
            if let Eng::Gated(GatedMode::Exhaustive, p) = e {
                let g = o.gated_counters().expect("conformance: gated record");
                let certified = matches!(p, GatePolicy::Always | GatePolicy::Budget(2));
                let want = if certified { (1, 0, 0) } else { (0, 1, 1) };
                let got = (
                    g.reports_certified,
                    g.reports_by_completion_test,
                    g.completion_probes,
                );
                if got != want {
                    bad.push(format!(
                        "{what}: (certified, by test, probes) {got:?}, expected {want:?}"
                    ));
                }
            }
        }
    }
    fail_if(bad, "criterion 2");
}

/// **Criterion 2, every exhaustive run's one report equal by key (round 02
/// m5).** Raw routes, both families kept: the stateful engine, complete-first
/// and gated exhaustive under every policy, each under `Flat` and `Sweep`,
/// report exactly the one complete Impl graph.
#[test]
fn c02_every_exhaustive_report_is_the_one_impl_graph() {
    let (imp, spec) = (server_impl(true, 3), t7_spec(true, false));
    let v = ks();
    let (imps, _) = families(&cfg(ConsType::FIFO), &v, &imp, &spec);
    assert_eq!(imps.len(), 1, "conformance: one Impl graph");
    let want = keys(&imps, &v);
    let mut bad = Vec::new();
    for cover in [CompletionCover::Flat, CompletionCover::Sweep] {
        let c = cc(Eng::CFirst, cfg(ConsType::FIFO), &v, Selector::Ltr, cover);
        let o = cfirst_raw(&c, &imp, &spec);
        if cfirst_keys(&o, &v) != want {
            bad.push(format!("cfirst {cover:?}: keys differ"));
        }
        if cover == CompletionCover::Flat {
            bad.extend(identity_cfirst(&o.counters, "cfirst raw"));
        }
        for p in [
            GatePolicy::Never,
            GatePolicy::Always,
            GatePolicy::Budget(1),
            GatePolicy::Budget(2),
        ] {
            let c = cc(
                Eng::Gated(GatedMode::Exhaustive, p),
                cfg(ConsType::FIFO),
                &v,
                Selector::Ltr,
                cover,
            );
            let o = gated_raw(&c, &imp, &spec);
            if gated_keys(&o, &v) != want || o.reports.len() != 1 {
                bad.push(format!("gated {p:?} {cover:?}: keys differ"));
            }
            if cover == CompletionCover::Flat {
                bad.extend(identity_gated(&o.counters, &format!("gated raw {p:?}")));
            }
        }
    }
    let c = cc(
        Eng::Stateful,
        cfg(ConsType::FIFO),
        &v,
        Selector::Ltr,
        CompletionCover::Sweep,
    );
    let o = stateful::run_with(&c, &imp, &spec, true);
    let sk: BTreeSet<String> = o.reports.iter().map(|(g, _)| canon_key(g, &v)).collect();
    if sk != want {
        bad.push("stateful: keys differ".to_string());
    }
    fail_if(bad, "criterion 2 keys");
}

/// **Criterion 2, the pinned `Reported` rendering (round 03 M1, round 04 M1,
/// m3; D2).** Complete-first `Flat`: `CFIRST_EACH_UNCOVERED_FLAT`'s text,
/// `CFIRST_EXACTLY_THE_SET_FLAT`'s (no cut, `StateSpaceExhausted`), the
/// report's `certifies` line in its `Flat` text, the eligibility line and the
/// `Flat` block's sentence — each written here from the criteria; and the
/// whole text is the `Sweep` rendering under criterion 8's substitution.
#[test]
fn c02_the_pinned_reported_rendering() {
    let (imp, spec) = (server_impl(true, 3), t7_spec(true, false));
    let flat = verify(
        cc(
            Eng::CFirst,
            cfg(ConsType::FIFO),
            &ks(),
            Selector::Ltr,
            CompletionCover::Flat,
        ),
        &imp,
        &spec,
    );
    let sweep = verify(
        cc(
            Eng::CFirst,
            cfg(ConsType::FIFO),
            &ks(),
            Selector::Ltr,
            CompletionCover::Sweep,
        ),
        &imp,
        &spec,
    );
    let tf = rendered(&flat);
    for want in [
        "Every complete graph in this list is an uncovered complete graph of the implementation: \
         at its completion no cached witness covered it, and `FlatCover` found no covering graph \
         (thm:flat).",
        "The list is exactly the set of such graphs (thm:cfirst): the outer exploration reached \
         the end of its state space, no early-error cut fired, and `FlatCover` is exact for this \
         communication-flat specification (thm:flat, cor:mixedflat).",
        "  certifies (CompleteCoverage): no graph of the specification covers the reported \
         complete graph: no cached witness did, and `FlatCover` found no covering graph of this \
         communication-flat specification (thm:flat, cor:mixedflat, thm:cfirst)",
        "completion reports not raised under an absence certificate are `FlatCover`'s \u{22a5} \
         (thm:flat)",
    ] {
        assert!(
            tf.lines().any(|l| l == want),
            "conformance: missing line {want:?} in:\n{tf}"
        );
    }
    assert!(
        tf.lines()
            .any(|l| l == "the specification is communication-flat: 2 graphs scanned"),
        "conformance: the eligibility line:\n{tf}"
    );
    // `Diagnostics::NotProduced` is unchanged by criterion 8 (round 02 M4) and
    // keeps its "(lem:sig)"; no other line may cite it.
    let not_produced = format!(
        "  {}",
        crate::conformance::report::Diagnostics::NotProduced {
            by: Engine::CompleteFirst
        }
    );
    assert!(
        !tf.lines()
            .any(|l| l.contains("(lem:sig") && l != not_produced),
        "conformance: a Flat rendering cites lem:sig outside NotProduced:\n{tf}"
    );
    assert_eq!(
        strip_flat_only(&tf, &[], &[]),
        subst_sweep(&rendered(&sweep)),
        "conformance: criterion 8's substitution"
    );
}

// =========================================================================
// Criterion 3 — the three boundary cases (D3)
// =========================================================================

/// One boundary case: the `Flat` runs (complete-first, gated `Exhaustive` ×
/// `Never`) carry `want` and conform or report as the `Sweep` reference does;
/// every engine's verdict and report-key set under `Flat` equals `Sweep`'s
/// (gated under every policy).
fn boundary(
    name: &str,
    config: Config,
    v: &[String],
    imp: &Prog,
    spec: &Prog,
    reports: usize,
    want: F,
) {
    let mut bad = Vec::new();
    let expect = if reports == 0 {
        "conforms".to_string()
    } else {
        format!("reported:{reports}")
    };
    for s in SELECTORS {
        for e in [
            Eng::Enum,
            Eng::Stateful,
            Eng::CFirst,
            Eng::Gated(GatedMode::Exhaustive, GatePolicy::Never),
            Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
            Eng::Gated(GatedMode::FirstFailure, GatePolicy::Always),
        ] {
            for cover in [CompletionCover::Sweep, CompletionCover::Flat] {
                if cover == CompletionCover::Flat && !e.flat_capable() {
                    continue;
                }
                let what = format!("{name} {e:?} {s:?} {cover:?}");
                let r = verify(cc(e, config.clone(), v, s, cover), imp, spec);
                if class(&r) != expect {
                    bad.push(format!("{what}: {}", class(&r)));
                    continue;
                }
                if cover == CompletionCover::Flat {
                    bad.extend(identity(outcome(&r), &what));
                    let pinned = matches!(e, Eng::CFirst | Eng::Gated(_, GatePolicy::Never));
                    if pinned && flat_of(outcome(&r)) != want {
                        bad.push(format!(
                            "{what}: flat {:?}, expected {want:?}",
                            flat_of(outcome(&r))
                        ));
                    }
                }
            }
        }
        for p in [GatePolicy::Never, GatePolicy::Always] {
            let kf = gated_keys(
                &gated_raw(
                    &cc(
                        Eng::Gated(GatedMode::Exhaustive, p),
                        config.clone(),
                        v,
                        s,
                        CompletionCover::Flat,
                    ),
                    imp,
                    spec,
                ),
                v,
            );
            let ks_ = gated_keys(
                &gated_raw(
                    &cc(
                        Eng::Gated(GatedMode::Exhaustive, p),
                        config.clone(),
                        v,
                        s,
                        CompletionCover::Sweep,
                    ),
                    imp,
                    spec,
                ),
                v,
            );
            if kf != ks_ {
                bad.push(format!(
                    "{name} gated {p:?} {s:?}: report keys differ Flat/Sweep"
                ));
            }
        }
        let kf = cfirst_keys(
            &cfirst_raw(
                &cc(Eng::CFirst, config.clone(), v, s, CompletionCover::Flat),
                imp,
                spec,
            ),
            v,
        );
        let ks_ = cfirst_keys(
            &cfirst_raw(
                &cc(Eng::CFirst, config.clone(), v, s, CompletionCover::Sweep),
                imp,
                spec,
            ),
            v,
        );
        if kf != ks_ {
            bad.push(format!(
                "{name} cfirst {s:?}: report keys differ Flat/Sweep"
            ));
        }
    }
    fail_if(bad, &format!("criterion 3 {name}"));
}

/// **Criterion 3(a) (D3).** A self-send is saturated before its slot and is
/// the slot's single source: `calls 1, visits 3, src 1, rec 1, w 1, md 3`.
#[test]
fn c03a_a_self_send() {
    let p = self_send();
    boundary(
        "self-send",
        cfg(ConsType::Bag),
        &vis(&["a"]),
        &p,
        &p,
        0,
        F {
            calls: 1,
            visits: 3,
            src: 1,
            rec: 1,
            w: 1,
            md: 3,
            ..F::default()
        },
    );
}

/// **Criterion 3(b) (D3).** A non-blocking receive reading ⊥ (the engine's
/// rule: ⊥ with a send available — two Impl graphs, measured): run totals
/// `calls 2, visits 6, src 3 (1 + 2: sources before None), rec 2, w 2, md 3`.
#[test]
fn c03b_a_non_blocking_receive_reading_bottom() {
    let p = nb_bottom();
    let v = vis(&["a", "b"]);
    let (imps, _) = families(&cfg(ConsType::Bag), &v, &p, &p);
    assert_eq!(imps.len(), 2, "conformance: B reads 1 or ⊥");
    boundary(
        "nb-bottom",
        cfg(ConsType::Bag),
        &v,
        &p,
        &p,
        0,
        F {
            calls: 2,
            visits: 6,
            src: 3,
            rec: 2,
            w: 2,
            md: 3,
            ..F::default()
        },
    );
}

/// **Criterion 3(c) (D3).** A blocking receive with nothing deliverable owns
/// no slot (`q = 0`): covered on statuses (`Blocked` both sides), `calls 1,
/// visits 1, w 1`; against `B: skip` uncovered — `done_kills 1`, one report,
/// as the sweep engines report it.
#[test]
fn c03c_a_blocking_receive_with_nothing_deliverable() {
    let (imp, other) = (blocked_b(true), blocked_b(false));
    let v = vis(&["a", "b"]);
    boundary(
        "blocked-self",
        cfg(ConsType::Bag),
        &v,
        &imp,
        &imp,
        0,
        F {
            calls: 1,
            visits: 1,
            w: 1,
            md: 1,
            ..F::default()
        },
    );
    boundary(
        "blocked-vs-skip",
        cfg(ConsType::Bag),
        &v,
        &imp,
        &other,
        1,
        F {
            calls: 1,
            visits: 1,
            dk: 1,
            md: 1,
            ..F::default()
        },
    );
}

// =========================================================================
// Criterion 4 — eligibility and refusal (D4)
// =========================================================================

/// The eligibility record of `spec` under complete-first `Flat` (precheck on),
/// or the refusal.
fn eligibility_of(
    config: Config,
    v: &[String],
    imp: &Prog,
    spec: &Prog,
) -> Result<FlatEligibility, ConfError> {
    let r = cfirst::run(
        cc(Eng::CFirst, config, v, Selector::Ltr, CompletionCover::Flat),
        Arc::clone(imp),
        Arc::clone(spec),
    );
    match r {
        Ok(verdict) => Ok(verdict
            .outcome()
            .flat_eligibility()
            .cloned()
            .expect("conformance: Some whenever the precheck ran under Flat")),
        Err(e) => Err(e),
    }
}

/// **Criterion 4(a) (D4).** `ex:naive`'s `Spec_k` (`k = 2, 3`, both
/// encodings; `k!` graphs, `thread_flat` true: `main` performs no send or
/// receive), `p1_direct` with `{main, c}` (one graph, `thread_flat` true:
/// its declared `main` sends) and test 7's Spec are communication-flat.
#[test]
fn c04a_the_flat_specifications() {
    for k in [2usize, 3] {
        for c_first in [true, false] {
            let (imp, spec) = naive_pair(k, c_first);
            let e = eligibility_of(cfg(ConsType::Bag), &naive_visible(k), &imp, &spec)
                .unwrap_or_else(|e| panic!("conformance: ex:naive k={k}: {e:?}"));
            assert_eq!(
                e,
                FlatEligibility {
                    communication_flat: true,
                    thread_flat: true,
                    spec_graphs_scanned: factorial(k),
                    first_invisible: None
                },
                "conformance: ex:naive k={k} c_first={c_first}"
            );
        }
    }
    let p1 = prog(crate::conformance::paper_examples::p1_direct);
    let e = eligibility_of(cfg(ConsType::FIFO), &vis(&["main", "c"]), &p1, &p1)
        .unwrap_or_else(|e| panic!("conformance: p1_direct: {e:?}"));
    assert_eq!(
        e,
        FlatEligibility {
            communication_flat: true,
            thread_flat: true,
            spec_graphs_scanned: 1,
            first_invisible: None
        },
        "conformance: p1_direct"
    );
    let e = eligibility_of(
        cfg(ConsType::FIFO),
        &ks(),
        &server_impl(true, 2),
        &t7_spec(true, false),
    )
    .unwrap_or_else(|e| panic!("conformance: test 7: {e:?}"));
    assert!(
        e.communication_flat && !e.thread_flat,
        "conformance: test 7 {e:?}"
    );
}

/// The expected refusal for `P4-MIXED` 1's Impl used as Spec (D4): `d` = t1
/// in the `d, s, k` spawn order is undeclared; `main` performs no send or
/// receive; `d`'s first send or receive is its receive at index 1.
fn d_receive(spec: &Prog) -> (String, String) {
    let v = ks();
    let (_, specs) = families(&cfg(ConsType::FIFO), &v, spec, spec);
    assert_eq!(specs.len(), 1, "conformance: one graph");
    let g = &specs[0];
    let d = tid(g, "d");
    let main = crate::thread::main_thread_id();
    for i in 0..g.thread_size(main) as u32 {
        assert!(
            !matches!(
                g.label(Event::new(main, i)),
                LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_)
            ),
            "conformance: main communicates"
        );
    }
    assert!(
        g.thread_ids().into_iter().filter(|t| *t != main).min() == Some(d),
        "conformance: d is the least spawned thread"
    );
    let e = Event::new(d, 1);
    assert!(
        matches!(g.label(e), LabelEnum::RecvMsg(_)),
        "conformance: d's index 1 is its receive"
    );
    assert!(
        !is_visible(g, e, &v),
        "conformance: d's receive is invisible"
    );
    ("d".to_string(), e.to_string())
}

/// **Criterion 4(b), (c) (D4).** `P4-MIXED` 1(b)'s annotated Impl, and 1(a)'s
/// unannotated one, used as Spec against itself: refused with
/// `SpecNotCommunicationFlat` naming `d`'s receive at its position, by
/// `verify` (both engines) and by `cfirst::run`/`gated::run`; before any
/// outer run (the refusal is the whole result).
#[test]
fn c04bc_the_server_impl_as_spec_is_refused_naming_d() {
    for annotated in [true, false] {
        let p = server_impl(annotated, 2);
        let (thread, pos) = d_receive(&p);
        let want = ConfError::SpecNotCommunicationFlat { thread, pos };
        for e in [
            Eng::CFirst,
            Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
            Eng::Gated(GatedMode::FirstFailure, GatePolicy::Never),
        ] {
            for s in SELECTORS {
                let c = cc(e, cfg(ConsType::FIFO), &ks(), s, CompletionCover::Flat);
                let r = verify(c.clone(), &p, &p);
                assert_eq!(
                    r.as_ref().err(),
                    Some(&want),
                    "conformance: annotated={annotated} {e:?} {s:?}"
                );
                let direct = match e {
                    Eng::CFirst => cfirst::run(c, Arc::clone(&p), Arc::clone(&p)),
                    _ => gated::run(c, Arc::clone(&p), Arc::clone(&p)),
                };
                assert_eq!(
                    direct.err(),
                    Some(want.clone()),
                    "conformance: direct {e:?}"
                );
            }
        }
    }
}

/// **Criterion 4(d), (e) (F5; D4).** `Flat` + `skip_spec_errfree_check(true)`
/// is a `KnobConflict` naming both knobs, from `verify` and from
/// `cfirst::run`/`gated::run`, before any engine runs (the programs here
/// panic if ever run); `Flat` + `Enumerator`/`Stateful` likewise from
/// `verify`. Each renders as one line naming both knobs.
#[test]
fn c04de_knob_conflicts() {
    let boom: Prog = prog(|| panic!("conformance: a refused run executed a program"));
    let skip = ConfError::KnobConflict {
        knob: "completion_cover(Flat)",
        conflicts_with: "skip_spec_errfree_check(true)",
    };
    for e in [
        Eng::CFirst,
        Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
    ] {
        let c = builder(
            e,
            cfg(ConsType::Bag),
            &vis(&["a"]),
            Selector::Ltr,
            CompletionCover::Flat,
        )
        .skip_spec_errfree_check(true)
        .build()
        .expect("conformance: in scope");
        assert_eq!(
            verify(c.clone(), &boom, &boom).err(),
            Some(skip.clone()),
            "conformance: {e:?}"
        );
        let direct = match e {
            Eng::CFirst => cfirst::run(c, Arc::clone(&boom), Arc::clone(&boom)),
            _ => gated::run(c, Arc::clone(&boom), Arc::clone(&boom)),
        };
        assert_eq!(
            direct.err(),
            Some(skip.clone()),
            "conformance: direct {e:?}"
        );
    }
    for e in [Eng::Enum, Eng::Stateful] {
        for skip_check in [false, true] {
            let c = builder(
                e,
                cfg(ConsType::Bag),
                &vis(&["a"]),
                Selector::Ltr,
                CompletionCover::Flat,
            )
            .skip_spec_errfree_check(skip_check)
            .build()
            .expect("conformance: in scope");
            match verify(c, &boom, &boom) {
                Err(ConfError::KnobConflict {
                    knob,
                    conflicts_with,
                }) => {
                    assert_eq!(knob, "completion_cover(Flat)", "conformance: {e:?}");
                    assert!(
                        conflicts_with.contains("Enumerator")
                            && conflicts_with.contains("Stateful"),
                        "conformance: {e:?}: {conflicts_with}"
                    );
                }
                other => panic!(
                    "conformance: {e:?}: expected a KnobConflict, got {:?}",
                    other.err()
                ),
            }
        }
    }
    let text = format!("{skip}");
    assert!(
        !text.trim_end().contains('\n'),
        "conformance: one line: {text:?}"
    );
    assert!(
        text.contains("completion_cover(Flat)") && text.contains("skip_spec_errfree_check(true)"),
        "conformance: both knobs named: {text}"
    );
}

/// Which branch Must completes **first** on [`branchy`] (the tester
/// establishes it — m9): `true` if the first complete Spec graph is the
/// `send^v` branch.
fn v_branch_first(v_on: bool) -> bool {
    let p = branchy(v_on);
    let v = vis(&["a", "c"]);
    let (_, specs) = families(&cfg(ConsType::Bag), &v, &p, &p);
    assert_eq!(
        specs.len(),
        3,
        "conformance: two graphs in the send^v branch, one in the other"
    );
    let g = &specs[0];
    let a = tid(g, "a");
    let e = Event::new(a, 2);
    assert!(
        matches!(g.label(e), LabelEnum::SendMsg(_)),
        "conformance: (a,2) is A's send"
    );
    is_visible(g, e, &v)
}

/// **Criterion 4, the mutation's target (round 02 m6, round 03 m3, m9; D4).**
/// Part 7's branch-dependent shape as Spec, in both orientations: refused in
/// both, naming `a`'s `send^i` at `(a,2)` — whichever branch Must completes
/// first. The completion order is established and pinned (measured): Must
/// completes the `n = true` branch first (its first execution takes `true`;
/// the probes' `nondet_values` order, `false` first, is a different order), so
/// the criterion's orientation `v_on = true` puts the `send^v` branch first —
/// the one a first-graph-only scan admits; `v_on = false` puts the `send^i`
/// graph first, refused even by that scan.
#[test]
fn c04_the_branch_dependent_spec_is_refused_in_both_orientations() {
    assert!(
        v_branch_first(true),
        "conformance: v_on = true: the send^v branch completes first"
    );
    assert!(
        !v_branch_first(false),
        "conformance: v_on = false: the send^i branch completes first"
    );
    let v = vis(&["a", "c"]);
    for v_on in [true, false] {
        let p = branchy(v_on);
        let (_, specs) = families(&cfg(ConsType::Bag), &v, &p, &p);
        let g = specs
            .iter()
            .find(|g| !is_visible(g, Event::new(tid(g, "a"), 2), &v))
            .expect("conformance: the send^i graph");
        let pos = Event::new(tid(g, "a"), 2).to_string();
        let want = ConfError::SpecNotCommunicationFlat {
            thread: "a".to_string(),
            pos,
        };
        for e in [
            Eng::CFirst,
            Eng::Gated(GatedMode::Exhaustive, GatePolicy::Always),
        ] {
            let r = verify(
                cc(
                    e,
                    cfg(ConsType::Bag),
                    &v,
                    Selector::Ltr,
                    CompletionCover::Flat,
                ),
                &p,
                &p,
            );
            assert_eq!(
                r.err(),
                Some(want.clone()),
                "conformance: v_on = {v_on}, {e:?}"
            );
        }
    }
}

// =========================================================================
// Criterion 5 — exactness against the sweep (D5)
// =========================================================================

/// D5's expectation for a registry pair, by name: `Some(true)` flat,
/// `Some(false)` not, `None` decided by [`independent_scan`] (the corpus).
fn c05_expected(name: &str) -> Option<bool> {
    const FLAT: [&str; 13] = [
        "ex:cone",
        "relay/paper",
        "ex:sched",
        "ex:restart",
        "ex:rebuild",
        "traces/self",
        "blocking/apparatus",
        "blocking/cfirst",
        "reset-pair",
        "forward-pop",
        "a27",
        "R1",
        "R2",
    ];
    const NOT_FLAT: [&str; 3] = ["relay/apparatus", "relay/paper/rev", "ex:nogate"];
    if name.starts_with("ex:naive/")
        || name.starts_with("mixed/server/")
        || name.starts_with("mixed/corpus/")
    {
        return Some(true);
    }
    if name.starts_with("ndk") || name.starts_with("2pc/") || name == "mixed/serverblock" {
        // serverblock's Spec is `server_spec`: flat. Listed apart below.
        return Some(!name.starts_with("ndk") && !name.starts_with("2pc/"));
    }
    if name == "mixed/branch" || name == "mixed/cut" {
        return Some(false);
    }
    if FLAT.contains(&name) {
        return Some(true);
    }
    if NOT_FLAT.contains(&name) {
        return Some(false);
    }
    if name.starts_with("corpus/") {
        return None;
    }
    panic!("conformance: criterion 5 has no expectation for `{name}`")
}

/// The tester's own scan, independent of `precheck::eligibility`: every
/// `SendMsg`/`RecvMsg` of every complete Spec graph the stateful engine's
/// enumeration keeps is visible under Part 7's `is_visible`.
fn independent_scan(f: &Fixture) -> (bool, usize) {
    let (_, specs) = families(&f.config, &f.visible, &f.implementation, &f.specification);
    let flat = specs.iter().all(|g| {
        g.thread_ids().into_iter().all(|t| {
            (0..g.thread_size(t) as u32).all(|i| {
                let e = Event::new(t, i);
                !matches!(g.label(e), LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_))
                    || is_visible(g, e, &f.visible)
            })
        })
    });
    (flat, specs.len())
}

/// Every `W` entry of a `Flat` run is a complete member of `Graphs(Spec)` (its
/// key is in the oracle's Spec family); with `must_cover` (no gate admits:
/// complete-first, gated `Never`) every entry is a `FlatCover` admission and
/// covers some completion of the run. Gate admissions (gated `Always`) need
/// not cover a completion — `|W|` includes them (F6).
fn w_entries_ok(
    entries: &[crate::conformance::witness::Witness],
    specs: &BTreeSet<String>,
    impls: &[ExecutionGraph],
    v: &[String],
    must_cover: bool,
    what: &str,
) -> Vec<String> {
    let mut bad = Vec::new();
    let sums: Vec<Summary> = impls.iter().map(|g| summary(g, v)).collect();
    for (i, w) in entries.iter().enumerate() {
        if CompleteExecution::try_finished(w.graph()).is_none() {
            bad.push(format!(
                "{what}: W[{i}] is not complete (flat::admit's expect would fire)"
            ));
        }
        if !specs.contains(&canon_key(w.graph(), v)) {
            bad.push(format!("{what}: W[{i}] is not a graph of Spec"));
        }
        if must_cover && !sums.iter().any(|s| covered(s, w.summary())) {
            bad.push(format!("{what}: W[{i}] covers no completion"));
        }
    }
    bad
}

/// Criterion 5 on one fixture: the eligibility decision against D5 (or the
/// independent scan), and on a flat pair, per selector, complete-first and
/// gated exhaustive (`Never`, `Always`) under `Flat` against `Sweep` — the
/// same verdict class and report-key set — plus `W`'s entries and F6's
/// identity. Returns failures and whether the pair was flat.
fn c05_one(f: &Fixture) -> (Vec<String>, bool) {
    let mut bad = Vec::new();
    let elig = eligibility_of(
        f.config.clone(),
        &f.visible,
        &f.implementation,
        &f.specification,
    );
    let decided = match &elig {
        Ok(e) => {
            if !e.communication_flat || e.first_invisible.is_some() {
                bad.push(format!("{}: an Ok run with {e:?}", f.name));
            }
            true
        }
        Err(ConfError::SpecNotCommunicationFlat { .. }) => false,
        Err(e) => {
            bad.push(format!("{}: {e:?}", f.name));
            return (bad, false);
        }
    };
    let expected = match c05_expected(&f.name) {
        Some(b) => b,
        None => independent_scan(f).0,
    };
    if decided != expected {
        bad.push(format!(
            "{}: F1 decided {decided}, the list says {expected}",
            f.name
        ));
    }
    if !decided {
        return (bad, false);
    }
    let (imps, specs) = families(&f.config, &f.visible, &f.implementation, &f.specification);
    let spec_keys = keys(&specs, &f.visible);
    if let Ok(e) = &elig {
        if e.spec_graphs_scanned != specs.len() {
            bad.push(format!(
                "{}: scanned {} graphs, the oracle has {}",
                f.name,
                e.spec_graphs_scanned,
                specs.len()
            ));
        }
    }
    for s in SELECTORS {
        let c = |e: Eng, cover| cc(e, f.config.clone(), &f.visible, s, cover);
        let what = format!("{} {s:?}", f.name);
        let of = cfirst_raw(
            &c(Eng::CFirst, CompletionCover::Flat),
            &f.implementation,
            &f.specification,
        );
        let os = cfirst_raw(
            &c(Eng::CFirst, CompletionCover::Sweep),
            &f.implementation,
            &f.specification,
        );
        if cfirst_keys(&of, &f.visible) != cfirst_keys(&os, &f.visible) {
            bad.push(format!("{what} cfirst: report keys differ Flat/Sweep"));
        }
        bad.extend(identity_cfirst(&of.counters, &format!("{what} cfirst")));
        bad.extend(w_entries_ok(
            of.witnesses.entries(),
            &spec_keys,
            &imps,
            &f.visible,
            true,
            &format!("{what} cfirst"),
        ));
        for p in [GatePolicy::Never, GatePolicy::Always] {
            let e = Eng::Gated(GatedMode::Exhaustive, p);
            let gf = gated_raw(
                &c(e, CompletionCover::Flat),
                &f.implementation,
                &f.specification,
            );
            let gs = gated_raw(
                &c(e, CompletionCover::Sweep),
                &f.implementation,
                &f.specification,
            );
            if gated_keys(&gf, &f.visible) != gated_keys(&gs, &f.visible)
                || gf.reports.len() != gs.reports.len()
            {
                bad.push(format!("{what} gated {p:?}: report keys differ Flat/Sweep"));
            }
            bad.extend(identity_gated(&gf.counters, &format!("{what} gated {p:?}")));
            bad.extend(w_entries_ok(
                gf.witnesses.entries(),
                &spec_keys,
                &imps,
                &f.visible,
                p == GatePolicy::Never,
                &format!("{what} gated {p:?}"),
            ));
        }
    }
    (bad, true)
}

fn c05_run(fixtures: &[Fixture]) -> (Vec<String>, Vec<String>) {
    let mut bad = Vec::new();
    let mut flat = Vec::new();
    for f in fixtures {
        let (b, is_flat) = c05_one(f);
        bad.extend(b);
        if is_flat {
            flat.push(f.name.clone());
        }
    }
    (bad, flat)
}

/// **Criterion 5 (round 01 m2, m10; D5), the default subset.** `ex:naive` both
/// encodings and E2 at `k = 2, 3`, every paper/closed-part pair, the `ndk`
/// pairs, 2PC at `N = 2`, the corpus at 3 per mode, and Part 7's mixed
/// benchmarks (outside Part 6's registry; added). Part 6 labels no pair
/// F79-breaking (`grid_tests.rs::label_of`), so none is excluded.
#[test]
fn c05_flat_equals_sweep_on_the_default_subset() {
    let mut fixtures = registry(2..=3, 2, 3);
    fixtures.extend(mixed_fixtures());
    let (bad, flat) = c05_run(&fixtures);
    assert!(
        flat.len() >= 30,
        "conformance: the flat subset is too small: {flat:?}"
    );
    fail_if(bad, "criterion 5");
}

/// **Criterion 5, the full registry** (`ex:naive` `k ≤ 4`, 2PC `N ≤ 3`, the
/// corpus at 10 per mode). Ignored: measured runtime in the report.
#[test]
#[ignore]
fn c05_flat_equals_sweep_on_the_full_registry() {
    let mut fixtures = registry(2..=4, 3, 10);
    fixtures.extend(mixed_fixtures());
    let (bad, _) = c05_run(&fixtures);
    fail_if(bad, "criterion 5 (full)");
}

// =========================================================================
// Criterion 6 — the cost (F7; D6)
// =========================================================================

/// **Criterion 6(a) (F7; D6).** `ex:naive` `Impl_k` against `Spec_k`,
/// complete-first `Flat`, `stop_at_first_report`, `k = 2, 3, 4`: encoding 1
/// `calls 1, visits 1, send_kills 1, md 1`; encoding 2 `visits = md = k + 1`;
/// every other count 0. Beside it, on the same completion: the sweep's
/// `sweep_sizes = [k!]` and the enumerator's first `Cover` (unlimited,
/// memo off / on: `R_k` = 5/16/65, `1 + k·2^{k−1}` = 5/13/33).
#[test]
fn c06a_naive_first_completion() {
    let mut bad = Vec::new();
    for k in [2usize, 3, 4] {
        for c_first in [true, false] {
            let (imp, spec) = naive_pair(k, c_first);
            let v = naive_visible(k);
            let what = format!("k={k} c_first={c_first}");
            let c = builder(
                Eng::CFirst,
                cfg(ConsType::Bag),
                &v,
                Selector::Ltr,
                CompletionCover::Flat,
            )
            .stop_at_first_report(true)
            .build()
            .expect("conformance: in scope");
            let r = verify(c, &imp, &spec);
            if class(&r) != "reported:1" {
                bad.push(format!("{what}: {}", class(&r)));
                continue;
            }
            let d = if c_first { 1 } else { k + 1 };
            let want = F {
                calls: 1,
                visits: d,
                sk: 1,
                md: d,
                ..F::default()
            };
            if flat_of(outcome(&r)) != want {
                bad.push(format!(
                    "{what}: {:?}, expected {want:?}",
                    flat_of(outcome(&r))
                ));
            }
            bad.extend(identity(outcome(&r), &what));
            // The sweep beside it.
            let c = builder(
                Eng::CFirst,
                cfg(ConsType::Bag),
                &v,
                Selector::Ltr,
                CompletionCover::Sweep,
            )
            .stop_at_first_report(true)
            .build()
            .expect("conformance: in scope");
            let r = verify(c, &imp, &spec);
            let sizes = outcome(&r).cfirst_counters().map(|c| c.sweep_sizes.clone());
            if sizes != Some(vec![factorial(k)]) {
                bad.push(format!(
                    "{what}: sweep_sizes {sizes:?}, expected [{}]",
                    factorial(k)
                ));
            }
            // The enumerator beside it.
            for (memo, want) in [(false, [5usize, 16, 65]), (true, [5, 13, 33])] {
                let f = crate::conformance::grid::naive_fixture(k, if c_first { 1 } else { 2 });
                let g = GridConfig::new(GridEngine::Enumerator)
                    .stop(true)
                    .memo(memo)
                    .budget(Budget::Unlimited);
                let GridEnd::Ok(r) = run_grid(&f, &g, None) else {
                    panic!("conformance: the enumerator run ended badly")
                };
                let GridRaw::Enumerator(o) = &r.raw else {
                    unreachable!("conformance: enumerator")
                };
                // The run stops at its first report, the `Cover` at `C`'s send
                // gate: encoding 1 — `C`'s send is the first gate, `NoCover` in
                // one call, no rebuild; encoding 2 — the seed fails in one call
                // and the rebuild pays `R_k` (`P4-ENUMERATOR` criterion 7's
                // derivation, cited by F7).
                let last = o.counters.per_cover.last().map(|p| {
                    (
                        p.spec_visit_calls,
                        p.spec_visit_calls_extend,
                        p.spec_visit_calls_rebuild,
                    )
                });
                let ok = match last {
                    Some((calls, _, rebuild)) if c_first => calls == 1 && rebuild == 0,
                    Some((_, _, rebuild)) => rebuild == want[k - 2],
                    None => false,
                };
                if !ok || o.reports.len() != 1 {
                    bad.push(format!(
                        "{what}: enumerator memo={memo}: last Cover (calls, extend, rebuild) {last:?}, \
                         R_k {}, reports {}",
                        want[k - 2],
                        o.reports.len()
                    ));
                }
            }
        }
    }
    fail_if(bad, "criterion 6(a)");
}

/// **Criterion 6(b) (F7, round 02 M2; D6).** `naive_d(k, 1, enc, None)`
/// against itself, `k = 2, 3`, both encodings, complete-first exhaustive and
/// gated `Exhaustive`/`Never`: run totals `calls = witnesses = k!`, `visits =
/// k!(2k+2)`, `rec = k!·k`, `src = k!·k(k+3)/4` (5, 27), every kill 0, no
/// `nd`, `md = 2k+2`; `|W| = k!`; wall time present.
#[test]
fn c06b_naive_self_conformance_run_totals() {
    let mut bad = Vec::new();
    for k in [2usize, 3] {
        let n = factorial(k);
        let want = F {
            calls: n,
            visits: n * (2 * k + 2),
            src: n * k * (k + 3) / 4,
            rec: n * k,
            w: n,
            md: 2 * k + 2,
            ..F::default()
        };
        for c_first in [true, false] {
            let p = naive_self(k, c_first);
            for s in SELECTORS {
                for e in [
                    Eng::CFirst,
                    Eng::Gated(GatedMode::Exhaustive, GatePolicy::Never),
                ] {
                    let what = format!("k={k} c_first={c_first} {e:?} {s:?}");
                    let r = verify(
                        cc(
                            e,
                            cfg(ConsType::Bag),
                            &naive_visible(k),
                            s,
                            CompletionCover::Flat,
                        ),
                        &p,
                        &p,
                    );
                    if class(&r) != "conforms" {
                        bad.push(format!("{what}: {}", class(&r)));
                        continue;
                    }
                    let o = outcome(&r);
                    if flat_of(o) != want {
                        bad.push(format!("{what}: {:?}, expected {want:?}", flat_of(o)));
                    }
                    let w = o
                        .cfirst_counters()
                        .map(|c| c.witnesses)
                        .or_else(|| o.gated_counters().map(|c| c.witnesses));
                    if w != Some(n) {
                        bad.push(format!("{what}: |W| {w:?}"));
                    }
                    bad.extend(identity(o, &what));
                }
            }
        }
    }
    fail_if(bad, "criterion 6(b)");
}

/// **F7's premise, measured (D6):** the 5 / 27 need `Offer::sources()`'s
/// order to be a function of the unread set. On `naive_self(3, ·)` the
/// per-completion option counts are the ranks of `π(i)`; summed per graph
/// they range over `[k, k(k+1)/2] = [3, 6]` and total 27 — measured by
/// calling `FlatCover` per Impl graph directly.
#[test]
fn c06b_per_completion_ranks() {
    for c_first in [true, false] {
        let p = naive_self(3, c_first);
        let v = naive_visible(3);
        let (imps, specs) = families(&cfg(ConsType::Bag), &v, &p, &p);
        assert_eq!(imps.len(), 6, "conformance: 3! Impl graphs");
        let ctx = flat::FlatCtx::new(&cfg(ConsType::Bag), &v, &p);
        let spec_keys = keys(&specs, &v);
        let mut per = Vec::new();
        for g in &imps {
            let (w, c) = flat::flat_cover(&ctx, g).expect("conformance: a valid input");
            let w = w.expect("conformance: self-conformance is covered");
            assert!(
                spec_keys.contains(&canon_key(w.graph(), &v)),
                "conformance: a Spec graph"
            );
            assert_eq!(
                canon_key(w.graph(), &v),
                canon_key(g, &v),
                "conformance: M_π = G_π"
            );
            per.push(c.source_branches);
        }
        per.sort_unstable();
        assert_eq!(per.iter().sum::<usize>(), 27, "conformance: total {per:?}");
        assert_eq!(
            per,
            vec![3, 4, 4, 5, 5, 6],
            "conformance: the rank sums {per:?}"
        );
    }
}

// =========================================================================
// Criterion 7 — the adapter is the only change (D7)
// =========================================================================

/// The gated figures criterion 7 requires identical, rendered for comparison
/// (everything but the completion sweeps, `flat`, and wall times).
fn gated_figures(c: &GatedCounters) -> String {
    format!(
        "gates {} inert {} skipped_replay {} skipped_certified {} declined {} c1_carried {} \
         carried_hits {} c1_cache {} gate_cache_hits {} c1_sweep {} gate_sweeps {} ok {} failing {} \
         budgeted {} aborted {} sizes {:?} certs {} resets {} pushed {} revisited {} certified {} \
         by_test {} impl {} probes {} hits {} cache_tests {} witnesses {} dups {} reports {}",
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
        c.gate_sweep_sizes,
        c.certificates_set,
        c.certificate_resets,
        c.states_pushed,
        c.certified_states_revisited,
        c.reports_certified,
        c.reports_by_completion_test,
        c.impl_graphs,
        c.completion_probes,
        c.completion_cache_hits,
        c.completion_cache_tests,
        c.witnesses,
        c.witness_duplicates,
        c.reports
    )
}

/// **Criterion 7 (round 01 M7; D7).** `naive_d(2, 1, enc, None)` against
/// itself, gated `Exhaustive`/`Never`, precheck on, every selector: every
/// completion a `W` miss, and the completion admissions **coincide** (each
/// `G_π` has exactly one covering Spec graph, `M_π = G_π`, so the sweep's
/// first and `FlatCover`'s first are the same canonical graph — asserted on
/// `W`'s keys) — hence every gated figure identical, the `W`-reading ones
/// included; `Sweep` pays two completion sweeps, `Flat` none. F6's
/// identity holds.
#[test]
fn c07_gated_figures_identical_at_k2() {
    let mut bad = Vec::new();
    let v = naive_visible(2);
    for c_first in [true, false] {
        let p = naive_self(2, c_first);
        for s in SELECTORS {
            let what = format!("c_first={c_first} {s:?}");
            let e = Eng::Gated(GatedMode::Exhaustive, GatePolicy::Never);
            let rf = verify(
                cc(e, cfg(ConsType::Bag), &v, s, CompletionCover::Flat),
                &p,
                &p,
            );
            let rs = verify(
                cc(e, cfg(ConsType::Bag), &v, s, CompletionCover::Sweep),
                &p,
                &p,
            );
            let (gf, gs) = (
                outcome(&rf).gated_counters().expect("conformance: gated"),
                outcome(&rs).gated_counters().expect("conformance: gated"),
            );
            if gated_figures(gf) != gated_figures(gs) {
                bad.push(format!(
                    "{what}:\n    Flat  {}\n    Sweep {}",
                    gated_figures(gf),
                    gated_figures(gs)
                ));
            }
            if gs.completion_sweeps != 2 || gf.completion_sweeps != 0 {
                bad.push(format!(
                    "{what}: completion sweeps {} / {}",
                    gf.completion_sweeps, gs.completion_sweeps
                ));
            }
            bad.extend(identity(outcome(&rf), &what));
            // The admissions, on the raw route.
            let wf = gated_raw(
                &cc(e, cfg(ConsType::Bag), &v, s, CompletionCover::Flat),
                &p,
                &p,
            );
            let ws = gated_raw(
                &cc(e, cfg(ConsType::Bag), &v, s, CompletionCover::Sweep),
                &p,
                &p,
            );
            let kf: Vec<String> = wf
                .witnesses
                .entries()
                .iter()
                .map(|w| canon_key(w.graph(), &v))
                .collect();
            let ks_: Vec<String> = ws
                .witnesses
                .entries()
                .iter()
                .map(|w| canon_key(w.graph(), &v))
                .collect();
            if kf != ks_ {
                bad.push(format!("{what}: the completion admissions do not coincide"));
            }
        }
    }
    fail_if(bad, "criterion 7");
}

/// **Criterion 7, M3 (L12).** `FlatCover` never runs on its caller's thread:
/// a `Must` installed as current on the calling thread is still current, the
/// same object, after a `flat_cover` call (`probe_from` would clear it).
#[test]
fn c07_must_current_is_unchanged_by_flat_cover() {
    let p = naive_self(2, true);
    let v = naive_visible(2);
    let (imps, _) = families(&cfg(ConsType::Bag), &v, &p, &p);
    let outer = Rc::new(std::cell::RefCell::new(Must::new(
        cfg(ConsType::Bag),
        false,
    )));
    Must::set_current(Some(Rc::clone(&outer)));
    let ctx = flat::FlatCtx::new(&cfg(ConsType::Bag), &v, &p);
    let r = flat::flat_cover(&ctx, &imps[0]);
    let after = Must::current();
    Must::set_current(None);
    assert!(
        r.expect("conformance: a valid input").0.is_some(),
        "conformance: covered"
    );
    assert!(
        after.is_some_and(|m| Rc::ptr_eq(&m, &outer)),
        "conformance: Must::current() changed across a FlatCover call"
    );
}

// =========================================================================
// Criterion 8 — rendering (D8)
// =========================================================================

/// **Criterion 8 (round 03 M1, round 04 M1, round 05 m1, round 06 n1; D8).**
/// Every `Flat` rendering is its `Sweep` rendering under criterion 8's
/// substitutions, byte for byte, once the `Flat`-only lines are removed — on
/// complete-first and gated, `Conforms` and `Reported`, exhaustive (certified
/// and by the completion test) and first-failure (at completion and at a
/// gate); the `Flat`-only lines are present exactly when `Flat`; `Sweep`
/// renderings contain no `FlatCover`; `Diagnostics::NotProduced` is the same
/// text under both covers.
#[test]
fn c08_every_flat_text_is_its_sweep_text_by_substitution() {
    let mut bad = Vec::new();
    let pairs: [(&str, Prog, Prog); 2] = [
        ("conforming", server_impl(true, 2), t7_spec(true, false)),
        ("violating", server_impl(true, 3), t7_spec(true, false)),
    ];
    for (name, imp, spec) in &pairs {
        for e in table_engines().into_iter().filter(|e| e.flat_capable()) {
            let what = format!("{name} {e:?}");
            let rf = verify(
                cc(
                    e,
                    cfg(ConsType::FIFO),
                    &ks(),
                    Selector::Ltr,
                    CompletionCover::Flat,
                ),
                imp,
                spec,
            );
            let rs = verify(
                cc(
                    e,
                    cfg(ConsType::FIFO),
                    &ks(),
                    Selector::Ltr,
                    CompletionCover::Sweep,
                ),
                imp,
                spec,
            );
            let (tf, ts) = (rendered(&rf), rendered(&rs));
            if ts.contains("FlatCover") || ts.contains("communication-flat") {
                bad.push(format!("{what}: a Sweep text names FlatCover"));
            }
            let (af, as_) = match (&rf, &rs) {
                (Ok(ConfVerdict::Conforms(a)), Ok(ConfVerdict::Conforms(b))) => {
                    (a.assumptions(), b.assumptions())
                }
                _ => (Vec::new(), Vec::new()),
            };
            if strip_flat_only(&tf, &af, &as_) != subst_sweep(&ts) {
                bad.push(format!(
                    "{what}: Flat != subst(Sweep)\n--- Flat ---\n{tf}\n--- subst(Sweep) ---\n{}",
                    subst_sweep(&ts)
                ));
            }
            for l in [
                "the specification is communication-flat: 2 graphs scanned",
                "FlatCover: ",
            ] {
                if !tf.lines().any(|x| x.starts_with(l)) {
                    bad.push(format!("{what}: missing `{l}`"));
                }
            }
            let block = tf.lines().any(|x| {
                x.starts_with("completion reports not raised under an absence certificate")
            });
            if block != name.starts_with("violating") {
                bad.push(format!("{what}: the Flat block present = {block}"));
            }
            if let (Ok(ConfVerdict::Reported(a)), Ok(ConfVerdict::Reported(b))) = (&rf, &rs) {
                for (x, y) in a.reports().iter().zip(b.reports()) {
                    if format!("{}", x.diagnostics()) != format!("{}", y.diagnostics()) {
                        bad.push(format!("{what}: NotProduced differs"));
                    }
                }
            }
        }
    }
    fail_if(bad, "criterion 8");
}

/// **Criterion 8, the cut and gate-site reports are never flagged (round 06
/// n2).** R2 with the early-error cut on, complete-first `Flat`: the cut
/// report's `certifies` line is `certifies_under`'s `VisibleError` text, and
/// the whole rendering is the `Sweep` one by substitution.
#[test]
fn c08_a_cut_report_keeps_its_sweep_text() {
    let (imp, spec) = (
        crate::conformance::grid::r2(true),
        crate::conformance::grid::r2(false),
    );
    let v = vis(&["a", "b"]);
    let mk = |cover| {
        builder(Eng::CFirst, cfg(ConsType::Bag), &v, Selector::Ltr, cover)
            .early_error_cut(true)
            .build()
            .expect("conformance: in scope")
    };
    let rf = verify(mk(CompletionCover::Flat), &imp, &spec);
    let rs = verify(mk(CompletionCover::Sweep), &imp, &spec);
    assert_eq!(class(&rf), class(&rs), "conformance: R2 cut");
    let o = outcome(&rf);
    let cut = o
        .reports()
        .iter()
        .find(|r| r.tag() == ReportTag::VisibleError)
        .expect("conformance: a cut report");
    let line = format!(
        "  certifies (VisibleError): {}",
        ReportTag::VisibleError.certifies_under(Engine::CompleteFirst)
    );
    assert!(
        format!("{cut}").lines().any(|l| l == line),
        "conformance: the cut report's text:\n{cut}"
    );
    assert_eq!(
        strip_flat_only(&rendered(&rf), &[], &[]),
        subst_sweep(&rendered(&rs)),
        "conformance: substitution"
    );
}

/// **Criterion 8, refusals.** A `SpecNotCommunicationFlat` renders the
/// thread and the position; a `KnobConflict` is one line naming both knobs.
#[test]
fn c08_refusal_renderings() {
    let p = server_impl(true, 2);
    let (thread, pos) = d_receive(&p);
    let r = verify(
        cc(
            Eng::CFirst,
            cfg(ConsType::FIFO),
            &ks(),
            Selector::Ltr,
            CompletionCover::Flat,
        ),
        &p,
        &p,
    );
    let t = rendered(&r);
    assert!(
        t.contains(&format!("`{thread}`")) && t.contains(&pos),
        "conformance: {t}"
    );
    assert!(t.starts_with("conformance: "), "conformance: {t}");
    let c = builder(
        Eng::Stateful,
        cfg(ConsType::FIFO),
        &ks(),
        Selector::Ltr,
        CompletionCover::Flat,
    )
    .build()
    .expect("conformance: in scope");
    let t = rendered(&verify(c, &p, &p));
    assert!(!t.trim_end().contains('\n'), "conformance: one line: {t}");
    assert!(
        t.contains("completion_cover(Flat)") && t.contains("Stateful"),
        "conformance: {t}"
    );
}

/// **Criterion 8, every `Flat` verdict renders the eligibility line and the
/// counters** — including an `Inconclusive` one (an outer run bounded by
/// `max_iterations`): "A `Flat` run's `ConfVerdict` renders the eligibility
/// line … and `FlatCounters` under the counters". `naive_self(2)`,
/// complete-first `Flat`, `max_iterations = Some(1)`: the verdict is
/// `Inconclusive` and its rendering carries both lines. Gate 3's T1 (the arm
/// did not call `render_flat`); fixed by the lead at gate 4 round 01, so this
/// guards the fix in the default suite.
#[test]
fn c08_an_inconclusive_flat_verdict_renders_the_flat_block() {
    let p = naive_self(2, true);
    let mut config = cfg(ConsType::Bag);
    config.max_iterations = Some(1);
    let r = verify(
        cc(
            Eng::CFirst,
            config,
            &naive_visible(2),
            Selector::Ltr,
            CompletionCover::Flat,
        ),
        &p,
        &p,
    );
    assert_eq!(
        class(&r),
        "inconclusive",
        "conformance: a bounded outer run"
    );
    assert!(outcome(&r).flat_counters().is_some(), "conformance: F6");
    let t = rendered(&r);
    assert!(
        t.lines()
            .any(|l| l.starts_with("the specification is communication-flat: ")),
        "conformance: no eligibility line in an Inconclusive Flat verdict:\n{t}"
    );
    assert!(
        t.lines().any(|l| l.starts_with("FlatCover: ")),
        "conformance: no FlatCover counters in an Inconclusive Flat verdict:\n{t}"
    );
}

// =========================================================================
// Criterion 9 — the grid (D9)
// =========================================================================

/// **Criterion 9, the refusals (round 02 m3; D9).** `run_grid` refuses `Flat`
/// with `precheck = false` on either sweeping engine, and with the
/// enumerator, the stateful engine or `Verify` whatever the precheck, as
/// `GridEnd::Panicked` with a `refused:` payload — before any thread runs a
/// program (the fixture's programs panic if run).
#[test]
fn c09_run_grid_refuses_flat_outside_its_arm() {
    let boom: Prog = prog(|| panic!("conformance: a refused grid run executed a program"));
    let f = crate::conformance::grid::mixed_fixture(
        "refusal-probe",
        "flat_tests.rs (tester)",
        cfg(ConsType::Bag),
        vis(&["a"]),
        Arc::clone(&boom),
        boom,
    );
    let mut cases = Vec::new();
    for e in [GridEngine::CompleteFirst, GridEngine::Gated] {
        cases.push(
            GridConfig::new(e)
                .cover(CompletionCover::Flat)
                .precheck(false),
        );
    }
    for e in [
        GridEngine::Enumerator,
        GridEngine::Stateful,
        GridEngine::Verify,
    ] {
        for pc in [false, true] {
            cases.push(GridConfig::new(e).cover(CompletionCover::Flat).precheck(pc));
        }
    }
    for c in cases {
        match run_grid(&f, &c, None) {
            GridEnd::Panicked {
                payload, config, ..
            } => {
                assert!(
                    payload.starts_with("refused: "),
                    "conformance: {}: {payload}",
                    c.label()
                );
                assert_eq!(config, c, "conformance: the config is carried");
            }
            other => panic!("conformance: {} not refused: {other:?}", c.label()),
        }
    }
}

/// The verdict of a grid `Verdict` run as (class, reports as (tag, gate,
/// graph dump)), for Flat/Sweep comparison on the rendered route.
fn verdict_shape(
    r: &crate::conformance::grid::GridResult,
) -> (String, Vec<(ReportTag, ReportGate, String)>) {
    let GridRaw::Verdict(v) = &r.raw else {
        panic!("conformance: the precheck arm returns a verdict")
    };
    let reps = match v {
        Ok(verdict) => verdict
            .outcome()
            .reports()
            .iter()
            .map(|x| (x.tag(), x.gate(), x.graph_dump().to_string()))
            .collect(),
        Err(_) => Vec::new(),
    };
    (class(v), reps)
}

/// Criterion 9 on a fixture list: the `Flat` arm (precheck on) of
/// complete-first and gated exhaustive (`Never`, `Always`) per selector
/// against the same arm under `Sweep`: on the flat subset (decided by the
/// `Flat` run's `FlatEligibility`) the same verdict and report set (Part 6
/// criteria 2–3); on a refused pair the row carries `communication_flat =
/// false`, no `thread_flat`, and `refused_at` from the error. Rows go to
/// `rows`.
fn c09_run(fixtures: &[Fixture], rows: &mut Vec<Row>) -> (Vec<String>, usize) {
    let mut bad = Vec::new();
    let mut flat_runs = 0;
    for f in fixtures {
        for s in SELECTORS {
            for (e, p) in [
                (GridEngine::CompleteFirst, GatePolicy::Always),
                (GridEngine::Gated, GatePolicy::Never),
                (GridEngine::Gated, GatePolicy::Always),
            ] {
                let base = GridConfig::new(e)
                    .gated(GatedMode::Exhaustive, p)
                    .selector(s)
                    .precheck(true);
                let ef = run_grid(f, &base.clone().cover(CompletionCover::Flat), None);
                let es = run_grid(f, &base.clone().cover(CompletionCover::Sweep), None);
                let what = format!("{} {}", f.name, base.label());
                let row = row_of_end(&ef);
                rows.push(row.clone());
                let (GridEnd::Ok(rf), GridEnd::Ok(rs)) = (&ef, &es) else {
                    bad.push(format!("{what}: a run did not complete"));
                    continue;
                };
                let col = |k: &str| row.iter().find(|(c, _)| *c == k).map(|(_, v)| v.clone());
                match &rf.raw {
                    GridRaw::Verdict(Ok(v)) => {
                        let o = v.outcome();
                        let e = o.flat_eligibility().expect("conformance: Some under Flat");
                        if !e.communication_flat {
                            bad.push(format!("{what}: a verdict on an ineligible Spec"));
                        }
                        if verdict_shape(rf) != verdict_shape(rs) {
                            bad.push(format!("{what}: Flat and Sweep differ"));
                        }
                        bad.extend(identity(o, &what));
                        if col("communication_flat").as_deref() != Some("true")
                            || col("flat_calls").is_none()
                        {
                            bad.push(format!("{what}: the row lacks the flat columns"));
                        }
                        flat_runs += 1;
                    }
                    GridRaw::Verdict(Err(ConfError::SpecNotCommunicationFlat { thread, pos })) => {
                        if col("communication_flat").as_deref() != Some("false")
                            || col("refused_at") != Some(format!("{thread} @ {pos}"))
                            || col("thread_flat").is_some()
                        {
                            bad.push(format!("{what}: the refusal row {row:?}"));
                        }
                    }
                    other => bad.push(format!("{what}: {other:?}")),
                }
            }
        }
    }
    (bad, flat_runs)
}

/// **Criterion 9 (round 01 M8; D9), the default subset.** The paper pairs,
/// `ex:naive` `k = 2`, the mixed benchmarks.
#[test]
fn c09_the_grid_flat_arm_on_the_default_subset() {
    let mut fixtures = registry(2..=2, 2, 0);
    fixtures.retain(|f| !f.name.starts_with("2pc/"));
    fixtures.extend(mixed_fixtures());
    let mut rows = Vec::new();
    let (bad, flat_runs) = c09_run(&fixtures, &mut rows);
    assert!(flat_runs > 0, "conformance: no flat run");
    fail_if(bad, "criterion 9");
}

/// **Criterion 9, the tables** — one process, `P4_DIFF_TABLES` pointed at a
/// **new** file: criterion 9 over `registry(2..=4, 3, 10)` and the mixed
/// benchmarks, the `Flat` arm's rows with the `FlatCounters` columns and the
/// eligibility Booleans (refused rows with `refused_at`); then criterion
/// 6's runs as a table (wall time reported). Ignored: measured runtime in
/// the report.
#[test]
#[ignore]
fn c09_the_grid_tables() {
    let mut fixtures = registry(2..=4, 3, 10);
    fixtures.extend(mixed_fixtures());
    let mut rows = Vec::new();
    let (bad, _) = c09_run(&fixtures, &mut rows);
    let mut c06 = Vec::new();
    for k in [2usize, 3, 4] {
        for enc in [1u8, 2] {
            let f = crate::conformance::grid::naive_fixture(k, enc);
            let g = GridConfig::new(GridEngine::CompleteFirst)
                .precheck(true)
                .stop(true)
                .cover(CompletionCover::Flat);
            c06.push(row_of_end(&run_grid(&f, &g, None)));
        }
    }
    for k in [2usize, 3] {
        for c_first in [true, false] {
            let p = naive_self(k, c_first);
            let mut f = crate::conformance::grid::naive_fixture(k, if c_first { 1 } else { 2 });
            f.name = format!("naive_self/k{k}/enc{}", if c_first { 1 } else { 2 });
            f.implementation = Arc::clone(&p);
            f.specification = p;
            for g in [
                GridConfig::new(GridEngine::CompleteFirst)
                    .precheck(true)
                    .cover(CompletionCover::Flat),
                GridConfig::new(GridEngine::Gated)
                    .gated(GatedMode::Exhaustive, GatePolicy::Never)
                    .precheck(true)
                    .cover(CompletionCover::Flat),
            ] {
                c06.push(row_of_end(&run_grid(&f, &g, None)));
            }
        }
    }
    if std::env::var_os("P4_DIFF_TABLES").is_some() {
        let mut t = Tables::open();
        t.table(
            "P4-FLAT criterion 9: the grid's Flat arm (precheck on), exhaustive, every selector",
            &rows,
        );
        t.table(
            "P4-FLAT criterion 6: the cost, Flat arm (wall time in flat_wall_time_ms)",
            &c06,
        );
    }
    fail_if(bad, "criterion 9 (tables)");
}

// =========================================================================
// F3, the canonical order's tie-break (the tester's addition)
// =========================================================================

/// **F3 (D-tie).** The tie between `W`'s and `X`'s receives in the graph where
/// `X` reads ⊥ is broken by declared name, not by `ThreadId`: run totals
/// `calls 2, visits 10, src 5, rec 4, w 2, md 5` (a `ThreadId` or a reversed
/// tie-break gives `src 4`). The verdict is unaffected either way (exactness
/// holds for any total extension of `ord`).
#[test]
fn f3_the_tie_break_is_by_declared_name() {
    let p = tie();
    let v = vis(&["m", "w", "x"]);
    let (imps, _) = families(&cfg(ConsType::Bag), &v, &p, &p);
    assert_eq!(imps.len(), 2, "conformance: X reads ⊥ or 1");
    for e in [
        Eng::CFirst,
        Eng::Gated(GatedMode::Exhaustive, GatePolicy::Never),
    ] {
        for s in SELECTORS {
            let r = verify(
                cc(e, cfg(ConsType::Bag), &v, s, CompletionCover::Flat),
                &p,
                &p,
            );
            assert_eq!(class(&r), "conforms", "conformance: {e:?} {s:?}");
            assert_eq!(
                flat_of(outcome(&r)),
                F {
                    calls: 2,
                    visits: 10,
                    src: 5,
                    rec: 4,
                    w: 2,
                    md: 5,
                    ..F::default()
                },
                "conformance: {e:?} {s:?}"
            );
        }
    }
}

// =========================================================================
// The lead's findings
// =========================================================================

/// **L2.** Every `FlatCover` witness is a complete graph of Spec covering its
/// completion (`flat::admit`'s `expect` cannot fire: `try_finished` is `Some`
/// on every one), on every Impl graph of the conforming fixtures of this
/// file, by calling `flat_cover` directly.
#[test]
fn l02_every_witness_is_a_complete_covering_spec_graph() {
    let cases: Vec<(Config, Vec<String>, Prog, Prog)> = vec![
        (
            cfg(ConsType::FIFO),
            ks(),
            server_impl(true, 2),
            t7_spec(true, false),
        ),
        (cfg(ConsType::Bag), vis(&["a"]), self_send(), self_send()),
        (
            cfg(ConsType::Bag),
            vis(&["a", "b"]),
            nb_bottom(),
            nb_bottom(),
        ),
        (
            cfg(ConsType::Bag),
            vis(&["a", "b"]),
            blocked_b(true),
            blocked_b(true),
        ),
        (cfg(ConsType::Bag), vis(&["m", "w", "x"]), tie(), tie()),
        (
            cfg(ConsType::Bag),
            naive_visible(3),
            naive_self(3, false),
            naive_self(3, false),
        ),
    ];
    for (config, v, imp, spec) in cases {
        let (imps, specs) = families(&config, &v, &imp, &spec);
        let spec_keys = keys(&specs, &v);
        let ctx = flat::FlatCtx::new(&config, &v, &spec);
        for g in &imps {
            let (w, c) = flat::flat_cover(&ctx, g).expect("conformance: a valid input");
            let w = w.expect("conformance: a conforming pair's completion is covered");
            assert_eq!(c.calls, 1, "conformance: calls = 1 per call");
            assert_eq!(c.witnesses, 1, "conformance: witnesses = 1 on a Some");
            assert!(
                CompleteExecution::try_finished(w.graph()).is_some(),
                "conformance: complete"
            );
            assert!(
                spec_keys.contains(&canon_key(w.graph(), &v)),
                "conformance: a graph of Spec"
            );
            assert!(
                covered(&summary(g, &v), w.summary()),
                "conformance: covers its completion"
            );
            let own = summary(w.graph(), &v);
            assert!(
                covered(&own, w.summary()) && covered(w.summary(), &own),
                "conformance: the summary is the graph's"
            );
            let mut cache = crate::conformance::witness::WitnessCache::new(v.clone());
            assert_eq!(
                flat::admit(&mut cache, w),
                Ok(true),
                "conformance: admitted"
            );
            assert_eq!(cache.len(), 1, "conformance: |W| = 1");
        }
    }
}

/// **F4's defence (the panic test; L5).** `flat_cover` on a Spec that is not
/// communication-flat panics naming the invisible offer — `relay/paper/rev`:
/// Impl `p1_direct`, Spec `p2_relay`; `main`'s send to the undeclared relay
/// `r` follows `G₁` (`⟨snd,1⟩`, the destination is not observed), and then
/// `r`'s receive is offered — through
/// `flat_cover` directly and through `cfirst::run_with`/`gated::run_with`
/// under `Flat` (no precheck: the test route F4 names).
#[test]
fn l05_the_defence_panics_naming_the_invisible_offer() {
    let f = paper_fixtures()
        .into_iter()
        .find(|f| f.name == "relay/paper/rev")
        .expect("conformance: the relay pair");
    let (imps, _) = families(&f.config, &f.visible, &f.implementation, &f.implementation);
    let ctx = flat::FlatCtx::new(&f.config, &f.visible, &f.specification);
    let msg =
        panic_of(|| flat::flat_cover(&ctx, &imps[0])).expect("conformance: the defence fires");
    assert!(
        msg.contains("not communication-flat") && msg.contains("offers an invisible"),
        "conformance: {msg}"
    );
    for e in [
        Eng::CFirst,
        Eng::Gated(GatedMode::Exhaustive, GatePolicy::Never),
    ] {
        let c = cc(
            e,
            f.config.clone(),
            &f.visible,
            Selector::Ltr,
            CompletionCover::Flat,
        );
        let m = panic_of(|| match e {
            Eng::CFirst => {
                let _ = cfirst::run_with(&c, &f.implementation, &f.specification, false);
            }
            _ => {
                let _ = gated::run_with(&c, &f.implementation, &f.specification, false);
            }
        })
        .unwrap_or_else(|| panic!("conformance: {e:?}: no panic"));
        assert!(
            m.contains("not communication-flat"),
            "conformance: {e:?}: {m}"
        );
    }
}

/// **L9.** `communication_flat = false` never comes with `first_invisible =
/// None`, and `first_invisible` is the first invisible send or receive in
/// scan order — checked on `precheck::eligibility` directly over the kept
/// Spec graphs of every paper and mixed fixture, against the tester's own
/// scan.
#[test]
fn l09_eligibility_names_the_first_invisible_operation() {
    let mut fixtures = paper_fixtures();
    fixtures.extend(mixed_fixtures());
    fixtures.extend(ndk_fixtures().into_iter().take(1));
    fixtures.extend(two_pc_fixtures(2).into_iter().take(1));
    fixtures.extend(corpus_fixtures(7, 2));
    for f in &fixtures {
        let (_, specs) = families(&f.config, &f.visible, &f.implementation, &f.specification);
        let e = precheck::eligibility(&specs, &f.visible);
        let mut first = None;
        'scan: for g in &specs {
            for t in g.thread_ids() {
                for i in 0..g.thread_size(t) as u32 {
                    let ev = Event::new(t, i);
                    if matches!(g.label(ev), LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_))
                        && !is_visible(g, ev, &f.visible)
                    {
                        let name = g
                            .get_thread_tclab(t)
                            .name()
                            .clone()
                            .unwrap_or_else(|| t.to_string());
                        first = Some((name, ev.to_string()));
                        break 'scan;
                    }
                }
            }
        }
        assert_eq!(
            e.communication_flat,
            first.is_none(),
            "conformance: {}",
            f.name
        );
        assert_eq!(e.first_invisible, first, "conformance: {}", f.name);
        assert_eq!(
            e.spec_graphs_scanned,
            specs.len(),
            "conformance: {}",
            f.name
        );
    }
}

/// Test 7's Spec with `Z` replaced by `Z′: n := nondet(); [send(Y,9) if n
/// and send_first]; assume(¬n); [send(Y,9) if n and ¬send_first]` — `Z′`
/// undeclared, so its send is invisible; `Y`'s mailbox a channel nobody
/// reads.
fn t7_assume_spec(send_first: bool) -> Prog {
    prog(move || {
        let (tx_k, rx_k) = fifo();
        let (tx_s, rx_s) = fifo();
        let (tx_y, _rx_y) = fifo();
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            tx_k.send_msg(2);
        });
        let _z = named("z", move || {
            let n = crate::nondet();
            if n && send_first {
                tx_y.send_msg(9);
            }
            crate::assume!(!n);
            if n && !send_first {
                tx_y.send_msg(9);
            }
        });
    })
}

/// **F1, "every performable send and receive" (the tester's addition).** An
/// invisible send performed only on an execution that then fails an
/// `assume` is performable — it lies in a graph Must completes (blocked at
/// the `assume`, collected at the completion gate) — so the Spec is **not**
/// communication-flat and is refused naming `z`'s send; the same send placed
/// after the failing `assume` is never performed, and the Spec is flat.
#[test]
fn f1_a_send_before_a_failing_assume_is_performable() {
    let imp = server_impl(true, 2);
    let r = eligibility_of(cfg(ConsType::FIFO), &ks(), &imp, &t7_assume_spec(true));
    match r {
        Err(ConfError::SpecNotCommunicationFlat { thread, .. }) => {
            assert_eq!(
                thread, "z",
                "conformance: z's send is the first invisible operation"
            )
        }
        other => panic!("conformance: expected a refusal, got {other:?}"),
    }
    let e = eligibility_of(cfg(ConsType::FIFO), &ks(), &imp, &t7_assume_spec(false))
        .unwrap_or_else(|e| panic!("conformance: the unperformed send refused: {e:?}"));
    assert!(e.communication_flat && !e.thread_flat, "conformance: {e:?}");
    let v = verify(
        cc(
            Eng::CFirst,
            cfg(ConsType::FIFO),
            &ks(),
            Selector::Ltr,
            CompletionCover::Flat,
        ),
        &imp,
        &t7_assume_spec(false),
    );
    assert_eq!(
        class(&v),
        "conforms",
        "conformance: test 7 with the unperformed send"
    );
}
