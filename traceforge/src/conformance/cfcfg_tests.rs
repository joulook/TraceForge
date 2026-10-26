//! `P5-CFCFG` gate 3: the tester's tests (criteria `P5-CFCFG.md` rev 1.4 and
//! the landing errata E-CF-1–E-CF-6).
//!
//! Tester-owned (the module lines in `mod.rs` are registered as
//! `apptab_tests`'s). Every expected figure was derived **before** the lead's
//! diff was read: `plan/traceForge/log/dev/P5-CFCFG.derived.md` (sha256 in
//! `backlog/changes.md`). The committed-engine pins (criterion 2) are the
//! campaign store's rows (`8f19f0f`, whose complete-first, gated, witness,
//! canon and Must sources equal `6036802`'s). Tests are named by criterion; a
//! test that reproduces a defect of the lead's code is `t<N>_…`, `#[ignore]`d
//! with both values. Tests that spawn child processes are `#[ignore]`d and run
//! one per invocation (`--ignored --exact … --test-threads=1`), writing only
//! under the system temporary directory.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::conformance::canon::CanonicalGraph;
use crate::conformance::cfirst;
use crate::conformance::config::{Capacity, ConfBuilder, Engine};
use crate::conformance::eval::{
    all_fixtures, eval_row_of, header, parse_label, profile_name, read_rows, record_of,
    run_row_in_process, Driver, Probes, Refusal, RowMeta, RowSpec, RunKind, Series, Spec, Store,
    Tier, LABEL_PIN, SCHEMA_VERSION,
};
use crate::conformance::grid::{r1, ApptabPair, Fixture, GridConfig, GridEnd, GridEngine, Group};
use crate::conformance::grid_oracle::canon_key;
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::wobs;
use crate::conformance::sig::Summary;
use crate::conformance::stateful;
use crate::conformance::witness::WitnessCache;
use crate::conformance::ConfError;

macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

type Rec = BTreeMap<String, String>;

const PLAN: &str = "../../plan/traceForge/";
// `MIN-ENGINES` E1 (2026-10-26, tester re-pin at gate 3): X1's complete-first
// key (the precheck off) prints `Plain` in the selector field; the gated key
// keeps `Ltr`.
const X1_CF: &str = concat!(
    "CompleteFirst/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/",
    "instr=false/cut=false/cover=Sweep"
);
const X1_GATED: &str = "Gated/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep";
/// The five configurations, F6's order, as label fields.
const CFGS: [&str; 5] = ["w=0", "w=inf", "w=1", "w=8", "w=64"];

fn prof() -> &'static str {
    profile_name()
}

fn plan(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(PLAN).join(rel)
}

/// The tester's own spelling of a `CFCFG` label (F6): X1's complete-first
/// label then `w=<c>/quiet=true`.
fn cf_label(w: &str) -> String {
    format!("{X1_CF}/{w}/quiet=true")
}

fn cfg_of(label: &str) -> GridConfig {
    parse_label(label).unwrap_or_else(|| panic!("conformance: the label does not parse: {label}"))
}

fn fixture(name: &str) -> Fixture {
    all_fixtures()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("conformance: no fixture {name}"))
}

/// The stored record of one in-process run (the runner's own path).
fn run_rec(f: &Fixture, cfg: &GridConfig) -> Rec {
    let end = run_row_in_process(f, cfg, false);
    rec_of(&end, f, cfg)
}

fn rec_of(end: &GridEnd, f: &Fixture, cfg: &GridConfig) -> Rec {
    let rs = RowSpec {
        fixture: f.name.clone(),
        config: cfg.clone(),
        rep: 0,
        tier: Tier::default_tier(),
        run_kind: RunKind::Timed,
        family: String::new(),
        knobs: String::new(),
        k: [None; 4],
        variant: String::new(),
        twin_key: String::new(),
        series: None,
    };
    let row = eval_row_of(end, &RowMeta::of(&rs, prof(), "cfcfg-tests", ""));
    header()
        .iter()
        .map(|h| (*h).to_owned())
        .zip(record_of(&row))
        .collect()
}

fn n(r: &Rec, c: &str) -> u64 {
    r.get(c)
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| panic!("conformance: column {c} = {:?}", r.get(c)))
}

/// The raw complete-first outcome under a `GridConfig` (report keys).
fn cfirst_raw(f: &Fixture, cfg: &GridConfig) -> cfirst::CFirstOutcome {
    let cc = cfg.conf_config(f);
    cfirst::run_with(&cc, &f.implementation, &f.specification, false)
}

/// F1's invariants on one completed record of a capacity `w`; the problems.
fn invariants(r: &Rec, w: &str) -> Vec<String> {
    let mut bad = Vec::new();
    let k = format!("{} {w}", r["fixture"]);
    let mut check = |what: &str, ok: bool| {
        if !ok {
            bad.push(format!("{k}: {what}"));
        }
    };
    check("end_class ok", r["end_class"] == "ok");
    check(
        "cache_probes = impl_graphs",
        n(r, "cache_probes") == n(r, "impl_graphs"),
    );
    check(
        "cache_hits + sweeps = cache_probes",
        n(r, "cache_hits") + n(r, "sweeps") == n(r, "cache_probes"),
    );
    check(
        "witnesses = admissions − evictions",
        n(r, "witnesses") + n(r, "evictions") == n(r, "admissions"),
    );
    check(
        "readmissions ≤ admissions, ≤ evictions",
        n(r, "readmissions") <= n(r, "admissions") && n(r, "readmissions") <= n(r, "evictions"),
    );
    check(
        "admissions = sweeps_successful",
        n(r, "admissions") == n(r, "sweeps_successful") || w == "w=0",
    );
    check("witness_duplicates = 0", n(r, "witness_duplicates") == 0);
    match w {
        "w=0" => {
            check("w=0: cache_hits 0", n(r, "cache_hits") == 0);
            check("w=0: cache_tests 0", n(r, "cache_tests") == 0);
            check(
                "w=0: witnesses = admissions = evictions = readmissions = 0",
                n(r, "witnesses") + n(r, "admissions") + n(r, "evictions") + n(r, "readmissions")
                    == 0,
            );
            check(
                "w=0: sweeps = impl_graphs",
                n(r, "sweeps") == n(r, "impl_graphs"),
            );
        }
        "w=inf" | "default" => {
            check(
                "w=inf: evictions = readmissions = 0",
                n(r, "evictions") + n(r, "readmissions") == 0,
            );
        }
        other => {
            let cap: u64 = other.trim_start_matches("w=").parse().unwrap();
            check("w=<n>: witnesses ≤ n", n(r, "witnesses") <= cap);
        }
    }
    bad
}

// =========================================================================
// Criterion 1 — vanilla is Algorithm 1
// =========================================================================

/// C1 (F1 `Zero`): on `apps/a1/correct/spec/n2r2` (the unbounded run hits 48
/// times), `w=0` sweeps at every completion: `cache_hits = cache_tests = 0`,
/// `witnesses = admissions = evictions = readmissions = 0`, `sweeps =
/// cache_probes = impl_graphs = 64`, the same `reports` (0), `executions` (64)
/// and `max_paper_events` (30); `sweep_graphs(w=0) ≥ 1781` (I4: every
/// completion's sweep is paid).
#[test]
fn c01_zero_is_algorithm_1() {
    let f = fixture("apps/a1/correct/spec/n2r2");
    let z = run_rec(&f, &cfg_of(&cf_label("w=0")));
    let u = run_rec(&f, &cfg_of(&cf_label("w=inf")));
    let mut bad = invariants(&z, "w=0");
    bad.extend(invariants(&u, "w=inf"));
    note!(
        "c01: w=0 sweeps {} sweep_graphs {}; w=inf hits {} sweeps {}",
        z["sweeps"],
        z["sweep_graphs"],
        u["cache_hits"],
        u["sweeps"]
    );
    if n(&u, "cache_hits") < 1 {
        bad.push("the unbounded run must hit".to_owned());
    }
    for c in ["reports", "executions", "impl_graphs", "max_paper_events"] {
        if z[c] != u[c] {
            bad.push(format!("{c}: w=0 {} w=inf {}", z[c], u[c]));
        }
    }
    if (n(&z, "sweeps"), n(&z, "impl_graphs"), n(&z, "reports")) != (64, 64, 0)
        || n(&z, "sweep_graphs") < 1781
    {
        bad.push(format!(
            "w=0 figures {} {} {}",
            z["sweeps"], z["impl_graphs"], z["sweep_graphs"]
        ));
    }
    assert!(bad.is_empty(), "conformance: criterion 1: {bad:#?}");
}

// =========================================================================
// Criterion 2 — unbounded is today's engine
// =========================================================================

/// C2: with the defaults (`Unbounded`, `quiet = false`: the eleven-field
/// label, E-CF-1) every complete-first counter equals the committed engine's
/// on six registry pairs (derived.md §2, from campaign-1), and the gated
/// engine's counters on `apps/a1/correct/spec/n2r2` (`Exhaustive`/`Always`).
/// The same counters hold under `w=inf` with `quiet = true`.
#[test]
fn c02_unbounded_equals_the_committed_engine() {
    // fixture, exec=impl, reports, probes, hits, tests, sweeps, succ, fail, sweep_graphs, witnesses, max_paper_events
    let pins: [(&str, [u64; 11]); 6] = [
        (
            "apps/a1/correct/spec/n2r2",
            [64, 0, 64, 48, 528, 16, 16, 0, 1781, 16, 30],
        ),
        ("ex:naive/k2/enc1", [2, 2, 2, 0, 0, 2, 0, 2, 4, 0, 5]),
        ("synth/share/m2c1", [2, 0, 2, 1, 1, 1, 1, 0, 1, 1, 9]),
        ("synth/naive-self/k2enc1", [2, 0, 2, 0, 1, 2, 2, 0, 3, 2, 5]),
        ("R1", [1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1]),
        ("a27", [2, 2, 2, 0, 0, 2, 0, 2, 4, 0, 3]),
    ];
    let cols = [
        "executions",
        "reports",
        "cache_probes",
        "cache_hits",
        "cache_tests",
        "sweeps",
        "sweeps_successful",
        "sweeps_failing",
        "sweep_graphs",
        "witnesses",
        "max_paper_events",
    ];
    let mut bad = Vec::new();
    for (name, want) in pins {
        let f = fixture(name);
        for label in [X1_CF.to_owned(), cf_label("w=inf")] {
            let r = run_rec(&f, &cfg_of(&label));
            if r["key"].split('|').nth(1) != Some(label.as_str()) {
                bad.push(format!("{name}: key label {}", r["key"]));
            }
            for (c, w) in cols.iter().zip(want) {
                if n(&r, c) != w {
                    bad.push(format!("{name} {label}: {c} {} (pin {w})", r[*c]));
                }
            }
            if n(&r, "impl_graphs") != want[0] || n(&r, "cut_reports") != 0 {
                bad.push(format!("{name}: impl_graphs/cut_reports"));
            }
            bad.extend(invariants(&r, "w=inf"));
            if n(&r, "admissions") != want[9] {
                bad.push(format!(
                    "{name}: admissions {} = witnesses {}",
                    r["admissions"], want[9]
                ));
            }
        }
    }
    let f = fixture("apps/a1/correct/spec/n2r2");
    let g = run_rec(&f, &cfg_of(X1_GATED));
    for (c, w) in [
        ("gates", 235u64),
        ("gate_sweeps", 23),
        ("completion_probes", 64),
        ("completion_cache_hits", 64),
        ("completion_sweeps", 0),
        ("witnesses", 23),
        ("reports", 0),
        ("executions", 64),
    ] {
        if n(&g, c) != w {
            bad.push(format!("gated: {c} {} (pin {w})", g[c]));
        }
    }
    // The gated rows carry none of the five new columns.
    for c in [
        "admissions",
        "evictions",
        "readmissions",
        "wall_ms_at_first_report",
        "vmhwm_kb_at_first_report",
    ] {
        if !g[c].is_empty() {
            bad.push(format!("gated row carries {c} = {}", g[c]));
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 2: {bad:#?}");
}

// =========================================================================
// Criterion 3 — FIFO with re-admission
// =========================================================================

/// The complete Spec graphs of `synth/width/w8` (eight distinct graphs), from
/// the stateful engine's kept family.
fn width_spec_graphs() -> (Vec<crate::exec_graph::ExecutionGraph>, Vec<String>) {
    let f = fixture("synth/width/w8");
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
    assert_eq!(
        o.kept_spec_graphs.len(),
        8,
        "conformance: width(8)'s Spec graphs"
    );
    (o.kept_spec_graphs, f.visible)
}

fn admit(w: &mut WitnessCache, g: &crate::exec_graph::ExecutionGraph) -> bool {
    let exec = CompleteExecution::try_finished(g).expect("conformance: a complete graph");
    w.admit_from_sweep(exec).expect("conformance: admission")
}

fn summary(g: &crate::exec_graph::ExecutionGraph, visible: &[String]) -> Summary {
    let exec = CompleteExecution::try_finished(g).expect("conformance: a complete graph");
    let w = wobs(g, visible).expect("conformance: wobs");
    Summary::of(exec, &w, visible).expect("conformance: summary")
}

/// C3 (derived.md §3) on `WitnessCache::with_capacity(_, Bounded(2))`: admit a,
/// b, c (c evicts a); probe a misses; admit a (a re-admission, evicts b);
/// admit c refused as held — `len 2`, `admissions 4`, `evictions 2`,
/// `readmissions 1`, the held entries [c, a]; `Zero` admits nothing and its
/// probe tests nothing; `Unbounded` never evicts.
#[test]
fn c03_fifo_with_readmission() {
    let (gs, vis) = width_spec_graphs();
    let (a, b, c) = (&gs[0], &gs[1], &gs[2]);
    let mut w = WitnessCache::with_capacity(vis.clone(), Capacity::Bounded(2));
    let mut log = Vec::new();
    log.push(admit(&mut w, a));
    log.push(admit(&mut w, b));
    log.push(admit(&mut w, c));
    let (hit, tests) = w.probe_covered_counted(&summary(a, &vis));
    let a_misses = hit.is_none();
    log.push(admit(&mut w, a));
    log.push(admit(&mut w, c));
    let held: Vec<String> = w
        .entries()
        .iter()
        .map(|e| format!("{:?}", CanonicalGraph::of(e.graph(), &vis).unwrap()))
        .collect();
    let canon = |g| format!("{:?}", CanonicalGraph::of(g, &vis).unwrap());
    assert_eq!(
        log,
        vec![true, true, true, true, false],
        "conformance: admissions"
    );
    assert!(
        a_misses && tests == 2,
        "conformance: a misses after its eviction ({tests} tests)"
    );
    assert_eq!(
        (w.len(), w.admissions(), w.evictions(), w.readmissions()),
        (2, 4, 2, 1),
        "conformance: len, admissions, evictions, readmissions"
    );
    assert_eq!(held, vec![canon(c), canon(a)], "conformance: held [c, a]");
    // Zero.
    let mut z = WitnessCache::with_capacity(vis.clone(), Capacity::Zero);
    assert!(!admit(&mut z, a), "conformance: Zero admits nothing");
    let (hit, tests) = z.probe_covered_counted(&summary(a, &vis));
    assert!(
        hit.is_none() && tests == 0 && z.is_empty(),
        "conformance: Zero's probe"
    );
    assert_eq!(
        (z.admissions(), z.evictions(), z.readmissions()),
        (0, 0, 0),
        "conformance: Zero"
    );
    // Unbounded: all eight held, nothing evicted.
    let mut u = WitnessCache::with_capacity(vis.clone(), Capacity::Unbounded);
    for g in &gs {
        assert!(admit(&mut u, g), "conformance: Unbounded admits");
    }
    assert!(
        !admit(&mut u, a),
        "conformance: Unbounded refuses a held graph"
    );
    assert_eq!(
        (u.len(), u.admissions(), u.evictions()),
        (8, 8, 0),
        "conformance: Unbounded"
    );
    // Bounded(1): every admission after the first evicts.
    let mut one = WitnessCache::with_capacity(vis.clone(), Capacity::Bounded(1));
    for g in [a, b, a, b] {
        assert!(admit(&mut one, g), "conformance: Bounded(1) admits");
    }
    assert_eq!(
        (
            one.len(),
            one.admissions(),
            one.evictions(),
            one.readmissions()
        ),
        (1, 4, 3, 2),
        "conformance: Bounded(1)"
    );
}

/// C3 / I3 / I4 in process over the five configurations: on eight fixtures
/// (conforming and violating, with and without hits), every completed row
/// meets F1's invariants for its capacity; `reports`, `executions`,
/// `impl_graphs`, `max_paper_events` and the reported graphs' canonical key
/// set are equal across the five; `sweep_graphs(w=0)` is the maximum and
/// `sweeps(w=0) = impl_graphs`.
#[test]
fn c03_invariants_across_the_five_configurations() {
    let mut bad = Vec::new();
    for name in [
        "apps/a1/correct/spec/n2r2",
        "apps/a1/eager/spec/n2r2",
        "apps/a3/fifo/spec/k2q2",
        "apps/a3/never-grant/spec/k2q2",
        "apps/a4/hash/a4a/k2q2m2",
        "2pc/leader/conf/n2",
        "synth/width/w8",
        "ex:naive/k3/enc1",
    ] {
        let f = fixture(name);
        let mut recs: Vec<(&str, Rec)> = Vec::new();
        let mut keys: Vec<BTreeSet<String>> = Vec::new();
        for w in CFGS {
            let cfg = cfg_of(&cf_label(w));
            let r = run_rec(&f, &cfg);
            bad.extend(invariants(&r, w));
            let o = cfirst_raw(&f, &cfg);
            keys.push(
                o.reports
                    .iter()
                    .map(|(g, _)| canon_key(g, &f.visible))
                    .collect(),
            );
            recs.push((w, r));
        }
        for c in ["reports", "executions", "impl_graphs", "max_paper_events"] {
            let vals: BTreeSet<&String> = recs.iter().map(|(_, r)| &r[c]).collect();
            if vals.len() != 1 {
                bad.push(format!("{name}: {c} differs {vals:?}"));
            }
        }
        if keys.iter().any(|k| *k != keys[0]) {
            bad.push(format!("{name}: report key sets differ"));
        }
        let z = n(&recs[0].1, "sweep_graphs");
        if recs.iter().any(|(_, r)| n(r, "sweep_graphs") > z) {
            bad.push(format!("{name}: a configuration sweeps more than w=0"));
        }
        note!(
            "c03 {name}: {}",
            recs.iter()
                .map(|(w, r)| format!(
                    "{w} hits {} sweeps {} sg {} |W| {} adm {} ev {} re {}",
                    r["cache_hits"],
                    r["sweeps"],
                    r["sweep_graphs"],
                    r["witnesses"],
                    r["admissions"],
                    r["evictions"],
                    r["readmissions"]
                ))
                .collect::<Vec<_>>()
                .join(" | ")
        );
    }
    assert!(bad.is_empty(), "conformance: criterion 3: {bad:#?}");
}

/// E-CF-2: `Bounded(0)` is refused by `cfirst::run` (`KnobConflict`) and
/// asserted against by `run_with` (a panic); `parse_capacity` never yields it
/// (`w=0` is `Zero`); the builder accepts it (E-CF-2: the engine refuses).
#[test]
fn c03_bounded_zero_is_refused_by_the_engine() {
    let f = fixture("synth/width/w2");
    let b0 = GridConfig::new(GridEngine::CompleteFirst)
        .witness_cache(Capacity::Bounded(0))
        .precheck(true);
    let cc = b0.conf_config(&f);
    match cfirst::run(
        cc.clone(),
        f.implementation.clone(),
        f.specification.clone(),
    ) {
        Err(ConfError::KnobConflict { knob, .. }) => {
            assert!(knob.contains("Bounded(0)"), "conformance: {knob}")
        }
        other => panic!(
            "conformance: Bounded(0) through run: {:?}",
            other.map(|_| ())
        ),
    }
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        cfirst::run_with(&cc, &f.implementation, &f.specification, false)
    }));
    std::panic::set_hook(prev);
    assert!(r.is_err(), "conformance: run_with on Bounded(0) must panic");
    assert_eq!(
        cfg_of(&cf_label("w=0")).witness_cache,
        Capacity::Zero,
        "conformance: w=0 is Zero"
    );
    let built = ConfBuilder::new()
        .engine(Engine::CompleteFirst)
        .witness_cache(Capacity::Bounded(0))
        .build();
    assert!(
        built.is_ok(),
        "conformance: the builder accepts Bounded(0) (E-CF-2)"
    );
}

/// **T1** (nit; documentation against E-CF-2): `ConfBuilder::witness_cache`'s
/// rustdoc said "`Bounded(0)` is refused at `build` (`ConfError::KnobConflict`)",
/// but `build` accepts it (E-CF-2: the engine refuses it at `cfirst::run`, and
/// `Capacity`'s own doc says so). Fixed by the lead (2026-10-14, the doc now
/// says the engine refuses it); un-ignored. The test reads the source.
#[test]
fn t1_the_builder_doc_does_not_claim_a_build_refusal() {
    let src =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/config.rs"))
            .unwrap();
    assert!(
        !src.contains("`Bounded(0)` is refused\n    /// at `build`")
            && !src.contains("at `build` (`ConfError::KnobConflict`)"),
        "conformance: T1: config.rs still says Bounded(0) is refused at build"
    );
    assert!(
        src.contains("`Bounded(0)` is refused\n    /// by the engine"),
        "conformance: T1: the builder doc names the engine's refusal"
    );
}

// =========================================================================
// Criterion 4 — the first-report counters
// =========================================================================

fn vmhwm_now() -> u64 {
    fs::read_to_string("/proc/self/status")
        .unwrap()
        .lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1).map(|v| v.parse().unwrap()))
        .unwrap()
}

/// C4 (F2): on `ex:naive/k2/enc1` (2 reports) and `apps/a1/eager/spec/n2r2`
/// (55 reports) under `stop = false`, every configuration:
/// `wall_ms_at_first_report` is `Some` and ≤ `outer_wall_time_ms`,
/// `vmhwm_kb_at_first_report` is `Some` and ≤ the process's `VmHWM` after the
/// run (monotone); both columns non-blank in the record. On
/// `apps/a1/correct/spec/n2r2` and `synth/share/m2c1` (no report): `None`,
/// blank. A `stop = true` run's first report is at the same completion (its
/// wall is a lower bound of nothing — only `Some` is pinned).
#[test]
fn c04_first_report_counters() {
    let mut bad = Vec::new();
    for (name, violating) in [
        ("ex:naive/k2/enc1", true),
        ("apps/a1/eager/spec/n2r2", true),
        ("apps/a1/correct/spec/n2r2", false),
        ("synth/share/m2c1", false),
    ] {
        let f = fixture(name);
        for w in CFGS {
            let cfg = cfg_of(&cf_label(w));
            let o = cfirst_raw(&f, &cfg);
            let after = vmhwm_now();
            let c = &o.counters;
            if violating {
                match (c.wall_ms_at_first_report, c.vmhwm_kb_at_first_report) {
                    (Some(t), Some(v)) => {
                        if t > c.outer_wall_time_ms || v > after {
                            bad.push(format!(
                                "{name} {w}: {t} > {} or {v} > {after}",
                                c.outer_wall_time_ms
                            ));
                        }
                    }
                    other => bad.push(format!("{name} {w}: {other:?}")),
                }
            } else if c.wall_ms_at_first_report.is_some() || c.vmhwm_kb_at_first_report.is_some() {
                bad.push(format!("{name} {w}: Some on a conforming pair"));
            }
            let r = run_rec(&f, &cfg);
            let blank =
                r["wall_ms_at_first_report"].is_empty() || r["vmhwm_kb_at_first_report"].is_empty();
            let both_blank =
                r["wall_ms_at_first_report"].is_empty() && r["vmhwm_kb_at_first_report"].is_empty();
            if violating == blank || (!violating && !both_blank) {
                bad.push(format!(
                    "{name} {w}: columns {:?} {:?}",
                    r["wall_ms_at_first_report"], r["vmhwm_kb_at_first_report"]
                ));
            }
            if violating && n(&r, "vmhwm_kb_at_first_report") > n(&r, "rss_child_hwm_kb") {
                bad.push(format!(
                    "{name} {w}: VmHWM at the first report above the row's"
                ));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 4: {bad:#?}");
}

// =========================================================================
// Criterion 5 — the quiet flag (child processes: stdout captured)
// =========================================================================

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tf-cfcfg-tests-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).expect("conformance: a temp directory");
    d
}

fn progress_lines(text: &str) -> Vec<String> {
    text.lines()
        .filter(|l| l.contains("Executions attempted so far"))
        .map(str::to_owned)
        .collect()
}

/// One row through the runner's child (`eval_row`), its stdout.
fn child_stdout(fx: &str, label: &str, dir: &Path) -> (String, Rec) {
    fs::create_dir_all(dir).unwrap();
    let rs = RowSpec {
        fixture: fx.to_owned(),
        config: cfg_of(label),
        rep: 0,
        tier: Tier::default_tier(),
        run_kind: RunKind::Timed,
        family: String::new(),
        knobs: String::new(),
        k: [None; 4],
        variant: String::new(),
        twin_key: String::new(),
        series: None,
    };
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--ignored",
            "--exact",
            "conformance::eval::eval_row",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("EVAL_ROW", crate::conformance::eval::row_json(&rs))
        .env("EVAL_REP", "0")
        .env("EVAL_COMMIT", "cfcfg-tests")
        .env("EVAL_RUN_DIR", dir)
        .env_remove("EVAL_EXPORT")
        .env_remove("EVAL_SCHEDULE")
        .env_remove("EVAL_OUT")
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&out.stdout).to_string();
    let s = crate::conformance::eval::SENTINEL;
    let i = text
        .find(s)
        .unwrap_or_else(|| panic!("conformance: no sentinel: {text}"));
    let cells =
        crate::conformance::eval::parse_csv_line(text[i + s.len()..].lines().next().unwrap())
            .unwrap();
    let rec = header()
        .iter()
        .map(|c| (*c).to_owned())
        .zip(cells)
        .collect();
    (text, rec)
}

/// C5 (F3), child processes on `apps/a1/correct/spec/n2r2` (64 outer
/// executions, 16 sweeps of 18–205 Spec graphs): under `w=inf/quiet=true` the
/// captured stdout holds exactly the outer run's progress lines — the line at
/// 1…10, 20, …, 60 executions (15 lines; derived from `must.rs`'s default
/// schedule), the sweeps' none — and under the eleven-field label
/// (`quiet=false`) strictly more; the counters equal between the two.
#[test]
#[ignore]
fn c05_quiet_silences_the_sweeps_only() {
    let base = temp("c05");
    let (loud, rl) = child_stdout("apps/a1/correct/spec/n2r2", X1_CF, &base.join("loud"));
    let (quiet, rq) = child_stdout(
        "apps/a1/correct/spec/n2r2",
        &cf_label("w=inf"),
        &base.join("quiet"),
    );
    let (pl, pq) = (progress_lines(&loud), progress_lines(&quiet));
    note!(
        "c05: loud {} lines, quiet {} lines: {:?}",
        pl.len(),
        pq.len(),
        pq
    );
    let outer: Vec<u64> = pq
        .iter()
        .filter_map(|l| {
            l.split("so far: ")
                .nth(1)?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
        .collect();
    let want: Vec<u64> = (1..=10).chain([20, 30, 40, 50, 60]).collect();
    assert_eq!(
        outer, want,
        "conformance: the quiet run's lines are the outer run's"
    );
    assert!(
        pl.len() > pq.len(),
        "conformance: the loud run prints the sweeps' lines"
    );
    for c in [
        "executions",
        "reports",
        "cache_hits",
        "sweeps",
        "sweep_graphs",
        "witnesses",
    ] {
        assert_eq!(rl[c], rq[c], "conformance: {c} equal loud/quiet");
    }
}

// =========================================================================
// Criterion 6 — the label round-trips
// =========================================================================

/// C6 (F4, E-CF-1, E-CF-11): `parse_label(label())` is the identity on the
/// five `CFCFG` configurations, on the defaults (eleven fields, `LABEL_PIN`
/// unchanged) and on every engine × capacity × quiet; an eleven-field label
/// parses to `Unbounded`/`quiet = false`; 12 and 14 fields are refused; a
/// non-canonical spelling (the thirteen-field form of the defaults, `w=08`,
/// `w=+8`, `w=00`, …) is refused (gate 4 n1).
#[test]
fn c06_the_label_round_trips() {
    for w in CFGS {
        let l = cf_label(w);
        let c = cfg_of(&l);
        assert_eq!(c.label(), l, "conformance: identity on {l}");
        assert!(c.quiet, "conformance: quiet");
    }
    let d = GridConfig::new(GridEngine::Enumerator);
    assert_eq!(d.label(), LABEL_PIN, "conformance: LABEL_PIN");
    assert_eq!(
        d.label().split('/').count(),
        11,
        "conformance: eleven at the defaults"
    );
    let p = cfg_of(X1_CF);
    assert_eq!(
        (p.witness_cache, p.quiet),
        (Capacity::Unbounded, false),
        "conformance: eleven fields parse to the defaults"
    );
    assert_eq!(p.label(), X1_CF, "conformance: identity on eleven fields");
    let long = format!("{X1_CF}/w=8/quiet=false");
    assert_eq!(cfg_of(&long).label(), long, "conformance: w=8 quiet=false");
    // Gate 4 n1 (E-CF-11): only `label()`'s own spelling parses. The
    // thirteen-field form at the defaults and non-canonical integers are
    // refused (they parsed, to a configuration printing otherwise, before).
    for bad in [
        format!("{X1_CF}/w=inf/quiet=false"),
        format!("{X1_CF}/w=08/quiet=true"),
        format!("{X1_CF}/w=+8/quiet=true"),
        format!("{X1_CF}/w=00/quiet=true"),
        format!("{X1_CF}/w=-1/quiet=true"),
        format!("{X1_CF}/w=Inf/quiet=true"),
        format!("{X1_CF}/w=8/quiet=True"),
    ] {
        assert!(
            parse_label(&bad).is_none(),
            "conformance: E-CF-11: a non-canonical spelling parsed: {bad}"
        );
    }
    // The identity on `label()`'s image: every engine × capacity × quiet.
    for e in [
        GridEngine::Enumerator,
        GridEngine::Stateful,
        GridEngine::CompleteFirst,
        GridEngine::Gated,
        GridEngine::Verify,
    ] {
        for cap in [
            Capacity::Zero,
            Capacity::Bounded(1),
            Capacity::Bounded(8),
            Capacity::Bounded(64),
            Capacity::Bounded(1000),
            Capacity::Unbounded,
        ] {
            for q in [false, true] {
                let c = GridConfig::new(e).witness_cache(cap).quiet(q);
                let l = c.label();
                let back = parse_label(&l)
                    .unwrap_or_else(|| panic!("conformance: label() not parsed: {l}"));
                assert_eq!(back.label(), l, "conformance: identity on {l}");
                assert_eq!(
                    (back.witness_cache, back.quiet),
                    (cap, q),
                    "conformance: the knobs of {l}"
                );
            }
        }
    }
    assert!(
        parse_label(&format!("{X1_CF}/w=8")).is_none(),
        "conformance: 12 fields"
    );
    assert!(
        parse_label(&format!("{X1_CF}/w=8/quiet=true/x")).is_none(),
        "conformance: 14 fields"
    );
    assert!(
        parse_label(&format!("{X1_CF}/w=x/quiet=true")).is_none(),
        "conformance: w=x"
    );
}

/// C6: every key of `campaign-1/rows.csv` and `apptab-1/rows.csv` parses
/// (read-only scan), and its label prints back byte for byte.
#[test]
fn c06_every_stored_key_parses() {
    let mut bad = Vec::new();
    let mut counts = Vec::new();
    for store in ["log/eval/campaign-1/rows.csv", "log/eval/apptab-1/rows.csv"] {
        let rows = read_rows(&plan(store)).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
        counts.push(rows.len());
        for r in &rows {
            let k = &r["key"];
            let parts: Vec<&str> = k.split('|').collect();
            match crate::conformance::eval::parse_key(k) {
                Some((_, c, ..)) if c.label() == parts[1] => {}
                _ => bad.push(k.clone()),
            }
        }
    }
    note!("c06: keys scanned {counts:?}");
    assert!(
        counts[0] > 20_000 && counts[1] > 0,
        "conformance: the stores were read"
    );
    assert!(
        bad.is_empty(),
        "conformance: unparsed keys: {:?}",
        &bad[..bad.len().min(5)]
    );
}

// =========================================================================
// Criterion 7 — schema 3
// =========================================================================

/// C7 (F5, E-CF-6): `SCHEMA_VERSION = 3`; the header is 185 columns with the
/// five new ones right after `witnesses`; `Store::open` refuses a schema-2
/// store (a copy of `apptab-1/rows.csv`) by name, with and without
/// `allow_mixed`; `read_rows` reads that copy by its own header (36 rows,
/// the five columns absent).
#[test]
fn c07_schema_three() {
    // COMPACT-INDEX re-pin (2026-10-17, gate 3 F1): schema 4, 202 columns;
    // the five schema-3 columns stay right after `witnesses`, and a schema-3
    // store (a copy of `cfirst-1/rows.csv`) is now refused as well.
    // COMPACT-INDEX phase 2 re-pin (2026-10-19): schema 5, 208 columns;
    // fix round P3 (`sig_aliases`): 209.
    assert_eq!(SCHEMA_VERSION, 5, "conformance: schema");
    let h = header();
    assert_eq!(h.len(), 209, "conformance: header width");
    let i = h.iter().position(|c| *c == "witnesses").unwrap();
    assert_eq!(
        &h[i + 1..i + 6],
        &[
            "admissions",
            "evictions",
            "readmissions",
            "wall_ms_at_first_report",
            "vmhwm_kb_at_first_report"
        ],
        "conformance: the five columns after witnesses"
    );
    let d = temp("c07");
    let copy = d.join("rows.csv");
    fs::copy(plan("log/eval/apptab-1/rows.csv"), &copy).unwrap();
    for allow in [false, true] {
        match Store::open(&copy, "cfcfg-tests-host", "cfcfg-tests", allow) {
            Err(Refusal::Header) | Err(Refusal::Schema(_)) => {}
            Err(e) => panic!("conformance: another refusal: {}", e.text()),
            Ok(_) => panic!("conformance: a schema-2 store opened (allow_mixed {allow})"),
        }
    }
    let copy3 = d.join("rows3.csv");
    fs::copy(plan("log/eval/cfirst-1/rows.csv"), &copy3).unwrap();
    for allow in [false, true] {
        match Store::open(&copy3, "cfcfg-tests-host", "cfcfg-tests", allow) {
            Err(Refusal::Header) | Err(Refusal::Schema(_)) => {}
            Err(e) => panic!("conformance: another refusal: {}", e.text()),
            Ok(_) => panic!("conformance: a schema-3 store opened (allow_mixed {allow})"),
        }
    }
    let rows = read_rows(&copy).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    assert_eq!(rows.len(), 36, "conformance: read by its own header");
    assert!(
        !rows[0].contains_key("admissions"),
        "conformance: no schema-3 column"
    );
    // A file whose first line is not a header is refused.
    let junk = d.join("junk.csv");
    fs::write(&junk, "not,a,header\n").unwrap();
    assert!(read_rows(&junk).is_err(), "conformance: no header, refused");
}

// =========================================================================
// Criterion 8 — the schedule parser (the tester's own expansion)
// =========================================================================

const FAMILIES: [&str; 5] = ["a1", "a2", "a3", "a4", "le"];

/// F6's rows, configuration → size → benchmark → pair, for `max_size`.
fn cf_rows(max: usize, profile: &str) -> Vec<serde_json::Value> {
    let mut out = Vec::new();
    for w in CFGS {
        for s in 2..=max {
            for fam in FAMILIES {
                for p in ApptabPair::ALL.iter().filter(|p| p.family() == fam) {
                    out.push(serde_json::json!({
                        "key": format!("{}|{}|0|default|timed|{profile}", p.name(s), cf_label(w)),
                        "benchmark": fam,
                        "pair": p.label(),
                        "variant": p.variant(),
                        "config": w,
                        "size": s,
                        "series": format!("{fam}|{}|{w}", p.variant()),
                    }));
                }
            }
        }
    }
    out
}

fn cf_schedule(rows: Vec<serde_json::Value>, max: usize) -> serde_json::Value {
    serde_json::json!({
        "date": "2026-10-14",
        "source": "cfcfg_tests",
        "commit": "6036802",
        "max_size": max,
        "limits": { "wall_ms": 600000, "mem_kb": 4194304, "budget_h": 60 },
        "configurations": CFGS,
        "rows": rows,
        "ended": [],
    })
}

fn cf_parse(v: &serde_json::Value) -> String {
    match crate::conformance::eval::CfcfgSchedule::parse(&v.to_string()) {
        Ok(s) => format!("accepted {}", s.rows.len()),
        Err(e) => e.text(),
    }
}

/// C8 (F6): the tester's complete row set at `max_size = 3` (150 rows) is
/// accepted; each malformed shape is refused by name.
#[test]
fn c08_the_schedule_parser() {
    let base = cf_schedule(cf_rows(3, "release"), 3);
    assert_eq!(cf_parse(&base), "accepted 150", "conformance: the 150 rows");
    let rows = cf_rows(3, "release");
    let mut cases: Vec<(&str, serde_json::Value, &str)> = Vec::new();
    let mut v = base.clone();
    v["reused"] = serde_json::json!([]);
    cases.push(("reused present", v, "unknown key `reused`"));
    let mut v = base.clone();
    v["profiling"] = serde_json::json!([]);
    cases.push(("profiling present", v, "unknown key `profiling`"));
    let mut v = base.clone();
    v["extension_reuse"] = serde_json::json!([]);
    cases.push((
        "extension_reuse present",
        v,
        "unknown key `extension_reuse`",
    ));
    let mut v = base.clone();
    v["frozen"] = serde_json::json!(1);
    cases.push(("unknown key", v, "unknown key `frozen`"));
    let mut v = base.clone();
    v["configurations"] = serde_json::json!(["w=0", "w=inf", "w=1", "w=8", "w=64", "w=2"]);
    cases.push(("a sixth configuration", v, "configurations"));
    let mut v = base.clone();
    v["rows"].as_array_mut().unwrap().pop();
    cases.push(("a missing row", v, "rows is incomplete"));
    // An extra row: a size-4 row at max_size 3.
    let mut v = base.clone();
    let mut extra = rows[0].clone();
    extra["key"] = serde_json::json!(rows[0]["key"].as_str().unwrap().replace("n2r2", "n4r4"));
    extra["size"] = serde_json::json!(4);
    v["rows"].as_array_mut().unwrap().push(extra);
    cases.push(("an extra row (size 4 at max 3)", v, "outside 2..=3"));
    let mut v = base.clone();
    let dup = v["rows"][3].clone();
    v["rows"].as_array_mut().unwrap().insert(4, dup);
    cases.push(("a duplicate", v, "repeats a cell"));
    let mut v = base.clone();
    v["rows"].as_array_mut().unwrap().swap(0, 1);
    cases.push(("pairs swapped", v, "out of the order"));
    // The former size-major order: size → configuration → benchmark → pair.
    let mut size_major = Vec::new();
    for s in 2..=3 {
        for r in &rows {
            if r["size"] == s {
                size_major.push(r.clone());
            }
        }
    }
    let mut v = base.clone();
    v["rows"] = serde_json::json!(size_major);
    cases.push((
        "the size-major order",
        v,
        "out of the order (configuration, size, benchmark, pair)",
    ));
    let mut v = base.clone();
    v["limits"]["budget_h"] = serde_json::json!(59);
    cases.push(("budget_h 59", v, "budget_h 59"));
    let mut v = base.clone();
    v["rows"][0]["key"] = serde_json::json!(rows[0]["key"]
        .as_str()
        .unwrap()
        .replace("|default|", "|extension|"));
    cases.push(("a wrong tier", v, "not `default`, `timed`, rep 0"));
    let mut v = base.clone();
    v["rows"][0]["key"] = serde_json::json!(rows[0]["key"]
        .as_str()
        .unwrap()
        .replace("quiet=true", "quiet=false"));
    cases.push(("quiet=false", v, "the label is not the configuration's"));
    // A row above an ended series' end (the series ended at 2, its size-3 row listed).
    let mut v = base.clone();
    v["ended"] = serde_json::json!([{ "series": rows[0]["series"], "size": 2, "reason": "x" }]);
    cases.push((
        "a row above an ended series' end",
        v,
        "lies above its series' end",
    ));
    let mut bad = Vec::new();
    for (what, v, needle) in &cases {
        let e = cf_parse(v);
        note!("c08 {what}: {e}");
        if !e.contains(needle) {
            bad.push(format!("{what}: {e}"));
        }
    }
    // With the ended series' size-3 row omitted, the file is accepted (149).
    let s0 = rows[0]["series"].as_str().unwrap().to_owned();
    let kept: Vec<serde_json::Value> = rows
        .iter()
        .filter(|r| !(r["series"] == s0.as_str() && r["size"] == 3))
        .cloned()
        .collect();
    let mut v = cf_schedule(kept, 3);
    v["ended"] = serde_json::json!([{ "series": s0, "size": 2, "reason": "x" }]);
    let got = cf_parse(&v);
    if got != "accepted 149" {
        bad.push(format!("ended with the row omitted: {got}"));
    }
    assert!(bad.is_empty(), "conformance: criterion 8: {bad:#?}");
}

/// `MIN-ENGINES` E1-2 (the tester, gate 3; derived §E1 item 14 (b)): a CFCFG
/// schedule row whose key spells a selector in place of `Plain` (each of the
/// three legacy spellings) is rejected at the row's validation by name, the
/// key quoted; the same file with the canonical key is accepted (150 rows).
#[test]
fn e1_a_legacy_key_in_the_cfcfg_schedule_is_rejected() {
    let base = cf_schedule(cf_rows(3, "release"), 3);
    assert_eq!(cf_parse(&base), "accepted 150", "conformance: the 150 rows");
    let k0 = base["rows"][0]["key"].as_str().unwrap().to_owned();
    assert!(k0.contains("|CompleteFirst/Plain/"), "conformance: {k0}");
    let mut bad = Vec::new();
    for s in ["Ltr", "Reverse", "FewestEvents"] {
        let legacy = k0.replace("|CompleteFirst/Plain/", &format!("|CompleteFirst/{s}/"));
        let mut v = base.clone();
        v["rows"][0]["key"] = serde_json::json!(legacy);
        let got = cf_parse(&v);
        if !(got.contains("a legacy key") && got.contains(&legacy) && got.contains("`Plain`")) {
            bad.push(format!("{s}: {got}"));
        }
    }
    assert!(bad.is_empty(), "conformance: E1-2: {bad:#?}");
}

// -------------------------------------------------------------------------
// Child processes: the driver
// -------------------------------------------------------------------------

fn clean_probes() -> Probes {
    Probes {
        git: Box::new(|| ("cfcfg-tests".to_owned(), false)),
        host: Box::new(|| "cfcfg-tests-host".to_owned()),
    }
}

/// The child of the driver tests (`CFCFG_CASE`): `from_env` runs
/// `Driver::from_env()` then `run()`; `custom` runs the criterion-9 custom
/// spec named `CFCFG_CASE_SPEC` into `CFCFG_CASE_OUT` with `CFCFG_CASE_ONLY`.
#[test]
#[ignore]
fn cfcfg_child() {
    let Ok(case) = std::env::var("CFCFG_CASE") else {
        return;
    };
    let line = match case.as_str() {
        "from_env" => match Driver::from_env() {
            Err(e) => format!("from_env: {}", e.text()),
            Ok(d) => match d.run() {
                Ok(s) => format!("ran {} skipped_dep {}", s.ran, s.skipped_dep),
                Err(e) => e.text(),
            },
        },
        "custom" => {
            let name = std::env::var("CFCFG_CASE_SPEC").unwrap();
            let d = Driver {
                spec: Spec {
                    name,
                    rows: custom_rows(),
                },
                specs: crate::conformance::eval::builtin_specs(),
                out_dir: PathBuf::from(std::env::var("CFCFG_CASE_OUT").unwrap()),
                sample_period: Duration::from_millis(100),
                probes: clean_probes(),
                allow_mixed: true,
                only: std::env::var("CFCFG_CASE_ONLY").ok(),
            };
            match d.run() {
                Ok(s) => format!(
                    "ran {} skipped_dep {} skipped_after_censor {} present {}",
                    s.ran, s.skipped_dep, s.skipped_after_censor, s.skipped_present
                ),
                Err(e) => e.text(),
            }
        }
        "spec" => match Driver::from_env() {
            Err(e) => format!("from_env: {}", e.text()),
            Ok(d) => {
                let keys: Vec<String> = d.spec.rows.iter().map(|r| r.key(prof())).collect();
                let scopes: Vec<String> = d
                    .spec
                    .rows
                    .iter()
                    .map(|r| match &r.series {
                        Some(s) => format!("{}#{}", s.scope, s.size),
                        None => "none".to_owned(),
                    })
                    .collect();
                format!("{}\t{}\t{}", d.spec.name, keys.join(" "), scopes.join(" "))
            }
        },
        "first_report" => first_report_case(),
        other => format!("unknown case {other}"),
    };
    use std::io::Write as _;
    writeln!(std::io::stdout().lock(), "CASE\t{line}").unwrap();
}

fn child_case(env: &[(&str, String)]) -> String {
    let mut c = std::process::Command::new(std::env::current_exe().unwrap());
    c.args([
        "--ignored",
        "--exact",
        "conformance::cfcfg_tests::cfcfg_child",
        "--nocapture",
        "--test-threads=1",
    ]);
    for k in [
        "EVAL_SCHEDULE",
        "EVAL_OUT",
        "EVAL_SPEC",
        "EVAL_ONLY",
        "CFCFG_CASE_ONLY",
    ] {
        c.env_remove(k);
    }
    for (k, v) in env {
        c.env(k, v);
    }
    let o = c.output().unwrap();
    String::from_utf8_lossy(&o.stdout)
        .lines()
        .find_map(|l| l.find("CASE\t").map(|k| l[k + 5..].to_owned()))
        .unwrap_or_else(|| {
            format!(
                "no case line: {}",
                String::from_utf8_lossy(&o.stderr)
                    .lines()
                    .filter(|l| l.contains("panicked") || l.contains("conformance:"))
                    .take(3)
                    .collect::<Vec<_>>()
                    .join(" / ")
            )
        })
}

/// C8 through `from_env` (child): a malformed schedule (`budget_h` 59) under
/// `EVAL_SPEC=CFCFG` is the parser's refusal by name (no panic, no record);
/// `EVAL_SPEC=X0` with the same file present runs one key and never reads it
/// (no record). The valid file is `c08_cfcfg_spec_on_a_valid_schedule`'s.
/// Run alone.
#[test]
#[ignore]
fn c08_a_malformed_schedule_through_from_env() {
    let base = temp("c08");
    let mut v = cf_schedule(cf_rows(2, prof()), 2);
    v["limits"]["budget_h"] = serde_json::json!(59);
    let f = base.join("schedule.json");
    fs::write(&f, v.to_string()).unwrap();
    let out = base.join("out-cfcfg");
    let got = child_case(&[
        ("CFCFG_CASE", "from_env".into()),
        ("EVAL_SPEC", "CFCFG".into()),
        ("EVAL_OUT", out.display().to_string()),
        ("EVAL_SCHEDULE", f.display().to_string()),
        ("EVAL_ALLOW_MIXED", "1".into()),
    ]);
    note!("c08 from_env CFCFG: {got}");
    assert_eq!(
        got,
        "from_env: refused: the CFCFG schedule is malformed: limits budget_h 59 is not D-T6's hard cap of 60 h",
        "conformance: CFCFG refused"
    );
    assert!(
        !out.join("schedule.used.json").exists(),
        "conformance: no record"
    );
    let outx = base.join("out-x0");
    let got = child_case(&[
        ("CFCFG_CASE", "from_env".into()),
        ("EVAL_SPEC", "X0".into()),
        ("EVAL_OUT", outx.display().to_string()),
        ("EVAL_SCHEDULE", f.display().to_string()),
        // `MIN-ENGINES` E1 (gate 3 re-pin): the stateful key prints `Plain`.
        ("EVAL_ONLY", "ex:naive/k2/enc1|Stateful/Plain/*|0|*".into()),
        ("EVAL_ALLOW_MIXED", "1".into()),
    ]);
    note!("c08 from_env X0: {got}");
    assert!(
        got.starts_with("ran 1"),
        "conformance: X0 ignores the file: {got}"
    );
    assert!(
        !outx.join("schedule.used.json").exists(),
        "conformance: X0 writes no record"
    );
}

// =========================================================================
// Criterion 9 — series and dependency (child processes)
// =========================================================================

/// The custom rows of criterion 9 (under the spec name `CFCFG` or `X0`):
/// - series `dep`: size 1 `synth/share/m2c1` (its `w=inf` run ends with
///   `|W| = 1`), size 2 `synth/naive-self/k2enc1` (`|W| = 2`), each with its
///   `w=inf` row first and then `w=1`, `w=8`, `w=64`;
/// - series `cen`: `eval/series/slow/k1` at rep 1 (sleeps 3 s) under a 2 s
///   tier — `w=0` and `w=inf` censored — its three bounded rows, then size 2
///   `eval/series/slow/k2` under `w=0`;
/// - `w=8` on `synth/width/w2` without its `w=inf` row.
fn custom_rows() -> Vec<RowSpec> {
    let t2 = Tier {
        name: "t2s".to_owned(),
        wall: Duration::from_secs(2),
        mem_kb: 4 * 1024 * 1024,
    };
    let mk = |fx: &str, w: &str, scope: &str, size: i64, tier: &Tier, rep: u32| {
        let cfg = cfg_of(&cf_label(w));
        RowSpec {
            fixture: fx.to_owned(),
            config: cfg.clone(),
            rep,
            tier: tier.clone(),
            run_kind: RunKind::Timed,
            family: "custom".to_owned(),
            knobs: String::new(),
            k: [Some(size), None, None, None],
            variant: "conforming".to_owned(),
            twin_key: String::new(),
            series: Some(Series::of(scope, "diag", &cfg, tier, RunKind::Timed, size)),
        }
    };
    let d = Tier::default_tier();
    let mut v = Vec::new();
    for w in ["w=inf", "w=1", "w=8", "w=64"] {
        v.push(mk("synth/share/m2c1", w, "dep", 1, &d, 0));
    }
    for w in ["w=0", "w=inf", "w=1", "w=8", "w=64"] {
        v.push(mk("eval/series/slow/k1", w, "cen", 1, &t2, 1));
    }
    v.push(mk("synth/width/w2", "w=8", "miss", 1, &d, 0));
    for w in ["w=inf", "w=1", "w=8", "w=64"] {
        v.push(mk("synth/naive-self/k2enc1", w, "dep", 2, &d, 0));
    }
    v.push(mk("eval/series/slow/k2", "w=0", "cen", 2, &t2, 1));
    // Gate 4 m3: series `cen2`, one cell under one tier of its own (`t2b`, 2 s,
    // so its rows share no rep set with `cen`'s) — `w=0` at rep 1 (sleeps 3 s,
    // capped), `w=inf` at rep 0 (no sleep, ok); at size 2 the `w=0` row is
    // `skipped_after_censor` and the `w=inf` row runs.
    let t2b = Tier {
        name: "t2b".to_owned(),
        ..t2.clone()
    };
    v.push(mk("eval/series/slow/k1", "w=0", "cen2", 1, &t2b, 1));
    v.push(mk("eval/series/slow/k1", "w=inf", "cen2", 1, &t2b, 0));
    v.push(mk("eval/series/slow/k2", "w=0", "cen2", 2, &t2b, 1));
    v.push(mk("eval/series/slow/k2", "w=inf", "cen2", 2, &t2b, 0));
    v
}

/// C9 (F7) through the driver, one invocation per fixture (`EVAL_ONLY`)
/// with a valid `CFCFG` schedule present (`max_size = 2`):
/// - `synth/share/m2c1` `w=inf` ok `|W| = 1` → its three bounded rows
///   `skipped_dep` / `w_le_1`, no `proc_wall_ms`; the `dep` series alive: at
///   size 2 (`naive-self(2,1)`, `|W| = 2`) the bounded rows run (`ok`);
/// - `eval/series/slow/k1` `w=0` and `w=inf` `capped_wall`; its bounded rows
///   `skipped_dep` / `unbounded_censored`; `eval/series/slow/k2` `w=0`
///   `skipped_after_censor` (the `w=0` series ended at size 1 in an earlier
///   invocation: the rule holds across invocations);
/// - `synth/width/w2` `w=8` alone → `skipped_dep` / `unbounded_missing`;
/// - series `cen2` (gate 4 m3): `slow/k1` `w=0` capped while `w=inf` of the
///   same cell and tier completes; at size 2 `w=0` is `skipped_after_censor`
///   and `w=inf` runs (`ok`) — a censored `w=0` row ends only its own series;
/// - a last invocation over everything runs nothing new (19 present).
///
/// Under the name `X0` no dependency applies: the nine `synth/*` rows all run.
/// Run alone.
#[test]
#[ignore]
fn c09_series_and_dependency_across_invocations() {
    let base = temp("c09");
    let f = base.join("schedule.json");
    fs::write(&f, cf_schedule(cf_rows(2, prof()), 2).to_string()).unwrap();
    let store_name = if prof() == "release" {
        "rows.csv"
    } else {
        "rows-test.csv"
    };
    let mut bad = Vec::new();
    let out = base.join("out");
    let run = |only: &str| {
        child_case(&[
            ("CFCFG_CASE", "custom".into()),
            ("CFCFG_CASE_SPEC", "CFCFG".into()),
            ("CFCFG_CASE_OUT", out.display().to_string()),
            ("CFCFG_CASE_ONLY", only.into()),
            ("EVAL_SCHEDULE", f.display().to_string()),
        ])
    };
    let r: Vec<String> = [
        "synth/share/m2c1|*",
        "eval/series/slow/k1|*",
        "synth/width/w2|*",
        "synth/naive-self/k2enc1|*",
        "eval/series/slow/k2|*",
        "*",
    ]
    .iter()
    .map(|g| run(g))
    .collect();
    note!("c09 invocations: {r:#?}");
    let rows = read_rows(&out.join(store_name)).unwrap_or_default();
    let get = |fx: &str, w: &str, rep: &str, tier: &str| -> (String, String, String) {
        rows.iter()
            .find(|x| {
                x["key"].starts_with(&format!("{fx}|"))
                    && x["key"].contains(&format!("/{w}/"))
                    && x["key"].split('|').nth(2) == Some(rep)
                    && x["key"].split('|').nth(3) == Some(tier)
            })
            .map(|x| {
                (
                    x["end_class"].clone(),
                    x["censor_via"].clone(),
                    x["proc_wall_ms"].clone(),
                )
            })
            .unwrap_or_else(|| ("absent".into(), String::new(), String::new()))
    };
    let expect: [(&str, &str, &str, &str); 15] = [
        ("synth/share/m2c1", "w=inf", "ok", ""),
        ("synth/share/m2c1", "w=1", "skipped_dep", "w_le_1"),
        ("synth/share/m2c1", "w=8", "skipped_dep", "w_le_1"),
        ("synth/share/m2c1", "w=64", "skipped_dep", "w_le_1"),
        ("eval/series/slow/k1", "w=0", "capped_wall", "kill"),
        ("eval/series/slow/k1", "w=inf", "capped_wall", "kill"),
        (
            "eval/series/slow/k1",
            "w=1",
            "skipped_dep",
            "unbounded_censored",
        ),
        (
            "eval/series/slow/k1",
            "w=8",
            "skipped_dep",
            "unbounded_censored",
        ),
        (
            "eval/series/slow/k1",
            "w=64",
            "skipped_dep",
            "unbounded_censored",
        ),
        ("synth/width/w2", "w=8", "skipped_dep", "unbounded_missing"),
        ("synth/naive-self/k2enc1", "w=inf", "ok", ""),
        ("synth/naive-self/k2enc1", "w=1", "ok", ""),
        ("synth/naive-self/k2enc1", "w=8", "ok", ""),
        ("synth/naive-self/k2enc1", "w=64", "ok", ""),
        ("eval/series/slow/k2", "w=0", "skipped_after_censor", ""),
    ];
    for (fx, w, class, via) in expect {
        let (rep, tier) = if fx.starts_with("eval/series/slow") {
            ("1", "t2s")
        } else {
            ("0", "default")
        };
        let (c, v, wall) = get(fx, w, rep, tier);
        if c != class || v != via {
            bad.push(format!("{fx} {w}: {c}/{v}, want {class}/{via}"));
        }
        if class.starts_with("skipped") && !wall.is_empty() {
            bad.push(format!(
                "{fx} {w}: a skipped row with proc_wall_ms {wall} (charge must be 0)"
            ));
        }
    }
    // Gate 4 m3: a censored `w=0` row ends only its own series.
    for (fx, w, rp, class, via) in [
        ("eval/series/slow/k1", "w=0", "1", "capped_wall", "kill"),
        ("eval/series/slow/k1", "w=inf", "0", "ok", ""),
        (
            "eval/series/slow/k2",
            "w=0",
            "1",
            "skipped_after_censor",
            "",
        ),
        ("eval/series/slow/k2", "w=inf", "0", "ok", ""),
    ] {
        let (c, v, _) = get(fx, w, rp, "t2b");
        if c != class || v != via {
            bad.push(format!(
                "cen2 {fx} {w} rep {rp}: {c}/{v}, want {class}/{via}"
            ));
        }
    }
    if rows.len() != 19 {
        bad.push(format!("{} rows, want 19", rows.len()));
    }
    if !r[5].starts_with("ran 0 skipped_dep 0 skipped_after_censor 0 present 19") {
        bad.push(format!("the final invocation ran something: {}", r[5]));
    }
    if !out.join("schedule.used.json").exists() {
        bad.push("no schedule.used.json".to_owned());
    }
    // The same rows under `X0`: no dependency.
    let outx = base.join("out-x0");
    let rx = child_case(&[
        ("CFCFG_CASE", "custom".into()),
        ("CFCFG_CASE_SPEC", "X0".into()),
        ("CFCFG_CASE_OUT", outx.display().to_string()),
        ("CFCFG_CASE_ONLY", "synth/*".into()),
    ]);
    note!("c09 X0: {rx}");
    if !rx.starts_with("ran 9 skipped_dep 0") {
        bad.push(format!("X0: {rx}"));
    }
    assert!(bad.is_empty(), "conformance: criterion 9: {bad:#?}");
}

// =========================================================================
// Criteria 14, 15 — E1 and E2
// =========================================================================

/// C14 (E1): a pair whose Spec fails an assertion (`grid::r1(true)` as the
/// Spec, `r1(false)` the Impl, `Tvis = {a}`), under the `CFCFG` labels `w=0`,
/// `w=inf`, `w=8`: the stored record is `end_class = ok`, `spec_errors ≥ 1`,
/// `aborted = true` (the sweep aborts; no new end class).
#[test]
fn c14_a_specification_assertion_is_an_error_row() {
    let f = Fixture {
        name: "cfcfg/spec-asserts".to_owned(),
        source: "cfcfg_tests",
        group: Group::Paper,
        implementation: r1(false),
        specification: r1(true),
        visible: vec!["a".to_owned()],
        config: crate::Config::builder().build(),
        k: None,
        encoding: None,
        big_stack: false,
        table: None,
    };
    let mut bad = Vec::new();
    for w in ["w=0", "w=inf", "w=8"] {
        let r = run_rec(&f, &cfg_of(&cf_label(w)));
        note!(
            "c14 {w}: end {} spec_errors {} aborted {} reports {}",
            r["end_class"],
            r["spec_errors"],
            r["aborted"],
            r["reports"]
        );
        if r["end_class"] != "ok" || n(&r, "spec_errors") < 1 || r["aborted"] != "true" {
            bad.push(format!(
                "{w}: {} {} {}",
                r["end_class"], r["spec_errors"], r["aborted"]
            ));
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 14: {bad:#?}");
}

/// C15 (E2): on `R1` and `a27` (an Impl assertion; the cut off),
/// `cut_reports = 0` and `executions`, `impl_graphs`, `reports`,
/// `sweep_graphs` under `w=0`, `w=inf`, `w=8` equal the committed engine's
/// (`R1` 1/1/1/1; `a27` 2/2/2/4), the reported graphs the same key set.
#[test]
fn c15_implementation_assertions_are_continued() {
    let mut bad = Vec::new();
    for (name, want) in [("R1", [1u64, 1, 1, 1]), ("a27", [2, 2, 2, 4])] {
        let f = fixture(name);
        let mut sets = Vec::new();
        for w in ["w=0", "w=inf", "w=8"] {
            let cfg = cfg_of(&cf_label(w));
            let r = run_rec(&f, &cfg);
            let got = [
                n(&r, "executions"),
                n(&r, "impl_graphs"),
                n(&r, "reports"),
                n(&r, "sweep_graphs"),
            ];
            if got != want || n(&r, "cut_reports") != 0 || r["aborted"] != "false" {
                bad.push(format!(
                    "{name} {w}: {got:?} cut {} aborted {}",
                    r["cut_reports"], r["aborted"]
                ));
            }
            let o = cfirst_raw(&f, &cfg);
            sets.push(
                o.reports
                    .iter()
                    .map(|(g, _)| canon_key(g, &f.visible))
                    .collect::<BTreeSet<_>>(),
            );
        }
        if sets.iter().any(|s| *s != sets[0]) {
            bad.push(format!("{name}: report sets differ"));
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 15: {bad:#?}");
}

/// `CFCFG` is not a built-in spec: it is reachable only through `EVAL_SPEC`
/// with its schedule file (F6).
#[test]
fn c12_the_cfcfg_spec_is_not_builtin() {
    let names: Vec<String> = crate::conformance::eval::builtin_specs()
        .into_iter()
        .map(|s| s.name)
        .collect();
    assert!(
        !names.iter().any(|n| n == "CFCFG"),
        "conformance: CFCFG is reachable only through the driver"
    );
}

// =========================================================================
// Gate 4 round 01 (substitute reviewer): M1, M2, m2, m3, m4
// =========================================================================

/// Gate 4 M1 (E-CF-9): a `Bounded(n)` cache retains at most `n` canonical
/// forms however many admissions and evictions it has seen —
/// `retained_canonical_forms() ≤ n` after every admission — and `readmissions`
/// stays exact: the eight Spec graphs of `width(8)` cycled three times through
/// `Bounded(3)` give 24 admissions (8 first, 16 re-admissions), 21
/// evictions, 3 held. The (a, b, c, probe a, a, c) sequence on `Bounded(2)`
/// keeps 2 retained forms at every step; `Unbounded` retains one per held
/// graph (8), `Zero` none.
#[test]
fn c03_m1_a_bounded_cache_retains_at_most_n_canonical_forms() {
    let (gs, vis) = width_spec_graphs();
    let mut bad = Vec::new();
    let mut w = WitnessCache::with_capacity(vis.clone(), Capacity::Bounded(3));
    for round in 0..3 {
        for (i, g) in gs.iter().enumerate() {
            if !admit(&mut w, g) {
                bad.push(format!("round {round} graph {i}: refused"));
            }
            if w.retained_canonical_forms() > 3 || w.retained_canonical_forms() != w.len() {
                bad.push(format!(
                    "round {round} graph {i}: retained {} len {}",
                    w.retained_canonical_forms(),
                    w.len()
                ));
            }
        }
    }
    let got = (w.len(), w.admissions(), w.evictions(), w.readmissions());
    if got != (3, 24, 21, 16) {
        bad.push(format!(
            "Bounded(3) × 24: (len, adm, ev, readm) {got:?}, want (3, 24, 21, 16)"
        ));
    }
    let (a, b, c) = (&gs[0], &gs[1], &gs[2]);
    let mut two = WitnessCache::with_capacity(vis.clone(), Capacity::Bounded(2));
    let mut retained = Vec::new();
    for g in [a, b, c] {
        admit(&mut two, g);
        retained.push(two.retained_canonical_forms());
    }
    let _ = two.probe_covered_counted(&summary(a, &vis));
    for g in [a, c] {
        admit(&mut two, g);
        retained.push(two.retained_canonical_forms());
    }
    if retained != vec![1, 2, 2, 2, 2] || two.readmissions() != 1 {
        bad.push(format!(
            "Bounded(2): retained {retained:?} readm {}",
            two.readmissions()
        ));
    }
    let mut u = WitnessCache::with_capacity(vis.clone(), Capacity::Unbounded);
    let mut z = WitnessCache::with_capacity(vis.clone(), Capacity::Zero);
    for g in &gs {
        admit(&mut u, g);
        admit(&mut z, g);
    }
    if (u.retained_canonical_forms(), z.retained_canonical_forms()) != (8, 0) {
        bad.push(format!(
            "Unbounded {} Zero {}",
            u.retained_canonical_forms(),
            z.retained_canonical_forms()
        ));
    }
    assert!(bad.is_empty(), "conformance: gate 4 M1: {bad:#?}");
}

/// **T2** (gate 4, closed by E-CF-9's rewording): `Unbounded` and the gated
/// checker retain what `6036802` did plus one `Option<u128>` field per witness
/// (`None` outside `Bounded(n)`): `size_of::<Witness>()` is at most 40 bytes
/// above the three `6036802` fields' `size_of::<(ExecutionGraph, Wobs,
/// Summary)>()` (measured 416 against 376). A further per-witness field fails
/// here and must be stated in the erratum first.
#[test]
fn t2_a_witness_is_at_most_40_bytes_above_6036802s() {
    let now = std::mem::size_of::<crate::conformance::witness::Witness>();
    let then = std::mem::size_of::<(
        crate::exec_graph::ExecutionGraph,
        crate::conformance::obs::Wobs,
        Summary,
    )>();
    note!("t2: size_of::<Witness>() {now}, the three 6036802 fields {then}");
    assert!(
        now <= then + 40,
        "conformance: E-CF-9: size_of::<Witness>() {now} bytes, the three 6036802 fields {then} + 40"
    );
}

/// Gate 4 M2 (E-CF-8): the `cache` metadata column follows the knob on
/// complete-first rows — `off` (`w=0`), `bounded(1)`, `bounded(8)`,
/// `bounded(64)`, `on` (`w=inf`, thirteen fields, and the eleven-field
/// default); the gated row `on`, the stateful and enumerator rows `n/a`.
#[test]
fn c02_m2_the_cache_column_follows_the_knob() {
    let f = fixture("synth/share/m2c1");
    let mut bad = Vec::new();
    let mut cases: Vec<(String, &str)> = vec![
        (cf_label("w=0"), "off"),
        (cf_label("w=1"), "bounded(1)"),
        (cf_label("w=8"), "bounded(8)"),
        (cf_label("w=64"), "bounded(64)"),
        (cf_label("w=inf"), "on"),
        (X1_CF.to_owned(), "on"),
        (X1_GATED.to_owned(), "on"),
    ];
    let st = GridConfig::new(GridEngine::Stateful).label();
    let en = GridConfig::new(GridEngine::Enumerator).label();
    cases.push((st, "n/a"));
    cases.push((en, "n/a"));
    for (label, want) in &cases {
        let r = run_rec(&f, &cfg_of(label));
        if r["cache"] != *want {
            bad.push(format!("{label}: cache {:?}, want {want}", r["cache"]));
        }
    }
    assert!(bad.is_empty(), "conformance: gate 4 M2: {bad:#?}");
}

/// The child of `c04_m2_the_first_report_is_taken_once`: `a27`'s violating
/// pair (two completions, two reports) whose Impl, from its second
/// invocation on, sleeps 400 ms and touches a 300 MiB allocation before
/// running. Prints `w,reports,calls,first_ms,outer_ms,first_kb,before_kb,after_kb`
/// per configuration (`w=0`, `w=inf`, `w=8`), `;`-separated.
fn first_report_case() -> String {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    let base = fixture("a27");
    let mut out = Vec::new();
    for w in ["w=0", "w=inf", "w=8"] {
        let calls = Arc::new(AtomicUsize::new(0));
        let inner = crate::conformance::grid::a27(true);
        let c2 = calls.clone();
        let mut f = base.clone();
        f.implementation = Arc::new(move || {
            if c2.fetch_add(1, Ordering::SeqCst) >= 1 {
                std::thread::sleep(Duration::from_millis(400));
                let v = vec![1u8; 300 << 20];
                std::hint::black_box(&v);
            }
            inner()
        });
        let before = vmhwm_now();
        let o = cfirst_raw(&f, &cfg_of(&cf_label(w)));
        let after = vmhwm_now();
        let c = &o.counters;
        out.push(format!(
            "{w},{},{},{},{},{},{before},{after}",
            o.reports.len(),
            calls.load(Ordering::SeqCst),
            c.wall_ms_at_first_report
                .map(|v| v.to_string())
                .unwrap_or_default(),
            c.outer_wall_time_ms,
            c.vmhwm_kb_at_first_report
                .map(|v| v.to_string())
                .unwrap_or_default(),
        ));
    }
    out.join(";")
}

/// Gate 4 m2 (criterion 4: "the report count at that moment is 1"; F2:
/// "never reset"), in a child process (its `VmHWM` is its own): on `a27`'s
/// violating pair, whose second completion is reached only after a 400 ms
/// sleep and a 300 MiB touched allocation, under `w=0`, `w=inf`, `w=8`:
/// two reports; `wall_ms_at_first_report < 400 ≤ outer_wall_time_ms` (the
/// value is the first report's, not overwritten by the second); in the
/// child's first run `vmhwm_kb_at_first_report` is below the pre-allocation
/// mark + 100 MiB while `VmHWM` after the run is ≥ 250 MiB above it.
#[test]
#[ignore]
fn c04_m2_the_first_report_is_taken_once() {
    let got = child_case(&[("CFCFG_CASE", "first_report".into())]);
    note!("c04 m2: {got}");
    let mut bad = Vec::new();
    for (i, part) in got.split(';').enumerate() {
        let f: Vec<&str> = part.split(',').collect();
        if f.len() != 8 {
            bad.push(format!("unparsed: {part}"));
            continue;
        }
        let num = |k: usize| f[k].parse::<u64>().unwrap_or(u64::MAX);
        let (reports, calls, first, outer) = (num(1), num(2), num(3), num(4));
        let (first_kb, before, after) = (num(5), num(6), num(7));
        if reports != 2 || calls < 2 {
            bad.push(format!("{}: reports {reports} calls {calls}", f[0]));
        }
        if !(first < 400 && outer >= 400) {
            bad.push(format!("{}: first {first} ms outer {outer} ms", f[0]));
        }
        if i == 0 && !(first_kb < before + 100 * 1024 && after >= before + 250 * 1024) {
            bad.push(format!(
                "{}: first-report VmHWM {first_kb} kB, before {before}, after {after}",
                f[0]
            ));
        }
    }
    assert!(bad.is_empty(), "conformance: gate 4 m2: {bad:#?}");
}

/// Gate 4 m3: `cfcfg_spec()` on a valid schedule through `Driver::from_env`
/// (child, `EVAL_SPEC=CFCFG`, the tester's own 75-row file at `max_size` 2):
/// the spec is named `CFCFG`; its rows' keys are the file's, in the file's
/// order; every row has a series whose scope carries its label (so the five
/// configurations are five series per pair: 75 scopes) and whose size is the
/// row's. Then the five rows of `apps/a1/correct/spec/n2r2` run through the
/// driver (`EVAL_ONLY`): `ran 5 skipped_dep 0`, and the store's `cache`
/// cells are `off`, `on`, `bounded(1)`, `bounded(8)`, `bounded(64)` (E-CF-8)
/// with the F1 invariants on every row. Run alone.
#[test]
#[ignore]
fn c08_cfcfg_spec_on_a_valid_schedule() {
    let base = temp("c08v");
    let rows = cf_rows(2, prof());
    let f = base.join("schedule.json");
    fs::write(&f, cf_schedule(rows.clone(), 2).to_string()).unwrap();
    let out = base.join("out");
    let env = |case: &str, only: Option<&str>| {
        let mut e = vec![
            ("CFCFG_CASE", case.to_owned()),
            ("EVAL_SPEC", "CFCFG".to_owned()),
            ("EVAL_OUT", out.display().to_string()),
            ("EVAL_SCHEDULE", f.display().to_string()),
            ("EVAL_ALLOW_MIXED", "1".to_owned()),
        ];
        if let Some(o) = only {
            e.push(("EVAL_ONLY", o.to_owned()));
        }
        e
    };
    let got = child_case(&env("spec", None));
    let parts: Vec<&str> = got.split('\t').collect();
    let mut bad = Vec::new();
    if parts.len() != 3 {
        panic!("conformance: m3: {got}");
    }
    let want: Vec<String> = rows
        .iter()
        .map(|r| r["key"].as_str().unwrap().to_owned())
        .collect();
    let keys: Vec<&str> = parts[1].split(' ').collect();
    let scopes: Vec<&str> = parts[2].split(' ').collect();
    if parts[0] != "CFCFG" {
        bad.push(format!("spec name {}", parts[0]));
    }
    if keys != want.iter().map(String::as_str).collect::<Vec<_>>() {
        bad.push(format!(
            "keys: {} rows, the file {}",
            keys.len(),
            want.len()
        ));
    }
    let distinct: BTreeSet<&str> = scopes
        .iter()
        .map(|s| s.split('#').next().unwrap())
        .collect();
    if distinct.len() != 75 {
        bad.push(format!("{} distinct scopes, want 75", distinct.len()));
    }
    for (k, sc) in keys.iter().zip(&scopes) {
        let label = k.split('|').nth(1).unwrap();
        let (scope, size) = sc.split_once('#').unwrap_or(("none", ""));
        if !scope.contains(label) || size != "2" {
            bad.push(format!("{k}: series {sc}"));
        }
    }
    let ran = child_case(&env("from_env", Some("apps/a1/correct/spec/n2r2|*")));
    note!("c08 valid: {ran}");
    if ran != "ran 5 skipped_dep 0" {
        bad.push(format!("the run: {ran}"));
    }
    let store_name = if prof() == "release" {
        "rows.csv"
    } else {
        "rows-test.csv"
    };
    let stored = read_rows(&out.join(store_name)).unwrap_or_default();
    let cache: Vec<&str> = stored.iter().map(|r| r["cache"].as_str()).collect();
    if cache != vec!["off", "on", "bounded(1)", "bounded(8)", "bounded(64)"] {
        bad.push(format!("cache cells {cache:?}"));
    }
    for (r, w) in stored.iter().zip(CFGS) {
        let rec: Rec = r.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        bad.extend(invariants(&rec, w));
    }
    if !out.join("schedule.used.json").exists() {
        bad.push("no schedule.used.json".to_owned());
    }
    assert!(bad.is_empty(), "conformance: gate 4 m3: {bad:#?}");
}

/// The stored row of one in-process run under `custom_rows()`'s row shape
/// (default tier, rep 0, timed), for a store the driver then reads.
fn custom_row(fx: &str, w: &str) -> crate::conformance::grid::Row {
    let f = fixture(fx);
    let cfg = cfg_of(&cf_label(w));
    let end = run_row_in_process(&f, &cfg, false);
    let rs = RowSpec {
        fixture: fx.to_owned(),
        config: cfg,
        rep: 0,
        tier: Tier::default_tier(),
        run_kind: RunKind::Timed,
        family: "custom".to_owned(),
        knobs: String::new(),
        k: [None; 4],
        variant: "conforming".to_owned(),
        twin_key: String::new(),
        series: None,
    };
    eval_row_of(&end, &RowMeta::of(&rs, prof(), "cfcfg-tests", ""))
}

/// Gate 4 m4 (E-CF-7) through the driver (child): the store already holds
/// the `w=inf` row of two cells, rewritten to E1's shape — `naive-self(2,1)`
/// (`|W| = 2`, so without the rule its bounded rows would run) with
/// `aborted = true`, `spec_errors = 1`; `share(2,1)` (`|W| = 1`, so without
/// the rule `w_le_1`) with `spec_errors = 1` only. Every bounded row of both
/// cells is `skipped_dep / unbounded_error`, charge 0. Run alone.
#[test]
#[ignore]
fn c09_m4_an_aborted_unbounded_row_is_unbounded_error() {
    let base = temp("c09m4");
    let f = base.join("schedule.json");
    fs::write(&f, cf_schedule(cf_rows(2, prof()), 2).to_string()).unwrap();
    let out = base.join("out");
    fs::create_dir_all(&out).unwrap();
    let store_name = if prof() == "release" {
        "rows.csv"
    } else {
        "rows-test.csv"
    };
    {
        let mut st = Store::open(
            &out.join(store_name),
            "cfcfg-tests-host",
            "cfcfg-tests",
            true,
        )
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
        for (fx, aborted) in [
            ("synth/naive-self/k2enc1", true),
            ("synth/share/m2c1", false),
        ] {
            let mut row = custom_row(fx, "w=inf");
            for (k, v) in row.iter_mut() {
                if *k == "aborted" && aborted {
                    *v = "true".to_owned();
                }
                if *k == "spec_errors" {
                    *v = "1".to_owned();
                }
            }
            st.append(&row)
                .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
        }
    }
    let mut bad = Vec::new();
    for only in ["synth/naive-self/k2enc1|*", "synth/share/m2c1|*"] {
        let got = child_case(&[
            ("CFCFG_CASE", "custom".into()),
            ("CFCFG_CASE_SPEC", "CFCFG".into()),
            ("CFCFG_CASE_OUT", out.display().to_string()),
            ("CFCFG_CASE_ONLY", only.into()),
            ("EVAL_SCHEDULE", f.display().to_string()),
        ]);
        note!("c09 m4 {only}: {got}");
        if !got.starts_with("ran 0 skipped_dep 3 skipped_after_censor 0 present 1") {
            bad.push(format!("{only}: {got}"));
        }
    }
    let rows = read_rows(&out.join(store_name)).unwrap_or_default();
    for r in &rows {
        if r["key"].contains("/w=inf/") {
            continue;
        }
        if (r["end_class"].as_str(), r["censor_via"].as_str()) != ("skipped_dep", "unbounded_error")
            || !r["proc_wall_ms"].is_empty()
        {
            bad.push(format!(
                "{}: {}/{} wall {:?}",
                r["key"], r["end_class"], r["censor_via"], r["proc_wall_ms"]
            ));
        }
    }
    if rows.len() != 8 {
        bad.push(format!("{} rows, want 8", rows.len()));
    }
    assert!(bad.is_empty(), "conformance: gate 4 m4: {bad:#?}");
}
