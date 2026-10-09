//! `P5-CAMPAIGN` gate 3: the tester's tests (criteria `P5-CAMPAIGN.md` revision 4.1).
//!
//! Tester-owned (the module lines in `mod.rs` are the lead's, criterion 10). Every
//! expected value here was derived **before** the lead's campaign code and
//! documents were read: `plan/traceForge/log/dev/P5-CAMPAIGN.derived.md` (its
//! sha256 is in `backlog/changes.md`). The tests are named by criterion (`c01_…`
//! … `c09_…`); a test that reproduces a defect of the lead's code is named
//! `t<N>_…` after its T-finding in `log/dev/P5-CAMPAIGN.report.md` and, while the
//! defect stands, is `#[ignore]`d with the expected and the measured values in
//! its rustdoc. Tests that spawn child processes (the driver and the child's
//! exports) are `#[ignore]`d too and run one per invocation with
//! `--ignored --exact … --test-threads=1`; they write only under the system
//! temporary directory.
//!
//! Records read at test time (all under `plan/traceForge/`, read-only):
//! `log/dev/P4-DIFF.tables.md`, `log/dev/P5-APPS.pilot.md`,
//! `log/dev/P5-SYNTH.pilot.md`, `log/eval/rows-test.csv` (the exhaustive
//! verdicts and the differential reach), `log/eval/P5-APPS-scaling-v2/rows.csv`
//! (the measured graph counts), `log/dev/P5-SYNTH.models.md` (criterion 7),
//! `log/dev/P5-CAMPAIGN.coverage.md` and `.counts.md`, and the
//! `log/dev/P5-APPS.expected.md` addendum.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use crate::conformance::config::{CompletionCover, GatePolicy, GatedMode};
use crate::conformance::eval::key_of;
use crate::conformance::eval::{
    builtin_specs, contract_fixtures, contract_specs, csv_line, experiments_of, exports_of,
    fixture_by_name, glob_match, header, mixed_of, parse_csv_line, profile_name, read_rows,
    row_json, run_row_in_process, x1_config, x2_config, Driver, Probes, Refusal, RowSpec, RunKind,
    Spec, Tier, SENTINEL,
};
use crate::conformance::eval::{frozen, FrozenLists};
use crate::conformance::grid::{
    apps_fixtures, apps_grid, apps_series_fixtures, corpus_fixtures, row_of, synth_grid, Budget,
    GridConfig, GridEnd, GridEngine, GridRaw, SynthPoint, APPS_CORNERS, APPS_CORNER_LINES,
};
use crate::conformance::selector::Selector;

/// Writes a line to stderr (the closed `s5_tests` emission scan forbids the
/// print macros in every file under `conformance/` but its test-only list).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

// =========================================================================
// Shared data: the specs as landed, and the tester's derivation
// =========================================================================

const ENGINES: [GridEngine; 4] = [
    GridEngine::Enumerator,
    GridEngine::Stateful,
    GridEngine::CompleteFirst,
    GridEngine::Gated,
];
const SELECTORS: [Selector; 3] = [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];

fn plan() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../plan/traceForge")
}

fn read_plan(rel: &str) -> String {
    fs::read_to_string(plan().join(rel))
        .unwrap_or_else(|e| panic!("conformance: campaign_tests: reading {rel}: {e}"))
}

fn prof() -> &'static str {
    profile_name()
}

/// `builtin_specs()` once per test process (the expansion builds every fixture).
fn specs() -> &'static Vec<Spec> {
    static S: OnceLock<Vec<Spec>> = OnceLock::new();
    S.get_or_init(builtin_specs)
}

fn spec(name: &str) -> &'static Spec {
    specs()
        .iter()
        .find(|s| s.name == name)
        .unwrap_or_else(|| panic!("conformance: campaign_tests: no builtin spec {name}"))
}

fn keys(s: &Spec) -> BTreeSet<String> {
    s.rows.iter().map(|r| r.key(prof())).collect()
}

fn key_sets() -> &'static BTreeMap<String, BTreeSet<String>> {
    static K: OnceLock<BTreeMap<String, BTreeSet<String>>> = OnceLock::new();
    K.get_or_init(|| specs().iter().map(|s| (s.name.clone(), keys(s))).collect())
}

fn ks(name: &str) -> &'static BTreeSet<String> {
    &key_sets()[name]
}

fn fixtures(s: &Spec) -> BTreeSet<String> {
    s.rows.iter().map(|r| r.fixture.clone()).collect()
}

fn set<I: IntoIterator<Item = S>, S: Into<String>>(it: I) -> BTreeSet<String> {
    it.into_iter().map(Into::into).collect()
}

/// The §6 paper fixtures by Part 6's exhaustive verdicts (derived.md §6).
const PAPER_CONFORMING: [&str; 6] = [
    "ex:nogate",
    "ex:sched",
    "ex:restart",
    "relay/paper",
    "relay/paper/rev",
    "traces/self",
];
const PAPER_VIOLATING: [&str; 10] = [
    "ex:cone",
    "relay/apparatus",
    "ex:rebuild",
    "blocking/apparatus",
    "blocking/cfirst",
    "reset-pair",
    "forward-pop",
    "a27",
    "R1",
    "R2",
];
/// The corpus' conforming generator modes (Part 6: `Identity`,
/// `InvisibleRefactor`, `DecoupleSpec`, `UnionCovered` report nothing on any
/// engine; `VisibleMutation`, `DecoupleImpl`, `SpecBlocks` report).
const CORPUS_CONFORMING_MODES: [&str; 4] = [
    "Identity",
    "InvisibleRefactor",
    "DecoupleSpec",
    "UnionCovered",
];

fn tf_conforming() -> Vec<String> {
    let mut v = vec!["ndk2/conf".to_owned(), "ndk3/conf".to_owned()];
    for n in 2..=4 {
        v.push(format!("2pc/coord/conf/n{n}"));
        v.push(format!("2pc/ring/conf/n{n}"));
    }
    for n in 2..=3 {
        v.push(format!("2pc/leader/conf/n{n}"));
    }
    v
}

fn tf_violating() -> Vec<String> {
    let mut v = vec!["ndk3/bad_A".to_owned()];
    for x in ["coord/eager", "leader/split", "ring/split"] {
        for n in 2..=4 {
            v.push(format!("2pc/{x}/n{n}"));
        }
    }
    v
}

fn corpus_sides() -> (Vec<String>, Vec<String>) {
    let mut conf = Vec::new();
    let mut viol = Vec::new();
    for f in corpus_fixtures(7, 10) {
        let mode = f.name.split('/').nth(1).unwrap_or_default().to_owned();
        if CORPUS_CONFORMING_MODES.contains(&mode.as_str()) {
            conf.push(f.name);
        } else {
            viol.push(f.name);
        }
    }
    (conf, viol)
}

fn a1(v: &str, n: usize, r: usize) -> String {
    format!("apps/a1/{v}/spec/n{n}r{r}")
}
fn a2(v: &str, k: usize, q: usize) -> String {
    match v {
        "sh" | "misroute" => format!("apps/a2/{v}/spec/k{k}q{q}s2"),
        _ => format!("apps/a2/{v}/spec/k{k}q{q}"),
    }
}
fn a3(v: &str, k: usize, q: usize) -> String {
    format!("apps/a3/{v}/spec/k{k}q{q}")
}
fn a4(v: &str, sp: &str, k: usize, q: usize, m: usize) -> String {
    format!("apps/a4/{v}/{sp}/k{k}q{q}m{m}")
}

/// The tester's derivation of every spec's point set (derived.md §1).
struct Derived {
    x1: BTreeSet<String>,
    x2: BTreeSet<String>,
    x1v: BTreeSet<String>,
    /// X2 fixture → its twin (C4's table).
    twins: BTreeMap<String, String>,
    twinless: BTreeSet<String>,
    /// The S1 and A1 X1 points (X3A(i)'s three-selector points).
    s1a1: BTreeSet<String>,
    apps_x1: BTreeSet<String>,
    apps_x2: BTreeSet<String>,
}

fn derived() -> &'static Derived {
    static D: OnceLock<Derived> = OnceLock::new();
    D.get_or_init(build_derived)
}

fn build_derived() -> Derived {
    let mut x1 = BTreeSet::new();
    let mut twins = BTreeMap::new();
    let mut x1v = BTreeSet::new();
    let mut s1a1 = BTreeSet::new();
    // S1.
    for e in [1, 2] {
        for k in 2..=7 {
            let c = format!("synth/naive-self/k{k}enc{e}");
            twins.insert(format!("ex:naive/k{k}/enc{e}"), c.clone());
            s1a1.insert(c.clone());
            x1.insert(c);
            if k <= 5 {
                x1v.insert(format!("ex:naive/k{k}/enc{e}"));
            }
        }
    }
    // S2–S4, S6.
    for m in [2usize, 4, 8, 12, 16, 24] {
        for c in [0, m / 2, m] {
            x1.insert(format!("synth/share/m{m}c{c}"));
            x1.insert(format!("synth/share-ctl/m{m}c{c}"));
        }
    }
    for n in [2usize, 4, 8, 12, 16, 20] {
        for j in [0, n / 2, n] {
            x1.insert(format!("synth/commit/n{n}j{j}"));
        }
    }
    for d in [2, 8, 32, 128, 512, 1024, 2048] {
        x1.insert(format!("synth/chain/d{d}"));
        x1.insert(format!("synth/width/w{d}"));
    }
    // S5: the twin conforms; the family and the control violate.
    for s in [1, 3, 4] {
        for k in 1..=10 {
            let t = format!("synth/reset-twin/k{k}s{s}");
            x1.insert(t.clone());
            for v in ["reset", "reset-ctl"] {
                let f = format!("synth/{v}/k{k}s{s}");
                twins.insert(f.clone(), t.clone());
                x1v.insert(f);
            }
        }
    }
    // The application grid (C3).
    let mut apps_x1 = BTreeSet::new();
    for n in 2..=6 {
        apps_x1.insert(a1("correct", n, 1));
    }
    for r in 2..=4 {
        apps_x1.insert(a1("correct", 2, r));
    }
    apps_x1.insert(a1("correct", 3, 2));
    for n in 2..=4 {
        apps_x1.insert(a1("control-reverse", n, 1));
    }
    for r in 2..=3 {
        apps_x1.insert(a1("control-reverse", 2, r));
    }
    for v in [
        "pb",
        "pb-br",
        "control-early-ack-primary",
        "control-early-ack-fwd",
        "sh",
    ] {
        for k in 1..=5 {
            apps_x1.insert(a2(v, k, 1));
        }
        for q in 2..=5 {
            apps_x1.insert(a2(v, 1, q));
        }
    }
    apps_x1.insert(a2("pb", 3, 3));
    apps_x1.insert(a2("sh", 2, 2));
    apps_x1.insert(a2("sh", 3, 2));
    for v in ["fifo", "control-lifo"] {
        for k in 2..=5 {
            apps_x1.insert(a3(v, k, 1));
        }
        for q in 2..=3 {
            apps_x1.insert(a3(v, 2, q));
        }
    }
    apps_x1.insert(a3("fifo", 3, 2));
    for (v, sp) in [("hash", "a4a"), ("hash", "a4b"), ("rr", "a4b")] {
        for k in 1..=4 {
            apps_x1.insert(a4(v, sp, k, 1, 2));
        }
        for q in 2..=3 {
            apps_x1.insert(a4(v, sp, 2, q, 2));
        }
        for m in 3..=4 {
            apps_x1.insert(a4(v, sp, 2, 1, m));
        }
    }
    for (v, sp) in [
        ("pair-swap-hash", "a4a"),
        ("pair-swap-hash", "a4b"),
        ("pair-swap-rr", "a4b"),
    ] {
        for (q, m) in [(1, 2), (2, 2), (1, 3)] {
            apps_x1.insert(a4(v, sp, 2, q, m));
        }
    }
    for (k, q, m) in [(1, 2, 2), (3, 2, 2), (1, 2, 3)] {
        apps_x1.insert(a4("hash", "a4a", k, q, m));
    }
    apps_x1.insert(a4("hash", "a4b", 3, 2, 3));
    for p in &apps_x1 {
        if p.starts_with("apps/a1/") {
            s1a1.insert(p.clone());
        }
    }
    let mut apps_x2 = BTreeSet::new();
    let mut tw = |f: String, t: String, set: &mut BTreeSet<String>| {
        twins.insert(f.clone(), t);
        set.insert(f);
    };
    for v in ["eager", "early-abort", "silent"] {
        for (n, r) in [(2, 1), (3, 1), (4, 1), (2, 2), (2, 3)] {
            tw(a1(v, n, r), a1("correct", n, r), &mut apps_x2);
            x1v.insert(a1(v, n, r));
        }
    }
    for (v, t) in [("early-ack", "pb-br"), ("stale-get", "pb")] {
        for (k, q) in [(2, 1), (3, 1), (1, 2), (1, 3)] {
            tw(a2(v, k, q), a2(t, k, q), &mut apps_x2);
        }
    }
    for (k, q) in [(1, 1), (2, 1), (3, 1), (1, 2), (1, 3)] {
        tw(a2("silent-put", k, q), a2("pb", k, q), &mut apps_x2);
    }
    for (k, q) in [(1, 2), (2, 2), (3, 2), (1, 3)] {
        tw(a2("misroute", k, q), a2("sh", k, q), &mut apps_x2);
    }
    for v in ["double-grant", "wrong-round", "never-grant"] {
        for (k, q) in [(2, 1), (3, 1), (2, 2)] {
            tw(a3(v, k, q), a3("fifo", k, q), &mut apps_x2);
        }
    }
    for (k, q, m) in [(1, 2, 2), (2, 2, 2), (3, 2, 2), (1, 2, 3)] {
        tw(
            a4("rr", "a4a", k, q, m),
            a4("hash", "a4a", k, q, m),
            &mut apps_x2,
        );
    }
    for (k, q, m) in [(1, 1, 2), (2, 1, 2), (3, 1, 2), (2, 2, 2), (2, 1, 3)] {
        tw(
            a4("drop", "a4b", k, q, m),
            a4("rr", "a4b", k, q, m),
            &mut apps_x2,
        );
    }
    x1.extend(apps_x1.iter().cloned());
    // §6.
    let (cc, cv) = corpus_sides();
    x1.extend(PAPER_CONFORMING.iter().map(|s| (*s).to_owned()));
    x1.extend(tf_conforming());
    x1.extend(cc);
    let mut twinless: BTreeSet<String> = PAPER_VIOLATING.iter().map(|s| (*s).to_owned()).collect();
    for k in 2..=7 {
        twinless.insert(format!("ex:naive/e2/k{k}"));
    }
    twinless.extend(tf_violating());
    twinless.extend(cv);
    let mut x2: BTreeSet<String> = twins.keys().cloned().collect();
    x2.extend(twinless.iter().cloned());
    Derived {
        x1,
        x2,
        x1v,
        twins,
        twinless,
        s1a1,
        apps_x1,
        apps_x2,
    }
}

/// derived.md §2: rows per spec and the distinct-key count.
const DERIVED_ROWS: [(&str, usize); 8] = [
    ("X0", 12),
    ("X1", 10_008),
    ("X1V", 1_494),
    ("X2", 6_408),
    ("X2P", 2_136),
    // 178 X2 fixtures minus the two round-02 m2 exclusions (176).
    ("X2S", 176),
    ("X1P", 0),
    ("X3A", 1_980),
];
const DERIVED_DISTINCT: usize = 21_218;

/// `P5-X5`'s two specs (criteria `P5-X5` F1, F2, criterion 1), every list
/// unfrozen (the X5 list empty); re-derived 2026-10-09 for the gate-3 fixes
/// (`eval.rs` `b34cf955…`: X5 lists every sweep partner). `A_flat` rows: the 12
/// in-grid violating `ex:naive/k{2..7}/enc{1,2}` × 3 selectors × `stop = true`
/// × 3 reps = 108, and `FLAT_SUBSET`'s 62 points under `Ltr` × 3 reps = 186
/// (the six `ex:naive/k{2,3,4}/enc{1,2}` included: with the list empty they are
/// not S1 rows) → 294. One `A_sweep` row per `A_flat` row, each key once: X2's
/// (the 108 stop pairs), X1V's (the six `ex:naive` `Ltr` points, 18), X1's (24
/// conforming §6 points, 72), X5's own (32 violating §6 points, 96) → 294; X5 =
/// 588. X5G (gated, both arms `precheck = true`; since `P5-X5-CODE` round 01
/// m2/n1, 2026-10-09, without the `stop = true` pairs): `FLAT_SUBSET` × `Ltr` ×
/// 3 reps = 186 + 186 own = 372 (588 at gate 3). Shared:
/// X1∩X5 72, X1V∩X5 18, X2∩X5 108 and X0∩X5 1 (`ex:naive/k2/enc1`
/// complete-first `Ltr` rep 0, also an X1V key); X5G none. Distinct: 21 218 +
/// (588 − 198) + 372 = **21 980** (22 196 at gate 3). (At the landing, `a2be4f81…`: X5 372, X5G
/// 552, distinct 22 142.)
const X5_ROWS: [(&str, usize); 2] = [("X5", 588), ("X5G", 372)];
const DERIVED_DISTINCT_WITH_X5: usize = 21_980;

/// X2S's exclusions (round 02 m2): the two X2 fixtures never run on the
/// stateful engine in Part 6 — `2pc/leader/split/n4` and `ndk3/bad_*`; the
/// other `n = 4` 2PC pairs completed there and stay in X2S.
fn x2s_excluded_by_derivation(f: &str) -> bool {
    f == "2pc/leader/split/n4" || f.starts_with("ndk3/bad_")
}

fn label_of(r: &RowSpec) -> String {
    r.config.label()
}

// =========================================================================
// Criterion 1 — the specs as data
// =========================================================================

/// C1: the builtin specs are X0, the seven campaign specs and (since the
/// `P5-X5` landing, 2026-10-08) `P5-X5`'s X5 and X5G; `V` is apart.
#[test]
fn c01_builtin_specs_hold_the_campaign_and_v_is_apart() {
    let names: BTreeSet<String> = specs().iter().map(|s| s.name.clone()).collect();
    assert_eq!(
        names,
        set(["X0", "X1", "X1V", "X1P", "X2", "X2P", "X2S", "X3A", "X5", "X5G"]),
        "conformance: builtin_specs()"
    );
    assert_eq!(specs().len(), 10, "conformance: no spec twice");
    let v = contract_specs();
    assert_eq!(v.len(), 1);
    assert_eq!(v[0].name, "V");
    assert!(
        !names.contains("V"),
        "conformance: V is not builtin (C1/C6)"
    );
    assert!(v[0].rows.iter().all(|r| r.run_kind == RunKind::Contract));
    // V: the contract's configurations — four engines × three selectors, the
    // enumerator memo on + unlimited.
    for r in &v[0].rows {
        assert!(!r.config.stop_at_first_report);
        assert_eq!(r.config.gated_mode, GatedMode::Exhaustive);
        if r.config.engine == GridEngine::Enumerator {
            assert!(r.config.memo && r.config.budget == Budget::Unlimited);
        }
    }
    let per_fixture: BTreeMap<&str, usize> = v[0].rows.iter().fold(BTreeMap::new(), |mut m, r| {
        *m.entry(r.fixture.as_str()).or_default() += 1;
        m
    });
    assert!(
        per_fixture.values().all(|n| *n == 12),
        "conformance: 4 engines × 3 selectors"
    );
    assert_eq!(per_fixture.len(), contract_fixtures().len());
    note!(
        "c01: V holds {} fixtures × 12 = {} rows",
        per_fixture.len(),
        v[0].rows.len()
    );
    // A V key is attributed to V alone.
    let mut all = specs().clone();
    all.extend(contract_specs());
    let k = v[0].rows[0].key(prof());
    assert_eq!(experiments_of(&k, &all, prof()), vec!["V".to_owned()]);
}

/// C1: every row's fixture resolves by name over a duplicate-free domain.
#[test]
fn c01_every_row_resolves_by_name() {
    let names: Vec<String> = crate::conformance::eval::all_fixtures()
        .into_iter()
        .map(|f| f.name)
        .collect();
    let uniq: BTreeSet<&String> = names.iter().collect();
    assert_eq!(
        uniq.len(),
        names.len(),
        "conformance: all_fixtures() names are unique"
    );
    for s in specs() {
        for f in fixtures(s) {
            assert!(
                uniq.contains(&f),
                "conformance: {}: {f} does not resolve",
                s.name
            );
        }
        if let Some(r) = s.rows.first() {
            let _ =
                fixture_by_name(&r.fixture).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
        }
    }
}

fn assert_x1_label(r: &RowSpec, what: &str) {
    let c = &r.config;
    assert!(!c.stop_at_first_report, "conformance: {what}: stop");
    assert_eq!(c.gated_mode, GatedMode::Exhaustive, "conformance: {what}");
    assert_eq!(c.gate_policy, GatePolicy::Always, "conformance: {what}");
    assert!(
        !c.precheck && !c.instrumented && !c.early_error_cut,
        "conformance: {what}"
    );
    assert_eq!(
        c.completion_cover,
        CompletionCover::Sweep,
        "conformance: {what}"
    );
    if c.engine == GridEngine::Enumerator {
        assert!(c.memo, "conformance: {what}: enumerator memo on");
        assert_eq!(c.budget, Budget::Unlimited, "conformance: {what}");
    }
}

/// C1/C2/C4/C7/C8: the configuration of every row per spec.
#[test]
fn c01_row_configurations_per_spec() {
    for r in &spec("X1").rows {
        assert_x1_label(r, "X1");
        assert_eq!(r.run_kind, RunKind::Timed);
        assert_eq!(
            r.tier.name, "default",
            "conformance: the extension list is unfrozen"
        );
    }
    for r in &spec("X1V").rows {
        assert_x1_label(r, "X1V");
        assert!(
            matches!(
                r.config.engine,
                GridEngine::CompleteFirst | GridEngine::Gated
            ),
            "conformance: X1V runs the two sweeping engines"
        );
        assert_eq!(r.run_kind, RunKind::Timed);
    }
    for name in ["X2", "X2P"] {
        for r in &spec(name).rows {
            let c = &r.config;
            assert!(
                c.stop_at_first_report,
                "conformance: {name}: stop on every engine"
            );
            if c.engine == GridEngine::Gated {
                assert_eq!(c.gated_mode, GatedMode::FirstFailure, "conformance: {name}");
            }
            assert_eq!(c.gate_policy, GatePolicy::Always, "conformance: {name}");
            assert!(!c.precheck && !c.instrumented && !c.early_error_cut);
            assert_eq!(c.completion_cover, CompletionCover::Sweep);
            if c.engine == GridEngine::Enumerator {
                assert!(
                    c.memo && c.budget == Budget::Unlimited,
                    "conformance: {name}: memo on"
                );
            }
            let kind = if name == "X2" {
                RunKind::Timed
            } else {
                RunKind::Profiling
            };
            assert_eq!(r.run_kind, kind, "conformance: {name}");
        }
    }
    // X2P = X2's rep-0 (fixture, label) pairs exactly, the label unchanged.
    let x2_rep0: BTreeSet<(String, String)> = spec("X2")
        .rows
        .iter()
        .filter(|r| r.rep == 0)
        .map(|r| (r.fixture.clone(), label_of(r)))
        .collect();
    let x2p: BTreeSet<(String, String)> = spec("X2P")
        .rows
        .iter()
        .map(|r| (r.fixture.clone(), label_of(r)))
        .collect();
    assert_eq!(
        x2p, x2_rep0,
        "conformance: X2P = X2's rep-0 keys as profiling rows"
    );
    // X2S: one stateful Ltr profiling row per X2 fixture.
    for r in &spec("X2S").rows {
        assert_eq!(r.config.engine, GridEngine::Stateful);
        assert_eq!(r.config.selector, Selector::Ltr);
        assert_eq!(r.run_kind, RunKind::Profiling);
        assert_eq!(r.rep, 0);
    }
    let x2s_want: BTreeSet<String> = fixtures(spec("X2"))
        .into_iter()
        .filter(|f| !x2s_excluded_by_derivation(f))
        .collect();
    assert_eq!(fixtures(spec("X2S")), x2s_want);
    assert_eq!(spec("X2S").rows.len(), 176, "conformance: X2S = 178 − 2");
    // X3A (pre-freeze): the enumerator, unlimited, exhaustive; the memo-off
    // arm new (990 rows), the memo-on arm X1's own keys (990; C1/C8, T4 fixed).
    let mut memo_off = 0;
    for r in &spec("X3A").rows {
        let c = &r.config;
        assert_eq!(
            c.engine,
            GridEngine::Enumerator,
            "conformance: pre-freeze X3A is the enumerator's memo arms only"
        );
        if c.memo {
            assert!(
                ks("X1").contains(&r.key(prof())),
                "conformance: a memo-on X3A row is X1's key: {}",
                r.fixture
            );
        } else {
            memo_off += 1;
        }
        assert_eq!(c.budget, Budget::Unlimited);
        assert!(!c.stop_at_first_report && !c.instrumented);
        if c.selector != Selector::Ltr {
            assert!(
                derived().s1a1.contains(&r.fixture),
                "conformance: non-Ltr memo-off only on S1 and A1: {}",
                r.fixture
            );
        }
    }
    assert_eq!(
        memo_off, 990,
        "conformance: X3A's memo-off arm (derived.md §1)"
    );
    assert!(
        spec("X1P").rows.is_empty(),
        "conformance: X1P's list is unfrozen"
    );
    // Every X1 fixture under all four engines and three selectors; X2 likewise.
    for name in ["X1", "X2"] {
        let mut per: BTreeMap<&str, BTreeSet<(String, String)>> = BTreeMap::new();
        for r in &spec(name).rows {
            per.entry(r.fixture.as_str()).or_default().insert((
                format!("{:?}", r.config.engine),
                format!("{:?}", r.config.selector),
            ));
        }
        assert!(
            per.values().all(|s| s.len() == 12),
            "conformance: {name}: 4 × 3 per fixture"
        );
    }
}

/// C1/H5: timed rows carry reps {0, 1, 2} per repetition set; X2P/X2S one rep.
#[test]
fn c01_reps_per_spec() {
    for s in specs() {
        let mut sets: BTreeMap<String, BTreeSet<u32>> = BTreeMap::new();
        for r in &s.rows {
            sets.entry(r.rep_set()).or_default().insert(r.rep);
        }
        let want: BTreeSet<u32> =
            if s.rows.first().map(|r| r.run_kind) == Some(RunKind::Timed) && s.name != "X0" {
                [0, 1, 2].into()
            } else {
                [0].into()
            };
        for (set, reps) in &sets {
            assert_eq!(reps, &want, "conformance: {}: {set}", s.name);
        }
        let kinds: BTreeSet<&str> = s.rows.iter().map(|r| r.run_kind.name()).collect();
        assert!(
            kinds.len() <= 1,
            "conformance: {}: one run kind per spec",
            s.name
        );
    }
}

fn points_of(name: &str) -> BTreeSet<String> {
    fixtures(spec(name))
}

/// The derivation's blocks that the landed specs get right (derived.md §1):
/// the application grid's X1/X2 split, S1–S4, S6 and S5's twin in X1, S1's
/// violating pair and S5's family in X2 and X1V, the A1 catalogue in X1V, and
/// the §6 paper fixtures' sides.
#[test]
fn c01_application_synthetic_and_paper_blocks_as_derived() {
    let d = derived();
    let x1 = points_of("X1");
    let x2 = points_of("X2");
    let x1v = points_of("X1V");
    let apps1: BTreeSet<String> = x1
        .iter()
        .filter(|f| f.starts_with("apps/"))
        .cloned()
        .collect();
    let apps2: BTreeSet<String> = x2
        .iter()
        .filter(|f| f.starts_with("apps/"))
        .cloned()
        .collect();
    assert_eq!(apps1, d.apps_x1, "conformance: X1's application points");
    assert_eq!(apps2, d.apps_x2, "conformance: X2's application points");
    assert_eq!(apps1.len(), 112);
    assert_eq!(apps2.len(), 50);
    for f in &d.x1 {
        if f.starts_with("synth/") {
            assert!(x1.contains(f), "conformance: X1 lacks {f}");
        }
    }
    for f in PAPER_CONFORMING {
        assert!(
            x1.contains(f) && !x2.contains(f),
            "conformance: {f} conforms (Part 6)"
        );
    }
    for f in PAPER_VIOLATING {
        assert!(
            x2.contains(f) && !x1.contains(f),
            "conformance: {f} violates (Part 6)"
        );
    }
    for k in 2..=7 {
        assert!(x2.contains(&format!("ex:naive/e2/k{k}")));
        for e in [1, 2] {
            assert!(x2.contains(&format!("ex:naive/k{k}/enc{e}")));
        }
    }
    for s in [1, 3, 4] {
        for k in 1..=10 {
            let f = format!("synth/reset/k{k}s{s}");
            assert!(x2.contains(&f) && x1v.contains(&f), "conformance: {f}");
        }
    }
    for f in d.x1v.iter().filter(|f| !f.starts_with("synth/reset-ctl/")) {
        assert!(x1v.contains(f), "conformance: X1V lacks {f}");
    }
    assert!(x2.contains("ndk3/bad_A"));
    for f in tf_violating() {
        assert!(x2.contains(&f), "conformance: {f}");
    }
}

/// **T1** (ignored while it stands). `synth/reset-ctl/*` violates (S5's control:
/// `P5-SYNTH` "the same uncovered projection"; Part 7's pilot reports on every
/// engine), so its 30 points belong to X2 (twin `reset-twin`) and X1V. The
/// landed `is_conforming` treats every `control:*` variant as conforming, so
/// all 30 are in **X1** and none in X2/X1V; and `synth_grid()` gives
/// `reset-ctl` no twin, so `x1_twin_key` would leave its X2 rows twinless.
/// Expected: reset-ctl ⊂ X2 ∩ X1V, ⊄ X1. Measured: reset-ctl ⊂ X1, X2 ∩ = ∅,
/// X1V ∩ = ∅.
#[test]
fn t1_reset_ctl_violates_and_belongs_to_x2_and_x1v() {
    let x1 = points_of("X1");
    let x2 = points_of("X2");
    let x1v = points_of("X1V");
    let mut bad = Vec::new();
    for s in [1, 3, 4] {
        for k in 1..=10 {
            let f = format!("synth/reset-ctl/k{k}s{s}");
            if x1.contains(&f) || !x2.contains(&f) || !x1v.contains(&f) {
                bad.push(f);
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: {} reset-ctl points misplaced: {bad:?}",
        bad.len()
    );
    for r in spec("X2")
        .rows
        .iter()
        .filter(|r| r.fixture.starts_with("synth/reset-ctl/"))
    {
        assert!(
            r.twin_key.starts_with("synth/reset-twin/"),
            "conformance: {}",
            r.fixture
        );
    }
}

/// **T2** (ignored while it stands). `corpus/DecoupleImpl/*` reports on every
/// engine and selector in Part 6 (`P4-DIFF.tables.md`: 1 report each;
/// `generator.rs`: `VisibleMutation | DecoupleImpl | SpecBlocks => false`), so
/// its 10 pairs are X2 rows; the landed `corpus_conforms` (and
/// `coverage.md`'s (iii)) puts them in X1. Expected X1 corpus 40 / X2 30;
/// measured 50 / 20.
#[test]
fn t2_corpus_decouple_impl_violates() {
    let (conf, viol) = corpus_sides();
    let x1 = points_of("X1");
    let x2 = points_of("X2");
    let x1c: BTreeSet<&String> = x1.iter().filter(|f| f.starts_with("corpus/")).collect();
    let x2c: BTreeSet<&String> = x2.iter().filter(|f| f.starts_with("corpus/")).collect();
    note!("t2: X1 corpus {}, X2 corpus {}", x1c.len(), x2c.len());
    assert_eq!(
        x1c,
        conf.iter().collect(),
        "conformance: X1's corpus = the conforming modes"
    );
    assert_eq!(
        x2c,
        viol.iter().collect(),
        "conformance: X2's corpus = the violating modes"
    );
}

/// **T3** (ignored while it stands). `2pc/coord/conf/n4` and `2pc/ring/conf/n4`
/// conform (Part 6's X6 runs: 0 reports on the enumerator, stateful and gated;
/// DEMO-2PC "conforms at 2, 3, 4") and are in `fixture_by_name`'s domain
/// (`two_pc_fixtures(4)`), but `SECTION6_CONFORMING` lists the 2PC pairs at
/// `n ≤ 3` only, so both land in X2 as twinless violating rows.
#[test]
fn t3_two_pc_conf_n4_conforms() {
    let x1 = points_of("X1");
    let x2 = points_of("X2");
    for f in tf_conforming() {
        assert!(
            x1.contains(&f) && !x2.contains(&f),
            "conformance: {f} conforms: X1, not X2"
        );
    }
}

/// C1: the frozen lists are empty and undated, and the driver refuses every
/// campaign spec, before it opens a store, with a `Refusal::Spec` naming the
/// unfrozen list.
#[test]
fn c01_unfrozen_lists_refuse_every_campaign_spec() {
    // The test process names no frozen file: every list unfrozen.
    assert_eq!(
        *frozen(),
        FrozenLists::default(),
        "conformance: no frozen lists in tests"
    );
    for name in ["X1", "X1V", "X1P", "X2", "X2P", "X2S", "X3A"] {
        let out = temp(&format!("unfrozen-{name}"));
        let d = driver(spec(name).clone(), &out, clean_probes());
        match d.run() {
            Err(e @ Refusal::Spec(_)) => {
                let t = e.text();
                assert!(t.contains("not frozen"), "conformance: {name}: {t}");
                // Round 01 n1: no longer worded as an unknown experiment.
                assert!(!t.contains("no experiment named"), "conformance: {t}");
                assert!(
                    t.starts_with(&format!("refused: {name} is not runnable")),
                    "conformance: {t}"
                );
            }
            Err(e) => panic!("conformance: {name}: wrong refusal {}", e.text()),
            Ok(s) => panic!("conformance: {name}: ran {s:?}"),
        }
        assert!(
            !d.store_path().exists(),
            "conformance: {name}: refused before opening the store"
        );
    }
}

/// C1/C6: the driver refuses any spec holding `run_kind = contract` rows — V,
/// and a spec mixing one contract row into timed rows.
#[test]
fn c01_contract_rows_are_refused() {
    let out = temp("contract-v");
    let d = driver(contract_specs().remove(0), &out, clean_probes());
    match d.run() {
        Err(Refusal::Spec(m)) => assert!(m.contains("contract"), "conformance: {m}"),
        other => panic!(
            "conformance: V must be refused: {:?}",
            other.map_err(|e| e.text())
        ),
    }
    let mut rows: Vec<RowSpec> = spec("X0").rows.clone();
    let mut c = rows[0].clone();
    c.run_kind = RunKind::Contract;
    rows.push(c);
    let out = temp("contract-mixed");
    let d = driver(
        Spec {
            name: "mixed".to_owned(),
            rows,
        },
        &out,
        clean_probes(),
    );
    assert!(matches!(d.run(), Err(Refusal::Spec(_))));
    assert!(!d.store_path().exists());
}

/// C1: the overlap structure. `X1 ∩ X2 = ∅`; X2S and X2P overlap nothing;
/// `X1 ∩ X3A` = X3A's memo-on arm (990 keys, all enumerator memo on — T4
/// fixed 2026-10-09); `X1V ∩ X3A = ∅` before the ceilings' freeze (the `Always`
/// arm needs a ceiling). **T6** (against the criteria, recorded by the lead as
/// an erratum): X0's complete-first and gated rows are X1V keys (6 keys).
/// X5 (`P5-X5` F1, gate-3 fixes 2026-10-09) lists its sweep partners: the
/// declared overlaps X1∩X5 72, X1V∩X5 18, X2∩X5 108 and X0∩X5 1 (the X0 key
/// that is also X1V's); X5G overlaps nothing.
#[test]
fn c01_overlaps() {
    let names = [
        "X0", "X1", "X1V", "X1P", "X2", "X2P", "X2S", "X3A", "X5", "X5G",
    ];
    let mut pairs = BTreeMap::new();
    for (i, a) in names.iter().enumerate() {
        for b in &names[i + 1..] {
            let n = ks(a).intersection(ks(b)).count();
            if n > 0 {
                pairs.insert(format!("{a}∩{b}"), n);
            }
        }
    }
    note!("c01 overlaps: {pairs:?}");
    let want: BTreeMap<String, usize> = [
        ("X0∩X1V".to_owned(), 6),
        ("X1∩X3A".to_owned(), 990),
        ("X0∩X5".to_owned(), 1),
        ("X1∩X5".to_owned(), 72),
        ("X1V∩X5".to_owned(), 18),
        ("X2∩X5".to_owned(), 108),
    ]
    .into();
    assert_eq!(pairs, want);
    // Every shared X5 key is an `A_sweep` (cover `Sweep`, no precheck,
    // complete-first) row; the X0 one is X1V's too.
    for t in ["X0", "X1", "X1V", "X2"] {
        for k in ks(t).intersection(ks("X5")) {
            let r = spec("X5")
                .rows
                .iter()
                .find(|r| &r.key(prof()) == k)
                .unwrap_or_else(|| panic!("conformance: {k}"));
            assert_eq!(
                r.config.engine,
                GridEngine::CompleteFirst,
                "conformance: {k}"
            );
            assert_eq!(
                r.config.completion_cover,
                CompletionCover::Sweep,
                "conformance: {k}"
            );
            assert!(!r.config.precheck, "conformance: {k}");
        }
    }
    let x0x5: Vec<&String> = ks("X0").intersection(ks("X5")).collect();
    assert!(x0x5.iter().all(|k| ks("X1V").contains(*k)));
    for k in ks("X1").intersection(ks("X3A")) {
        assert!(
            k.contains("|Enumerator/") && k.contains("/memo=true/Unlimited/"),
            "conformance: X1 ∩ X3A is the memo-on arm: {k}"
        );
    }
    let x0x1v: BTreeSet<String> = ks("X0").intersection(ks("X1V")).cloned().collect();
    for k in &x0x1v {
        assert!(
            k.starts_with("ex:naive/k2/enc1|CompleteFirst/")
                || k.starts_with("ex:naive/k2/enc1|Gated/")
        );
    }
}

/// **T4** (ignored while it stands). C1/C8: X3A's memo-on arm (and, after the
/// freeze, its `Always` arm) are X1's/X1V's rows **by key**, so X3A must hold
/// those keys for `experiments_of` to name both (criterion 2). The landed
/// `x3a_spec` builds the memo-off rows only: `X1 ∩ X3A = ∅`. Expected
/// `|X1 ∩ X3A|` = the memo-on enumerator keys at X3A's memo-off points
/// (as landed: 316 × 3 + 26 × 6 = 1 104; derived: 990); measured 0.
#[test]
fn t4_x3a_holds_its_memo_on_arm() {
    let want: BTreeSet<String> = spec("X3A")
        .rows
        .iter()
        .map(|r| {
            let mut c = r.config.clone();
            c.memo = true;
            key_of(
                &r.fixture,
                &c.label(),
                r.rep,
                &r.tier.name,
                r.run_kind,
                prof(),
            )
        })
        .collect();
    let have: BTreeSet<String> = ks("X1").intersection(ks("X3A")).cloned().collect();
    assert_eq!(
        have.len(),
        want.len(),
        "conformance: X1 ∩ X3A = the memo-on arm"
    );
    for k in want.iter().take(5) {
        let e = experiments_of(k, specs(), prof());
        assert_eq!(
            e,
            vec!["X1".to_owned(), "X3A".to_owned()],
            "conformance: {k}"
        );
    }
}

/// The landed point sets are the derived ones exactly (derived.md §1; T1–T3,
/// T8 fixed 2026-10-09): X1 278, X2 178, X1V 83 points; the twin table's 122
/// entries and the 56 twinless §6/corpus points.
#[test]
fn c01_point_sets_are_the_derivations() {
    let d = derived();
    assert_eq!(points_of("X1"), d.x1, "conformance: X1's points");
    assert_eq!(points_of("X2"), d.x2, "conformance: X2's points");
    assert_eq!(points_of("X1V"), d.x1v, "conformance: X1V's points");
    assert_eq!(
        (d.x1.len(), d.x2.len(), d.x1v.len()),
        (278, 178, 83),
        "conformance: derived.md §1"
    );
    assert_eq!((d.twins.len(), d.twinless.len()), (122, 56));
    let x2s: BTreeSet<String> =
        d.x2.iter()
            .filter(|f| !x2s_excluded_by_derivation(f))
            .cloned()
            .collect();
    assert_eq!(
        d.x2.len() - x2s.len(),
        2,
        "conformance: 2pc/leader/split/n4 and ndk3/bad_A"
    );
    assert_eq!(points_of("X2S"), x2s);
    assert_eq!(fixtures(spec("X2P")), d.x2);
}

/// The harness tester's test-only fixtures (`eval_tests::test_fixtures()`).
fn eval_fixtures() -> BTreeSet<String> {
    crate::conformance::eval_tests::test_fixtures()
        .into_iter()
        .map(|f| f.name)
        .collect()
}

/// **T8** (ignored while it stands). `section6_points()` takes every
/// `all_fixtures()` member of the §6 groups, and `all_fixtures()` includes
/// `eval_tests::test_fixtures()` (11 fixtures, `Group::Paper`): `eval/abort`
/// (aborts the process), `eval/panic`, `eval/alloc256` (256 MiB), `eval/sleeper`,
/// `eval/series/*`, `eval/naive_self/k6`. None is a §6 obligation; all 11 land in
/// X2 (twinless), X2P and X2S. Expected: no campaign key on an `eval/*` fixture.
#[test]
fn t8_no_campaign_row_on_a_test_only_fixture() {
    let ev = eval_fixtures();
    assert_eq!(ev.len(), 11);
    let mut bad = BTreeMap::new();
    for s in specs() {
        let n = s.rows.iter().filter(|r| ev.contains(&r.fixture)).count();
        if n > 0 {
            bad.insert(s.name.clone(), n);
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: rows on eval/* fixtures: {bad:?}"
    );
}

/// **T0** (the row counts pinned): the derived row counts and distinct-key
/// count (derived.md §2): X0 12, X1 10 008, X1V 1 494, X2 6 408, X2P 2 136,
/// X2S 176 (178 − the two round-02 m2 exclusions; 174 at round 01), X1P 0,
/// X3A 1 980 (990 memo-off + 990 memo-on = X1's keys); distinct 21 218
/// (21 220 before the exclusions). At the first landing (gate 3) it measured X1 11 376, X1V
/// 954, X2 5 436, X2P 1 812, X2S 151, X3A 1 104, distinct 20 839 (T1–T4, T8).
///
/// Re-pinned after the `P5-X5` landing (2026-10-08): the eight rows of
/// `DERIVED_ROWS` are **unchanged** (a change there is a T-finding against the
/// landing), and the eight specs' distinct count is still 21 218. After the X5
/// gate-3 fixes and `P5-X5-CODE` round 01 (2026-10-09): X5 588 and X5G 372
/// rows, each key once per spec;
/// 198 of X5's keys are other specs' (`c01_overlaps`), so the distinct count
/// over `builtin_specs()` is 21 980 (`X5_ROWS`; 22 142 at the landing, 22 196
/// at gate 3).
#[test]
fn t0_row_counts_as_derived() {
    for (name, n) in DERIVED_ROWS {
        assert_eq!(spec(name).rows.len(), n, "conformance: {name}");
    }
    let campaign: BTreeSet<&String> = DERIVED_ROWS
        .iter()
        .flat_map(|(name, _)| ks(name).iter())
        .collect();
    assert_eq!(
        campaign.len(),
        DERIVED_DISTINCT,
        "conformance: X0 and the seven campaign specs"
    );
    for (name, n) in X5_ROWS {
        assert_eq!(spec(name).rows.len(), n, "conformance: {name}");
        assert_eq!(ks(name).len(), n, "conformance: {name}'s keys are distinct");
    }
    let distinct: BTreeSet<&String> = key_sets().values().flatten().collect();
    assert_eq!(distinct.len(), DERIVED_DISTINCT_WITH_X5);
}

// =========================================================================
// Criterion 2 — deduplication and naming
// =========================================================================

/// C1/criterion 2: `experiments_of` names every spec holding a key — checked
/// on every overlap key as landed (X0 ∩ X1V; one of them is X5's too since the
/// X5 gate-3 fixes), on every X5 key another spec holds, and on a sample of
/// every spec's keys (exactly the specs whose key set holds it).
#[test]
fn c02_experiments_of_names_every_holder() {
    let mut x0x1v = BTreeMap::new();
    for k in ks("X0").intersection(ks("X1V")) {
        *x0x1v
            .entry(experiments_of(k, specs(), prof()).join("+"))
            .or_insert(0) += 1;
    }
    assert_eq!(
        x0x1v,
        [("X0+X1V".to_owned(), 5), ("X0+X1V+X5".to_owned(), 1)].into()
    );
    let mut x5 = BTreeMap::new();
    for k in ks("X5") {
        let e = experiments_of(k, specs(), prof());
        assert!(e.contains(&"X5".to_owned()), "conformance: {k}");
        *x5.entry(e.join("+")).or_insert(0) += 1;
    }
    assert_eq!(
        x5,
        [
            ("X5".to_owned(), 390),
            ("X1+X5".to_owned(), 72),
            ("X1V+X5".to_owned(), 17),
            ("X0+X1V+X5".to_owned(), 1),
            ("X2+X5".to_owned(), 108),
        ]
        .into(),
        "conformance: the holders of X5's keys"
    );
    for s in specs() {
        for r in s.rows.iter().step_by(997) {
            let k = r.key(prof());
            let want: Vec<String> = specs()
                .iter()
                .filter(|t| ks(&t.name).contains(&k))
                .map(|t| t.name.clone())
                .collect();
            assert_eq!(
                experiments_of(&k, specs(), prof()),
                want,
                "conformance: {k}"
            );
        }
    }
}

/// Criterion 2's small-tier driver test (one process per row; run alone):
/// X1's rows at two hand-count points and X1V's at `ex:naive/k2/enc1` (`Ltr`),
/// then X3A's rows at the same points, through `eval::Driver` into a temporary
/// `EVAL_OUT`. X3A runs only its memo-off keys; its memo-on arm (X1's keys) is
/// skipped as present and named by `experiments_of` under both specs.
#[test]
#[ignore]
fn c02_x3a_after_x1_and_x1v_runs_only_its_new_keys() {
    let pts = set(["synth/naive-self/k2enc1", "apps/a1/correct/spec/n2r1"]);
    let small = |name: &str, s: &Spec, ltr_only: bool| Spec {
        name: name.to_owned(),
        rows: s
            .rows
            .iter()
            .filter(|r| pts.contains(&r.fixture) || r.fixture == "ex:naive/k2/enc1")
            .filter(|r| !ltr_only || r.config.selector == Selector::Ltr)
            .cloned()
            .map(|mut r| {
                r.tier = small_tier();
                r
            })
            .collect(),
    };
    let x1 = small("X1-small", spec("X1"), false);
    let x1v = small("X1V-small", spec("X1V"), true);
    let x3a = small("X3A-small", spec("X3A"), false);
    assert_eq!(x1.rows.len(), 2 * 4 * 3 * 3);
    assert_eq!(x1v.rows.len(), 2 * 3);
    // X3A at the two points: the memo-off arm (18) and the memo-on arm, X1's
    // enumerator keys (18; T4 fixed).
    assert_eq!(x3a.rows.len(), 2 * 3 * 3 * 2);
    let all = vec![x1.clone(), x1v.clone(), x3a.clone()];
    let out = temp("c02-driver");
    let mut ran_before = BTreeSet::new();
    for s in [&x1, &x1v] {
        let d = real_driver(s.clone(), all.clone(), &out);
        let sum = d
            .run()
            .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
        assert_eq!(sum.ran, s.rows.len(), "conformance: {}: {sum:?}", s.name);
        ran_before.extend(keys(s));
    }
    let shared: BTreeSet<String> = keys(&x3a).intersection(&ran_before).cloned().collect();
    let d = real_driver(x3a.clone(), all.clone(), &out);
    let sum = d
        .run()
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    note!("c02: X3A-small {sum:?}, shared {}", shared.len());
    assert_eq!(
        shared.len(),
        18,
        "conformance: the memo-on arm: 2 points × 3 selectors × 3 reps"
    );
    assert_eq!(sum.ran, x3a.rows.len() - shared.len());
    assert_eq!(
        sum.ran,
        x3a.rows.iter().filter(|r| !r.config.memo).count(),
        "conformance: X3A ran exactly the memo-off keys"
    );
    assert_eq!(sum.skipped_present, shared.len());
    for k in &shared {
        assert_eq!(
            experiments_of(k, &all, prof()),
            vec!["X1-small".to_owned(), "X3A-small".to_owned()],
            "conformance: {k}"
        );
    }
    let rows = read_rows(&d.store_path()).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let stored: Vec<&String> = rows.iter().map(|r| &r["key"]).collect();
    let uniq: BTreeSet<&&String> = stored.iter().collect();
    assert_eq!(uniq.len(), stored.len(), "conformance: every key once");
    for r in &rows {
        assert_eq!(r["end_class"], "ok", "conformance: {}", r["key"]);
        let k = &r["key"];
        if keys(&x3a).contains(k) && !ran_before.contains(k) {
            assert!(
                k.contains("/memo=false/"),
                "conformance: X3A ran only memo-off keys: {k}"
            );
        }
        assert!(!experiments_of(k, &all, prof()).is_empty());
    }
}

// =========================================================================
// Criterion 3 — the application grid
// =========================================================================

/// C3: `apps_grid()` enumerates exactly the derived points (112 X1 + 50 X2 =
/// 162), each once, the variants on the derived sides.
#[test]
fn c03_apps_grid_points_are_c3s() {
    let g = apps_grid();
    let names: Vec<&String> = g.iter().map(|p| &p.fixture).collect();
    let uniq: BTreeSet<&String> = names.iter().copied().collect();
    assert_eq!(uniq.len(), names.len(), "conformance: every point once");
    let d = derived();
    let want: BTreeSet<String> = d.apps_x1.union(&d.apps_x2).cloned().collect();
    assert_eq!(uniq.into_iter().cloned().collect::<BTreeSet<_>>(), want);
    for p in &g {
        let conforming = p.variant == "conforming" || p.variant.starts_with("control:");
        assert_eq!(
            conforming,
            d.apps_x1.contains(&p.fixture),
            "conformance: {}: {}",
            p.fixture,
            p.variant
        );
        assert!(p.in_grid);
        if conforming {
            assert!(p.twin.is_none());
        } else {
            assert_eq!(
                p.twin.as_ref(),
                d.twins.get(&p.fixture),
                "conformance: {}",
                p.fixture
            );
        }
    }
    // The corners.
    let corners: BTreeSet<&str> = APPS_CORNERS.iter().map(|(f, _)| *f).collect();
    assert_eq!(
        corners,
        [
            "apps/a1/correct/spec/n3r2",
            "apps/a2/pb/spec/k3q3",
            "apps/a3/fifo/spec/k3q2",
            "apps/a4/hash/a4b/k3q2m3"
        ]
        .into()
    );
}

/// The axis knob of a line: the one coordinate that varies (none on a
/// one-point line).
fn varying(points: &[&SynthPoint]) -> BTreeSet<usize> {
    (0..4)
        .filter(|&i| points.iter().map(|p| p.k[i]).collect::<BTreeSet<_>>().len() > 1)
        .collect()
}

/// C3/criterion 3: the lines are a partition — every point on exactly one
/// line, sizes distinct within a line, one axis per line with the size its
/// value; per (configuration, tier) the X1 and X2 rows group by `series.scope`
/// into the declared lines (40 X1 and 25 X2 application lines; derived.md §5),
/// no key in two scopes.
#[test]
fn c03_lines_partition_per_configuration_and_tier() {
    let g = apps_grid();
    let mut lines: BTreeMap<(&str, &str), Vec<&SynthPoint>> = BTreeMap::new();
    for p in &g {
        lines.entry((p.family, p.line)).or_default().push(p);
    }
    assert_eq!(
        lines.len(),
        65,
        "conformance: application lines (derived.md §5)"
    );
    for ((fam, line), pts) in &lines {
        let sizes: BTreeSet<i64> = pts.iter().map(|p| p.size).collect();
        assert_eq!(
            sizes.len(),
            pts.len(),
            "conformance: {fam} {line}: sizes distinct"
        );
        let v = varying(pts);
        assert!(v.len() <= 1, "conformance: {line}: one axis, varying {v:?}");
        if let Some(&ax) = v.iter().next() {
            for p in pts {
                assert_eq!(
                    p.k[ax],
                    Some(p.size),
                    "conformance: {line}: size is the axis value"
                );
            }
        }
        let vars: BTreeSet<&str> = pts.iter().map(|p| p.variant).collect();
        assert_eq!(vars.len(), 1, "conformance: {line}: one variant per line");
    }
    for (name, cfg, want) in [
        ("X1", x1_config(GridEngine::Gated, Selector::Ltr), 40usize),
        ("X2", x2_config(GridEngine::Gated, Selector::Ltr), 25),
    ] {
        let mut scopes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for r in spec(name)
            .rows
            .iter()
            .filter(|r| r.fixture.starts_with("apps/") && r.config == cfg && r.rep == 0)
        {
            let s = r
                .series
                .as_ref()
                .expect("conformance: an application row carries its series");
            assert!(s
                .scope
                .ends_with(&format!("|{}|{}", r.tier.name, r.run_kind.name())));
            assert!(s.scope.contains(&cfg.label()));
            scopes
                .entry(s.scope.clone())
                .or_default()
                .insert(r.fixture.clone());
        }
        assert_eq!(
            scopes.len(),
            want,
            "conformance: {name}: application scopes"
        );
        let mut seen = BTreeSet::new();
        for fx in scopes.values().flatten() {
            assert!(seen.insert(fx.clone()), "conformance: {fx} in two scopes");
        }
    }
}

/// **T5** (ignored while it stands). Hand-wrapping split several string
/// literals across lines in `apps_grid()`, so line labels and knob labels
/// carry a newline and indentation: measured `"a2/sh/q=2,\n            s=2"`,
/// `"a4/hash-a4a/q=2,\n            m=2"`, `"a4/hash-a4a/k=1,\n        q=2"`,
/// the `rr-a4a` and `drop` lines, and the knobs of A3 mutants' `(2,2)`,
/// `hash-a4a`/`rr-a4a`/`drop`/`pair-swap` `(·,·,3)`/`(2,2,2)` points. Expected:
/// C3's labels (`a2/sh/q=2,s=2`, …) and knob labels without whitespace (the
/// `knobs` column is written to the store).
#[test]
fn t5_line_and_knob_labels_hold_no_whitespace() {
    let mut bad = Vec::new();
    for p in apps_grid() {
        if p.line.chars().any(char::is_whitespace) || p.knobs.chars().any(char::is_whitespace) {
            bad.push(format!(
                "{} line={:?} knobs={:?}",
                p.fixture, p.line, p.knobs
            ));
        }
    }
    let lines: BTreeSet<&str> = apps_grid().iter().map(|p| p.line).collect();
    for want in [
        "a2/sh/q=2,s=2",
        "a4/hash-a4a/q=2,m=2",
        "a4/hash-a4a/k=1,q=2",
        "a4/rr-a4a/q=2,m=2",
        "a4/rr-a4a/k=1,q=2",
        "a4/drop/q=1,m=2",
        "a4/drop/k=2,m=2",
        "a4/drop/k=2,q=1",
        "a2/misroute/q=2,s=2",
        "a2/misroute/k=1,s=2",
    ] {
        if !lines.contains(want) {
            bad.push(format!("missing line {want}"));
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: {} labels: {bad:#?}",
        bad.len()
    );
}

fn fact(n: u64) -> u128 {
    (1..=n as u128).product()
}

/// `(kq)! / (q!)^k`.
fn arrivals(k: u64, q: u64) -> u128 {
    fact(k * q) / fact(q).pow(k as u32)
}

/// The tester's A3 count (derived.md §7): the coordinator's maximal read
/// sequences; `kind` ∈ {fifo, wrong-round, control-lifo, double-grant,
/// never-grant}.
fn a3_count(k: usize, q: usize, kind: &str) -> u128 {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum Ph {
        Acq,
        Wait,
        Rel,
        Done,
    }
    type St = (Vec<(usize, Ph)>, bool, Vec<usize>);
    fn go(st: &St, k: usize, q: usize, kind: &str, memo: &mut BTreeMap<St, u128>) -> u128 {
        if let Some(v) = memo.get(st) {
            return *v;
        }
        let (cl, held, queue) = st;
        let mut tot = 0u128;
        let mut moved = false;
        for i in 0..cl.len() {
            let (r, ph) = cl[i];
            match ph {
                Ph::Acq => {
                    moved = true;
                    let mut n = cl.clone();
                    let (nh, nq) = if !*held || kind == "double-grant" {
                        n[i] = (r, Ph::Rel);
                        (true, queue.clone())
                    } else {
                        n[i] = (r, Ph::Wait);
                        let mut q2 = queue.clone();
                        q2.push(i);
                        (*held, q2)
                    };
                    tot += go(&(n, nh, nq), k, q, kind, memo);
                }
                Ph::Rel => {
                    moved = true;
                    let mut n = cl.clone();
                    n[i] = if r + 1 < q {
                        (r + 1, Ph::Acq)
                    } else {
                        (r + 1, Ph::Done)
                    };
                    let mut nq = queue.clone();
                    let next = if nq.is_empty() {
                        None
                    } else if kind == "control-lifo" {
                        nq.pop()
                    } else {
                        Some(nq.remove(0))
                    };
                    let nh = match next {
                        Some(w) if kind == "never-grant" && w == k - 1 => false,
                        Some(w) => {
                            n[w].1 = Ph::Rel;
                            true
                        }
                        None => false,
                    };
                    tot += go(&(n, nh, nq), k, q, kind, memo);
                }
                Ph::Wait | Ph::Done => {}
            }
        }
        let v = if moved { tot } else { 1 };
        memo.insert(st.clone(), v);
        v
    }
    go(
        &(vec![(0, Ph::Acq); k], false, Vec::new()),
        k,
        q,
        kind,
        &mut BTreeMap::new(),
    )
}

/// The graph-count formula at a fixture, `(Impl, Spec)`, where C3 states one.
fn formula(f: &str) -> Option<(u128, u128)> {
    let parts: Vec<&str> = f.split('/').collect();
    if parts.len() != 5 || parts[0] != "apps" {
        return None;
    }
    let knobs = parts[4];
    let num = |c: char| -> Option<u64> {
        let i = knobs.find(c)?;
        knobs[i + 1..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect::<String>()
            .parse()
            .ok()
    };
    match (parts[1], parts[2], parts[3]) {
        ("a1", "correct" | "control-reverse", _) => {
            let (n, r) = (num('n')?, num('r')?);
            let per = 2u128.pow(n as u32) * fact(n);
            Some((per.pow(r as u32), 16u128.pow(r as u32)))
        }
        ("a2", "pb" | "pb-br" | "sh", _) => {
            let a = arrivals(num('k')?, num('q')?);
            Some((a, a))
        }
        (
            "a3",
            v @ ("fifo" | "control-lifo" | "double-grant" | "wrong-round" | "never-grant"),
            _,
        ) => {
            let (k, q) = (num('k')?, num('q')?);
            Some((a3_count(k as usize, q as usize, v), arrivals(k, q)))
        }
        ("a4", imp @ ("hash" | "rr" | "pair-swap-hash" | "pair-swap-rr"), sp) => {
            let (k, q, m) = (num('k')?, num('q')?, num('m')?);
            let base = arrivals(k, q);
            let spec = base
                * if sp == "a4a" {
                    (m as u128).pow(k as u32)
                } else {
                    (m as u128).pow((k * q) as u32)
                };
            let imp_n = if imp.starts_with("pair-swap") {
                2u128.pow(q as u32)
            } else {
                base
            };
            Some((imp_n, spec))
        }
        _ => None,
    }
}

/// A markdown table: its header and rows.
type MdTable = (Vec<String>, Vec<Vec<String>>);

fn md_tables(text: &str) -> Vec<MdTable> {
    let split = |l: &str| -> Vec<String> {
        let t = l.trim();
        let t = t.strip_prefix('|').unwrap_or(t);
        let t = t.strip_suffix('|').unwrap_or(t);
        // A `|` inside backticks (a key glob) is not a cell separator.
        let mut cells = vec![String::new()];
        let mut tick = false;
        for ch in t.chars() {
            match ch {
                '`' => {
                    tick = !tick;
                    cells.last_mut().unwrap().push(ch);
                }
                '|' if !tick => cells.push(String::new()),
                _ => cells.last_mut().unwrap().push(ch),
            }
        }
        cells.into_iter().map(|c| c.trim().to_owned()).collect()
    };
    let lines: Vec<&str> = text.lines().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i + 1 < lines.len() {
        if lines[i].starts_with('|') && lines[i + 1].starts_with("|---") {
            let hdr = split(lines[i]);
            let mut rows = Vec::new();
            let mut j = i + 2;
            while j < lines.len() && lines[j].starts_with('|') {
                rows.push(split(lines[j]));
                j += 1;
            }
            out.push((hdr, rows));
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

fn col(hdr: &[String], name: &str) -> Option<usize> {
    hdr.iter().position(|c| c == name)
}

/// The measured `(impl_graphs, spec_graphs)` of every stateful exhaustive row
/// of the v2 scaling store and the `P5-APPS` pilot.
fn measured_counts() -> Vec<(String, u128, u128, &'static str)> {
    let mut out = Vec::new();
    let v2 = plan().join("log/eval/P5-APPS-scaling-v2/rows.csv");
    for r in read_rows(&v2).unwrap_or_else(|e| panic!("conformance: {}", e.text())) {
        let key = &r["key"];
        if !key.contains("|Stateful/") || r["end_class"] != "ok" {
            continue;
        }
        let fx = key.split('|').next().unwrap_or_default().to_owned();
        if let (Ok(i), Ok(s)) = (r["impl_graphs"].parse(), r["spec_graphs"].parse()) {
            out.push((fx, i, s, "v2"));
        }
    }
    for (hdr, rows) in md_tables(&read_plan("log/dev/P5-APPS.pilot.md")) {
        let (Some(f), Some(e), Some(i), Some(s)) = (
            col(&hdr, "fixture"),
            col(&hdr, "engine"),
            col(&hdr, "impl_graphs"),
            col(&hdr, "spec_graphs"),
        ) else {
            continue;
        };
        for r in rows {
            if r.get(e).map(String::as_str) != Some("Stateful") {
                continue;
            }
            if let (Some(Ok(a)), Some(Ok(b))) = (
                r.get(i).map(|x| x.parse::<u128>()),
                r.get(s).map(|x| x.parse::<u128>()),
            ) {
                out.push((r[f].clone(), a, b, "pilot"));
            }
        }
    }
    out
}

/// Criterion 3: A1/A2/A4's formulas (`pair-swap`: `2^q`) and the A3 counts hold
/// at every point the v2 store or the pilot measured.
#[test]
fn c03_count_formulas_hold_where_measured() {
    let mut checked = 0;
    let mut bad = Vec::new();
    for (fx, i, s, src) in measured_counts() {
        if let Some((fi, fs)) = formula(&fx) {
            checked += 1;
            if (fi, fs) != (i, s) {
                bad.push(format!("{src} {fx}: measured {i}/{s}, formula {fi}/{fs}"));
            }
        }
    }
    note!("c03: {checked} measured points checked");
    assert!(bad.is_empty(), "conformance: {bad:#?}");
    assert!(
        checked >= 100,
        "conformance: the store and the pilot measure ≥ 100 such rows"
    );
    // The joint corners and C3's quoted end points by the formulas.
    assert_eq!(formula("apps/a1/correct/spec/n3r2"), Some((2_304, 256)));
    assert_eq!(
        formula("apps/a1/correct/spec/n6r1").map(|x| x.0),
        Some(46_080)
    );
    assert_eq!(
        formula("apps/a1/correct/spec/n2r4").map(|x| x.0),
        Some(4_096)
    );
    assert_eq!(formula("apps/a2/pb/spec/k3q3"), Some((1_680, 1_680)));
    assert_eq!(formula("apps/a2/pb/spec/k5q1").map(|x| x.0), Some(120));
    assert_eq!(formula("apps/a3/fifo/spec/k3q2").map(|x| x.0), Some(2_898));
    assert_eq!(formula("apps/a4/hash/a4b/k3q2m3"), Some((90, 65_610)));
    assert_eq!(formula("apps/a4/hash/a4b/k4q1m2").map(|x| x.0), Some(24));
    assert_eq!(
        formula("apps/a4/hash/a4b/k2q3m2").map(|x| x.1),
        Some(20 * 64)
    );
    assert_eq!(
        formula("apps/a4/pair-swap-hash/a4a/k2q2m2").map(|x| x.0),
        Some(4)
    );
}

/// C3/criterion 3: A3's counts by the tester's procedure equal C3's eleven
/// quoted figures and every cell of the lead's `counts.md` table.
#[test]
fn c03_a3_counts_by_the_testers_procedure() {
    for (kind, k, q, n) in [
        ("fifo", 2, 1, 4),
        ("fifo", 3, 1, 30),
        ("fifo", 2, 2, 28),
        ("double-grant", 2, 1, 6),
        ("double-grant", 3, 1, 90),
        ("double-grant", 2, 2, 70),
        ("fifo", 4, 1, 336),
        ("fifo", 5, 1, 5_040),
        ("fifo", 2, 3, 212),
        ("fifo", 3, 2, 2_898),
        ("fifo", 3, 3, 330_252),
    ] {
        assert_eq!(a3_count(k, q, kind), n, "conformance: {kind} ({k},{q})");
    }
    let text = read_plan("log/dev/P5-CAMPAIGN.counts.md");
    let tables = md_tables(&text);
    let (hdr, rows) = tables
        .iter()
        .find(|(h, _)| h.first().is_some_and(|c| c.contains("kind")))
        .expect("conformance: counts.md's table");
    let pts: Vec<(usize, usize)> = hdr[1..]
        .iter()
        .map(|c| {
            let c = c.trim_matches(|x| x == '`' || x == '(' || x == ')');
            let (a, b) = c.split_once(',').expect("conformance: a (k, q) column");
            (a.trim().parse().unwrap(), b.trim().parse().unwrap())
        })
        .collect();
    let mut cells = 0;
    for r in rows {
        let kinds: Vec<&str> = if r[0].starts_with("Spec") {
            vec!["spec"]
        } else {
            r[0].split(',')
                .map(|s| s.trim().trim_matches('`'))
                .collect()
        };
        for (j, &(k, q)) in pts.iter().enumerate() {
            let v: u128 = r[j + 1]
                .replace([' ', '\u{202f}', '\u{a0}'], "")
                .parse()
                .unwrap();
            for kind in &kinds {
                let want = if *kind == "spec" {
                    arrivals(k as u64, q as u64)
                } else {
                    a3_count(k, q, kind)
                };
                assert_eq!(v, want, "conformance: counts.md {kind} ({k},{q})");
                cells += 1;
            }
        }
    }
    assert_eq!(
        cells,
        6 * 8,
        "conformance: counts.md: five kinds + Spec over eight points"
    );
}

/// C3/criterion 3: `apps_series_fixtures()` adds exactly the 38 points beyond
/// `apps_fixtures()`'s loops (derived.md §10), every grid point resolves, and
/// the names are unique across `all_fixtures()`.
#[test]
fn c03_apps_series_fixtures_are_exactly_the_points_beyond_the_loops() {
    let looped: BTreeSet<String> = apps_fixtures().into_iter().map(|f| f.name).collect();
    let series: Vec<String> = apps_series_fixtures().into_iter().map(|f| f.name).collect();
    let s: BTreeSet<String> = series.iter().cloned().collect();
    assert_eq!(s.len(), series.len());
    assert_eq!(series.len(), 38, "conformance: derived.md §10");
    assert!(s.is_disjoint(&looped));
    let grid: BTreeSet<String> = apps_grid().into_iter().map(|p| p.fixture).collect();
    let beyond: BTreeSet<String> = grid.difference(&looped).cloned().collect();
    assert_eq!(
        s, beyond,
        "conformance: series fixtures = grid points beyond the loops"
    );
    let mut want = BTreeSet::new();
    for (n, r) in [(5, 1), (6, 1), (2, 4)] {
        want.insert(a1("correct", n, r));
    }
    for v in [
        "pb",
        "pb-br",
        "control-early-ack-primary",
        "control-early-ack-fwd",
        "sh",
    ] {
        for (k, q) in [(4, 1), (5, 1), (1, 4), (1, 5)] {
            want.insert(a2(v, k, q));
        }
    }
    for v in ["fifo", "control-lifo"] {
        for (k, q) in [(4, 1), (5, 1), (2, 3)] {
            want.insert(a3(v, k, q));
        }
    }
    for (v, sp) in [("hash", "a4a"), ("hash", "a4b"), ("rr", "a4b")] {
        for (k, q, m) in [(4, 1, 2), (2, 3, 2), (2, 1, 4)] {
            want.insert(a4(v, sp, k, q, m));
        }
    }
    assert_eq!(s, want);
}

/// RFC 1321 MD5 (no crate in the tree has one).
fn md5_hex(data: &[u8]) -> String {
    const S: [u32; 64] = [
        7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 5, 9, 14, 20, 5, 9, 14, 20, 5,
        9, 14, 20, 5, 9, 14, 20, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 6, 10,
        15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
    ];
    let k: Vec<u32> = (0..64)
        .map(|i| ((i as f64 + 1.0).sin().abs() * 4_294_967_296.0) as u32)
        .collect();
    let mut h: [u32; 4] = [0x6745_2301, 0xefcd_ab89, 0x98ba_dcfe, 0x1032_5476];
    let mut msg = data.to_vec();
    let bits = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bits.to_le_bytes());
    for chunk in msg.chunks(64) {
        let m: Vec<u32> = (0..16)
            .map(|i| {
                u32::from_le_bytes([
                    chunk[4 * i],
                    chunk[4 * i + 1],
                    chunk[4 * i + 2],
                    chunk[4 * i + 3],
                ])
            })
            .collect();
        let [mut a, mut b, mut c, mut d] = h;
        for i in 0..64 {
            let (f, g) = match i / 16 {
                0 => ((b & c) | (!b & d), i),
                1 => ((d & b) | (!d & c), (5 * i + 1) % 16),
                2 => (b ^ c ^ d, (3 * i + 5) % 16),
                _ => (c ^ (b | !d), (7 * i) % 16),
            };
            let f = f.wrapping_add(a).wrapping_add(k[i]).wrapping_add(m[g]);
            a = d;
            d = c;
            c = b;
            b = b.wrapping_add(f.rotate_left(S[i]));
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
    }
    h.iter()
        .flat_map(|w| w.to_le_bytes())
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Criteria 3 and 10: `grid.rs` before the `P5-CAMPAIGN` block is byte-identical
/// to the gate-4 record (`fee6f42a…`, the `P5-SYNTH` close): the `P5-APPS` block
/// md5 `543b5315…`, the `P5-SYNTH` block `9f2dcb0e…` (block-level md5s computed
/// from the gate-4 file, derived.md §11).
#[test]
fn c03_earlier_blocks_are_byte_identical_to_gate_4() {
    assert_eq!(md5_hex(b""), "d41d8cd98f00b204e9800998ecf8427e");
    assert_eq!(md5_hex(b"abc"), "900150983cd24fb0d6963f7d28e17f72");
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/grid.rs");
    let text = fs::read_to_string(path).expect("conformance: grid.rs");
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let at = |marker: &str| {
        lines
            .iter()
            .position(|l| l.starts_with(marker))
            .unwrap_or_else(|| panic!("conformance: no {marker}"))
    };
    let (apps, synth, camp) = (
        at("// P5-APPS — "),
        at("// P5-SYNTH — "),
        at("// P5-CAMPAIGN — "),
    );
    // Each block starts at the `// ====` line above its title.
    let block = |a: usize, b: usize| lines[a - 1..b - 1].concat();
    assert_eq!(
        md5_hex(block(apps, synth).as_bytes()),
        "543b5315f824e994d3e86fff058db0cf"
    );
    assert_eq!(
        md5_hex(lines[synth - 1..camp - 2].concat().as_bytes()),
        "9f2dcb0e484e5411b70b51544f9fb729",
        "conformance: the P5-SYNTH block (its trailing blank line excluded)"
    );
    assert_eq!(
        md5_hex(lines[..camp - 2].concat().as_bytes()),
        "fee6f42a5263760a22beedebda3ee6cf",
        "conformance: everything before the P5-CAMPAIGN block = the gate-4 file"
    );
}

/// C3/criterion 3: each corner's `EVAL_ONLY` glob selects exactly its four
/// `Ltr` rep-0 X1 keys, one per engine.
#[test]
fn c03_corner_globs_select_their_ltr_rep0_keys() {
    for (fx, _) in APPS_CORNERS {
        let glob = format!("{fx}|*/Ltr/*|0|*");
        let hit: Vec<&String> = ks("X1").iter().filter(|k| glob_match(&glob, k)).collect();
        assert_eq!(hit.len(), 4, "conformance: {glob}: {hit:?}");
        let engines: BTreeSet<&str> = hit
            .iter()
            .map(|k| k.split('|').nth(1).unwrap().split('/').next().unwrap())
            .collect();
        assert_eq!(engines.len(), 4);
        for k in hit {
            let parts: Vec<&str> = k.split('|').collect();
            assert_eq!(parts[0], fx);
            assert_eq!(parts[2], "0");
            assert!(parts[1].split('/').nth(1) == Some("Ltr"));
        }
        // Nothing of another spec is selected through X1.
        assert!(!ks("X2").iter().any(|k| glob_match(&glob, k)));
    }
}

// =========================================================================
// Criterion 4 — twins
// =========================================================================

/// Criterion 4: every X2 row whose fixture is in C4's twin table carries the
/// twin's key under X1's configuration (same engine, selector, rep; the twin's
/// tier; timed), and that key **is an X1 key**; every other X2 row is twinless.
#[test]
fn c04_twin_keys_are_x1_keys() {
    let d = derived();
    let mut with = 0;
    for r in &spec("X2").rows {
        match d.twins.get(&r.fixture) {
            Some(t) => {
                let want = key_of(
                    t,
                    &x1_config(r.config.engine, r.config.selector).label(),
                    r.rep,
                    "default",
                    RunKind::Timed,
                    prof(),
                );
                assert_eq!(r.twin_key, want, "conformance: {}", r.fixture);
                assert!(
                    ks("X1").contains(&r.twin_key),
                    "conformance: {} → {}",
                    r.fixture,
                    r.twin_key
                );
                with += 1;
            }
            None => assert!(
                r.twin_key.is_empty(),
                "conformance: {} is twinless",
                r.fixture
            ),
        }
    }
    // Every one of the derived 122 table entries is an X2 point (T1 fixed).
    assert_eq!(with, 122 * 36);
    let twinless: BTreeSet<&String> = spec("X2")
        .rows
        .iter()
        .filter(|r| r.twin_key.is_empty())
        .map(|r| &r.fixture)
        .collect();
    // The twinless X2 points are exactly the derived 56 §6/corpus points
    // (2 016 rows); T2, T3, T8 fixed.
    let want: BTreeSet<&String> = d.twinless.iter().collect();
    assert_eq!(twinless, want, "conformance: the twinless X2 points");
    assert_eq!(
        spec("X2")
            .rows
            .iter()
            .filter(|r| r.twin_key.is_empty())
            .count(),
        56 * 36
    );
    // The twin lines hold every twin point.
    for t in d.twins.values() {
        assert!(
            points_of("X1").contains(t),
            "conformance: twin {t} is an X1 point"
        );
    }
}

/// Criterion 4: `pair-swap` rows are X1 rows; no X2 row of A2's mutants at
/// `(1,1)` except silent-put; no `rr`×A4a X2 row at `q = 1`.
#[test]
fn c04_controls_in_x1_and_the_excluded_points() {
    let x1 = points_of("X1");
    let x2 = points_of("X2");
    let ps: Vec<&String> = x1.iter().filter(|f| f.contains("/pair-swap-")).collect();
    assert_eq!(ps.len(), 9);
    assert!(!x2.iter().any(|f| f.contains("/pair-swap-")));
    for v in ["early-ack", "stale-get"] {
        assert!(!x2.contains(&a2(v, 1, 1)), "conformance: {v} (1,1)");
    }
    assert!(!x2.contains(&a2("misroute", 1, 1)));
    assert!(x2.contains(&a2("silent-put", 1, 1)));
    assert!(!x2
        .iter()
        .any(|f| f.starts_with("apps/a4/rr/a4a/") && f.contains("q1")));
    for f in x1.iter().filter(|f| f.starts_with("apps/")) {
        assert!(
            !f.contains("/eager/") && !f.contains("/early-ack/") && !f.contains("/drop/"),
            "conformance: {f}"
        );
    }
}

/// Criterion 4: every application point's expected verdict is total
/// (derived.md §8: every X2 point reports, every X1 point conforms; none
/// vacuous) and the lead's addendum lists exactly the six classes of points
/// the earlier tables do not, with the derived verdicts.
#[test]
fn c04_expected_verdicts_are_total() {
    let text = read_plan("log/dev/P5-APPS.expected.md");
    let add = text
        .split("## Addendum for `P5-CAMPAIGN`")
        .nth(1)
        .expect("conformance: the gate-2 addendum");
    let tables = md_tables(add);
    let rows = &tables.first().expect("conformance: the addendum's table").1;
    let got: BTreeMap<String, String> = rows
        .iter()
        .map(|r| {
            let verdict = if r[2].contains("reports") {
                "reports"
            } else if r[2].contains("conforms") {
                "conforms"
            } else {
                "?"
            };
            (format!("{} @ {}", r[0], r[1]), verdict.to_owned())
        })
        .collect();
    let want: BTreeMap<String, String> = [
        ("`early-ack` (`pb-br`) @ `(1, 3)`", "reports"),
        ("`stale-get` (`pb`) @ `(1, 3)`", "reports"),
        ("`drop` (`rr`×A4b) @ `(3, 1, 2)`", "reports"),
        ("`drop` @ `(2, 2, 2)`", "reports"),
        ("`drop` @ `(2, 1, 3)`", "reports"),
        (
            "`pair-swap-hash`×{A4a, A4b}, `pair-swap-rr`×A4b @ `(2, 2, 2)`",
            "conforms",
        ),
        ("`sh` (`s = 2`) @ `(2, 2, 2)`, `(3, 2, 2)`", "conforms"),
    ]
    .iter()
    .map(|(a, b)| ((*a).to_owned(), (*b).to_owned()))
    .collect();
    assert_eq!(
        got, want,
        "conformance: the addendum's verdicts = derived.md §8"
    );
    assert!(add.contains("None of these is vacuous"));
    // Totality over the grid: the derived side of every application point.
    let d = derived();
    for p in apps_grid() {
        let reports = !(p.variant == "conforming" || p.variant.starts_with("control:"));
        assert_eq!(
            reports,
            d.apps_x2.contains(&p.fixture),
            "conformance: {}",
            p.fixture
        );
    }
}

/// C4: RQ2(b)'s identities on a fixture with a known Spec count
/// (`ex:naive/k3/enc1`, `|Graphs(Spec)| = 3! = 6`; hand-count size, lean path):
/// every failing unbudgeted sweep tests `|Graphs(Spec)|` graphs, every
/// `Budgeted` sweep tests `B`, so `Σ sizes − failing·6 − budgeted·B` is the
/// successful sweeps' total, each at most 6.
#[test]
fn c04_rq2b_identities_on_a_known_spec_count() {
    let f =
        fixture_by_name("ex:naive/k3/enc1").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let cell = |row: &crate::conformance::grid::Row, c: &str| -> String {
        row.iter()
            .find(|(k, _)| *k == c)
            .map(|(_, v)| v.clone())
            .unwrap_or_default()
    };
    let list = |s: &str| -> Vec<usize> {
        s.trim_matches(|c| c == '[' || c == ']')
            .split(',')
            .filter(|x| !x.trim().is_empty())
            .map(|x| x.trim().parse().unwrap())
            .collect()
    };
    let stateful =
        match run_row_in_process(&f, &x1_config(GridEngine::Stateful, Selector::Ltr), false) {
            GridEnd::Ok(r) => row_of(&r),
            _ => panic!("conformance: stateful run"),
        };
    let spec_n: usize = cell(&stateful, "spec_graphs").parse().unwrap();
    assert_eq!(spec_n, 6);
    // Complete-first, exhaustive.
    let cf = match run_row_in_process(
        &f,
        &x1_config(GridEngine::CompleteFirst, Selector::Ltr),
        false,
    ) {
        GridEnd::Ok(r) => row_of(&r),
        _ => panic!("conformance: complete-first run"),
    };
    let sizes = list(&cell(&cf, "sweep_sizes"));
    let failing: usize = cell(&cf, "sweeps_failing").parse().unwrap();
    let successful: usize = cell(&cf, "sweeps_successful").parse().unwrap();
    assert!(failing > 0);
    assert_eq!(
        sizes.len(),
        failing + successful + cell(&cf, "sweeps_aborted").parse::<usize>().unwrap()
    );
    assert!(sizes.iter().filter(|s| **s == spec_n).count() >= failing);
    assert!(sizes.iter().all(|s| *s <= spec_n));
    let succ_total = sizes.iter().sum::<usize>() - failing * spec_n;
    assert!(succ_total >= successful && succ_total <= successful * spec_n);
    // Gated, `Budget(2)`, exhaustive: budgeted sweeps test exactly B = 2.
    let cfg = x1_config(GridEngine::Gated, Selector::Ltr)
        .gated(GatedMode::Exhaustive, GatePolicy::Budget(2));
    let g = match run_row_in_process(&f, &cfg, false) {
        GridEnd::Ok(r) => row_of(&r),
        _ => panic!("conformance: gated run"),
    };
    let gs = list(&cell(&g, "gate_sweep_sizes"));
    let gf: usize = cell(&g, "gate_sweeps_failing").parse().unwrap();
    let gb: usize = cell(&g, "gate_sweeps_budgeted").parse().unwrap();
    let gok: usize = cell(&g, "gate_sweeps_successful").parse().unwrap();
    let gab: usize = cell(&g, "gate_sweeps_aborted").parse().unwrap();
    assert_eq!(gab, 0, "conformance: exhaustive: no aborted gate sweep");
    assert_eq!(gs.len(), gf + gb + gok);
    note!("c04 rq2b: cf sizes {sizes:?} failing {failing}; gated sizes {gs:?} failing {gf} budgeted {gb} ok {gok}");
    assert!(gs.iter().all(|s| *s <= spec_n));
    assert!(gs.iter().filter(|s| **s == 2).count() >= gb);
    let rest = gs.iter().sum::<usize>() as i64 - (gf * spec_n) as i64 - (gb * 2) as i64;
    assert!(
        rest >= gok as i64 && rest <= (gok * 2) as i64,
        "conformance: successful sweeps stop at ≤ B under Budget(B)"
    );
}

// =========================================================================
// Criterion 5 — the coverage map
// =========================================================================

/// `(spec, glob)` pairs of `coverage.md`'s glob tables (a spec cell with no
/// X-name, the criterion-7 baselines, is returned as "baseline").
fn coverage_globs() -> Vec<(String, String)> {
    let text = read_plan("log/dev/P5-CAMPAIGN.coverage.md");
    let ticks = |s: &str| -> Vec<String> {
        s.split('`')
            .enumerate()
            .filter(|(i, _)| i % 2 == 1)
            .map(|(_, t)| t.to_owned())
            .collect()
    };
    let xname = |s: &str| -> Option<String> {
        s.split(|c: char| !c.is_ascii_alphanumeric())
            .find(|w| {
                w.starts_with('X') && w.len() >= 2 && w[1..2].chars().all(|c| c.is_ascii_digit())
            })
            .map(str::to_owned)
    };
    let mut out = Vec::new();
    for (hdr, rows) in md_tables(&text) {
        let Some(gi) = col(&hdr, "glob") else {
            continue;
        };
        let si = 1; // `spec` / `read from`
        for r in rows {
            let specs_g: Vec<&str> = r[si].split(" / ").collect();
            let globs_g: Vec<&str> = r[gi].split(" / ").collect();
            for (j, g) in globs_g.iter().enumerate() {
                let sp = if specs_g.len() == globs_g.len() {
                    specs_g[j]
                } else {
                    specs_g[0]
                };
                let name = xname(sp).unwrap_or_else(|| "baseline".to_owned());
                for t in ticks(g) {
                    if t.contains('|') {
                        out.push((name.clone(), t));
                    }
                }
            }
        }
    }
    out
}

/// Criterion 5: every glob of the map selects ≥ 1 key of its spec.
/// **Fails while T1 stands**: E2's `synth/reset-ctl/*|Gated/*` names X1V, which
/// holds no reset-ctl key. (Ignored while it stands.)
#[test]
fn t1_c05_every_coverage_glob_selects_a_key_of_its_spec() {
    let mut bad = Vec::new();
    for (sp, g) in coverage_globs() {
        if sp == "baseline" {
            continue;
        }
        if !ks(&sp).iter().any(|k| glob_match(&g, k)) {
            bad.push(format!("{sp}: {g}"));
        }
    }
    assert!(bad.is_empty(), "conformance: {bad:#?}");
}

/// Criterion 5 (the parts T1 does not touch): the map parses into ≥ 40
/// (spec, glob) pairs; every glob but E2's reset-ctl one selects ≥ 1 key of its
/// spec; the baselines' globs name `baseline` rows; every §6 key of X1/X2 is
/// named by a glob of its own spec; every synthetic/application key is on its
/// family's line (a series); the "not run" cells are listed.
#[test]
fn c05_coverage_map_names_every_key_and_the_cells_not_run() {
    let globs = coverage_globs();
    assert!(globs.len() >= 40, "conformance: {}", globs.len());
    for (sp, g) in &globs {
        if sp == "baseline" {
            assert!(g.contains("|baseline|"), "conformance: {g}");
            continue;
        }
        assert!(
            ks(sp).iter().any(|k| glob_match(g, k)),
            "conformance: {sp}: {g} selects nothing"
        );
    }
    // E2's control glob selects X1V's gated reset-ctl rows (T1 fixed): 30
    // points × 3 selectors × 3 reps.
    let e2 = ks("X1V")
        .iter()
        .filter(|k| glob_match("synth/reset-ctl/*|Gated/*", k))
        .count();
    assert_eq!(e2, 30 * 9, "conformance: E2's reset-ctl glob");
    for name in ["X1", "X2", "X1V", "X3A"] {
        let mine: Vec<&String> = globs
            .iter()
            .filter(|(s, _)| s == name)
            .map(|(_, g)| g)
            .collect();
        for r in &spec(name).rows {
            // X3A is named as a whole by (vii)'s memo-off and budget cells.
            if r.family == "sec6" && name != "X3A" {
                let k = r.key(prof());
                assert!(
                    mine.iter().any(|g| glob_match(g, &k)),
                    "conformance: {name}: {k} unnamed"
                );
            } else {
                assert!(
                    r.series.is_some(),
                    "conformance: {name}: {} has no line",
                    r.fixture
                );
            }
        }
    }
    let text = read_plan("log/dev/P5-CAMPAIGN.coverage.md");
    // (vii): the run grid's cells name X1, X1V, X2 and X3A.
    let grid_specs: BTreeSet<String> = md_tables(&text)
        .into_iter()
        .filter(|(h, _)| h.first().map(String::as_str) == Some("cell"))
        .flat_map(|(_, rows)| {
            rows.into_iter().map(|r| {
                r[1].split_whitespace()
                    .next()
                    .unwrap_or_default()
                    .trim_matches(',')
                    .to_owned()
            })
        })
        .collect();
    assert_eq!(
        grid_specs,
        set(["X1", "X2", "X3A"]),
        "conformance: (vii)'s first-named specs"
    );
    assert!(text.contains("| X1, X1V |"), "conformance: (vii) names X1V");
    let flat: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    for cell in [
        "gated `Exhaustive` + `stop`",
        "`Budget(B)` × first-failure",
        "memo-off × first-report",
        "memo-off × non-`Ltr` outside S1 and A1",
        "`Never` × first-failure",
        "the precheck arms",
    ] {
        assert!(
            flat.contains(cell),
            "conformance: not-run cell missing: {cell}"
        );
    }
}

/// Exhaustive verdicts and differential reach from the records: every table of
/// `P4-DIFF.tables.md`, `P5-APPS.pilot.md`, `P5-SYNTH.pilot.md` and the contract
/// store `rows-test.csv` with a fixture, an engine and a `reports` column; a
/// row counts when it is exhaustive (`stop=false`, gated `Exhaustive`) and
/// completed (`StateSpaceExhausted` where an end column exists).
struct Record {
    verdict: BTreeMap<String, bool>,
    reach: BTreeSet<(String, String)>,
    conflicts: BTreeSet<String>,
}

fn record() -> &'static Record {
    static R: OnceLock<Record> = OnceLock::new();
    R.get_or_init(|| {
        let mut rec = Record {
            verdict: BTreeMap::new(),
            reach: BTreeSet::new(),
            conflicts: BTreeSet::new(),
        };
        let add = |fx: &str, eng: &str, reports: usize, rec: &mut Record| {
            if !["Enumerator", "Stateful", "CompleteFirst", "Gated"].contains(&eng) {
                return;
            }
            let v = reports > 0;
            if let Some(old) = rec.verdict.insert(fx.to_owned(), v) {
                if old != v {
                    rec.conflicts.insert(fx.to_owned());
                }
            }
            rec.reach.insert((fx.to_owned(), eng.to_owned()));
        };
        for file in [
            "log/dev/P4-DIFF.tables.md",
            "log/dev/P5-APPS.pilot.md",
            "log/dev/P5-SYNTH.pilot.md",
        ] {
            for (hdr, rows) in md_tables(&read_plan(file)) {
                let fx = col(&hdr, "fixture").or_else(|| col(&hdr, "pilot_fixture"));
                let (Some(fx), Some(e), Some(rp)) = (fx, col(&hdr, "engine"), col(&hdr, "reports"))
                else {
                    continue;
                };
                let (st, gm, end, iend) = (
                    col(&hdr, "stop"),
                    col(&hdr, "gated_mode"),
                    col(&hdr, "end"),
                    col(&hdr, "impl_end"),
                );
                for r in rows {
                    let g = |i: Option<usize>| i.and_then(|i| r.get(i)).map(String::as_str);
                    if g(st).is_some_and(|s| s != "false")
                        || g(gm).is_some_and(|s| s != "Exhaustive")
                    {
                        continue;
                    }
                    // `Gated (replay window: F83; …)`: the engine is the first word.
                    let eng = g(Some(e))
                        .and_then(|x| x.split_whitespace().next())
                        .unwrap_or_default();
                    if eng == "Enumerator" && g(end).is_some_and(|s| s != "StateSpaceExhausted") {
                        continue;
                    }
                    if g(iend).is_some_and(|s| !s.is_empty() && s != "StateSpaceExhausted") {
                        continue;
                    }
                    let Some(Ok(n)) = g(Some(rp)).map(str::parse::<usize>) else {
                        continue;
                    };
                    add(g(Some(fx)).unwrap_or_default(), eng, n, &mut rec);
                }
            }
        }
        let rows = read_rows(&plan().join("log/eval/rows-test.csv")).unwrap_or_default();
        for r in rows {
            if r["run_kind"] == "contract"
                && r["stop"] == "false"
                && r["gated_mode"] == "Exhaustive"
                && r["end_class"] == "ok"
            {
                if let Ok(n) = r["reports"].parse() {
                    add(&r["fixture"].clone(), &r["engine"].clone(), n, &mut rec);
                }
            }
        }
        rec
    })
}

fn reach(fx: &str, e: GridEngine) -> bool {
    record().reach.contains(&(fx.to_owned(), format!("{e:?}")))
}

/// Criterion 5: the §6 sides — the tester's lists (derived.md §6) equal Part
/// 6's exhaustive verdicts as recorded, on every §6 fixture the records
/// decide; the records hold no conflicting verdicts.
#[test]
fn c05_section6_sides_are_part_6s() {
    let rec = record();
    assert!(
        rec.conflicts.is_empty(),
        "conformance: conflicting exhaustive verdicts: {:?}",
        rec.conflicts
    );
    let (cc, cv) = corpus_sides();
    let conf: Vec<String> = PAPER_CONFORMING
        .iter()
        .map(|s| (*s).to_owned())
        .chain(tf_conforming())
        .chain(cc)
        .collect();
    let viol: Vec<String> = PAPER_VIOLATING
        .iter()
        .map(|s| (*s).to_owned())
        .chain(tf_violating())
        .chain(cv)
        .chain((2..=7).map(|k| format!("ex:naive/e2/k{k}")))
        .collect();
    let mut decided = 0;
    for f in &conf {
        if let Some(v) = rec.verdict.get(f) {
            assert!(!v, "conformance: {f} conforms in Part 6");
            decided += 1;
        }
    }
    for f in &viol {
        if let Some(v) = rec.verdict.get(f) {
            assert!(v, "conformance: {f} violates in Part 6");
            decided += 1;
        }
    }
    note!("c05: {decided} §6 fixtures decided by the records");
    // Every §6 fixture except the never-run ones (`e2` k ≥ 5, `2pc/leader/split/n4`).
    assert_eq!(decided, conf.len() + viol.len() - 3 - 1);
}

/// Criterion 5: the corpus under all three selectors — 70 fixtures × 36 =
/// 2 520 rows across X1 and X2.
#[test]
fn c05_corpus_rows_under_all_three_selectors() {
    let mut n = 0;
    let mut sels = BTreeSet::new();
    for name in ["X1", "X2"] {
        for r in spec(name)
            .rows
            .iter()
            .filter(|r| r.fixture.starts_with("corpus/"))
        {
            n += 1;
            sels.insert(format!("{:?}", r.config.selector));
        }
    }
    assert_eq!(n, 2_520);
    assert_eq!(sels.len(), 3);
}

// =========================================================================
// Criterion 6 — differential reach
// =========================================================================

fn reach_counts(
    points: &BTreeSet<String>,
    engines: &[GridEngine],
    sels: usize,
    reps: usize,
) -> (usize, usize) {
    let mut inside = 0;
    let mut all = 0;
    for f in points {
        for &e in engines {
            all += sels * reps;
            if reach(f, e) {
                inside += sels * reps;
            }
        }
    }
    (inside, all - inside)
}

/// Criterion 6: the reach predicate (fixture, engine) from the records; the
/// derived specs' keys inside/outside reach equal derived.md §9's figures; the
/// landed specs' counts (reported); `ex:naive` `k ∈ {6,7}`'s X2 rows on the
/// sweeping engines (72) all outside, on the enumerator and stateful inside.
#[test]
fn c06_reach_predicate_and_counts_per_spec() {
    let d = derived();
    let sw = [GridEngine::CompleteFirst, GridEngine::Gated];
    assert_eq!(reach_counts(&d.x1, &ENGINES, 3, 3), (5_076, 4_932));
    assert_eq!(reach_counts(&d.x1v, &sw, 3, 3), (558, 936));
    assert_eq!(reach_counts(&d.x2, &ENGINES, 3, 3), (4_077, 2_331));
    assert_eq!(reach_counts(&d.x2, &ENGINES, 3, 1), (1_359, 777));
    assert_eq!(
        reach_counts(&d.x2, &[GridEngine::Stateful], 1, 1),
        (116, 62)
    );
    let x3a_in = reach_counts(&d.x1, &[GridEngine::Enumerator], 1, 3).0
        + reach_counts(&d.s1a1, &[GridEngine::Enumerator], 2, 3).0;
    assert_eq!(x3a_in, 522);
    let mut sweeping_out = 0;
    for r in &spec("X2").rows {
        if ["k6", "k7"]
            .iter()
            .any(|k| r.fixture.starts_with(&format!("ex:naive/{k}/")))
        {
            let e = r.config.engine;
            if matches!(e, GridEngine::CompleteFirst | GridEngine::Gated) {
                assert!(!reach(&r.fixture, e), "conformance: {} {e:?}", r.fixture);
                sweeping_out += 1;
            } else {
                assert!(reach(&r.fixture, e), "conformance: {} {e:?}", r.fixture);
            }
        }
    }
    assert_eq!(sweeping_out, 72);
    for s in specs() {
        let inside = s
            .rows
            .iter()
            .filter(|r| reach(&r.fixture, r.config.engine))
            .count();
        note!(
            "c06 as landed: {} inside {} outside {}",
            s.name,
            inside,
            s.rows.len() - inside
        );
    }
}

/// Criterion 6's obligation on rows inside reach, checked where it can be
/// before the campaign: every landed X1 point decided by the records conforms
/// there and every X2 point violates there. **Fails while T1–T3 stand** (the
/// misplaced points disagree with their exhaustive runs). Ignored while it
/// stands; measured: the reset-ctl, `DecoupleImpl` and `conf/n4` points.
#[test]
fn t1_t2_t3_c06_sides_agree_with_the_exhaustive_runs() {
    let rec = record();
    let mut bad = Vec::new();
    for (name, want) in [("X1", false), ("X2", true)] {
        for f in points_of(name) {
            if let Some(v) = rec.verdict.get(&f) {
                if *v != want {
                    bad.push(format!("{name}: {f}"));
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: {} disagreements: {bad:#?}",
        bad.len()
    );
}

// =========================================================================
// Criterion 7 — the frozen tables against the grids
// =========================================================================

/// `x ∈ {…}` sets in `s`, in order, as (name, values); `a..b` ranges expanded,
/// symbolic members (`m/2`) make the set symbolic (skipped).
fn sets_in(s: &str) -> Vec<(String, Option<BTreeSet<i64>>)> {
    let mut out = Vec::new();
    let mut rest = s;
    while let Some(i) = rest.find(" ∈ {") {
        let name: String = rest[..i]
            .chars()
            .rev()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect::<String>()
            .chars()
            .rev()
            .collect();
        let body_start = i + " ∈ {".len();
        let end = rest[body_start..]
            .find('}')
            .map(|j| body_start + j)
            .unwrap_or(rest.len());
        let body = &rest[body_start..end];
        let mut vals = Some(BTreeSet::new());
        for item in body.split(',').map(str::trim) {
            if let Some((a, b)) = item.split_once("..") {
                match (a.parse::<i64>(), b.parse::<i64>()) {
                    (Ok(a), Ok(b)) => vals.as_mut().map(|v| v.extend(a..=b)),
                    _ => vals.take().map(|_| ()),
                };
            } else if let Ok(x) = item.parse::<i64>() {
                if let Some(v) = vals.as_mut() {
                    v.insert(x);
                }
            } else {
                vals = None;
            }
        }
        out.push((name, vals));
        rest = &rest[end.min(rest.len())..];
    }
    out
}

/// Criterion 7: `models.md`'s predeclared grid table (parsed) against
/// `synth_grid()` — per family the point count, every numeric knob set and
/// the line count — and its gate-4 A-series note (parsed) against
/// `apps_grid()`: each model's three-or-fewer axis sets and the four corners.
#[test]
fn c07_models_md_tables_match_the_grids() {
    let text = read_plan("log/dev/P5-SYNTH.models.md");
    let grid = synth_grid();
    let fam = |s: &str| match s {
        "S1" => "naive",
        "S2" => "share",
        "S3" => "commit",
        "S4" => "chain",
        "S5" => "reset",
        "S6" => "width",
        _ => panic!("conformance: family {s}"),
    };
    let axis = |f: &str, name: &str| -> usize {
        match (f, name) {
            (_, "k" | "m" | "n" | "d" | "w") => 0,
            (_, "enc" | "s" | "c" | "j") => 1,
            _ => panic!("conformance: axis {name}"),
        }
    };
    let tables = md_tables(&text);
    let (_, rows) = tables
        .iter()
        .find(|(h, _)| h.iter().any(|c| c.starts_with("lines")))
        .expect("conformance: the predeclared grid table");
    assert_eq!(rows.len(), 6);
    let mut total_lines = 0;
    for r in rows {
        let f = fam(&r[0]);
        let pts: Vec<&SynthPoint> = grid.iter().filter(|p| p.family == f && p.in_grid).collect();
        let count: usize = r[1].rsplit("= ").next().unwrap().trim().parse().unwrap();
        assert_eq!(pts.len(), count, "conformance: {f}: points");
        for (name, vals) in sets_in(&r[1]) {
            let Some(vals) = vals else { continue };
            let ax = axis(f, &name);
            let got: BTreeSet<i64> = pts.iter().filter_map(|p| p.k[ax]).collect();
            assert_eq!(got, vals, "conformance: {f}: {name}");
        }
        let nlines: usize = r[2]
            .rsplit('(')
            .next()
            .unwrap()
            .trim_end_matches(')')
            .parse()
            .unwrap();
        let lines: BTreeSet<&str> = pts.iter().map(|p| p.line).collect();
        assert_eq!(lines.len(), nlines, "conformance: {f}: lines");
        total_lines += nlines;
    }
    assert_eq!(total_lines, 24);
    // The A-series note.
    let note_start = text
        .find("**D5's A-series extension")
        .expect("conformance: the D5 note");
    let note_text: String = text[note_start..]
        .lines()
        .take_while(|l| !l.trim().is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    let mut per_model: BTreeMap<String, Vec<BTreeSet<i64>>> = BTreeMap::new();
    let corner_part = note_text
        .split("four joint corners")
        .nth(1)
        .expect("conformance: corners");
    let lines_part = note_text.split("four joint corners").next().unwrap();
    for seg in lines_part.split("; A").skip(1) {
        let model = format!("a{}", &seg[..1]);
        let sets: Vec<BTreeSet<i64>> = sets_in(seg).into_iter().filter_map(|(_, v)| v).collect();
        per_model.insert(model, sets);
    }
    // A1's segment starts the note ("— A1 `correct` …").
    let a1_seg = lines_part.split("; A2").next().unwrap();
    per_model.insert(
        "a1".to_owned(),
        sets_in(a1_seg).into_iter().filter_map(|(_, v)| v).collect(),
    );
    let ag = apps_grid();
    let sizes = |line: &str| -> BTreeSet<i64> {
        ag.iter()
            .filter(|p| p.line == line)
            .map(|p| p.size)
            .collect()
    };
    let want: BTreeMap<String, Vec<BTreeSet<i64>>> = [
        ("a1", vec![sizes("a1/correct/r=1"), sizes("a1/correct/n=2")]),
        ("a2", vec![sizes("a2/pb/q=1"), sizes("a2/pb/k=1")]),
        ("a3", vec![sizes("a3/fifo/q=1"), sizes("a3/fifo/k=2")]),
        (
            "a4",
            vec![
                sizes("a4/hash-a4a/q=1,m=2"),
                sizes("a4/hash-a4a/k=2,m=2"),
                sizes("a4/hash-a4a/k=2,q=1"),
            ],
        ),
    ]
    .into_iter()
    .map(|(a, b)| (a.to_owned(), b))
    .collect();
    assert_eq!(
        per_model, want,
        "conformance: models.md's D5 note vs apps_grid()"
    );
    // Corners: the tuples after "four joint corners".
    let tuples: Vec<Vec<i64>> = corner_part
        .split('(')
        .skip(1)
        .filter_map(|t| {
            let body = t.split(')').next()?;
            let v: Vec<i64> = body
                .split(',')
                .filter_map(|x| x.trim().parse().ok())
                .collect();
            (v.len() >= 2).then_some(v)
        })
        .take(4)
        .collect();
    let corner_k: Vec<Vec<i64>> = APPS_CORNERS
        .iter()
        .map(|(f, _)| {
            ag.iter()
                .find(|p| p.fixture == *f)
                .unwrap()
                .k
                .iter()
                .flatten()
                .copied()
                .collect()
        })
        .collect();
    assert_eq!(tuples, corner_k, "conformance: the four corners");
}

// =========================================================================
// Criterion 9 — the read-time checker on a constructed store
// =========================================================================

/// One finding of the tester's read-time checker.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
enum Finding {
    Missing(String),
    Duplicate(String),
    Dirty(String),
    Mixed(String),
    VerdictDisagrees(String),
    BudgetedOutOfOrder(String),
    FirstReportOutsideSpecWords(String),
    /// A growing first report (`growth: growing`): classifiable only inside
    /// C6's reach, never genuine from `spec_words` (round 01 M1).
    UnclassifiedGrowing(String),
    /// A visible-error first report (`cause: visible-error`): genuine by
    /// construction, no family needed (IMPL-PLAN §1/§6 case (3); round 02 m1).
    GenuineVisibleError(String),
    /// An export whose words or statuses could not be computed (`error`).
    UnclassifiedError(String),
    /// A visible-error report whose Spec has no assertion-safety evidence in
    /// the store (round 03 m4): unclassified.
    UnclassifiedVisibleError(String),
}

/// The checker (criteria 8–9): planned keys present; no key twice; no `+dirty`
/// commit; no mixed repetition set; every row inside reach agrees with its
/// exhaustive verdict; `gate_sweeps_budgeted` non-increasing in `B` per
/// (fixture, selector); every X2P first report classified against its fixture's
/// X2S `spec_words.json` (a word/status pair outside it is flagged — genuine).
/// Same-Spec substitutes for assertion-safety evidence where a fixture has no
/// X2S row (round 03 m4). **Empty by derivation**: the reviewer named
/// `2pc/leader/conf/n4` and `ndk3/conf` for the two X2S-excluded fixtures, but
/// `two_pc_fixtures` builds the leader `conf` pair at `n ≤ 3` only, and
/// `ndk3/bad_A`'s Spec is `ndk3_bad_a()`, not `ndk3/conf`'s `ndk_conf(3)` (its
/// Impl is) — so neither has a same-Spec fixture, and their visible-error
/// reports stay unclassified.
const SAME_SPEC: &[(&str, &str)] = &[];

fn check_store(
    store_dir: &Path,
    rows: &[BTreeMap<String, String>],
    planned: &BTreeSet<String>,
) -> BTreeSet<Finding> {
    // Fixtures whose Spec an exhaustive stateful row shows assertion-safe.
    let safe_spec: BTreeSet<&str> = rows
        .iter()
        .filter(|r| {
            r.get("engine").map(String::as_str) == Some("Stateful")
                && r.get("stop").map(String::as_str) == Some("false")
                && r.get("end_class").map(String::as_str) == Some("ok")
                && r.get("spec_errors").map(String::as_str) == Some("0")
        })
        .map(|r| r["fixture"].as_str())
        .collect();
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for r in rows {
        let k = r["key"].clone();
        if !seen.insert(k.clone()) {
            out.insert(Finding::Duplicate(k.clone()));
        }
        if r["commit"].ends_with("+dirty") {
            out.insert(Finding::Dirty(k.clone()));
        }
    }
    for k in planned {
        if !seen.contains(k) {
            out.insert(Finding::Missing(k.clone()));
        }
    }
    let rep_sets: BTreeSet<String> = rows
        .iter()
        .filter_map(|r| {
            let p: Vec<&str> = r["key"].split('|').collect();
            (p.len() == 6).then(|| format!("{}|{}|{}|{}", p[0], p[1], p[3], p[4]))
        })
        .collect();
    for s in rep_sets {
        if mixed_of(rows, &s) {
            out.insert(Finding::Mixed(s));
        }
    }
    let rec = record();
    for r in rows {
        if r["end_class"] != "ok" {
            continue;
        }
        let (f, e) = (&r["fixture"], &r["engine"]);
        if rec.reach.contains(&(f.clone(), e.clone())) {
            if let (Some(v), Ok(n)) = (rec.verdict.get(f), r["reports"].parse::<usize>()) {
                if (n > 0) != *v {
                    out.insert(Finding::VerdictDisagrees(r["key"].clone()));
                }
            }
        }
    }
    // (fixture, selector) → [(B, gate_sweeps_budgeted, key)].
    type Sweep = Vec<(usize, usize, String)>;
    let mut budget: BTreeMap<(String, String), Sweep> = BTreeMap::new();
    for r in rows {
        if let Some(b) = r["policy"]
            .strip_prefix("Budget(")
            .and_then(|s| s.strip_suffix(')'))
        {
            if let (Ok(b), Ok(n)) = (
                b.parse::<usize>(),
                r["gate_sweeps_budgeted"].parse::<usize>(),
            ) {
                budget
                    .entry((r["fixture"].clone(), r["selector"].clone()))
                    .or_default()
                    .push((b, n, r["key"].clone()));
            }
        }
    }
    for v in budget.values_mut() {
        v.sort();
        for w in v.windows(2) {
            if w[1].1 > w[0].1 {
                out.insert(Finding::BudgetedOutOfOrder(w[1].2.clone()));
            }
        }
    }
    let read_json = |rel: &str, file: &str| -> Option<serde_json::Value> {
        let t = fs::read_to_string(store_dir.join(rel).join(file)).ok()?;
        serde_json::from_str(&t).ok()
    };
    let mut spec_words: BTreeMap<String, Vec<serde_json::Value>> = BTreeMap::new();
    for r in rows {
        if let Some(v) = read_json(&r["run_dir"], "spec_words.json") {
            let gs = v["spec_graphs"].as_array().cloned().unwrap_or_default();
            spec_words.insert(r["fixture"].clone(), gs);
        }
    }
    for r in rows {
        if let Some(fr) = read_json(&r["run_dir"], "first_report.json") {
            if fr.get("error").is_some() {
                out.insert(Finding::UnclassifiedError(r["key"].clone()));
                continue;
            }
            if fr["cause"] == "visible-error" {
                // §6 case (3): genuine only when the Spec is shown
                // assertion-safe — an exhaustive stateful row (the fixture's
                // X2S row, or a same-Spec fixture's per `SAME_SPEC`) ended `ok`
                // with no Spec error (round 03 m4).
                let evidence = std::iter::once(r["fixture"].as_str())
                    .chain(
                        SAME_SPEC
                            .iter()
                            .filter(|(f, _)| *f == r["fixture"])
                            .map(|(_, t)| *t),
                    )
                    .any(|f| safe_spec.contains(f));
                out.insert(if evidence {
                    Finding::GenuineVisibleError(r["key"].clone())
                } else {
                    Finding::UnclassifiedVisibleError(r["key"].clone())
                });
                continue;
            }
            if fr["growth"] != "complete" {
                out.insert(Finding::UnclassifiedGrowing(r["key"].clone()));
                continue;
            }
            if let Some(gs) = spec_words.get(&r["fixture"]) {
                let inside = gs
                    .iter()
                    .any(|g| g["words"] == fr["words"] && g["statuses"] == fr["statuses"]);
                if !inside {
                    out.insert(Finding::FirstReportOutsideSpecWords(r["key"].clone()));
                }
            }
        }
    }
    out
}

/// Criterion 9: on a constructed store — rows of the harness's development
/// store (`log/eval/rows.csv`, X0's `ex:naive/k2/enc1` rows) plus seven planted
/// violations — the checker detects every plant, at its key, and nothing else.
#[test]
fn c09_read_time_checker_detects_the_seven_plants() {
    let dev = read_rows(&plan().join("log/eval/rows.csv"))
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let base: Vec<BTreeMap<String, String>> = dev
        .into_iter()
        .filter(|r| {
            r["key"].starts_with("ex:naive/k2/enc1|") && r["run_kind"] == "timed" && r["rep"] == "0"
        })
        .filter(|r| r["end_class"] == "ok")
        .collect();
    assert!(
        base.len() >= 12,
        "conformance: X0's rows in the development store: {}",
        base.len()
    );
    // The development store's commit is `6e79e53…+dirty`; the constructed
    // store's rows carry a clean commit except the planted one.
    let base: Vec<_> = base
        .into_iter()
        .take(12)
        .map(|mut r| {
            r.insert("commit".to_owned(), "6e79e53".to_owned());
            r
        })
        .collect();
    let template = base[0].clone();
    let with = |key: &str, edits: &[(&str, &str)]| -> BTreeMap<String, String> {
        let mut r = template.clone();
        r.insert("key".to_owned(), key.to_owned());
        let p: Vec<&str> = key.split('|').collect();
        r.insert("fixture".to_owned(), p[0].to_owned());
        r.insert("rep".to_owned(), p[2].to_owned());
        r.insert("run_dir".to_owned(), String::new());
        for (c, v) in edits {
            assert!(r.contains_key(*c), "conformance: {c}");
            r.insert((*c).to_owned(), (*v).to_owned());
        }
        r
    };
    let lab = |e: GridEngine, pol: GatePolicy| {
        x1_config(e, Selector::Ltr)
            .gated(GatedMode::Exhaustive, pol)
            .label()
    };
    let k =
        |fx: &str, label: &str, rep: u32| key_of(fx, label, rep, "default", RunKind::Timed, prof());
    let mut rows = base.clone();
    let mut planned: BTreeSet<String> = base.iter().map(|r| r["key"].clone()).collect();
    // (1) a missing key.
    let missing = k(
        "synth/width/w2",
        &lab(GridEngine::Stateful, GatePolicy::Always),
        0,
    );
    planned.insert(missing.clone());
    // (2) a duplicate.
    rows.push(base[1].clone());
    let dup = base[1]["key"].clone();
    // (3) a `+dirty` commit.
    let dirty = k(
        "synth/width/w8",
        &lab(GridEngine::Stateful, GatePolicy::Always),
        0,
    );
    rows.push(with(
        &dirty,
        &[("commit", "abc123+dirty"), ("reports", "0")],
    ));
    planned.insert(dirty.clone());
    // (4) a mixed repetition set.
    let ml = lab(GridEngine::Gated, GatePolicy::Always);
    for (rep, ec, cens) in [
        (0, "ok", "false"),
        (1, "capped_wall", "true"),
        (2, "skipped_rep", "false"),
    ] {
        let key = k("synth/width/w32", &ml, rep);
        rows.push(with(
            &key,
            &[
                ("end_class", ec),
                ("censored", cens),
                ("engine", "Gated"),
                ("reports", "0"),
            ],
        ));
        planned.insert(key);
    }
    let mixed = format!("synth/width/w32|{ml}|default|timed");
    // (5) a verdict disagreement: `ex:cone` (violating, inside reach on the
    // stateful engine) with no report.
    let dis = k("ex:cone", &lab(GridEngine::Stateful, GatePolicy::Always), 0);
    rows.push(with(&dis, &[("engine", "Stateful"), ("reports", "0")]));
    planned.insert(dis.clone());
    // (6) a budgeted count out of order (B = 2 budgets more than B = 1).
    let b1 = k(
        "synth/reset/k2s1",
        &lab(GridEngine::Gated, GatePolicy::Budget(1)),
        0,
    );
    let b2 = k(
        "synth/reset/k2s1",
        &lab(GridEngine::Gated, GatePolicy::Budget(2)),
        0,
    );
    rows.push(with(
        &b1,
        &[
            ("engine", "Gated"),
            ("policy", "Budget(1)"),
            ("gate_sweeps_budgeted", "1"),
            ("selector", "Ltr"),
            ("reports", "1"),
        ],
    ));
    rows.push(with(
        &b2,
        &[
            ("engine", "Gated"),
            ("policy", "Budget(2)"),
            ("gate_sweeps_budgeted", "3"),
            ("selector", "Ltr"),
            ("reports", "1"),
        ],
    ));
    planned.insert(b1);
    planned.insert(b2.clone());
    // (7) a first report outside `spec_words` (and one inside, not flagged).
    let dir = temp("c09-store");
    let s_key = key_of(
        "apps/a4/drop/a4b/k1q1m1",
        &x1_config(GridEngine::Stateful, Selector::Ltr).label(),
        0,
        "default",
        RunKind::Profiling,
        prof(),
    );
    let p_out = key_of(
        "apps/a4/drop/a4b/k1q1m1",
        &x2_config(GridEngine::Gated, Selector::Ltr).label(),
        0,
        "default",
        RunKind::Profiling,
        prof(),
    );
    let p_in = key_of(
        "apps/a4/drop/a4b/k1q1m1",
        &x2_config(GridEngine::Stateful, Selector::Ltr).label(),
        0,
        "default",
        RunKind::Profiling,
        prof(),
    );
    let word = |c0: &[&str], st: &str| serde_json::json!({ "words": { "c0": c0 }, "statuses": { "c0": st }, "growth": "complete", "cause": "no-cover" });
    let p_grow = key_of(
        "apps/a4/drop/a4b/k1q1m1",
        &x2_config(GridEngine::Enumerator, Selector::Ltr).label(),
        0,
        "default",
        RunKind::Profiling,
        prof(),
    );
    let p_ve = key_of(
        "apps/a4/drop/a4b/k1q1m1",
        &x2_config(GridEngine::Enumerator, Selector::Reverse).label(),
        0,
        "default",
        RunKind::Profiling,
        prof(),
    );
    // A visible-error report on a fixture with no assertion-safety evidence.
    let p_ve2 = key_of(
        "synth/reset/k2s1",
        &x2_config(GridEngine::Enumerator, Selector::Reverse).label(),
        0,
        "default",
        RunKind::Profiling,
        prof(),
    );
    for (key, rel, file, v) in [
        (
            &s_key,
            "runs/s",
            "spec_words.json",
            serde_json::json!({ "spec_graphs": [word(&["snd Req(0,0)", "rcv Reply(0,0)"], "Done")] }),
        ),
        (
            &p_out,
            "runs/p1",
            "first_report.json",
            word(&["snd Req(0,0)"], "Blocked"),
        ),
        (
            &p_in,
            "runs/p2",
            "first_report.json",
            word(&["snd Req(0,0)", "rcv Reply(0,0)"], "Done"),
        ),
        (
            &p_grow,
            "runs/p3",
            "first_report.json",
            serde_json::json!({ "words": { "c0": ["snd Req(0,0)"] }, "statuses": null, "growth": "growing", "cause": "no-cover" }),
        ),
        (
            &p_ve,
            "runs/p4",
            "first_report.json",
            serde_json::json!({ "words": { "c0": [] }, "statuses": null, "growth": "growing", "cause": "visible-error" }),
        ),
        (
            &p_ve2,
            "runs/p5",
            "first_report.json",
            serde_json::json!({ "words": { "a0": [] }, "statuses": null, "growth": "growing", "cause": "visible-error" }),
        ),
    ] {
        fs::create_dir_all(dir.join(rel)).unwrap();
        fs::write(dir.join(rel).join(file), v.to_string()).unwrap();
        let mut r = with(key, &[("run_kind", "profiling"), ("reports", "1")]);
        r.insert("run_dir".to_owned(), rel.to_owned());
        if key == &s_key {
            // The X2S row: exhaustive stateful, `ok`, no Spec error — the
            // assertion-safety evidence for its fixture (round 03 m4).
            for (c, v) in [
                ("engine", "Stateful"),
                ("stop", "false"),
                ("end_class", "ok"),
                ("spec_errors", "0"),
            ] {
                r.insert(c.to_owned(), v.to_owned());
            }
        }
        rows.push(r);
        planned.insert(key.clone());
    }
    // Through the real reader: write the store, read it back.
    let path = dir.join("rows.csv");
    let hdr: Vec<String> = header().iter().map(|s| (*s).to_owned()).collect();
    let mut text = format!("{}\n#host: test; schema=2\n", csv_line(&hdr));
    for r in &rows {
        let cells: Vec<String> = hdr
            .iter()
            .map(|c| r.get(c).cloned().unwrap_or_default())
            .collect();
        text.push_str(&csv_line(&cells));
        text.push('\n');
    }
    fs::write(&path, text).unwrap();
    let back = read_rows(&path).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    assert_eq!(back.len(), rows.len());
    let found = check_store(&dir, &back, &planned);
    let want: BTreeSet<Finding> = [
        Finding::Missing(missing),
        Finding::Duplicate(dup),
        Finding::Dirty(dirty),
        Finding::Mixed(mixed),
        Finding::VerdictDisagrees(dis),
        Finding::BudgetedOutOfOrder(b2),
        Finding::FirstReportOutsideSpecWords(p_out),
        // Not a violation: the growing report is routed to "unclassified".
        Finding::UnclassifiedGrowing(p_grow),
        // A growing visible-error report: genuine (round 02 m1).
        Finding::GenuineVisibleError(p_ve),
        // Without evidence: unclassified (round 03 m4).
        Finding::UnclassifiedVisibleError(p_ve2),
    ]
    .into();
    assert_eq!(found, want);
    // The clean base alone: nothing.
    let clean: BTreeSet<String> = base.iter().map(|r| r["key"].clone()).collect();
    assert!(check_store(&dir, &base, &clean).is_empty());
}

// =========================================================================
// The exports (C4) and the determinism check — through the runner's child
// =========================================================================

fn small_tier() -> Tier {
    Tier {
        name: "t10s".to_owned(),
        wall: Duration::from_secs(10),
        mem_kb: 4 * 1024 * 1024,
    }
}

/// Runs one row as the driver's child does (`EVAL_ROW`, `EVAL_REP`,
/// `EVAL_COMMIT`, `EVAL_RUN_DIR`, `EVAL_EXPORT`), with the 10 s tier enforced
/// here; the child's record by column, or the child's stderr when it printed
/// no sentinel (a crash, as the driver would classify it).
fn child(spec: &RowSpec, export: &str, run_dir: &Path) -> Result<BTreeMap<String, String>, String> {
    fs::create_dir_all(run_dir).unwrap();
    let stdout = fs::File::create(run_dir.join("stdout")).unwrap();
    let stderr = fs::File::create(run_dir.join("stderr")).unwrap();
    let mut c = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--ignored",
            "--exact",
            "conformance::eval::eval_row",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("EVAL_ROW", row_json(spec))
        .env("EVAL_REP", spec.rep.to_string())
        .env("EVAL_COMMIT", "campaign-tests")
        .env("EVAL_RUN_DIR", run_dir)
        .env("EVAL_EXPORT", export)
        .stdin(std::process::Stdio::null())
        .stdout(stdout)
        .stderr(stderr)
        .spawn()
        .unwrap();
    let t = Instant::now();
    loop {
        if c.try_wait().unwrap().is_some() {
            break;
        }
        if t.elapsed() > spec.tier.wall {
            let _ = c.kill();
            let _ = c.wait();
            return Err(format!("{}: over the 10 s tier", spec.fixture));
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    let text = fs::read_to_string(run_dir.join("stdout")).unwrap();
    let Some(i) = text.find(SENTINEL) else {
        let err = fs::read_to_string(run_dir.join("stderr")).unwrap_or_default();
        return Err(format!(
            "no sentinel; stderr: {}",
            err.lines().take(2).collect::<Vec<_>>().join(" / ")
        ));
    };
    let cells = parse_csv_line(text[i + SENTINEL.len()..].lines().next().unwrap()).unwrap();
    Ok(header()
        .iter()
        .map(|c| (*c).to_owned())
        .zip(cells)
        .collect())
}

fn row(fx: &str, cfg: GridConfig, kind: RunKind) -> RowSpec {
    let mut r = spec("X0").rows[0].clone();
    r.fixture = fx.to_owned();
    r.config = cfg;
    r.run_kind = kind;
    r.rep = 0;
    r.tier = small_tier();
    r
}

fn json_at(dir: &Path, file: &str) -> Option<serde_json::Value> {
    let t = fs::read_to_string(dir.join(file)).ok()?;
    Some(serde_json::from_str(&t).expect("conformance: valid JSON"))
}

/// C4's exports through the runner's child (run alone). **The driver path is
/// not reachable before the freeze** (T7: the export is chosen by the spec's
/// name and the driver refuses `X2P`/`X2S` while the extension list is
/// unfrozen), so the child is spawned exactly as `spawn_child` does. On
/// `ex:naive/k2/enc1` under X2P's configuration, every engine: the row
/// reports, `first_report.json` holds the canonical key, the kind, the words
/// and the statuses (the enumerator: `report_keys` too, non-empty when
/// instrumented), and the child kept no graphs; on the conforming twin no file
/// is written; X2S's stateful row writes `spec_words.json` with the 2 Spec
/// graphs, and the first report's word is outside it (`ex:naive` is genuinely
/// violating); the X2 rep-0 timed row and the X2P row agree on `executions` and
/// the engine's first-report column (the determinism check).
///
/// **T9** (measured at the first landing, fixed 2026-10-09): the X2P child
/// panicked in `graph_words_json` (`assume_finished_at_gate`) on every growing
/// first report — the enumerator's (a gate report) and the gated engine's at a
/// gate. Now a growing report exports its words, canonical key and kind with
/// `statuses: null`; a complete one (stateful, complete-first) its status
/// vector. The per-engine outcomes are collected and listed by the assertion.
#[test]
#[ignore]
fn c04_exports_and_determinism_through_the_child() {
    let base = temp("c04-exports");
    let fx = "ex:naive/k2/enc1";
    let mut bad: Vec<String> = Vec::new();
    let mut first_keys: Vec<(GridEngine, String)> = Vec::new();
    assert_eq!(exports_of("X2P"), Some("first_report"));
    assert_eq!(exports_of("X2S"), Some("spec_words"));
    assert_eq!(exports_of("X2"), None);
    let x2s = row(
        fx,
        x1_config(GridEngine::Stateful, Selector::Ltr),
        RunKind::Profiling,
    );
    let sdir = base.join("x2s");
    let srow = child(&x2s, "spec_words", &sdir).expect("conformance: the X2S child");
    assert_eq!(srow["end_class"], "ok");
    let sw = json_at(&sdir, "spec_words.json").expect("conformance: spec_words.json");
    let sg = sw["spec_graphs"]
        .as_array()
        .expect("conformance: spec_graphs")
        .clone();
    assert_eq!(sg.len(), 2, "conformance: ex:naive k=2: 2! Spec graphs");
    for g in &sg {
        assert!(
            g["words"].is_object() && g["statuses"].is_object() && g["canonical_key"].is_string()
        );
    }
    note!("c04: X2S spec_words {sw}");
    for e in ENGINES {
        let cfg = x2_config(e, Selector::Ltr);
        let pdir = base.join(format!("x2p-{e:?}"));
        let p = match child(
            &row(fx, cfg.clone(), RunKind::Profiling),
            "first_report",
            &pdir,
        ) {
            Ok(p) => p,
            Err(m) => {
                bad.push(format!("{e:?}: X2P child: {m}"));
                continue;
            }
        };
        if p["end_class"] != "ok" || p["reports"].parse::<usize>().unwrap_or(0) == 0 {
            bad.push(format!(
                "{e:?}: end_class {} reports {}",
                p["end_class"], p["reports"]
            ));
        }
        for kc in ["kept_impl_graphs", "kept_spec_graphs"] {
            if !["", "0"].contains(&p[kc].as_str()) {
                bad.push(format!("{e:?}: {kc} = {}", p[kc]));
            }
        }
        match json_at(&pdir, "first_report.json") {
            None => bad.push(format!("{e:?}: no first_report.json")),
            Some(fr) => {
                note!("c04 {e:?}: first_report {fr}");
                // A complete report (stateful, complete-first) carries its
                // status vector; a growing one (the enumerator's gate report,
                // gated at a gate) `statuses: null` (T9 fixed).
                // On `ex:naive/k2/enc1` the enumerator's and gated engine's
                // first reports are gate reports (growing); the stateful and
                // complete-first ones complete (round 01 M1).
                let growing = matches!(e, GridEngine::Enumerator | GridEngine::Gated);
                let want_growth = if growing { "growing" } else { "complete" };
                if fr["cause"] != "no-cover" {
                    bad.push(format!("{e:?}: cause {} (want no-cover)", fr["cause"]));
                }
                if fr["growth"] != want_growth {
                    bad.push(format!(
                        "{e:?}: growth {} (want {want_growth})",
                        fr["growth"]
                    ));
                }
                // `statuses: null` iff growing.
                let statuses_ok = if fr["growth"] == "growing" {
                    fr["statuses"].is_null()
                } else {
                    fr["statuses"].is_object()
                };
                if !growing {
                    first_keys.push((
                        e,
                        fr["canonical_key"].as_str().unwrap_or_default().to_owned(),
                    ));
                }
                if fr["canonical_key"].as_str().unwrap_or_default().is_empty()
                    || fr["kind"].as_str().unwrap_or_default().is_empty()
                    || !fr["words"].is_object()
                    || !statuses_ok
                {
                    bad.push(format!("{e:?}: fields missing in {fr}"));
                }
                if e == GridEngine::Enumerator && !fr["report_keys"].is_array() {
                    bad.push(format!("{e:?}: no report_keys"));
                }
                let inside = sg
                    .iter()
                    .any(|g| g["words"] == fr["words"] && g["statuses"] == fr["statuses"]);
                if inside {
                    bad.push(format!(
                        "{e:?}: the first report's word is inside vis(Spec)"
                    ));
                }
            }
        }
        // Determinism: the X2 rep-0 timed row (no export).
        let tdir = base.join(format!("x2-{e:?}"));
        let t = match child(&row(fx, cfg, RunKind::Timed), "", &tdir) {
            Ok(t) => t,
            Err(m) => {
                bad.push(format!("{e:?}: X2 child: {m}"));
                continue;
            }
        };
        assert!(
            json_at(&tdir, "first_report.json").is_none(),
            "conformance: no export without EVAL_EXPORT"
        );
        if t["executions"] != p["executions"] {
            bad.push(format!(
                "{e:?}: executions {} vs {}",
                t["executions"], p["executions"]
            ));
        }
        let colname = match e {
            GridEngine::Enumerator | GridEngine::Gated => Some("paper_events_at_first_report"),
            GridEngine::CompleteFirst => Some("paper_events_at_first_report(grid)"),
            _ => None,
        };
        if let Some(c) = colname {
            if t[c].is_empty() || t[c] != p[c] {
                bad.push(format!("{e:?}: {c} {:?} vs {:?}", t[c], p[c]));
            }
        }
        note!(
            "c04 {e:?}: executions {} / {}",
            t["executions"],
            p["executions"]
        );
    }
    // Round 01 M2: the instrumented enumerator's exported `canonical_key` is
    // in its own `report_keys` (entries `"<ReportGate Debug>: <CanonKey Debug>"`) — the
    // first-report X2P configuration.
    // `report_keys` entries are `"<gate Debug>: <CanonKey Debug>"`.
    let in_keys = |fr: &serde_json::Value, key: &str| -> bool {
        fr["report_keys"].as_array().is_some_and(|a| {
            a.iter().any(|x| {
                x.as_str()
                    .and_then(|s| s.split_once(": "))
                    .is_some_and(|(_, k)| k == key)
            })
        })
    };
    let idir = base.join("x2p-instr");
    let cfg = x2_config(GridEngine::Enumerator, Selector::Ltr).instrumented(true);
    match child(&row(fx, cfg, RunKind::Profiling), "first_report", &idir) {
        Err(m) => bad.push(format!("instrumented enumerator: {m}")),
        Ok(_) => match json_at(&idir, "first_report.json") {
            Some(fr) if fr["report_keys"].as_array().is_some_and(|a| !a.is_empty()) => {
                note!(
                    "c04 instrumented X2P: key {} report_keys {}",
                    fr["canonical_key"],
                    fr["report_keys"]
                );
                let k = fr["canonical_key"].as_str().unwrap_or_default().to_owned();
                if k.is_empty() || !in_keys(&fr, &k) {
                    bad.push(format!(
                        "instrumented enumerator: canonical_key {k} ∉ report_keys {}",
                        fr["report_keys"]
                    ));
                }
            }
            other => bad.push(format!("instrumented enumerator: report_keys in {other:?}")),
        },
    }
    // C6's membership on the enumerator: the X2P (first-report) key is in the
    // exhaustive instrumented run's report-key set.
    let x2p_key = json_at(&idir, "first_report.json")
        .and_then(|fr| fr["canonical_key"].as_str().map(str::to_owned))
        .unwrap_or_default();
    let xdir = base.join("x1-instr");
    let cfg = x1_config(GridEngine::Enumerator, Selector::Ltr).instrumented(true);
    match child(&row(fx, cfg, RunKind::Profiling), "first_report", &xdir) {
        Err(m) => bad.push(format!("exhaustive instrumented enumerator: {m}")),
        Ok(_) => match json_at(&xdir, "first_report.json") {
            Some(fr) if in_keys(&fr, &x2p_key) => {}
            Some(fr) => bad.push(format!(
                "X2P key ∉ the exhaustive report_keys {}",
                fr["report_keys"]
            )),
            None => bad.push("exhaustive instrumented enumerator: no export".to_owned()),
        },
    }
    // The complete reports' keys are the counters' form: the stateful and
    // complete-first exports equal `format!("{:?}", CanonicalGraph::of(g).key())`
    // of the stateful engine's first reported graph, computed in process.
    let f = fixture_by_name(fx).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let cfg = x2_config(GridEngine::Stateful, Selector::Ltr);
    if let GridEnd::Ok(r) = run_row_in_process(&f, &cfg, false) {
        if let GridRaw::Stateful(o) = &r.raw {
            let g = &o.reports.first().expect("conformance: a stateful report").0;
            let want = crate::conformance::canon::CanonicalGraph::of(g, &f.visible)
                .map(|c| format!("{:?}", c.key()))
                .unwrap_or_default();
            for (e, k) in &first_keys {
                if *k != want {
                    bad.push(format!(
                        "{e:?}: exported key is not the CanonKey of the graph"
                    ));
                }
            }
        }
    }
    // Round 01 M1's instance (pinned by `r01_m1_…`): a gate report with every
    // spawned thread stopped still exports `growing` and `statuses: null`; and
    // R1's visible-error report (the enumerator's, `gate` not `Completion`).
    for (f, e, s) in [
        (
            "corpus/VisibleMutation/0x200000000",
            GridEngine::Gated,
            Selector::Reverse,
        ),
        (
            "corpus/VisibleMutation/0x200000000",
            GridEngine::Enumerator,
            Selector::Reverse,
        ),
        ("R1", GridEngine::Enumerator, Selector::Ltr),
        // Round 03 n2: R1 on the complete engines (a complete report).
        ("R1", GridEngine::Stateful, Selector::Ltr),
        ("R1", GridEngine::CompleteFirst, Selector::Ltr),
    ] {
        let d = base.join(format!("m1-{}-{e:?}", f.replace('/', "_")));
        match child(
            &row(f, x2_config(e, s), RunKind::Profiling),
            "first_report",
            &d,
        ) {
            Err(m) => bad.push(format!("{f} {e:?}: {m}")),
            Ok(_) => match json_at(&d, "first_report.json") {
                Some(fr) => {
                    note!(
                        "c04 M1 {f} {e:?} {s:?}: growth {} kind {} statuses {}",
                        fr["growth"],
                        fr["kind"],
                        fr["statuses"]
                    );
                    let want_cause = if f == "R1" {
                        "visible-error"
                    } else {
                        "no-cover"
                    };
                    if fr["cause"] != want_cause {
                        bad.push(format!(
                            "{f} {e:?}: cause {} (want {want_cause})",
                            fr["cause"]
                        ));
                    }
                    let complete = matches!(e, GridEngine::Stateful | GridEngine::CompleteFirst);
                    let ok = if complete {
                        fr["growth"] == "complete" && fr["statuses"].is_object()
                    } else {
                        fr["growth"] == "growing" && fr["statuses"].is_null()
                    };
                    if !ok {
                        bad.push(format!(
                            "{f} {e:?}: growth {} statuses {}",
                            fr["growth"], fr["statuses"]
                        ));
                    }
                }
                None => bad.push(format!("{f} {e:?}: no first_report.json")),
            },
        }
    }
    // A conforming fixture writes no first report.
    for e in ENGINES {
        let d = base.join(format!("conf-{e:?}"));
        let r = row(
            "synth/naive-self/k2enc1",
            x2_config(e, Selector::Ltr),
            RunKind::Profiling,
        );
        match child(&r, "first_report", &d) {
            Err(m) => bad.push(format!("{e:?} conforming: {m}")),
            Ok(r) => {
                if r["reports"] != "0" || json_at(&d, "first_report.json").is_some() {
                    bad.push(format!("{e:?} conforming: reports {}", r["reports"]));
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: {} export findings: {bad:#?}",
        bad.len()
    );
}

// =========================================================================
// Round 01 (P5-CAMPAIGN-CODE) items: m4, m3, n2, M1's concrete instance
// =========================================================================

/// Round 01 m4: `twin_key` (the RQ2 pairing) is non-empty on X2 and X2P rows
/// and, since the X5 gate-3 fixes (2026-10-09, `P5-X5` T4/T6), on exactly the
/// 108 X5 rows whose key X2 holds, with X2's value; every non-empty `twin_key`
/// of every builtin spec is a key of some builtin spec (the dangling check
/// stays on for X5/X5G). The X5/X5G sweep partner (`P5-X5` F1, criterion 1) is
/// checked independently of `x5_partner`: each `A_flat` row's label with
/// `cover = Sweep` (and `precheck = false` in the complete-first host) is a key
/// the spec itself lists, held by X1 (24 conforming §6 points × 3 reps), X1V
/// (the six `ex:naive/k{2,3,4}` `Ltr` points × 3; one key also X0's), X2 (the
/// 108 stop pairs) or no other spec (X5: 32 violating §6 points × 3; X5G:
/// all 186: no `stop = true` pairs since round 01 m2/n1). T6: on every X2∩X5 key the two rows agree in fixture, label, tier,
/// run kind, rep and `twin_key`.
#[test]
fn r01_every_twin_key_is_a_key_of_some_spec() {
    let all: BTreeSet<&String> = key_sets().values().flatten().collect();
    let mut dangling = Vec::new();
    for s in specs() {
        let with = s.rows.iter().filter(|r| !r.twin_key.is_empty()).count();
        match s.name.as_str() {
            "X2" => assert_eq!(with, 122 * 36, "conformance: X2's twinned rows"),
            "X2P" => assert_eq!(with, 122 * 12, "conformance: X2P's twinned rows"),
            "X5" => assert_eq!(with, 108, "conformance: X5's X2-held rows"),
            other => assert_eq!(with, 0, "conformance: {other} carries no twin key"),
        }
        for r in s.rows.iter().filter(|r| !r.twin_key.is_empty()) {
            if !all.contains(&r.twin_key) {
                dangling.push(format!("{}: {} → {}", s.name, r.fixture, r.twin_key));
            }
        }
    }
    assert!(
        dangling.is_empty(),
        "conformance: dangling twin keys: {} {dangling:#?}",
        dangling.len()
    );
    // T6: X5's rows on X2's keys are X2's rows.
    let x2: BTreeMap<String, &RowSpec> =
        spec("X2").rows.iter().map(|r| (r.key(prof()), r)).collect();
    let mut shared = 0;
    for r in &spec("X5").rows {
        let k = r.key(prof());
        match x2.get(&k) {
            Some(o) => {
                shared += 1;
                assert_eq!(
                    (
                        &r.fixture,
                        label_of(r),
                        &r.tier.name,
                        r.run_kind,
                        r.rep,
                        &r.twin_key
                    ),
                    (
                        &o.fixture,
                        label_of(o),
                        &o.tier.name,
                        o.run_kind,
                        o.rep,
                        &o.twin_key
                    ),
                    "conformance: X2∩X5 row {k}"
                );
                assert!(!r.twin_key.is_empty(), "conformance: {k}");
            }
            None => assert!(r.twin_key.is_empty(), "conformance: X5 {k}"),
        }
    }
    assert_eq!(shared, 108, "conformance: X2∩X5");
    let mut holders: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
    for name in ["X5", "X5G"] {
        let own = ks(name);
        let mut flat = 0;
        for r in &spec(name).rows {
            if r.config.completion_cover != CompletionCover::Flat {
                continue;
            }
            flat += 1;
            assert!(r.config.precheck, "conformance: {name}: A_flat precheck");
            let mut c = r.config.clone();
            c.completion_cover = CompletionCover::Sweep;
            if name == "X5" {
                c.precheck = false;
            }
            let partner = key_of(
                &r.fixture,
                &c.label(),
                r.rep,
                &r.tier.name,
                r.run_kind,
                prof(),
            );
            assert!(
                own.contains(&partner),
                "conformance: {name} lists its partner {partner}"
            );
            let held: Vec<String> = specs()
                .iter()
                .filter(|t| t.name != name && ks(&t.name).contains(&partner))
                .map(|t| t.name.clone())
                .collect();
            let held = if held.is_empty() {
                name.to_owned()
            } else {
                held.join("+")
            };
            *holders
                .entry(name.to_owned())
                .or_default()
                .entry(held)
                .or_default() += 1;
        }
        let want_flat = if name == "X5" { 294 } else { 186 };
        assert_eq!(flat, want_flat, "conformance: {name}'s A_flat rows");
        assert_eq!(
            spec(name).rows.len(),
            2 * flat,
            "conformance: {name}: one partner each"
        );
    }
    note!("r01: X5/X5G partner holders: {holders:?}");
    let want: BTreeMap<String, BTreeMap<String, usize>> = [
        (
            "X5".to_owned(),
            [
                ("X1".to_owned(), 72),
                ("X1V".to_owned(), 17),
                ("X0+X1V".to_owned(), 1),
                ("X2".to_owned(), 108),
                ("X5".to_owned(), 96),
            ]
            .into(),
        ),
        ("X5G".to_owned(), [("X5G".to_owned(), 186)].into()),
    ]
    .into();
    assert_eq!(holders, want, "conformance: X5/X5G partner holders");
}

/// A `frozen.json` text: two extension steps, X1P and the ceilings.
fn frozen_json(ext: &[&[&str]], x1p: Option<&[&str]>, ceilings: Option<&[&str]>) -> String {
    let step = |items: &[&str]| serde_json::json!({ "date": "2026-10-09", "source": "campaign_tests", "items": items });
    serde_json::json!({
        "extension": ext.iter().map(|i| step(i)).collect::<Vec<_>>(),
        "x1p": x1p.map(step),
        "budget_ceilings": ceilings.map(step),
    })
    .to_string()
}

/// Round 02 M1 (the lists as data): `FrozenLists::parse` on valid steps gives
/// the union of the extension steps (`extension_items`) and the ceilings as
/// `(fixture, i)`; every list's bogus name panics (`catch_unwind`, the
/// `conformance:` message naming the list); an `in_grid = false` point (S5's
/// validation-only `(1, 2)`) is no grid point; malformed JSON is refused; an
/// empty object is "every list unfrozen". The process-wide `frozen()` is read
/// once (a `OnceLock`), so the driver's use of the lists is tested in child
/// processes (`r02_two_step_extension_rule_through_the_driver`).
#[test]
fn r02_frozen_lists_parse_and_validate() {
    let ok = frozen_json(
        &[
            &[
                "apps/a1/correct/spec/n5r1",
                "apps/a1/correct/spec/n6r1",
                "apps/a1/correct/spec/n2r4",
            ],
            &["synth/share/m24c12"],
        ],
        Some(&["synth/commit/n4j2", "apps/a1/correct/spec/n3r1"]),
        Some(&["synth/reset/k2s1|3", "apps/a1/correct/spec/n2r1|5"]),
    );
    let f = FrozenLists::parse(&ok).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    assert_eq!(f.extension.len(), 2);
    assert_eq!(
        f.extension_items(),
        vec![
            "apps/a1/correct/spec/n5r1",
            "apps/a1/correct/spec/n6r1",
            "apps/a1/correct/spec/n2r4",
            "synth/share/m24c12"
        ]
    );
    assert_eq!(
        f.ceilings(),
        vec![
            ("synth/reset/k2s1".to_owned(), 3),
            ("apps/a1/correct/spec/n2r1".to_owned(), 5)
        ]
    );
    assert_eq!(f.x1p.as_ref().map(|s| s.items.len()), Some(2));
    assert!(f
        .extension
        .iter()
        .all(|s| !s.date.is_empty() && !s.source.is_empty()));
    assert_eq!(
        FrozenLists::parse("{}").unwrap_or_else(|e| panic!("conformance: {}", e.text())),
        FrozenLists::default()
    );
    assert!(matches!(
        FrozenLists::parse("{not json"),
        Err(Refusal::Spec(_))
    ));
    for (what, bad) in [
        (
            "extension",
            frozen_json(&[&["apps/a1/correct/spec/n9r9"]], None, None),
        ),
        ("X1P", frozen_json(&[], Some(&["synth/nowhere/k1"]), None)),
        (
            "budget-ceilings",
            frozen_json(&[], None, Some(&["synth/reset/k99s1|2"])),
        ),
        (
            "extension",
            frozen_json(&[&["synth/reset/k1s2"]], None, None),
        ),
    ] {
        let r = std::panic::catch_unwind(|| FrozenLists::parse(&bad));
        let msg = match r {
            Err(p) => p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_default(),
            Ok(_) => panic!("conformance: a bogus {what} name was accepted: {bad}"),
        };
        assert!(
            msg.starts_with("conformance: ") && msg.contains(&format!("frozen {what} list")),
            "conformance: {msg}"
        );
    }
}

/// **T10** (round 03 code; fixed 2026-10-08 — `CAMPAIGN_SPECS`; now a regression test). The corner-only rule
/// (`Driver::run`: "under one extension step only the corner pass may run")
/// applies to **every** spec while fewer than two steps are frozen — X0, the
/// harness's test specs and any non-campaign spec included — so any `EVAL_ONLY`
/// run of them is refused "beyond the corners" when no list is frozen. The
/// closed `P5-HARNESS` test `eval_tests::t7_eval_only_is_a_glob` (ignored,
/// X0 + `EVAL_ONLY=*|Stateful/*`) fails on this tree for that reason (measured:
/// "refused: X0 is not runnable beyond the corners with one extension step:
/// ex:naive/k2/enc1"). Expected: the rule is scoped to the seven campaign specs.
/// In process, no child: with a dirty fake probe the fixed driver refuses
/// `Dirty`; the landed one refuses on the corners first.
#[test]
fn t10_eval_only_on_a_non_campaign_spec_is_not_corner_restricted() {
    let out = temp("t10");
    let mut d = driver(
        spec("X0").clone(),
        &out,
        Probes {
            git: Box::new(|| ("campaign-tests".to_owned(), true)),
            host: Box::new(|| "campaign-tests-host".to_owned()),
        },
    );
    d.only = Some("ex:naive/k2/enc1|Stateful/*".to_owned());
    match d.run() {
        Err(Refusal::Dirty(_)) => {}
        other => panic!(
            "conformance: X0 + EVAL_ONLY: {:?}",
            other.map_err(|e| e.text())
        ),
    }
}

/// Round 03 m2: `parse` refuses every malformed case with "the frozen lists
/// are malformed: …" (an unknown key; an unknown step key; a step without a
/// date, with an empty source; a non-string item; a ceiling item without `|i`,
/// with a non-numeric `i`, with `i = 21`; three extension steps; a null step);
/// `validate` panics on a grid point outside its list's admissible set — X1P
/// (`synth/width/w2`), the ceilings (`synth/share/m2c0`, the family not the
/// control; the catalogue at `n2r3`) — and an extension name off the grid.
#[test]
fn r03_parse_refuses_malformed_lists_and_inadmissible_names() {
    let step = |d: &str, s: &str, items: serde_json::Value| serde_json::json!({ "date": d, "source": s, "items": items });
    let ok_step = step(
        "2026-10-08",
        "src",
        serde_json::json!(["apps/a1/correct/spec/n5r1"]),
    );
    let cases: Vec<(&str, serde_json::Value)> = vec![
        (
            "unknown key",
            serde_json::json!({ "extension": [ok_step.clone()], "x1q": null }),
        ),
        (
            // `x5` is a known key since the `P5-X5` landing; `x5g` is not.
            "unknown key x5g",
            serde_json::json!({ "x5": null, "x5g": null }),
        ),
        (
            "unknown step key",
            serde_json::json!({ "extension": [{ "date": "d", "source": "s", "items": [], "note": "x" }] }),
        ),
        (
            "no date",
            serde_json::json!({ "extension": [{ "source": "s", "items": ["apps/a1/correct/spec/n5r1"] }] }),
        ),
        (
            "empty source",
            serde_json::json!({ "extension": [step("d", "", serde_json::json!([]))] }),
        ),
        (
            "non-string item",
            serde_json::json!({ "extension": [step("d", "s", serde_json::json!([3]))] }),
        ),
        (
            "ceiling without i",
            serde_json::json!({ "budget_ceilings": step("d", "s", serde_json::json!(["synth/reset/k2s1"])) }),
        ),
        (
            "ceiling i not a number",
            serde_json::json!({ "budget_ceilings": step("d", "s", serde_json::json!(["synth/reset/k2s1|x"])) }),
        ),
        (
            "ceiling i = 21",
            serde_json::json!({ "budget_ceilings": step("d", "s", serde_json::json!(["synth/reset/k2s1|21"])) }),
        ),
        (
            "three steps",
            serde_json::json!({ "extension": [ok_step.clone(), ok_step.clone(), ok_step.clone()] }),
        ),
        ("null step", serde_json::json!({ "extension": [null] })),
    ];
    for (what, v) in cases {
        match FrozenLists::parse(&v.to_string()) {
            Err(Refusal::Spec(m)) => assert!(
                m.starts_with("the frozen lists are malformed: "),
                "conformance: {what}: {m}"
            ),
            Err(e) => panic!("conformance: {what}: wrong refusal {}", e.text()),
            Ok(_) => panic!("conformance: {what} was accepted"),
        }
    }
    // `i = 20` is the bound, accepted.
    let ok = serde_json::json!({ "budget_ceilings": step("d", "s", serde_json::json!(["synth/reset/k2s1|20"])) });
    assert!(FrozenLists::parse(&ok.to_string()).is_ok());
    // `x5` is not an unknown key: `null` is "unfrozen", a step is parsed.
    let x5_null = serde_json::json!({ "x5": null });
    assert_eq!(
        FrozenLists::parse(&x5_null.to_string())
            .unwrap_or_else(|e| panic!("conformance: x5 null: {}", e.text())),
        FrozenLists::default()
    );
    let x5_step =
        serde_json::json!({ "x5": step("d", "s", serde_json::json!(["synth/share/m24c12"])) });
    let f = FrozenLists::parse(&x5_step.to_string())
        .unwrap_or_else(|e| panic!("conformance: x5 step: {}", e.text()));
    assert_eq!(
        f.x5.as_ref().map(|s| s.items.clone()),
        Some(vec!["synth/share/m24c12".to_owned()])
    );
    // A malformed `x5` step is refused like any other list's.
    match FrozenLists::parse(
        &serde_json::json!({ "x5": { "date": "d", "source": "s", "items": [], "note": 1 } })
            .to_string(),
    ) {
        Err(Refusal::Spec(m)) => assert!(
            m.starts_with("the frozen lists are malformed: X5: unknown step key"),
            "conformance: {m}"
        ),
        other => panic!(
            "conformance: a malformed x5 step: {:?}",
            other.map_err(|e| e.text())
        ),
    }
    for (what, v, needle) in [
        (
            "X1P",
            serde_json::json!({ "x1p": step("d", "s", serde_json::json!(["synth/width/w2"])) }),
            "outside its admissible set",
        ),
        (
            "budget-ceilings",
            serde_json::json!({ "budget_ceilings": step("d", "s", serde_json::json!(["synth/share/m2c0|1"])) }),
            "outside its admissible set",
        ),
        (
            "budget-ceilings",
            serde_json::json!({ "budget_ceilings": step("d", "s", serde_json::json!(["apps/a1/eager/spec/n2r3|3"])) }),
            "outside its admissible set",
        ),
        (
            "extension",
            serde_json::json!({ "extension": [step("d", "s", serde_json::json!(["apps/a1/correct/spec/n9r1"]))] }),
            "names no grid point",
        ),
    ] {
        let text = v.to_string();
        let msg = match std::panic::catch_unwind(|| FrozenLists::parse(&text)) {
            Err(p) => p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_default(),
            Ok(_) => panic!("conformance: {what}: an inadmissible name was accepted"),
        };
        assert!(
            msg.starts_with("conformance: ")
                && msg.contains(&format!("frozen {what} list"))
                && msg.contains(needle),
            "conformance: {msg}"
        );
    }
}

/// The panic message of `FrozenLists::parse(text)`, or `None` if it returned.
fn parse_panic(text: &str) -> Option<String> {
    match std::panic::catch_unwind(|| FrozenLists::parse(text)) {
        Err(p) => Some(
            p.downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_default(),
        ),
        Ok(_) => None,
    }
}

/// Round 04 m1 (criteria rev 4.5): the extension steps' admissible sets.
/// Step 1 ⊆ D5's three A1 points `apps/a1/correct/spec/{n5r1, n6r1, n2r4}`;
/// step 2 ⊆ `synth/*`. Refused at parse (a panic whose message starts with
/// `conformance: `, names the frozen extension list and says "outside its
/// admissible set"): step 1 naming a corner (`apps/a1/correct/spec/n3r2`,
/// the case m1 is about), another A1 point (`n2r1`), the catalogue
/// (`eager/spec/n2r1`), a synthetic point; step 2 naming a corner, a D5 point,
/// an A2 point. Accepted: step 1 = the three points, any non-empty subset of
/// them; step 2 = synthetic points of several families.
#[test]
fn r04_m1_extension_steps_admissible_sets() {
    let step = |items: &[&str]| serde_json::json!({ "date": "2026-10-08", "source": "campaign_tests", "items": items });
    let ext = |steps: &[&[&str]]| {
        serde_json::json!({ "extension": steps.iter().map(|s| step(s)).collect::<Vec<_>>() })
            .to_string()
    };
    let d5: &[&str] = &[
        "apps/a1/correct/spec/n5r1",
        "apps/a1/correct/spec/n6r1",
        "apps/a1/correct/spec/n2r4",
    ];
    let synth: &[&str] = &[
        "synth/share/m24c12",
        "synth/commit/n4j2",
        "synth/reset/k2s1",
    ];
    // Accepted.
    for (what, text) in [
        ("step 1 = D5", ext(&[d5])),
        ("step 1 ⊂ D5", ext(&[&["apps/a1/correct/spec/n2r4"]])),
        ("both steps", ext(&[d5, synth])),
        ("step 2 one synth", ext(&[&d5[..1], &synth[..1]])),
    ] {
        let f = FrozenLists::parse(&text)
            .unwrap_or_else(|e| panic!("conformance: {what}: refused {}", e.text()));
        assert!(!f.extension.is_empty(), "conformance: {what}");
    }
    // Refused.
    let a2 = apps_grid()
        .into_iter()
        .find(|p| p.in_grid && p.fixture.starts_with("apps/a2/"))
        .map(|p| p.fixture)
        .unwrap_or_else(|| panic!("conformance: an in-grid A2 point"));
    for (what, text) in [
        ("step 1 a corner", ext(&[&["apps/a1/correct/spec/n3r2"]])),
        (
            "step 1 D5 + a corner",
            ext(&[&[d5[0], "apps/a1/correct/spec/n3r2"]]),
        ),
        (
            "step 1 another A1 point",
            ext(&[&["apps/a1/correct/spec/n2r1"]]),
        ),
        ("step 1 the catalogue", ext(&[&["apps/a1/eager/spec/n2r1"]])),
        ("step 1 a synth point", ext(&[&["synth/share/m24c12"]])),
        (
            "step 2 a corner",
            ext(&[d5, &["apps/a1/correct/spec/n3r2"]]),
        ),
        ("step 2 a D5 point", ext(&[&d5[..1], &d5[1..2]])),
        (
            "step 2 synth + an apps point",
            ext(&[d5, &[synth[0], a2.as_str()]]),
        ),
    ] {
        let msg =
            parse_panic(&text).unwrap_or_else(|| panic!("conformance: {what}: accepted: {text}"));
        assert!(
            msg.starts_with("conformance: ")
                && msg.contains("frozen extension list")
                && msg.contains("outside its admissible set"),
            "conformance: {what}: {msg}"
        );
    }
}

/// Round 04 n5 (criteria rev 4.5): no frozen list names a fixture twice —
/// within an extension step, X1P, the budget ceilings (by fixture: `f|3` and
/// `f|4` are one point twice, C8(ii)'s one ceiling per point) and X5. Each a
/// panic at parse whose message starts with `conformance: ` and names the list
/// ("the frozen <list> list names a fixture twice: <fixture>"); the same lists
/// without the repeat are accepted.
#[test]
fn r04_n5_no_list_names_a_fixture_twice() {
    let step = |items: &[&str]| serde_json::json!({ "date": "2026-10-08", "source": "campaign_tests", "items": items });
    let d5a = "apps/a1/correct/spec/n5r1";
    let d5b = "apps/a1/correct/spec/n6r1";
    let cases: Vec<(&str, serde_json::Value, serde_json::Value, &str)> = vec![
        (
            "extension",
            serde_json::json!({ "extension": [step(&[d5a, d5a])] }),
            serde_json::json!({ "extension": [step(&[d5a, d5b])] }),
            d5a,
        ),
        (
            "extension",
            serde_json::json!({ "extension": [step(&[d5a]), step(&["synth/share/m24c12", "synth/share/m24c12"])] }),
            serde_json::json!({ "extension": [step(&[d5a]), step(&["synth/share/m24c12", "synth/commit/n4j2"])] }),
            "synth/share/m24c12",
        ),
        (
            "X1P",
            serde_json::json!({ "x1p": step(&["synth/commit/n4j2", "synth/commit/n4j2"]) }),
            serde_json::json!({ "x1p": step(&["synth/commit/n4j2", "apps/a1/correct/spec/n3r1"]) }),
            "synth/commit/n4j2",
        ),
        (
            "budget-ceilings",
            serde_json::json!({ "budget_ceilings": step(&["synth/reset/k2s1|3", "synth/reset/k2s1|4"]) }),
            serde_json::json!({ "budget_ceilings": step(&["synth/reset/k2s1|3", "apps/a1/correct/spec/n2r1|4"]) }),
            "synth/reset/k2s1",
        ),
        (
            "budget-ceilings",
            serde_json::json!({ "budget_ceilings": step(&["synth/reset/k2s1|3", "synth/reset/k2s1|3"]) }),
            serde_json::json!({ "budget_ceilings": step(&["synth/reset/k2s1|3"]) }),
            "synth/reset/k2s1",
        ),
        (
            "X5",
            serde_json::json!({ "x5": step(&["synth/share/m24c12", "synth/share/m24c12"]) }),
            serde_json::json!({ "x5": step(&["synth/share/m24c12", "synth/commit/n4j2"]) }),
            "synth/share/m24c12",
        ),
    ];
    for (what, bad, good, name) in cases {
        let msg = parse_panic(&bad.to_string())
            .unwrap_or_else(|| panic!("conformance: {what}: a repeat was accepted: {bad}"));
        assert_eq!(
            msg,
            format!("conformance: the frozen {what} list names a fixture twice: {name}"),
            "conformance: {what}"
        );
        FrozenLists::parse(&good.to_string())
            .unwrap_or_else(|e| panic!("conformance: {what}: refused {}", e.text()));
    }
}

/// `P5-X5`'s `x5` list in the record (round 04 n1 with the landing):
/// `consumed_by` gives the X5 list to X5 and X5G only, the extension list to
/// every campaign spec, and nothing to X0 or a test spec; `merged` keeps a
/// recorded X5 list.
#[test]
fn r04_x5_list_is_consumed_by_x5_and_x5g_only() {
    let f = FrozenLists::parse(
        &serde_json::json!({
            "extension": [{ "date": "d", "source": "s", "items": ["apps/a1/correct/spec/n5r1"] }],
            "x1p": { "date": "d", "source": "s", "items": ["synth/commit/n4j2"] },
            "budget_ceilings": { "date": "d", "source": "s", "items": ["synth/reset/k2s1|3"] },
            "x5": { "date": "d", "source": "s", "items": ["synth/share/m24c12"] },
        })
        .to_string(),
    )
    .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    for name in ["X1", "X1V", "X2", "X2P", "X2S", "X1P", "X3A", "X5", "X5G"] {
        let c = f.consumed_by(name);
        assert_eq!(c.extension, f.extension, "conformance: {name}");
        assert_eq!(c.x1p.is_some(), name == "X1P", "conformance: {name}");
        assert_eq!(
            c.budget_ceilings.is_some(),
            name == "X3A",
            "conformance: {name}"
        );
        assert_eq!(
            c.x5.is_some(),
            name == "X5" || name == "X5G",
            "conformance: {name}"
        );
    }
    for name in ["X0", "T", "eval-test"] {
        assert_eq!(
            f.consumed_by(name),
            FrozenLists::default(),
            "conformance: {name}"
        );
    }
    let rec = FrozenLists::merged(&FrozenLists::default(), &f.consumed_by("X5"));
    assert_eq!(rec.x5, f.x5);
    let rec2 = FrozenLists::merged(&rec, &f.consumed_by("X1"));
    assert_eq!(rec2.x5, f.x5, "conformance: a recorded X5 list is kept");
}

/// The child of `r02_two_step_extension_rule_through_the_driver`: with
/// `CAMPAIGN_CASE_SPEC` set it runs that builtin spec through `Driver` (the
/// lists from `EVAL_FROZEN`, `EVAL_ONLY` from `CAMPAIGN_CASE_ONLY`) and prints
/// one line `CASE\t<ran N | refused text>`; a no-op otherwise.
#[test]
#[ignore]
fn r02_frozen_child() {
    let Ok(name) = std::env::var("CAMPAIGN_CASE_SPEC") else {
        return;
    };
    let out =
        PathBuf::from(std::env::var("CAMPAIGN_CASE_OUT").expect("conformance: CAMPAIGN_CASE_OUT"));
    let mut d = real_driver(spec(&name).clone(), specs().clone(), &out);
    d.only = std::env::var("CAMPAIGN_CASE_ONLY").ok();
    let line = match d.run() {
        Ok(s) => format!("CASE\tran {}", s.ran),
        Err(e) => format!("CASE\t{}", e.text()),
    };
    use std::io::Write as _;
    let mut o = std::io::stdout().lock();
    writeln!(o, "{line}").expect("conformance: writing the case line");
}

/// Round 02 M1 / round 01 m2: the two-step extension rule through `Driver`,
/// each case a child process (the lists are read once per process) with
/// `EVAL_FROZEN` naming a scratch `frozen.json`: no step + `EVAL_ONLY` →
/// refused (extension); one step + `EVAL_ONLY` (one cheap X1 key) → runs it;
/// one step, no `EVAL_ONLY` → X3A refused **on the extension list**; both steps,
/// no `EVAL_ONLY` → X3A refused on the ceilings only, X1P on its own list (the
/// extension rule satisfied; no full spec is ever run). Run alone.
#[test]
#[ignore]
fn r02_two_step_extension_rule_through_the_driver() {
    let base = temp("r02-two-step");
    let one = frozen_json(&[&["apps/a1/correct/spec/n5r1"]], None, None);
    let two = frozen_json(
        &[&["apps/a1/correct/spec/n5r1"], &["synth/share/m24c12"]],
        None,
        None,
    );
    let cheap = "synth/width/w2|Stateful/Ltr/*|0|*";
    let corner = "apps/a1/correct/spec/n3r2|Stateful/Ltr/*|0|*";
    let cases: [(&str, &str, Option<&str>, &str); 6] = [
        (
            "{}",
            "X1",
            Some(cheap),
            "refused: X1 is not runnable: the extension list is not frozen",
        ),
        // Round 03 m1: under one step only corner keys run.
        (
            &one,
            "X1",
            Some(cheap),
            "refused: X1 is not runnable beyond the corners with one extension step: synth/width/w2",
        ),
        (&one, "X1", Some(corner), "ran 1"),
        (
            &one,
            "X3A",
            None,
            "refused: X3A is not runnable: the extension list is not frozen",
        ),
        (
            &two,
            "X3A",
            None,
            "refused: X3A is not runnable: the budget ceilings list is not frozen",
        ),
        (
            &two,
            "X1P",
            None,
            "refused: X1P is not runnable: the X1P list is not frozen",
        ),
    ];
    let mut bad = Vec::new();
    for (i, (json, sp, only, want)) in cases.iter().enumerate() {
        let dir = base.join(format!("case{i}"));
        fs::create_dir_all(&dir).unwrap();
        let fz = dir.join("frozen.json");
        fs::write(&fz, json).unwrap();
        let mut c = std::process::Command::new(std::env::current_exe().unwrap());
        c.args([
            "--ignored",
            "--exact",
            "conformance::campaign_tests::r02_frozen_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("EVAL_FROZEN", &fz)
        .env("CAMPAIGN_CASE_SPEC", sp)
        .env("CAMPAIGN_CASE_OUT", dir.join("out"))
        .env_remove("CAMPAIGN_CASE_ONLY");
        if let Some(o) = only {
            c.env("CAMPAIGN_CASE_ONLY", o);
        }
        let out = c.output().unwrap();
        let text = String::from_utf8_lossy(&out.stdout).to_string();
        let got = text
            .lines()
            .find_map(|l| l.find("CASE\t").map(|k| l[k + 5..].to_owned()))
            .unwrap_or_else(|| format!("no case line: {}", String::from_utf8_lossy(&out.stderr)));
        note!("r02 case {i} ({sp}, only {only:?}): {got}");
        if got != *want {
            bad.push(format!("case {i} ({sp}): got {got:?}, want {want:?}"));
        }
    }
    assert!(bad.is_empty(), "conformance: {bad:#?}");
}

/// Round 02 M1(a)'s second clause: `FrozenLists::extends` is append-only —
/// identical lists, an appended extension step and a newly frozen X1P list are
/// `Ok`; a changed first step, a removed step and a changed ceilings list are
/// `Err` naming the difference.
#[test]
fn r02_frozen_lists_only_grow() {
    let p = |j: &str| FrozenLists::parse(j).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let a1: &[&str] = &["apps/a1/correct/spec/n5r1"];
    let s2: &[&str] = &["synth/share/m24c12"];
    let base = p(&frozen_json(&[a1], None, Some(&["synth/reset/k2s1|3"])));
    assert_eq!(base.extends(&base), Ok(()), "conformance: identical");
    assert_eq!(
        p(&frozen_json(&[a1, s2], None, Some(&["synth/reset/k2s1|3"]))).extends(&base),
        Ok(()),
        "conformance: an appended step"
    );
    assert_eq!(
        p(&frozen_json(
            &[a1],
            Some(&["synth/commit/n4j2"]),
            Some(&["synth/reset/k2s1|3"])
        ))
        .extends(&base),
        Ok(()),
        "conformance: a newly frozen X1P list"
    );
    assert_eq!(
        base.extends(&FrozenLists::default()),
        Ok(()),
        "conformance: from nothing"
    );
    let changed = p(&frozen_json(
        &[&["apps/a1/correct/spec/n6r1"]],
        None,
        Some(&["synth/reset/k2s1|3"]),
    ));
    assert_eq!(
        changed.extends(&base),
        Err("extension step 1 changed".to_owned())
    );
    let removed = p(&frozen_json(&[], None, Some(&["synth/reset/k2s1|3"])));
    assert_eq!(
        removed.extends(&base),
        Err("an extension step was removed".to_owned())
    );
    let ceil = p(&frozen_json(&[a1], None, Some(&["synth/reset/k2s1|4"])));
    assert_eq!(
        ceil.extends(&base),
        Err("the budget-ceilings list changed or was removed".to_owned())
    );
    // Round 03 M1: once both steps are recorded, a third step (constructed in
    // memory: `parse` refuses three) or any change is refused.
    let both = p(&frozen_json(&[a1, s2], None, None));
    let mut three = both.clone();
    three.extension.push(both.extension[1].clone());
    assert_eq!(
        three.extends(&both),
        Err("the extension list changed after both steps were recorded".to_owned())
    );
    let step2 = p(&frozen_json(&[a1, &["synth/share/m24c24"]], None, None));
    assert_eq!(
        step2.extends(&both),
        Err("the extension list changed after both steps were recorded".to_owned())
    );
    assert_eq!(both.extends(&both), Ok(()));
    let gone = p(&frozen_json(&[a1], None, None));
    assert!(
        gone.extends(&base).is_err(),
        "conformance: a frozen list removed"
    );
    // `to_json` round-trips through `parse`.
    assert_eq!(p(&base.to_json().to_string()), base);
    // … with the `x5` key too (the `P5-X5` landing): every list frozen,
    // `to_json` writes `x5`, `parse` reads it back; a changed or removed X5
    // list does not extend.
    let mut full = p(&frozen_json(
        &[a1, s2],
        Some(&["synth/commit/n4j2"]),
        Some(&["synth/reset/k2s1|3"]),
    ));
    full.x5 = p(&serde_json::json!({ "x5": { "date": "2026-10-08", "source": "campaign_tests", "items": ["synth/share/m24c12"] } }).to_string()).x5;
    assert!(full.x5.is_some());
    assert!(full.to_json().get("x5").is_some_and(|v| v.is_object()));
    assert_eq!(p(&full.to_json().to_string()), full);
    assert_eq!(
        p(&FrozenLists::default().to_json().to_string()),
        FrozenLists::default()
    );
    let mut no_x5 = full.clone();
    no_x5.x5 = None;
    assert_eq!(full.extends(&no_x5), Ok(()), "conformance: X5 newly frozen");
    assert_eq!(
        no_x5.extends(&full),
        Err("the X5 list changed or was removed".to_owned())
    );
}

/// One driver case in a child process (`r02_frozen_child`): the lists from
/// `frozen` (`None`: no file), the store directory `out`; the child's case line.
fn frozen_case(
    dir: &Path,
    frozen: Option<&str>,
    sp: &str,
    only: Option<&str>,
    out: &Path,
) -> String {
    fs::create_dir_all(dir).unwrap();
    let fz = dir.join("frozen.json");
    let _ = fs::remove_file(&fz);
    if let Some(j) = frozen {
        fs::write(&fz, j).unwrap();
    }
    let mut c = std::process::Command::new(std::env::current_exe().unwrap());
    c.args([
        "--ignored",
        "--exact",
        "conformance::campaign_tests::r02_frozen_child",
        "--nocapture",
        "--test-threads=1",
    ])
    .env("EVAL_FROZEN", &fz)
    .env_remove("EVAL_OUT")
    .env("CAMPAIGN_CASE_SPEC", sp)
    .env("CAMPAIGN_CASE_OUT", out)
    .env_remove("CAMPAIGN_CASE_ONLY");
    if let Some(o) = only {
        c.env("CAMPAIGN_CASE_ONLY", o);
    }
    let o = c.output().unwrap();
    String::from_utf8_lossy(&o.stdout)
        .lines()
        .find_map(|l| l.find("CASE\t").map(|k| l[k + 5..].to_owned()))
        .unwrap_or_else(|| format!("no case line: {}", String::from_utf8_lossy(&o.stderr)))
}

/// Round 02 M1(a) / round 03 M1, m1 through `Driver` (child processes; the
/// record is `frozen.used.json` in the store directory):
/// - A: one step, a corner key → `ran 1`; the record = `consumed_by("X1")` of the
///   lists merged into the empty record (no `x1p`, no ceilings);
/// - A′: one step, a synthetic key → refused "beyond the corners";
/// - B: both steps and a frozen X1P list, X1 on the corner key → runs (`ran 0`,
///   the key present); the record holds both steps and **no** `x1p` (X1 does not
///   consume it);
/// - B′: the same file, X1P on one of its keys → `ran 1`; the record now holds
///   the X1P list too;
/// - C: step 2 changed after both were recorded → refused ("the extension list
///   changed after both steps were recorded"), the record unchanged;
/// - D: an unfrozen X0 run (no file, all 12 rows) writes no record;
/// - E: a run that stops at its first row's `store.append` (the store
///   directory's `rows-test.csv` made read-only before the run, so the first
///   row runs in its child and its append fails — `refused: io`) has already
///   written its record (written before the first row).
///
/// Run alone.
#[test]
#[ignore]
fn r02_frozen_record_through_the_driver() {
    let base = temp("r02-record");
    let out = base.join("out");
    let a1: &[&str] = &["apps/a1/correct/spec/n5r1"];
    let s2: &[&str] = &["synth/share/m24c12"];
    let x1p: &[&str] = &["synth/commit/n2j0"];
    let one = frozen_json(&[a1], None, None);
    let two = frozen_json(&[a1, s2], Some(x1p), None);
    let changed = frozen_json(&[a1, &["synth/share/m24c24"]], Some(x1p), None);
    let corner = "apps/a1/correct/spec/n3r2|Stateful/Ltr/*|0|*";
    let cheap = "synth/width/w2|Stateful/Ltr/*|0|*";
    let used = out.join("frozen.used.json");
    let record = |path: &Path| -> serde_json::Value {
        serde_json::from_str(&fs::read_to_string(path).expect("conformance: the record")).unwrap()
    };
    let lists =
        |j: &str| FrozenLists::parse(j).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    // A
    let a = frozen_case(&base.join("a"), Some(&one), "X1", Some(corner), &out);
    note!("r03 record A: {a}");
    assert_eq!(a, "ran 1");
    let rec_a = FrozenLists::merged(&FrozenLists::default(), &lists(&one).consumed_by("X1"));
    assert_eq!(
        record(&used),
        rec_a.to_json(),
        "conformance: the record after A"
    );
    // A′
    let a2 = frozen_case(&base.join("a2"), Some(&one), "X1", Some(cheap), &out);
    note!("r03 record A': {a2}");
    assert_eq!(
        a2,
        "refused: X1 is not runnable beyond the corners with one extension step: synth/width/w2"
    );
    // B
    let b = frozen_case(&base.join("b"), Some(&two), "X1", Some(corner), &out);
    note!("r03 record B: {b}");
    assert_eq!(
        b, "ran 0",
        "conformance: B runs (its one key already present)"
    );
    let rec_b = FrozenLists::merged(&rec_a, &lists(&two).consumed_by("X1"));
    assert!(rec_b.x1p.is_none() && rec_b.extension.len() == 2);
    assert_eq!(
        record(&used),
        rec_b.to_json(),
        "conformance: the record after B (no x1p)"
    );
    // B′
    let b2 = frozen_case(
        &base.join("b2"),
        Some(&two),
        "X1P",
        Some("synth/commit/n2j0|*"),
        &out,
    );
    note!("r03 record B': {b2}");
    assert_eq!(b2, "ran 1");
    let rec_b2 = FrozenLists::merged(&rec_b, &lists(&two).consumed_by("X1P"));
    assert!(rec_b2.x1p.is_some());
    assert_eq!(
        record(&used),
        rec_b2.to_json(),
        "conformance: the record after B' (x1p)"
    );
    // C
    let c = frozen_case(&base.join("c"), Some(&changed), "X1", Some(corner), &out);
    note!("r03 record C: {c}");
    assert!(
        c.starts_with(
            "refused: the frozen lists changed under rows already run: the extension list changed after both steps were recorded (see "
        ),
        "conformance: {c}"
    );
    assert_eq!(
        record(&used),
        rec_b2.to_json(),
        "conformance: a refused run leaves the record"
    );
    // D (no `EVAL_ONLY`: with it, X0 is refused today — T10)
    let out2 = base.join("out-unfrozen");
    let d = frozen_case(&base.join("d"), None, "X0", None, &out2);
    note!("r03 record D: {d}");
    assert_eq!(d, "ran 12");
    assert!(
        !out2.join("frozen.used.json").exists(),
        "conformance: no record for an unfrozen run"
    );
    // E: a read-only store; the run stops at its first append.
    let out3 = base.join("out-stop");
    let store = out3.join(if prof() == "release" {
        "rows.csv"
    } else {
        "rows-test.csv"
    });
    drop(
        crate::conformance::eval::Store::open(
            &store,
            "campaign-tests-host",
            "campaign-tests",
            true,
        )
        .unwrap_or_else(|e| panic!("conformance: {}", e.text())),
    );
    let mut perm = fs::metadata(&store).unwrap().permissions();
    perm.set_readonly(true);
    fs::set_permissions(&store, perm).unwrap();
    let e = frozen_case(&base.join("e"), Some(&one), "X1", Some(corner), &out3);
    note!("r03 record E: {e}");
    assert!(
        e.starts_with("refused: io"),
        "conformance: the run stopped at its first append: {e}"
    );
    assert!(
        fs::read_dir(out3.join("runs"))
            .map(|d| d.count())
            .unwrap_or(0)
            == 1,
        "conformance: exactly one row ran in its child"
    );
    assert_eq!(
        record(&out3.join("frozen.used.json")),
        rec_a.to_json(),
        "conformance: the record was written before the first row"
    );
}

/// Round 01 n2: the four corners are one-point lines labelled
/// `<model>/<variant>/corner/<knobs>` (`APPS_CORNER_LINES`, round 02 n4: the
/// fixed coordinates included), each holding exactly its corner fixture.
#[test]
fn r01_corner_lines_follow_the_label_rule() {
    assert_eq!(
        APPS_CORNER_LINES,
        [
            "a1/correct/corner/n=3,r=2",
            "a2/pb/corner/k=3,q=3",
            "a3/fifo/corner/k=3,q=2",
            "a4/hash-a4b/corner/k=3,q=2,m=3"
        ]
    );
    let g = apps_grid();
    for (i, (fx, fam)) in APPS_CORNERS.iter().enumerate() {
        let on: Vec<&SynthPoint> = g
            .iter()
            .filter(|p| p.line == APPS_CORNER_LINES[i])
            .collect();
        assert_eq!(
            on.len(),
            1,
            "conformance: {} is a one-point line",
            APPS_CORNER_LINES[i]
        );
        assert_eq!(on[0].fixture, *fx);
        assert_eq!(on[0].family, *fam);
        assert!(APPS_CORNER_LINES[i].starts_with(&format!("{fam}/")));
    }
    assert!(!g
        .iter()
        .any(|p| p.line.contains("/corner") && !APPS_CORNER_LINES.contains(&p.line)));
}

/// Round 01 M1: the pinned gate report with every spawned thread stopped.
const M1_INSTANCE: &str = "corpus/VisibleMutation/0x200000000|Gated|Reverse";

/// The first report of an X2P-configured in-process run (lean path), as
/// (is a gate report, every spawned thread stopped) — `None` without a report.
fn first_report_shape(fixture: &str, cfg: &GridConfig) -> Option<(bool, bool)> {
    use crate::conformance::morphism::CompleteExecution;
    let f = fixture_by_name(fixture).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let GridEnd::Ok(r) = run_row_in_process(&f, cfg, false) else {
        panic!("conformance: {fixture}: the run did not complete");
    };
    match &r.raw {
        GridRaw::Gated(o) => o.reports.first().map(|(g, _, site)| {
            let gate = !matches!(site, crate::conformance::gated::ReportSite::Completion);
            (gate, CompleteExecution::try_finished(g).is_some())
        }),
        GridRaw::Enumerator(o) => o.reports.first().map(|rep| {
            let gate = !matches!(rep.gate, Some(crate::conformance::ctx::Gate::Completion));
            (gate, CompleteExecution::try_finished(&rep.graph).is_some())
        }),
        _ => None,
    }
}

/// Round 01 M1's concrete instance: a **gate** first report whose spawned
/// threads have all stopped (`try_finished` holds — main's half aside), so a
/// status vector computed from `try_finished` alone would be written for a
/// growing report. Searched over every hand-count X2 fixture (the §6 paper and
/// corpus violating pairs, `ex:naive/e2/k{2,3}`, `ex:naive/k{2,3}`, S5 at
/// `k ≤ 2, s = 1`) on the enumerator and the gated engine under all three
/// selectors (X2P's configuration, lean path). The fixtures found are pinned;
/// the exports test checks that such a report exports `growth: growing`,
/// `statuses: null`.
#[test]
fn r01_m1_gate_reports_with_every_spawned_thread_stopped() {
    let mut fx: Vec<String> = PAPER_VIOLATING.iter().map(|s| (*s).to_owned()).collect();
    fx.extend(corpus_sides().1);
    for k in [2, 3] {
        fx.push(format!("ex:naive/e2/k{k}"));
        fx.push(format!("ex:naive/k{k}/enc1"));
        fx.push(format!("ex:naive/k{k}/enc2"));
    }
    for k in [1, 2] {
        fx.push(format!("synth/reset/k{k}s1"));
        fx.push(format!("synth/reset-ctl/k{k}s1"));
    }
    let mut found = BTreeSet::new();
    let mut gate_reports = 0;
    for f in &fx {
        for e in [GridEngine::Enumerator, GridEngine::Gated] {
            for s in SELECTORS {
                if let Some((gate, stopped)) = first_report_shape(f, &x2_config(e, s)) {
                    if gate {
                        gate_reports += 1;
                        if stopped {
                            found.insert(format!("{f}|{e:?}|{s:?}"));
                        }
                    }
                }
            }
        }
    }
    note!(
        "r01 M1: {gate_reports} gate first reports; every spawned thread stopped in {}: {found:?}",
        found.len()
    );
    // Measured 2026-10-09: 219 gate first reports, 25 with every spawned
    // thread stopped — `R1` (enumerator, every selector: a visible-error
    // report), `R2` and `a27` (enumerator, `Reverse`), and the ten
    // `corpus/VisibleMutation/*` pairs on both engines under `Reverse` (main's
    // `FreshSend` to `c`, which blocked first — the reviewer's derivation).
    assert_eq!(gate_reports, 219);
    assert_eq!(found.len(), 25, "conformance: {found:?}");
    assert!(
        found.contains(M1_INSTANCE),
        "conformance: the pinned M1 instance {M1_INSTANCE}"
    );
}

// =========================================================================
// Driver helpers
// =========================================================================

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tf-campaign-tests-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).expect("conformance: a temp directory");
    d
}

fn clean_probes() -> Probes {
    Probes {
        git: Box::new(|| ("campaign-tests".to_owned(), false)),
        host: Box::new(|| "campaign-tests-host".to_owned()),
    }
}

fn driver(s: Spec, out: &Path, probes: Probes) -> Driver {
    Driver {
        spec: s,
        specs: specs().clone(),
        out_dir: out.to_path_buf(),
        sample_period: Duration::from_millis(100),
        probes,
        allow_mixed: false,
        // A safety net for the refusal tests: should a refusal be missing (a
        // mutation), the driver refuses this filter instead of running the
        // spec's children; the test still fails on the refusal's reason.
        only: Some("campaign-tests: selects no key".to_owned()),
    }
}

/// The real probes with `allow_mixed` (the gate-3 tree is dirty).
fn real_driver(s: Spec, all: Vec<Spec>, out: &Path) -> Driver {
    Driver {
        spec: s,
        specs: all,
        out_dir: out.to_path_buf(),
        sample_period: Duration::from_millis(100),
        probes: Probes::real(),
        allow_mixed: true,
        only: None,
    }
}
