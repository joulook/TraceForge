//! `P5-X5` gate 3: the tester's tests (criteria `P5-X5.md` revision 3.1, the
//! gate-2 erratum and the landing errata E-X5-1..3).
//!
//! Tester-owned (the two module lines in `mod.rs` are the lead's, criterion
//! 10). Every expected figure here was derived **before** the lead's `P5-X5`
//! code was read: `plan/traceForge/log/dev/P5-X5.derived.md` (its sha256 is in
//! `backlog/changes.md`). Tests are named by criterion (`c01_…` … `c07_…`); a
//! test that reproduces a defect of the lead's code is named `t<N>_…` after its
//! T-finding in `log/dev/P5-X5.report.md` and is `#[ignore]`d while the defect
//! stands, with the expected and measured values in its rustdoc. Tests that
//! spawn child processes (the driver, the frozen lists) are `#[ignore]`d too and
//! run one per invocation (`--ignored --exact … --test-threads=1`); they write
//! only under the system temporary directory.
//!
//! The read-time functions criteria 3, 4 and 7 ask for — the pair checker
//! [`check_store`] and the measures [`measures`] — live here and are applied
//! to a constructed store (`c07_…`) and to the pilot's store (`c05_…`).
//!
//! Records read at test time (read-only): `plan/traceForge/log/dev/P4-FLAT.tables.md`
//! (criterion 9's table: `communication_flat` and the verdict per fixture).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::Duration;

use crate::conformance::cfirst;
use crate::conformance::config::{CompletionCover, GatePolicy, GatedMode};
use crate::conformance::eval::{
    all_fixtures, builtin_specs, eval_row_of, experiments_of, header, profile_name, read_rows,
    record_of, run_row_in_process, x1_config, x2_config, x5_partner, Driver, FrozenLists,
    PartnerClass, Probes, RowMeta, RowSpec, RunKind, Spec, Tier, SCHEMA_VERSION,
};
use crate::conformance::gated;
use crate::conformance::grid::{
    apps_grid, synth_grid, Fixture, GridConfig, GridEnd, GridEngine, Row, SynthPoint, FLAT_SUBSET,
};
use crate::conformance::grid_oracle::canon_key;
use crate::conformance::selector::Selector;

/// Writes a line to stderr (the closed `s5_tests` emission scan forbids the
/// print macros in every file under `conformance/` outside its test-only list).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

// =========================================================================
// Shared data
// =========================================================================

const SELECTORS: [Selector; 3] = [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];

type Rec = BTreeMap<String, String>;

fn plan() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../plan/traceForge")
}

fn prof() -> &'static str {
    profile_name()
}

/// `builtin_specs()` once per test process.
fn specs() -> &'static Vec<Spec> {
    static S: OnceLock<Vec<Spec>> = OnceLock::new();
    S.get_or_init(builtin_specs)
}

fn spec(name: &str) -> &'static Spec {
    specs()
        .iter()
        .find(|s| s.name == name)
        .unwrap_or_else(|| panic!("conformance: x5_tests: no builtin spec {name}"))
}

fn key_sets() -> &'static BTreeMap<String, BTreeSet<String>> {
    static K: OnceLock<BTreeMap<String, BTreeSet<String>>> = OnceLock::new();
    K.get_or_init(|| {
        specs()
            .iter()
            .map(|s| {
                (
                    s.name.clone(),
                    s.rows.iter().map(|r| r.key(prof())).collect(),
                )
            })
            .collect()
    })
}

fn ks(name: &str) -> &'static BTreeSet<String> {
    &key_sets()[name]
}

/// Every fixture by name, once per process (`all_fixtures` builds them all).
fn fixtures() -> &'static BTreeMap<String, Fixture> {
    static F: OnceLock<BTreeMap<String, Fixture>> = OnceLock::new();
    F.get_or_init(|| {
        all_fixtures()
            .into_iter()
            .map(|f| (f.name.clone(), f))
            .collect()
    })
}

fn fixture(name: &str) -> &'static Fixture {
    fixtures()
        .get(name)
        .unwrap_or_else(|| panic!("conformance: x5_tests: no fixture {name}"))
}

/// `P4-FLAT.tables.md`'s criterion-9 table, parsed: per fixture, whether every
/// row says `communication_flat = true`, and the verdict (one per fixture —
/// asserted consistent across engines and selectors).
fn flat_table() -> &'static BTreeMap<String, (bool, String)> {
    static T: OnceLock<BTreeMap<String, (bool, String)>> = OnceLock::new();
    T.get_or_init(|| {
        let text = fs::read_to_string(plan().join("log/dev/P4-FLAT.tables.md"))
            .expect("conformance: x5_tests: reading P4-FLAT.tables.md");
        let mut hdr: Vec<String> = Vec::new();
        let mut out: BTreeMap<String, (bool, String)> = BTreeMap::new();
        for line in text.lines() {
            if line.starts_with("### P4-FLAT criterion 6") {
                break;
            }
            if !line.starts_with('|') || line.starts_with("|---") {
                continue;
            }
            let cells: Vec<String> = line
                .trim()
                .trim_matches('|')
                .split('|')
                .map(|c| c.trim().to_owned())
                .collect();
            if cells[0] == "fixture" {
                hdr = cells;
                continue;
            }
            let col = |n: &str| {
                let i = hdr
                    .iter()
                    .position(|h| h == n)
                    .unwrap_or_else(|| panic!("conformance: x5_tests: no column {n}"));
                cells[i].clone()
            };
            let flat = col("communication_flat") == "true";
            let verdict = col("verdict");
            let e = out
                .entry(col("fixture"))
                .or_insert_with(|| (flat, verdict.clone()));
            assert_eq!(
                (e.0, &e.1),
                (flat, &verdict),
                "conformance: x5_tests: a fixture with two flat labels or verdicts"
            );
        }
        out
    })
}

/// The parsed `FLAT_SUBSET`: the table's flat fixtures minus `mixed/*`.
fn parsed_flat_subset() -> BTreeSet<String> {
    flat_table()
        .iter()
        .filter(|(n, (flat, _))| *flat && !n.starts_with("mixed/"))
        .map(|(n, _)| n.clone())
        .collect()
}

fn parsed_violating(name: &str) -> bool {
    flat_table()
        .get(name)
        .map(|(_, v)| v == "Reported")
        .unwrap_or_else(|| panic!("conformance: x5_tests: {name} not in the table"))
}

/// My partner class per point kind (derived.md §2), independent of
/// `x5_partner`: `stop = true` → X2; a conforming point → X1; an exhaustive
/// `ex:naive/k*` → X1V; every other violating registry point → own.
fn derived_class(fixture: &str, stop: bool, gated: bool) -> PartnerClass {
    if gated {
        return PartnerClass::Own;
    }
    if stop {
        return PartnerClass::X2;
    }
    let synthetic_conforming = ["synth/naive-self/", "synth/share/", "synth/commit/"]
        .iter()
        .chain(["synth/chain/", "synth/width/"].iter())
        .any(|p| fixture.starts_with(p));
    if synthetic_conforming || (flat_table().contains_key(fixture) && !parsed_violating(fixture)) {
        PartnerClass::X1
    } else if fixture.starts_with("ex:naive/k") {
        PartnerClass::X1V
    } else {
        PartnerClass::Own
    }
}

fn holder(class: PartnerClass, own: &str) -> &'static str {
    match class {
        PartnerClass::X1 => "X1",
        PartnerClass::X1V => "X1V",
        PartnerClass::X2 => "X2",
        PartnerClass::Own => {
            if own == "X5" {
                "X5"
            } else {
                "X5G"
            }
        }
    }
}

fn is_flat(r: &RowSpec) -> bool {
    r.config.completion_cover == CompletionCover::Flat
}

/// The sweep arm's configuration of a host, as derived (F1; E-X5-3).
fn sweep_cfg(gated: bool, s: Selector, stop: bool) -> GridConfig {
    if gated {
        x1_config(GridEngine::Gated, s)
            .gated(GatedMode::Exhaustive, GatePolicy::Never)
            .precheck(true)
            .stop(stop)
    } else if stop {
        x2_config(GridEngine::CompleteFirst, s)
    } else {
        x1_config(GridEngine::CompleteFirst, s)
    }
}

fn flat_cfg(gated: bool, s: Selector, stop: bool) -> GridConfig {
    sweep_cfg(gated, s, stop)
        .precheck(true)
        .cover(CompletionCover::Flat)
}

/// The eight-point sample list of derived.md §3.1.
const SAMPLE: [&str; 8] = [
    "synth/naive-self/k2enc1",
    "synth/naive-self/k3enc2",
    "ex:naive/k2/enc1",
    "ex:naive/k5/enc2",
    "synth/share/m2c0",
    "synth/commit/n4j2",
    "synth/chain/d8",
    "synth/width/w8",
];

/// F2's admissible set, from the criteria's text (E-X5-1): S1's conforming
/// twin at every `k`, `ex:naive/k{k}/enc*` at `k ≤ 5`, `synth/share/*`,
/// `synth/commit/*`, `synth/chain/*`, `synth/width/*`.
fn admissible_by_derivation(n: &str) -> bool {
    let naive_k_le5 = (2..=5).any(|k| n.starts_with(&format!("ex:naive/k{k}/enc")));
    n.starts_with("synth/naive-self/")
        || naive_k_le5
        || [
            "synth/share/",
            "synth/commit/",
            "synth/chain/",
            "synth/width/",
        ]
        .iter()
        .any(|p| n.starts_with(p))
}

/// The admissible in-grid points (70 by derivation).
fn full_admissible_list() -> Vec<String> {
    synth_grid()
        .into_iter()
        .filter(|p| p.in_grid && admissible_by_derivation(&p.fixture))
        .map(|p| p.fixture)
        .collect()
}

/// A `frozen.json` text with two admissible extension steps (neither naming a
/// point of the sample) and the given `x5` list.
fn frozen_text(x5: Option<&[String]>) -> String {
    let step = |items: Vec<String>| serde_json::json!({ "date": "2026-10-08", "source": "x5_tests", "items": items });
    let mut v = serde_json::json!({
        "extension": [
            step(vec!["apps/a1/correct/spec/n5r1".to_owned()]),
            step(vec!["synth/share/m24c12".to_owned()]),
        ],
    });
    if let Some(items) = x5 {
        v["x5"] = step(items.to_vec());
    }
    v.to_string()
}

// =========================================================================
// Criterion 1 — the spec as data
// =========================================================================

/// C1: `FLAT_SUBSET` is the parsed table's `communication_flat = true` set
/// minus `mixed/*` (62 names: 24 conforming, 38 violating), names no `apps/*`,
/// `synth/reset*`, `synth/share-ctl*`, and no name twice.
#[test]
fn c01_flat_subset_is_the_parsed_table_minus_mixed() {
    let parsed = parsed_flat_subset();
    let landed: BTreeSet<String> = FLAT_SUBSET.iter().map(|s| (*s).to_owned()).collect();
    assert_eq!(landed.len(), FLAT_SUBSET.len(), "conformance: a name twice");
    assert_eq!(parsed.len(), 62, "conformance: the table's flat subset");
    assert_eq!(landed, parsed, "conformance: FLAT_SUBSET against the table");
    let violating = parsed.iter().filter(|n| parsed_violating(n)).count();
    assert_eq!(
        (parsed.len() - violating, violating),
        (24, 38),
        "conformance: conforming / violating"
    );
    for n in &landed {
        assert!(
            !n.starts_with("apps/")
                && !n.starts_with("synth/reset")
                && !n.starts_with("synth/share-ctl"),
            "conformance: FLAT_SUBSET names {n}"
        );
        assert!(
            !n.starts_with("ex:naive/e2/k5")
                && !n.starts_with("ex:naive/e2/k6")
                && !n.starts_with("ex:naive/e2/k7"),
            "conformance: the e2/k{{5,6,7}} exclusion: {n}"
        );
    }
}

/// Splits a host's spec into its Flat and sweep rows and checks every row's
/// configuration against the derivation (F1; E-X5-3; gate 3 T4/T5): engine,
/// `precheck`, cover, `stop` only on `ex:naive/k*` (three selectors) and every
/// other point under its kind's selectors, the sweep rows built by the
/// partner's configuration function (`x2_config` for the `stop` pairs), the
/// gated mode and policy (X5G), three reps, the default tier, timed, and
/// `twin_key` empty on every row (T4) except the 108 sweep rows X5 lists for
/// X2-held keys, which carry X2's RQ2 twin key exactly (T6). Returns the Flat rows and the sweep
/// rows.
fn check_host_rows(name: &str, gated: bool) -> (Vec<&'static RowSpec>, Vec<&'static RowSpec>) {
    let s = spec(name);
    let (flat, sweep): (Vec<&RowSpec>, Vec<&RowSpec>) = s.rows.iter().partition(|r| is_flat(r));
    let mut bad = Vec::new();
    let x2_twins: BTreeMap<String, String> = spec("X2")
        .rows
        .iter()
        .map(|r| (r.key(prof()), r.twin_key.clone()))
        .collect();
    let mut x2_held = 0usize;
    for r in s.rows.iter() {
        let stop = r.config.stop_at_first_report;
        let want = if is_flat(r) {
            flat_cfg(gated, r.config.selector, stop)
        } else {
            sweep_cfg(gated, r.config.selector, stop)
        };
        if r.config.label() != want.label() {
            bad.push(format!(
                "{}: label {} not {}",
                r.fixture,
                r.config.label(),
                want.label()
            ));
        }
        if stop && !r.fixture.starts_with("ex:naive/k") {
            bad.push(format!("{}: stop = {stop}", r.fixture));
        }
        // T4/T6: empty on every row except the sweep rows X5 lists for an
        // X2-held key, which carry X2's RQ2 twin key.
        match x2_twins.get(&r.key(prof())) {
            Some(t) if !is_flat(r) => {
                x2_held += 1;
                if t.is_empty() || &r.twin_key != t {
                    bad.push(format!(
                        "{}: twin_key {:?}, X2's {t:?}",
                        r.fixture, r.twin_key
                    ));
                }
            }
            _ => {
                if !r.twin_key.is_empty() {
                    bad.push(format!("{}: twin_key {}", r.fixture, r.twin_key));
                }
            }
        }
        if r.tier != Tier::default_tier() || r.run_kind != RunKind::Timed || r.rep > 2 {
            bad.push(format!(
                "{}: tier/kind/rep {:?} {:?} {}",
                r.fixture, r.tier.name, r.run_kind, r.rep
            ));
        }
    }
    assert!(bad.is_empty(), "conformance: {name} rows: {bad:#?}");
    let want_held = if gated { 0 } else { 108 };
    assert_eq!(
        x2_held, want_held,
        "conformance: {name}'s X2-held sweep rows (with X2's twin key)"
    );
    (flat, sweep)
}

/// Selectors per (fixture, stop) over a row list.
fn selectors_of(rows: &[&RowSpec]) -> BTreeMap<(String, bool), BTreeSet<String>> {
    let mut m: BTreeMap<(String, bool), BTreeSet<String>> = BTreeMap::new();
    for r in rows {
        m.entry((r.fixture.clone(), r.config.stop_at_first_report))
            .or_default()
            .insert(format!("{:?}", r.config.selector));
    }
    m
}

/// C1 with the X5 list empty (this process reads no `frozen.json`), derived
/// (derived.md §3) and measured on the fixed tree (`eval.rs` `bb9da53e…`): X5
/// = **294** `A_flat` rows (the 12 `ex:naive/k{2..7}/enc{1,2}` × 3 selectors ×
/// 3 reps with `stop = true` = 108, and the 62 `FLAT_SUBSET` points × `Ltr` × 3
/// reps = 186 — T1 fixed) + **294** sweep rows (every partner listed, T2
/// fixed) = **588** keys, each once; X5G (gate 4 m2: exhaustive points only) 186 + 186 = **372**. The
/// sweep rows are exactly the partners of the Flat rows (`x5_partner`).
#[test]
fn c01_x5_and_x5g_rows_with_the_list_empty() {
    for (name, gated) in [("X5", false), ("X5G", true)] {
        let (flat, sweep) = check_host_rows(name, gated);
        let keys: BTreeSet<String> = spec(name).rows.iter().map(|r| r.key(prof())).collect();
        assert_eq!(
            keys.len(),
            spec(name).rows.len(),
            "conformance: {name} duplicate keys"
        );
        let sel = selectors_of(&flat);
        let three: BTreeSet<String> = SELECTORS.iter().map(|s| format!("{s:?}")).collect();
        let ltr: BTreeSet<String> = ["Ltr".to_owned()].into();
        let mut stop_points = BTreeSet::new();
        let mut ltr_points = BTreeSet::new();
        for ((f, stop), s) in &sel {
            if *stop {
                assert_eq!(s, &three, "conformance: {name} {f} stop selectors");
                stop_points.insert(f.clone());
            } else {
                assert_eq!(s, &ltr, "conformance: {name} {f} selectors");
                ltr_points.insert(f.clone());
            }
        }
        let want_stop: BTreeSet<String> = (2..=7)
            .flat_map(|k| (1..=2).map(move |e| format!("ex:naive/k{k}/enc{e}")))
            .collect();
        // m2: X5G runs the exhaustive points only.
        let want_stop = if gated { BTreeSet::new() } else { want_stop };
        assert_eq!(stop_points, want_stop, "conformance: {name} stop points");
        assert_eq!(
            ltr_points,
            parsed_flat_subset(),
            "conformance: {name} FLAT_SUBSET points (all 62)"
        );
        let n_flat = if gated { 186 } else { 294 };
        assert_eq!(flat.len(), n_flat, "conformance: {name} A_flat rows");
        let partners: BTreeSet<String> = flat.iter().map(|r| x5_partner(r).0).collect();
        let sweep_keys: BTreeSet<String> = sweep.iter().map(|r| r.key(prof())).collect();
        assert_eq!(
            sweep_keys, partners,
            "conformance: {name}'s sweep rows are its partners"
        );
        assert_eq!(sweep.len(), n_flat, "conformance: {name} sweep rows");
        assert_eq!(
            keys.len(),
            2 * n_flat,
            "conformance: {name} keys (588 / 372)"
        );
        let reps: BTreeSet<u32> = spec(name).rows.iter().map(|r| r.rep).collect();
        assert_eq!(reps, [0, 1, 2].into(), "conformance: {name} reps");
    }
}

/// T1 fixed (the former `t1_…` pin, now positive): with the X5 list empty
/// every `FLAT_SUBSET` point has its three `Ltr` `A_flat` rows, the six
/// `ex:naive/k{2,3,4}/enc{1,2}` included; `A_flat` = 294.
#[test]
fn c01_every_flat_subset_point_has_its_ltr_rows_with_the_list_empty() {
    let mut per: BTreeMap<String, usize> = BTreeMap::new();
    for r in spec("X5")
        .rows
        .iter()
        .filter(|r| is_flat(r) && !r.config.stop_at_first_report)
    {
        *per.entry(r.fixture.clone()).or_default() += 1;
    }
    let missing: Vec<String> = parsed_flat_subset()
        .into_iter()
        .filter(|n| per.get(n) != Some(&3))
        .collect();
    let n_flat = spec("X5").rows.iter().filter(|r| is_flat(r)).count();
    assert!(
        missing.is_empty() && n_flat == 294,
        "conformance: T1: FLAT_SUBSET points without their 3 Ltr rows {missing:?}; A_flat {n_flat}, derived 294"
    );
}

/// T2 fixed (the former `t2_…` pin, now positive; F1, criterion 1, round 03
/// m2, `P5-CAMPAIGN` C1): every `A_flat` row's partner key is an X5 key; a
/// shared partner is also a key of its named spec and `experiments_of` names
/// both there; the overlaps with the list empty are `X1 ∩ X5` = 72, `X1V ∩ X5`
/// = 18, `X2 ∩ X5` = 108 (= the shared partners), `X0 ∩ X5` = 1 (X0's
/// complete-first `Ltr` key of `ex:naive/k2/enc1` is X1V's partner key), and
/// every other spec's overlap with X5 and with X5G is empty.
#[test]
fn c01_x5_lists_every_sweep_partner_and_shares_the_key() {
    let x5 = ks("X5");
    let mut bad = Vec::new();
    for r in spec("X5").rows.iter().filter(|r| is_flat(r)) {
        let (pk, class) = x5_partner(r);
        if !x5.contains(&pk) {
            bad.push(format!("not held: {class:?} {pk}"));
            continue;
        }
        if class != PartnerClass::Own {
            let names = experiments_of(&pk, specs(), prof());
            let h = holder(class, "X5").to_owned();
            if !(names.contains(&"X5".to_owned()) && names.contains(&h)) {
                bad.push(format!("experiments_of({pk}) = {names:?}"));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: T2: {bad:#?}");
    let mut over: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for s in specs() {
        if s.name == "X5" || s.name == "X5G" {
            continue;
        }
        let a = ks(&s.name).intersection(ks("X5")).count();
        let b = ks(&s.name).intersection(ks("X5G")).count();
        if a + b > 0 {
            over.insert(s.name.clone(), (a, b));
        }
    }
    note!("overlaps with (X5, X5G): {over:?}");
    let want: BTreeMap<String, (usize, usize)> = [
        ("X0".to_owned(), (1, 0)),
        ("X1".to_owned(), (72, 0)),
        ("X1V".to_owned(), (18, 0)),
        ("X2".to_owned(), (108, 0)),
    ]
    .into();
    assert_eq!(over, want, "conformance: the overlaps with X5 and X5G");
    assert_eq!(
        ks("X5").intersection(ks("X5G")).count(),
        0,
        "conformance: X5 ∩ X5G"
    );
}

/// The shared keys' stored content does not depend on which spec runs them
/// first: for every X5 row whose key another spec holds, the two `RowSpec`s
/// agree field by field (fixture, configuration, rep, tier, run kind, family,
/// knobs, k, variant, series) — **except `twin_key`**, which this test reports
/// separately (`twin_key` is a stored column, H7).
fn shared_row_differences() -> (Vec<String>, Vec<String>) {
    let mut fields = Vec::new();
    let mut twins = Vec::new();
    let x5: BTreeMap<String, &RowSpec> =
        spec("X5").rows.iter().map(|r| (r.key(prof()), r)).collect();
    for s in specs() {
        // X0 (the harness's own spec, `P5-HARNESS` criterion 1) labels its one
        // shared key `family = ex:naive` with no series — the same difference
        // it already has with X1V (`P5-CAMPAIGN` gate-3 T6), not X5's.
        if s.name == "X5" || s.name == "X5G" || s.name == "X0" {
            continue;
        }
        for r in &s.rows {
            let Some(o) = x5.get(&r.key(prof())) else {
                continue;
            };
            let a = (
                &r.family,
                &r.knobs,
                r.k,
                &r.variant,
                r.series.as_ref().map(|x| format!("{x:?}")),
            );
            let b = (
                &o.family,
                &o.knobs,
                o.k,
                &o.variant,
                o.series.as_ref().map(|x| format!("{x:?}")),
            );
            if a != b {
                fields.push(format!("{} {}: {a:?} vs X5 {b:?}", s.name, r.fixture));
            }
            if r.twin_key != o.twin_key {
                twins.push(format!(
                    "{} {}: {:?} vs X5 {:?}",
                    s.name, r.fixture, r.twin_key, o.twin_key
                ));
            }
        }
    }
    (fields, twins)
}

/// The shared keys' metadata agree between X5 and their holder (the store
/// writes whichever spec runs a key first).
#[test]
fn c01_shared_keys_carry_the_same_row_metadata() {
    let (fields, _) = shared_row_differences();
    assert!(fields.is_empty(), "conformance: {fields:#?}");
}

/// T6 fixed (the former `t6_…` pin, now positive; H1's "a row in two specs is
/// one key, run once"): on every key X5 shares with another spec (X1, X1V, X2)
/// the two `RowSpec`s carry the same `twin_key`, so the stored row does not
/// depend on which spec runs the key first.
#[test]
fn c01_shared_keys_carry_the_same_twin_key() {
    let (_, twins) = shared_row_differences();
    assert!(
        twins.is_empty(),
        "conformance: T6: {} shared keys with another twin_key (first: {:?})",
        twins.len(),
        twins.first()
    );
}

/// C1 (round 03 m1, m2; E-X5-3; T4): `x5_partner` is the sole partner API —
/// its class equals the class derived per point kind, its key is the Flat
/// label with `cover = Sweep` (and `precheck = false` in the complete-first
/// host only), and **the partner key is a key of its named spec** (X1, X1V, X2,
/// or the host's own) and of the host. With the list empty: X5's partners X1
/// 72, X1V 18, X2 108, own 96; X5G's own 186. No own partner is a key of X1,
/// X1V or X2. X2's complete-first configuration is X1's with `stop`.
#[test]
fn c01_every_partner_is_a_key_of_its_named_spec() {
    for (name, gated) in [("X5", false), ("X5G", true)] {
        let mut per: BTreeMap<String, usize> = BTreeMap::new();
        let mut bad = Vec::new();
        for r in spec(name).rows.iter().filter(|r| is_flat(r)) {
            let (pk, class) = x5_partner(r);
            let want = derived_class(&r.fixture, r.config.stop_at_first_report, gated);
            if class != want {
                bad.push(format!("{}: class {class:?}, derived {want:?}", r.fixture));
            }
            let mut pc = r.config.clone();
            pc.completion_cover = CompletionCover::Sweep;
            if !gated {
                pc.precheck = false;
            }
            let want_key = crate::conformance::eval::key_of(
                &r.fixture,
                &pc.label(),
                r.rep,
                &r.tier.name,
                r.run_kind,
                prof(),
            );
            if pk != want_key {
                bad.push(format!("{}: partner {pk}, derived {want_key}", r.fixture));
            }
            let h = holder(want, name);
            if !ks(h).contains(&pk) || !ks(name).contains(&pk) {
                bad.push(format!(
                    "{}: partner {pk} not a key of {h} and {name}",
                    r.fixture
                ));
            }
            if want == PartnerClass::Own && ["X1", "X1V", "X2"].iter().any(|s| ks(s).contains(&pk))
            {
                bad.push(format!(
                    "{}: an own partner held elsewhere: {pk}",
                    r.fixture
                ));
            }
            *per.entry(h.to_owned()).or_default() += 1;
        }
        assert!(bad.is_empty(), "conformance: {name}: {bad:#?}");
        let want: BTreeMap<String, usize> = if gated {
            [("X5G".to_owned(), 186)].into()
        } else {
            [
                ("X1".to_owned(), 72),
                ("X1V".to_owned(), 18),
                ("X2".to_owned(), 108),
                ("X5".to_owned(), 96),
            ]
            .into()
        };
        assert_eq!(per, want, "conformance: {name}'s partners per holder");
    }
    for s in SELECTORS {
        assert_eq!(
            x2_config(GridEngine::CompleteFirst, s).label(),
            x1_config(GridEngine::CompleteFirst, s).stop(true).label(),
            "conformance: X2's complete-first configuration"
        );
    }
}

/// C1, F5/criterion 6's status per point: every X5 point is an X1 point (X1
/// holds its four checkers under `Ltr`) or "not an X1 point". With the list
/// empty: the 24 conforming `FLAT_SUBSET` points are X1 points (incl.
/// `traces/self`: the reason the own count is 96, not 99); the 32 violating
/// ones and the 12 `ex:naive` `stop` points are not.
#[test]
fn c06_x1_status_of_every_x5_point() {
    let x1 = ks("X1");
    let mut x1_points = BTreeSet::new();
    let mut not_x1 = BTreeSet::new();
    for r in spec("X5").rows.iter().filter(|r| is_flat(r)) {
        let four = [
            GridEngine::Enumerator,
            GridEngine::Stateful,
            GridEngine::CompleteFirst,
            GridEngine::Gated,
        ]
        .iter()
        .all(|e| {
            let k = crate::conformance::eval::key_of(
                &r.fixture,
                &x1_config(*e, Selector::Ltr).label(),
                0,
                "default",
                RunKind::Timed,
                prof(),
            );
            x1.contains(&k)
        });
        if four {
            x1_points.insert(r.fixture.clone());
        } else {
            not_x1.insert(r.fixture.clone());
        }
    }
    assert!(
        x1_points.contains("traces/self"),
        "conformance: traces/self is an X1 point"
    );
    assert_eq!(
        (x1_points.len(), not_x1.len()),
        (24, 44),
        "conformance: X1 points / not"
    );
    assert!(
        x1_points.iter().all(|n| !parsed_violating(n)),
        "conformance: every X1 point conforms"
    );
}

/// The frozen `x5` list's admissible set (E-X5-1; F2): a `synth/reset/*`,
/// `synth/reset-twin/*`, `synth/reset-ctl/*`, `synth/share-ctl/*`, `apps/*`
/// or `ex:naive/k{6,7}/*` name panics at parse with a `conformance:` message
/// naming the X5 list ("outside its admissible set"); a name twice panics;
/// a non-grid name panics; the sample list and the full admissible list (70
/// points, my set) parse, and every in-grid point the parser accepts alone is
/// in my set.
#[test]
fn c01_the_x5_lists_admissible_set() {
    let grid: BTreeSet<String> = synth_grid()
        .into_iter()
        .chain(apps_grid())
        .filter(|p| p.in_grid)
        .map(|p| p.fixture)
        .collect();
    let parse = |items: Vec<String>| -> Result<FrozenLists, String> {
        let text = frozen_text(Some(&items));
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let r = catch_unwind(AssertUnwindSafe(|| FrozenLists::parse(&text)));
        std::panic::set_hook(prev);
        match r {
            Ok(Ok(l)) => Ok(l),
            Ok(Err(e)) => Err(format!("refusal: {}", e.text())),
            Err(p) => Err(p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_default()),
        }
    };
    let inadmissible = [
        "synth/reset/k1s1",
        "synth/reset-twin/k1s1",
        "synth/reset-ctl/k1s1",
        "synth/share-ctl/m2c0",
        "apps/a1/correct/spec/n2r1",
        "ex:naive/k6/enc1",
        "ex:naive/k7/enc2",
    ];
    for n in inadmissible {
        assert!(grid.contains(n), "conformance: {n} is a grid point");
        let e = parse(vec![n.to_owned()]).expect_err("conformance: an inadmissible name parsed");
        assert!(
            e.starts_with(
                "conformance: the frozen X5 list names a point outside its admissible set"
            ),
            "conformance: {n}: {e}"
        );
    }
    let e = parse(vec!["synth/width/w3".to_owned()]).expect_err("conformance: a non-grid name");
    assert!(
        e.starts_with("conformance: the frozen X5 list names no grid point"),
        "conformance: {e}"
    );
    let e = parse(vec![
        "synth/width/w2".to_owned(),
        "synth/width/w2".to_owned(),
    ])
    .expect_err("conformance: a name twice");
    assert!(
        e.starts_with("conformance: the frozen X5 list names a fixture twice"),
        "conformance: {e}"
    );
    let sample: Vec<String> = SAMPLE.iter().map(|s| (*s).to_owned()).collect();
    let l = parse(sample.clone()).unwrap_or_else(|e| panic!("conformance: the sample: {e}"));
    assert_eq!(
        l.x5.map(|s| s.items),
        Some(sample),
        "conformance: the sample list"
    );
    let full = full_admissible_list();
    assert_eq!(
        full.len(),
        70,
        "conformance: the full admissible list (derived 70)"
    );
    parse(full.clone()).unwrap_or_else(|e| panic!("conformance: the full list: {e}"));
    // No in-grid point outside my set is accepted.
    let accepted_outside: Vec<String> = grid
        .iter()
        .filter(|n| !admissible_by_derivation(n))
        .filter(|n| parse(vec![(*n).clone()]).is_ok())
        .cloned()
        .collect();
    assert!(
        accepted_outside.is_empty(),
        "conformance: accepted outside F2's set: {accepted_outside:?}"
    );
}

// -------------------------------------------------------------------------
// Children: the frozen list is read once per process, so a list is tested
// in a child process (`EVAL_FROZEN` naming a scratch file).
// -------------------------------------------------------------------------

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tf-x5-tests-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).expect("conformance: a temp directory");
    d
}

fn clean_probes() -> Probes {
    Probes {
        git: Box::new(|| ("x5-tests".to_owned(), false)),
        host: Box::new(|| "x5-tests-host".to_owned()),
    }
}

/// The child of the frozen-list tests. `X5_CASE=driver`: runs the builtin spec
/// `X5_CASE_SPEC` through `Driver` into `X5_CASE_OUT` (`EVAL_ONLY` from
/// `X5_CASE_ONLY`) and prints `CASE\tran N` or `CASE\t<refusal>`.
/// `X5_CASE=count`: prints `CASE\t<json>` with X5's and X5G's counts under the
/// lists in force, the partner holders, and per listed point the selectors and
/// reps of its `A_flat` rows. A no-op without `X5_CASE`.
#[test]
#[ignore]
fn x5_child() {
    let Ok(case) = std::env::var("X5_CASE") else {
        return;
    };
    let line = if case == "driver" {
        let name = std::env::var("X5_CASE_SPEC").expect("conformance: X5_CASE_SPEC");
        let out = PathBuf::from(std::env::var("X5_CASE_OUT").expect("conformance: X5_CASE_OUT"));
        let d = Driver {
            spec: spec(&name).clone(),
            specs: specs().clone(),
            out_dir: out,
            sample_period: Duration::from_millis(100),
            probes: clean_probes(),
            allow_mixed: true,
            only: std::env::var("X5_CASE_ONLY").ok(),
        };
        match d.run() {
            Ok(s) => format!("CASE\tran {}", s.ran),
            Err(e) => format!("CASE\t{}", e.text()),
        }
    } else {
        let mut v = serde_json::json!({});
        let listed: Vec<String> = crate::conformance::eval::frozen()
            .x5
            .iter()
            .flat_map(|s| s.items.clone())
            .collect();
        for name in ["X5", "X5G"] {
            let s = spec(name);
            let flat: Vec<&RowSpec> = s.rows.iter().filter(|r| is_flat(r)).collect();
            let keys: BTreeSet<String> = s.rows.iter().map(|r| r.key(prof())).collect();
            let mut holders: BTreeMap<String, usize> = BTreeMap::new();
            let mut dangling = 0usize;
            let mut unheld = 0usize;
            for r in &flat {
                let (pk, class) = x5_partner(r);
                let h = holder(class, name);
                if !ks(h).contains(&pk) {
                    dangling += 1;
                }
                if !keys.contains(&pk) {
                    unheld += 1;
                }
                *holders.entry(h.to_owned()).or_default() += 1;
            }
            let mut points = serde_json::Map::new();
            for n in &listed {
                let rows: Vec<&&RowSpec> = flat
                    .iter()
                    .filter(|r| &r.fixture == n && !r.config.stop_at_first_report)
                    .collect();
                let sel: BTreeSet<String> = rows
                    .iter()
                    .map(|r| format!("{:?}", r.config.selector))
                    .collect();
                points.insert(
                    n.clone(),
                    serde_json::json!({ "rows": rows.len(), "selectors": sel.len() }),
                );
            }
            v[name] = serde_json::json!({
                "rows": s.rows.len(),
                "keys": keys.len(),
                "flat": flat.len(),
                "sweep": s.rows.len() - flat.len(),
                "holders": holders,
                "dangling": dangling,
                "unheld": unheld,
                "points": points,
            });
        }
        format!("CASE\t{v}")
    };
    use std::io::Write as _;
    let mut o = std::io::stdout().lock();
    writeln!(o, "{line}").expect("conformance: writing the case line");
}

fn child_case(dir: &Path, frozen: &str, case: &str, sp: &str, only: Option<&str>) -> String {
    fs::create_dir_all(dir).unwrap();
    let fz = dir.join("frozen.json");
    fs::write(&fz, frozen).unwrap();
    let mut c = std::process::Command::new(std::env::current_exe().unwrap());
    c.args([
        "--ignored",
        "--exact",
        "conformance::x5_tests::x5_child",
        "--nocapture",
        "--test-threads=1",
    ])
    .env("EVAL_FROZEN", &fz)
    .env_remove("EVAL_OUT")
    .env("X5_CASE", case)
    .env("X5_CASE_SPEC", sp)
    .env("X5_CASE_OUT", dir.join("out"))
    .env_remove("X5_CASE_ONLY");
    if let Some(o) = only {
        c.env("X5_CASE_ONLY", o);
    }
    let o = c.output().unwrap();
    String::from_utf8_lossy(&o.stdout)
        .lines()
        .find_map(|l| l.find("CASE\t").map(|k| l[k + 5..].to_owned()))
        .unwrap_or_else(|| format!("no case line: {}", String::from_utf8_lossy(&o.stderr)))
}

/// C1 / E-X5-1 through child processes: (a) both extension steps frozen and
/// **no `x5` key** → the driver refuses X5 and X5G ("the X5 list is not
/// frozen"); (b) the sample list (derived.md §3.1) → each listed point has
/// `A_flat` rows under three selectors × 3 reps; counts as derived (derived.md
/// §3.1; T1/T2 fixed): X5 `A_flat` **363** (= 294 + 72 − 3, the listed
/// `ex:naive/k2/enc1`'s `Ltr` rows once), 363 sweep rows, **726** keys = rows
/// (each key once); X5G 255 + 255 = 510 (no stop pairs, m2); every partner held by X5 and by its named spec;
/// holders X1 72 + 54, X1V 18 + 15, X2 108, own 96; (c) the full admissible
/// list (70 points) → `A_flat` **906** (the criteria's figure: 630 + 108 + 186 −
/// 18), 906 sweep rows, 1 812 keys (X5G 2 × 798 = 1 596), holders X1 630, X1V 72, X2 108, own 96;
/// (d) with the sample frozen, one X5 key runs (`ran 1`) and the used-record
/// holds the `x5` list. Run alone.
#[test]
#[ignore]
fn c01_the_frozen_x5_list_through_children() {
    let base = temp("frozen");
    let no_x5 = frozen_text(None);
    for sp in ["X5", "X5G"] {
        let got = child_case(&base.join(format!("a-{sp}")), &no_x5, "driver", sp, None);
        note!("c01 (a) {sp}: {got}");
        assert_eq!(
            got,
            format!("refused: {sp} is not runnable: the X5 list is not frozen"),
            "conformance: (a) {sp}"
        );
    }
    let sample: Vec<String> = SAMPLE.iter().map(|s| (*s).to_owned()).collect();
    let got = child_case(
        &base.join("b"),
        &frozen_text(Some(&sample)),
        "count",
        "",
        None,
    );
    note!("c01 (b): {got}");
    let v: serde_json::Value =
        serde_json::from_str(&got).unwrap_or_else(|e| panic!("conformance: (b) {e}: {got}"));
    for n in SAMPLE {
        assert_eq!(
            v["X5"]["points"][n]["selectors"], 3,
            "conformance: (b) {n} selectors"
        );
        assert_eq!(v["X5"]["points"][n]["rows"], 9, "conformance: (b) {n} rows");
    }
    assert_eq!(v["X5"]["flat"], 363, "conformance: (b) A_flat");
    assert_eq!(v["X5"]["sweep"], 363, "conformance: (b) sweep rows");
    for (h, n) in [("X5", 726), ("X5G", 510)] {
        assert_eq!(v[h]["keys"], n, "conformance: (b) {h} keys");
        assert_eq!(v[h]["rows"], n, "conformance: (b) {h} rows (each key once)");
        assert_eq!(v[h]["dangling"], 0, "conformance: (b) {h} dangling");
        assert_eq!(v[h]["unheld"], 0, "conformance: (b) {h} partners not held");
    }
    assert_eq!(
        v["X5"]["holders"],
        serde_json::json!({ "X1": 126, "X1V": 33, "X2": 108, "X5": 96 }),
        "conformance: (b) holders"
    );
    let full = full_admissible_list();
    let got = child_case(
        &base.join("c"),
        &frozen_text(Some(&full)),
        "count",
        "",
        None,
    );
    let v: serde_json::Value =
        serde_json::from_str(&got).unwrap_or_else(|e| panic!("conformance: (c) {e}: {got}"));
    note!("c01 (c): X5 {} / X5G {}", v["X5"], v["X5G"]["keys"]);
    assert_eq!(
        v["X5G"]["keys"], 1596,
        "conformance: (c) X5G keys (2 × 798)"
    );
    assert_eq!(
        v["X5"]["flat"], 906,
        "conformance: (c) A_flat with the full list"
    );
    assert_eq!(v["X5"]["sweep"], 906, "conformance: (c) sweep rows");
    assert_eq!(v["X5"]["keys"], 1812, "conformance: (c) keys");
    assert_eq!(v["X5"]["dangling"], 0, "conformance: (c) dangling");
    assert_eq!(v["X5"]["unheld"], 0, "conformance: (c) unheld");
    assert_eq!(
        v["X5"]["holders"],
        serde_json::json!({ "X1": 630, "X1V": 72, "X2": 108, "X5": 96 }),
        "conformance: (c) holders"
    );
    let only = "synth/width/w8|CompleteFirst/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=true/instr=false/cut=false/cover=Flat|0|*";
    let d = base.join("d");
    let got = child_case(&d, &frozen_text(Some(&sample)), "driver", "X5", Some(only));
    note!("c01 (d): {got}");
    assert_eq!(
        got, "ran 1",
        "conformance: (d) the sample makes X5 runnable"
    );
    let rec: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(d.join("out/frozen.used.json")).expect("conformance: the used-record"),
    )
    .unwrap();
    assert_eq!(
        rec["x5"]["items"],
        serde_json::json!(SAMPLE),
        "conformance: (d) the record holds the x5 list"
    );
}

// =========================================================================
// Criterion 2 — the counters on `Verdict` rows
// =========================================================================

/// The counter columns the `run_with` routes push (`row_of`'s `CompleteFirst`
/// and `Gated` arms), minus `*_ms` and `precheck_*`; `max_paper_events` is in
/// (gate 4 round 01 B1: `ConfOutcome::counters().max_paper_events_per_execution`,
/// set by `cfirst::run`/`gated::run` from the `run_with` outcome).
const CFIRST_COUNTER_COLUMNS: [&str; 16] = [
    "max_paper_events",
    "impl_graphs",
    "cache_probes",
    "cache_hits",
    "cache_tests",
    "sweeps",
    "sweeps_successful",
    "sweeps_failing",
    "sweeps_aborted",
    "sweep_sizes",
    "sweep_graphs",
    "sweep_graphs_max",
    "witnesses",
    "witness_duplicates",
    "counter_reports",
    "cut_reports",
];

const GATED_COUNTER_COLUMNS: [&str; 36] = [
    "max_paper_events",
    "gates",
    "gates_inert",
    "gates_skipped_replay",
    "gates_skipped_certified",
    "gates_declined",
    "c1_tests_carried",
    "carried_hits",
    "c1_tests_cache",
    "gate_cache_hits",
    "c1_tests_sweep",
    "gate_sweeps",
    "gate_sweeps_successful",
    "gate_sweeps_failing",
    "gate_sweeps_budgeted",
    "gate_sweeps_aborted",
    "gate_sweep_sizes",
    "certificates_set",
    "certificate_resets",
    "states_pushed",
    "certified_states_revisited",
    "reports_certified",
    "reports_by_completion_test",
    "paper_events_at_first_report",
    "impl_graphs",
    "completion_probes",
    "completion_cache_hits",
    "completion_cache_tests",
    "completion_sweeps",
    "completion_sweeps_successful",
    "completion_sweeps_failing",
    "completion_sweeps_aborted",
    "completion_sweep_sizes",
    "witnesses",
    "witness_duplicates",
    "executions",
];

/// T3's two gated columns (the fill omitted them before the fix).
const GATED_MISSING: [&str; 2] = ["first_failure_mode", "counter_reports"];

/// The runner's row of one in-process run, as the store holds it (header
/// order, blank where absent).
fn rec_of(end: &GridEnd, rs: &RowSpec) -> Rec {
    let meta = RowMeta::of(rs, prof(), "x5-tests", "");
    let row: Row = eval_row_of(end, &meta);
    header()
        .iter()
        .map(|h| (*h).to_owned())
        .zip(record_of(&row))
        .collect()
}

fn row_spec_for(name: &str, config: GridConfig) -> RowSpec {
    let mut rs = RowSpec {
        fixture: name.to_owned(),
        config,
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
    // T4: `twin_key` stays empty on X5/X5G rows (the partner is `x5_partner`'s).
    rs.twin_key.clear();
    rs
}

/// One row run in process (`run_row_in_process(.., false)`, the runner's
/// own run path) and turned into the stored record.
fn run_rec(name: &str, config: GridConfig) -> Rec {
    let f = fixture(name);
    let end = run_row_in_process(f, &config, false);
    rec_of(&end, &row_spec_for(name, config))
}

/// Criterion 2 on `ex:naive/k2/enc1` and `naive-self(2, 1)`, every selector:
/// the `Verdict` route (`cfirst::run` / `gated::run`, precheck on, cover
/// `Sweep`) and the `run_with` route (precheck off) give equal values in every
/// counter column the `run_with` arm pushes (`*_ms`, `precheck_*` excluded;
/// `max_paper_events` **included**, gate 4 round 01 B1), complete-first and gated (`Exhaustive` ×
/// `Always`/`Never`); T3's two gated columns (fixed) are compared by
/// `c02_gated_verdict_rows_carry_first_failure_mode_and_counter_reports`. The `Flat` arm's `Verdict` row carries every one of them too
/// (non-blank). The header is unchanged: `SCHEMA_VERSION` 2, 180 columns, every
/// compared column declared.
#[test]
fn c02_verdict_rows_carry_the_run_with_counters() {
    assert_eq!(SCHEMA_VERSION, 2, "conformance: the schema version");
    assert_eq!(header().len(), 180, "conformance: the header's width");
    for c in CFIRST_COUNTER_COLUMNS
        .iter()
        .chain(GATED_COUNTER_COLUMNS.iter())
        .chain(GATED_MISSING.iter())
    {
        assert!(header().contains(c), "conformance: {c} is not declared");
    }
    let mut bad = Vec::new();
    let mut compared = 0usize;
    for name in ["ex:naive/k2/enc1", "synth/naive-self/k2enc1"] {
        for s in SELECTORS {
            let hosts: [(GridConfig, &[&str]); 3] = [
                (
                    x1_config(GridEngine::CompleteFirst, s),
                    &CFIRST_COUNTER_COLUMNS,
                ),
                (x1_config(GridEngine::Gated, s), &GATED_COUNTER_COLUMNS),
                (
                    x1_config(GridEngine::Gated, s).gated(GatedMode::Exhaustive, GatePolicy::Never),
                    &GATED_COUNTER_COLUMNS,
                ),
            ];
            for (cfg, cols) in hosts {
                let what = format!("{name} {}", cfg.label());
                let raw = run_rec(name, cfg.clone());
                let ver = run_rec(name, cfg.clone().precheck(true));
                let fl = run_rec(
                    name,
                    cfg.clone().precheck(true).cover(CompletionCover::Flat),
                );
                assert_eq!(
                    ver["verdict"],
                    if name.starts_with("ex:") {
                        "Reported"
                    } else {
                        "Conforms"
                    },
                    "conformance: {what}"
                );
                for c in cols.iter() {
                    compared += 1;
                    if raw[*c].is_empty() {
                        bad.push(format!("{what}: run_with left {c} blank"));
                    }
                    if raw[*c] != ver[*c] {
                        bad.push(format!(
                            "{what}: {c} run_with {:?} Verdict {:?}",
                            raw[*c], ver[*c]
                        ));
                    }
                    if fl[*c].is_empty() {
                        bad.push(format!("{what}: the Flat row left {c} blank"));
                    }
                }
                for c in ["outer_wall_time_ms", "sweep_wall_time_ms"] {
                    if ver[c].is_empty() || fl[c].is_empty() {
                        bad.push(format!("{what}: {c} blank on a Verdict row"));
                    }
                }
            }
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 2: {bad:#?}");
    note!("c02: {compared} column comparisons");
}

/// T3 fixed (the former `t3_…` pin, now positive): on a gated `Verdict` row
/// (both arms) `first_failure_mode` and `counter_reports` equal the `run_with`
/// row's (`row_of`'s `Gated` arm: `c.first_failure_mode`, `c.reports`), every
/// selector, `Always` and `Never`.
#[test]
fn c02_gated_verdict_rows_carry_first_failure_mode_and_counter_reports() {
    let mut bad = Vec::new();
    for (name, s, p) in ["ex:naive/k2/enc1", "synth/naive-self/k2enc1"]
        .iter()
        .flat_map(|n| SELECTORS.iter().map(move |s| (*n, *s)))
        .flat_map(|(n, s)| [GatePolicy::Always, GatePolicy::Never].map(|p| (n, s, p)))
    {
        let cfg = x1_config(GridEngine::Gated, s).gated(GatedMode::Exhaustive, p);
        let raw = run_rec(name, cfg.clone());
        let ver = run_rec(name, cfg.clone().precheck(true));
        let fl = run_rec(name, cfg.precheck(true).cover(CompletionCover::Flat));
        for c in GATED_MISSING {
            if raw[c].is_empty() || fl[c].is_empty() {
                bad.push(format!("{name} {s:?} {p:?}: {c} blank"));
            }
            if raw[c] != ver[c] {
                bad.push(format!(
                    "{name}: {c} run_with {:?} Verdict {:?}",
                    raw[c], ver[c]
                ));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: T3: {bad:#?}");
}

/// Criterion 2's last clause: a refused `Flat` run leaves the counter columns
/// blank — the eligibility refusal (`relay/paper/rev`, `Verdict(Err)`, both
/// hosts: `communication_flat = false`, `refused_at` the refusal's position,
/// `verdict = Err`) and the runner's own refusal (`Flat` without the precheck:
/// `panicked`, the payload `refused: …`).
#[test]
fn c02_a_refused_flat_run_leaves_the_counter_columns_blank() {
    let mut bad = Vec::new();
    for engine in [GridEngine::CompleteFirst, GridEngine::Gated] {
        let base = x1_config(engine, Selector::Ltr);
        let r = run_rec(
            "relay/paper/rev",
            base.clone().precheck(true).cover(CompletionCover::Flat),
        );
        if (r["verdict"].as_str(), r["communication_flat"].as_str()) != ("Err", "false")
            || r["refused_at"].is_empty()
        {
            bad.push(format!(
                "{engine:?}: verdict {} flat {} refused_at {}",
                r["verdict"], r["communication_flat"], r["refused_at"]
            ));
        }
        let p = run_rec("relay/paper/rev", base.cover(CompletionCover::Flat));
        if p["end_class"] != "panicked" || !p["payload"].starts_with("refused:") {
            bad.push(format!(
                "{engine:?}: no-precheck Flat: {} {}",
                p["end_class"], p["payload"]
            ));
        }
        for rec in [&r, &p] {
            for c in CFIRST_COUNTER_COLUMNS
                .iter()
                .chain(GATED_COUNTER_COLUMNS.iter())
                .chain(["outer_wall_time_ms", "sweep_wall_time_ms", "flat_calls"].iter())
            {
                if !rec[*c].is_empty() {
                    bad.push(format!("{engine:?}: {c} = {:?} on a refused row", rec[*c]));
                }
            }
        }
    }
    assert!(bad.is_empty(), "conformance: {bad:#?}");
}

// =========================================================================
// The read-time functions (criteria 3, 4, 7)
// =========================================================================

fn num(r: &Rec, c: &str) -> Option<u64> {
    let v = r.get(c)?;
    let v = v
        .strip_prefix("Some(")
        .and_then(|x| x.strip_suffix(')'))
        .unwrap_or(v);
    v.parse().ok()
}

fn list_sum(r: &Rec, c: &str) -> Option<u64> {
    let v = r.get(c)?.trim();
    let inner = v.strip_prefix('[')?.strip_suffix(']')?;
    if inner.trim().is_empty() {
        return Some(0);
    }
    inner.split(',').map(|x| x.trim().parse::<u64>().ok()).sum()
}

fn key_parts(key: &str) -> Vec<String> {
    key.split('|').map(str::to_owned).collect()
}

fn is_flat_key(key: &str) -> bool {
    key_parts(key)
        .get(1)
        .is_some_and(|l| l.ends_with("cover=Flat"))
}

fn is_gated_key(key: &str) -> bool {
    key_parts(key)
        .get(1)
        .is_some_and(|l| l.starts_with("Gated/"))
}

/// A Flat row's partner key, from the key alone (F1; E-X5-3): `cover=Sweep`,
/// and `precheck=false` in the complete-first host.
fn partner_key(flat_key: &str) -> String {
    let mut p = key_parts(flat_key);
    let mut label = p[1].replace("cover=Flat", "cover=Sweep");
    if label.starts_with("CompleteFirst/") {
        label = label.replace("precheck=true", "precheck=false");
    }
    p[1] = label;
    p.join("|")
}

/// The verdict class of a row (F4, round 02 m3): a `Verdict` row's own
/// `verdict`; a sweep row (no `verdict` column): `reports > 0` → violates,
/// `reports = 0 ∧ impl_end = StateSpaceExhausted` → conforms, else
/// inconclusive.
fn verdict_class(r: &Rec) -> &'static str {
    match r.get("verdict").map(String::as_str).unwrap_or("") {
        "Conforms" => "conforms",
        "Reported" => "violates",
        "Inconclusive" => "inconclusive",
        "Err" => "refused",
        _ => match num(r, "reports") {
            Some(n) if n > 0 => "violates",
            Some(0) if r.get("impl_end").map(String::as_str) == Some("StateSpaceExhausted") => {
                "conforms"
            }
            _ => "inconclusive",
        },
    }
}

fn censored(r: &Rec) -> bool {
    r.get("censored").map(String::as_str) == Some("true")
        || r.get("end_class").is_some_and(|e| e.starts_with("capped"))
}

/// The pair checker (criteria 3, 4, 7): every Flat row paired with its sweep
/// partner by key. **Findings** (each fails the build): `missing:` partner,
/// `twin:` a Flat row carries a `twin_key` (T4: empty on X5/X5G rows; the
/// partner is recomputed from the key), `panicked:`/`crashed:`
/// member, `refused:` a Flat row not `communication_flat = true` or with
/// `refused_at` set, `verdict:` classes differ (F4's mapping on the sweep row),
/// `count:` report counts differ, `identity:` an F6 identity or a per-run
/// `cache_probes − cache_hits` identity broken, or `witness_duplicates ≠ 0`,
/// `outer:` `impl_graphs`/`executions`/`max_paper_events` differ. **Labels** (no finding):
/// `censored:` a censored member (lower bounds only; the pair enters no
/// comparison), `eligibility-cost:` a `capped_memory` Flat row (F5),
/// `skipped:` a `skipped_*` member.
fn check_store(rows: &[Rec]) -> (Vec<String>, Vec<String>) {
    let by_key: BTreeMap<&str, &Rec> = rows.iter().map(|r| (r["key"].as_str(), r)).collect();
    let mut findings = Vec::new();
    let mut labels = Vec::new();
    for f in rows.iter().filter(|r| is_flat_key(&r["key"])) {
        let k = f["key"].as_str();
        let pk = partner_key(k);
        if !f.get("twin_key").map(String::is_empty).unwrap_or(true) {
            findings.push(format!("twin: {k}: {:?}", f.get("twin_key")));
        }
        let Some(s) = by_key.get(pk.as_str()) else {
            findings.push(format!("missing: {k}"));
            continue;
        };
        let mut skip = false;
        for (side, r) in [("flat", f), ("sweep", *s)] {
            let ec = r["end_class"].as_str();
            if ec == "panicked" || ec.starts_with("crashed") {
                findings.push(format!("{ec}: {side} {}", r["key"]));
                skip = true;
            } else if ec.starts_with("skipped") {
                labels.push(format!("skipped: {side} {}", r["key"]));
                skip = true;
            }
        }
        if f["end_class"] == "capped_memory" {
            labels.push(format!("eligibility-cost: {k}"));
            skip = true;
        } else if censored(f) || censored(s) {
            labels.push(format!("censored: {k}"));
            skip = true;
        }
        if skip {
            continue;
        }
        if f["communication_flat"] != "true" || !f["refused_at"].is_empty() {
            findings.push(format!(
                "refused: {k}: {} {}",
                f["communication_flat"], f["refused_at"]
            ));
            continue;
        }
        let (cf, cs) = (verdict_class(f), verdict_class(s));
        if cf != cs {
            findings.push(format!("verdict: {k}: flat {cf}, sweep {cs}"));
        }
        if num(f, "reports") != num(s, "reports") {
            findings.push(format!(
                "count: {k}: flat {:?}, sweep {:?}",
                f["reports"], s["reports"]
            ));
        }
        for (a, b) in [
            ("impl_graphs", "impl_graphs"),
            ("executions", "executions"),
            ("max_paper_events", "max_paper_events"),
        ] {
            if num(f, a).is_none() || num(f, a) != num(s, b) {
                findings.push(format!("outer: {k}: {a} {:?} vs {:?}", f[a], s[b]));
            }
        }
        findings.extend(identities(f, s, k));
    }
    (findings, labels)
}

/// F6's identities on the Flat row and the per-run identity on both rows,
/// per host; `witness_duplicates` 0 on both.
fn identities(f: &Rec, s: &Rec, k: &str) -> Vec<String> {
    let mut out = Vec::new();
    let n = |r: &Rec, c: &str| num(r, c).unwrap_or(u64::MAX);
    let calls = n(f, "flat_calls");
    let fw = n(f, "flat_witnesses");
    let mut check = |what: &str, ok: bool| {
        if !ok {
            out.push(format!("identity: {k}: {what}"));
        }
    };
    if is_gated_key(k) {
        check(
            "impl_graphs = completion_cache_hits + reports_certified + flat_calls",
            n(f, "impl_graphs")
                == n(f, "completion_cache_hits") + n(f, "reports_certified") + calls,
        );
        check(
            "flat_calls = completion_probes − completion_cache_hits",
            calls + n(f, "completion_cache_hits") == n(f, "completion_probes"),
        );
        check(
            "completion_sweeps = completion_probes − completion_cache_hits (sweep)",
            n(s, "completion_sweeps") + n(s, "completion_cache_hits") == n(s, "completion_probes"),
        );
        if !f["key"].contains("/stop=true/") {
            check(
                "reports_by_completion_test = flat_calls − flat_witnesses",
                n(f, "reports_by_completion_test") + fw == calls,
            );
        }
    } else {
        check(
            "impl_graphs = cache_hits + flat_calls",
            n(f, "impl_graphs") == n(f, "cache_hits") + calls,
        );
        check("witnesses = flat_witnesses", n(f, "witnesses") == fw);
        check(
            "reports = flat_calls − flat_witnesses",
            n(f, "counter_reports") + fw == calls,
        );
        check(
            "flat_calls = cache_probes − cache_hits",
            calls + n(f, "cache_hits") == n(f, "cache_probes"),
        );
        check(
            "sweeps = cache_probes − cache_hits (sweep)",
            n(s, "sweeps") + n(s, "cache_hits") == n(s, "cache_probes"),
        );
    }
    check(
        "witness_duplicates = 0",
        n(f, "witness_duplicates") == 0 && n(s, "witness_duplicates") == 0,
    );
    out
}

/// Criterion 4's measures of one completed pair (F3).
#[derive(Debug, Clone, PartialEq)]
struct Measures {
    /// `sweeps` (sweep arm; gated: `completion_sweeps`) and `flat_calls`.
    inner_calls: (u64, u64),
    /// `sweeps − flat_calls`, and `cache_hits(Flat) − cache_hits(Sweep)`
    /// (gated: the completion cache hits) — equal by the per-run identities.
    difference: (i64, i64),
    /// The sweep's unit: `Σ sweep_sizes`, `sweep_graphs` (complete-first).
    sweep_graphs: (u64, Option<u64>),
    /// The Flat unit: visits, nd branches, source branches, source
    /// recursions, kills (send + slot + source + done).
    flat_units: [u64; 5],
    /// `sweep_wall_time_ms` per call, on each arm (`None` at 0 calls).
    ms_per_call: (Option<f64>, Option<f64>),
    /// `sweep_wall_time_ms / outer_wall_time_ms`, on each arm (`None` at 0 ms).
    share: (Option<f64>, Option<f64>),
    /// `impl_graphs`, `executions`, `max_paper_events`: (sweep, flat).
    outer: [(u64, u64); 3],
}

/// The measures of a pair, or the reason it has none: a `capped_memory` Flat
/// row → `eligibility cost …` (F5); any other censored member → `censored
/// member: lower bounds only`; a skipped member → `skipped`.
fn measures(f: &Rec, s: &Rec) -> Result<Measures, String> {
    if f["end_class"] == "capped_memory" {
        return Err(format!("eligibility cost exceeded (F5): {}", f["key"]));
    }
    if censored(f) || censored(s) {
        return Err(format!("censored member: lower bounds only: {}", f["key"]));
    }
    if f["end_class"] != "ok" || s["end_class"] != "ok" {
        return Err(format!(
            "not comparable: {} / {}",
            f["end_class"], s["end_class"]
        ));
    }
    let g = |r: &Rec, c: &str| -> Result<u64, String> {
        num(r, c).ok_or_else(|| format!("no {c} on {}", r["key"]))
    };
    let gated = is_gated_key(&f["key"]);
    let (sw_calls, hits, sizes, graphs) = if gated {
        (
            "completion_sweeps",
            "completion_cache_hits",
            "completion_sweep_sizes",
            None,
        )
    } else {
        ("sweeps", "cache_hits", "sweep_sizes", Some("sweep_graphs"))
    };
    let sweeps = g(s, sw_calls)?;
    let calls = g(f, "flat_calls")?;
    let per = |ms: u64, n: u64| {
        if n == 0 {
            None
        } else {
            Some(ms as f64 / n as f64)
        }
    };
    let share = |a: u64, b: u64| {
        if b == 0 {
            None
        } else {
            Some(a as f64 / b as f64)
        }
    };
    let (sms, fms) = (g(s, "sweep_wall_time_ms")?, g(f, "sweep_wall_time_ms")?);
    let (sout, fout) = (g(s, "outer_wall_time_ms")?, g(f, "outer_wall_time_ms")?);
    Ok(Measures {
        inner_calls: (sweeps, calls),
        difference: (
            sweeps as i64 - calls as i64,
            g(f, hits)? as i64 - g(s, hits)? as i64,
        ),
        sweep_graphs: (
            list_sum(s, sizes).ok_or_else(|| format!("no {sizes}"))?,
            graphs.map(|c| g(s, c)).transpose()?,
        ),
        flat_units: [
            g(f, "flat_visits")?,
            g(f, "flat_nd_branches")?,
            g(f, "flat_source_branches")?,
            g(f, "flat_source_recursions")?,
            g(f, "flat_send_kills")?
                + g(f, "flat_slot_kills")?
                + g(f, "flat_source_kills")?
                + g(f, "flat_done_kills")?,
        ],
        ms_per_call: (per(sms, sweeps), per(fms, calls)),
        share: (share(sms, sout), share(fms, fout)),
        outer: [
            (g(s, "impl_graphs")?, g(f, "impl_graphs")?),
            (g(s, "executions")?, g(f, "executions")?),
            (g(s, "max_paper_events")?, g(f, "max_paper_events")?),
        ],
    })
}

/// A pair run in process on the runner's path: (flat, sweep) records.
fn pair_recs(name: &str, gated: bool, s: Selector, stop: bool) -> (Rec, Rec) {
    (
        run_rec(name, flat_cfg(gated, s, stop)),
        run_rec(name, sweep_cfg(gated, s, stop)),
    )
}

/// The base store of criterion 7: pilot-sized pairs in both hosts — `width(2)`,
/// `naive-self(2, 1)`, `share(2, 0)` (conforming), `ex:naive/k2/enc2` with
/// `stop = true` and `R1` (violating) — every one clean under the checker.
fn base_store() -> Vec<Rec> {
    let mut rows = Vec::new();
    for gated in [false, true] {
        for (n, stop) in [
            ("synth/width/w2", false),
            ("synth/naive-self/k2enc1", false),
            ("synth/share/m2c0", false),
            ("ex:naive/k2/enc2", true),
            ("R1", false),
        ] {
            let (f, s) = pair_recs(n, gated, Selector::Ltr, stop);
            rows.push(f);
            rows.push(s);
        }
    }
    rows
}

fn find<'a>(rows: &'a mut [Rec], fixture: &str, flat: bool, gated: bool) -> &'a mut Rec {
    rows.iter_mut()
        .find(|r| {
            r["key"].starts_with(&format!("{fixture}|"))
                && is_flat_key(&r["key"]) == flat
                && is_gated_key(&r["key"]) == gated
        })
        .unwrap_or_else(|| panic!("conformance: no row {fixture} flat={flat} gated={gated}"))
}

/// A measures case: the point, the inner calls (sweep, flat), `Σ sweep_sizes`,
/// the Flat units.
type MeasureCase = (&'static str, (u64, u64), u64, [u64; 5]);

/// Criterion 4 (F3) on the base store's pairs: the measures as derived —
/// `width(2)`: inner calls 2 / 2, difference 0 = the hit difference, `Σ
/// sweep_sizes` 3, Flat visits 9, nd 3, src 2, rec 2, kills 1; `naive-self(2,
/// 1)`: 2 / 2, Σ 3, visits 12, src 5, rec 4; `share(2, 0)`: 1 / 1, Σ 1, visits
/// 5; `ex:naive/k2/enc2` stop: 1 / 1, Σ 2 (`[k!]`), visits 3, kills 1; the three
/// outer counters (`impl_graphs`, `executions`, `max_paper_events`) equal; the time per call and the share defined iff their
/// denominator is non-zero. A censored member refuses the pair; a
/// `capped_memory` Flat row is labelled "eligibility cost".
#[test]
fn c04_the_measures_function() {
    let mut rows = base_store();
    let pair = |rows: &[Rec], n: &str, gated: bool| -> (Rec, Rec) {
        let get = |flat: bool| {
            rows.iter()
                .find(|r| {
                    r["key"].starts_with(&format!("{n}|"))
                        && is_flat_key(&r["key"]) == flat
                        && is_gated_key(&r["key"]) == gated
                })
                .cloned()
                .unwrap_or_else(|| panic!("conformance: no pair {n}"))
        };
        (get(true), get(false))
    };
    let cases: [MeasureCase; 4] = [
        ("synth/width/w2", (2, 2), 3, [9, 3, 2, 2, 1]),
        ("synth/naive-self/k2enc1", (2, 2), 3, [12, 0, 5, 4, 0]),
        ("synth/share/m2c0", (1, 1), 1, [5, 0, 2, 2, 0]),
        ("ex:naive/k2/enc2", (1, 1), 2, [3, 0, 0, 0, 1]),
    ];
    let mut bad = Vec::new();
    for gated in [false, true] {
        for (n, calls, sigma, units) in cases {
            let (f, s) = pair(&rows, n, gated);
            let m = measures(&f, &s).unwrap_or_else(|e| panic!("conformance: {n}: {e}"));
            let what = format!("{n} gated={gated}");
            if m.inner_calls != calls || m.sweep_graphs.0 != sigma || m.flat_units != units {
                bad.push(format!("{what}: {m:?}"));
            }
            if m.difference.0 != m.difference.1 || m.difference.0 != 0 {
                bad.push(format!("{what}: difference {:?}", m.difference));
            }
            if m.outer.iter().any(|(a, b)| a != b) {
                bad.push(format!("{what}: outer {:?}", m.outer));
            }
            if !gated && m.sweep_graphs.1 != Some(sigma) {
                bad.push(format!("{what}: sweep_graphs {:?}", m.sweep_graphs.1));
            }
            let ms = num(&s, "sweep_wall_time_ms").unwrap();
            let want_per = if calls.0 > 0 {
                Some(ms as f64 / calls.0 as f64)
            } else {
                None
            };
            if m.ms_per_call.0 != want_per {
                bad.push(format!("{what}: ms per call {:?}", m.ms_per_call));
            }
            let outer = num(&s, "outer_wall_time_ms").unwrap();
            if m.share.0.is_some() != (outer > 0) {
                bad.push(format!("{what}: share {:?} (outer {outer} ms)", m.share));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 4: {bad:#?}");
    // Refusals and labels.
    {
        let s = find(&mut rows, "synth/width/w2", false, false);
        s.insert("end_class".into(), "capped_wall".into());
        s.insert("censored".into(), "true".into());
    }
    let (f, s) = pair(&rows, "synth/width/w2", false);
    let e = measures(&f, &s).expect_err("conformance: a censored member refuses the pair");
    assert!(
        e.starts_with("censored member: lower bounds only"),
        "conformance: {e}"
    );
    {
        let f = find(&mut rows, "synth/share/m2c0", true, false);
        f.insert("end_class".into(), "capped_memory".into());
        f.insert("censored".into(), "true".into());
    }
    let (f, s) = pair(&rows, "synth/share/m2c0", false);
    let e = measures(&f, &s).expect_err("conformance: a capped_memory Flat row");
    assert!(e.starts_with("eligibility cost"), "conformance: {e}");
}

/// Criterion 7: on a constructed store (the base store's pairs plus planted
/// rows) every plant is detected or labelled as F4/F5 require, and the
/// unplanted store is clean: (1) a verdict mismatch (the Flat row says
/// `Conforms` on a violating pair) → `verdict:`; (2) a report-count mismatch
/// (the sweep row reports one more) → `count:`; (3) an identity break
/// (`cache_hits` + 1 on a Flat row) → `identity:`; (4) a censored member →
/// `censored:` label, no finding; (5) a refused `Flat` row
/// (`communication_flat = false`, `refused_at` set) → `refused:`; (6) a
/// `capped_memory` Flat row → `eligibility-cost:` label; (7) a sweep row with
/// `reports > 0` paired with a conforming Flat row (only F4's mapping tells) →
/// `verdict:`. Plus (8) a sweep row with `reports = 0` and an
/// `impl_end` other than `StateSpaceExhausted` → inconclusive, `verdict:`; (9) a
/// missing partner → `missing:`; (10) a non-empty `twin_key` → `twin:`; (11) unequal
/// outer work (`executions` + 1 on a Flat row; `impl_graphs`, `executions`
/// and `max_paper_events` are compared) → `outer:`.
#[test]
fn c07_the_read_time_checks_catch_every_plant() {
    let base = base_store();
    let (f0, l0) = check_store(&base);
    assert!(
        f0.is_empty() && l0.is_empty(),
        "conformance: the base store: {f0:#?} {l0:#?}"
    );
    type Plant = fn(&mut Vec<Rec>);
    let plants: [(&str, Plant, &str, bool); 11] = [
        (
            "1 verdict",
            |r| {
                find(r, "R1", true, false).insert("verdict".into(), "Conforms".into());
            },
            "verdict:",
            true,
        ),
        (
            "2 count",
            |r| {
                let s = find(r, "R1", false, true);
                let n = num(s, "reports").unwrap() + 1;
                s.insert("reports".into(), n.to_string());
            },
            "count:",
            true,
        ),
        (
            "3 identity",
            |r| {
                let f = find(r, "synth/width/w2", true, false);
                let n = num(f, "cache_hits").unwrap() + 1;
                f.insert("cache_hits".into(), n.to_string());
            },
            "identity:",
            true,
        ),
        (
            "4 censored",
            |r| {
                let s = find(r, "synth/naive-self/k2enc1", false, false);
                s.insert("end_class".into(), "capped_wall".into());
                s.insert("censored".into(), "true".into());
            },
            "censored:",
            false,
        ),
        (
            "5 refused",
            |r| {
                let f = find(r, "synth/share/m2c0", true, true);
                f.insert("communication_flat".into(), "false".into());
                f.insert("refused_at".into(), "r0 @ (t2, 1)".into());
            },
            "refused:",
            true,
        ),
        (
            "6 capped_memory",
            |r| {
                let f = find(r, "synth/naive-self/k2enc1", true, true);
                f.insert("end_class".into(), "capped_memory".into());
                f.insert("censored".into(), "true".into());
            },
            "eligibility-cost:",
            false,
        ),
        (
            "7 sweep reports on a conforming pair",
            |r| {
                let s = find(r, "synth/width/w2", false, false);
                s.insert("reports".into(), "1".into());
            },
            "verdict:",
            true,
        ),
        (
            "8 sweep inconclusive",
            |r| {
                let s = find(r, "synth/share/m2c0", false, false);
                s.insert("impl_end".into(), "IterationLimit".into());
            },
            "verdict:",
            true,
        ),
        (
            "9 missing",
            |r| {
                let i = r
                    .iter()
                    .position(|x| {
                        x["key"].starts_with("R1|")
                            && !is_flat_key(&x["key"])
                            && !is_gated_key(&x["key"])
                    })
                    .unwrap();
                r.remove(i);
            },
            "missing:",
            true,
        ),
        (
            "10 twin",
            |r| {
                find(r, "ex:naive/k2/enc2", true, false).insert("twin_key".into(), "x".into());
            },
            "twin:",
            true,
        ),
        (
            "11 outer",
            |r| {
                let f = find(r, "ex:naive/k2/enc2", true, true);
                let n = num(f, "executions").unwrap() + 1;
                f.insert("executions".into(), n.to_string());
            },
            "outer:",
            true,
        ),
    ];
    let mut bad = Vec::new();
    for (what, plant, kind, is_finding) in plants {
        let mut rows = base.clone();
        plant(&mut rows);
        let (f, l) = check_store(&rows);
        let hit = if is_finding {
            f.iter().any(|x| x.starts_with(kind))
        } else {
            l.iter().any(|x| x.starts_with(kind)) && f.is_empty()
        };
        note!("c07 plant {what}: findings {f:?} labels {l:?}");
        if !hit {
            bad.push(format!("plant {what}: findings {f:?}, labels {l:?}"));
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 7: {bad:#?}");
}

// =========================================================================
// Criterion 3 — exactness in process (report-key sets, both hosts, every
// selector) at the tractable sizes
// =========================================================================

/// The synthetic hand-count points of the in-process exactness check.
const TRACTABLE_SYNTH: [&str; 18] = [
    "synth/naive-self/k2enc1",
    "synth/naive-self/k2enc2",
    "synth/naive-self/k3enc1",
    "synth/naive-self/k3enc2",
    "synth/width/w2",
    "synth/width/w8",
    "synth/chain/d2",
    "synth/chain/d8",
    "synth/share/m2c0",
    "synth/share/m2c1",
    "synth/share/m2c2",
    "synth/commit/n2j0",
    "synth/commit/n2j1",
    "synth/commit/n2j2",
    "synth/commit/n4j0",
    "synth/commit/n4j2",
    "synth/commit/n4j4",
    "ex:naive/k3/enc1",
];

/// Criterion 3 (F4) in process (test profile): on `FLAT_SUBSET` (62) and the
/// tractable synthetic points, × 3 selectors, complete-first and gated
/// `Exhaustive`/`Never` (X5G's host), `run_with` under `Flat` and under
/// `Sweep` give the same report-key set (canonical keys), the same verdict
/// class and count; the Flat run's F6 identities and both runs' per-run
/// identities hold; `impl_graphs`, `executions` and `max_paper_events` are
/// equal across the arms (outer work).
#[test]
fn c03_report_key_sets_equal_in_process() {
    let mut names: Vec<&str> = FLAT_SUBSET.to_vec();
    names.extend(TRACTABLE_SYNTH);
    let mut bad = Vec::new();
    let mut runs = 0usize;
    for name in names {
        let f = fixture(name);
        for s in SELECTORS {
            let cf = |cover| flat_cfg(false, s, false).cover(cover).conf_config(f);
            let (a, b) = (
                cfirst::run_with(
                    &cf(CompletionCover::Flat),
                    &f.implementation,
                    &f.specification,
                    false,
                ),
                cfirst::run_with(
                    &cf(CompletionCover::Sweep),
                    &f.implementation,
                    &f.specification,
                    false,
                ),
            );
            let keys = |o: &cfirst::CFirstOutcome| -> BTreeSet<String> {
                o.reports
                    .iter()
                    .map(|(g, _)| canon_key(g, &f.visible))
                    .collect()
            };
            let what = format!("{name} {s:?} cfirst");
            if keys(&a) != keys(&b)
                || a.reports.len() != b.reports.len()
                || a.impl_end != b.impl_end
            {
                bad.push(format!(
                    "{what}: reports {} / {}",
                    a.reports.len(),
                    b.reports.len()
                ));
            }
            if (a.counters.impl_graphs, a.executions, a.max_paper_events)
                != (b.counters.impl_graphs, b.executions, b.max_paper_events)
            {
                bad.push(format!("{what}: outer work differs"));
            }
            let fc = a.counters.flat.clone().unwrap_or_default();
            let c = &a.counters;
            if c.impl_graphs != c.cache_hits + fc.calls
                || c.witnesses + c.witness_duplicates != fc.witnesses
                || c.reports + fc.witnesses != fc.calls
                || fc.calls + c.cache_hits != c.cache_probes
                || b.counters.sweeps + b.counters.cache_hits != b.counters.cache_probes
                || c.witness_duplicates != 0
            {
                bad.push(format!("{what}: an identity"));
            }
            let gf = |cover| flat_cfg(true, s, false).cover(cover).conf_config(f);
            let (a, b) = (
                gated::run_with(
                    &gf(CompletionCover::Flat),
                    &f.implementation,
                    &f.specification,
                    false,
                ),
                gated::run_with(
                    &gf(CompletionCover::Sweep),
                    &f.implementation,
                    &f.specification,
                    false,
                ),
            );
            let gkeys = |o: &gated::GatedOutcome| -> BTreeSet<String> {
                o.reports
                    .iter()
                    .map(|(g, _, _)| canon_key(g, &f.visible))
                    .collect()
            };
            let what = format!("{name} {s:?} gated Never");
            if gkeys(&a) != gkeys(&b)
                || a.reports.len() != b.reports.len()
                || a.impl_end != b.impl_end
            {
                bad.push(format!(
                    "{what}: reports {} / {}",
                    a.reports.len(),
                    b.reports.len()
                ));
            }
            if (a.counters.impl_graphs, a.executions, a.max_paper_events)
                != (b.counters.impl_graphs, b.executions, b.max_paper_events)
            {
                bad.push(format!("{what}: outer work differs"));
            }
            let fc = a.counters.flat.clone().unwrap_or_default();
            let c = &a.counters;
            if c.impl_graphs != c.completion_cache_hits + c.reports_certified + fc.calls
                || fc.calls + c.completion_cache_hits != c.completion_probes
                || c.reports_by_completion_test + fc.witnesses != fc.calls
            {
                bad.push(format!("{what}: an identity"));
            }
            runs += 4;
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 3: {bad:#?}");
    note!("c03: {runs} runs");
}

// =========================================================================
// Criterion 5 — the derived cells through the runner's child
// =========================================================================

/// One pilot cell: the point, `stop`, the expected Flat counters (calls,
/// witnesses, visits, nd, src, rec, send kills, max depth), the expected sweep
/// (sweeps, Σ sweep_sizes, the sizes as a sorted multiset or `None`), and
/// `impl_graphs`.
struct Cell {
    fixture: &'static str,
    stop: bool,
    flat: [u64; 8],
    sweeps: u64,
    sigma: u64,
    sizes: Option<Vec<u64>>,
    impl_graphs: u64,
}

fn range(n: u64) -> Option<Vec<u64>> {
    Some((1..=n).collect())
}

/// derived.md §5.
fn pilot_cells() -> Vec<Cell> {
    let mut v = Vec::new();
    for e in [1, 2] {
        v.push(Cell {
            fixture: if e == 1 {
                "synth/naive-self/k2enc1"
            } else {
                "synth/naive-self/k2enc2"
            },
            stop: false,
            flat: [2, 2, 12, 0, 5, 4, 0, 6],
            sweeps: 2,
            sigma: 3,
            sizes: range(2),
            impl_graphs: 2,
        });
        v.push(Cell {
            fixture: if e == 1 {
                "synth/naive-self/k3enc1"
            } else {
                "synth/naive-self/k3enc2"
            },
            stop: false,
            flat: [6, 6, 48, 0, 27, 18, 0, 8],
            sweeps: 6,
            sigma: 21,
            sizes: range(6),
            impl_graphs: 6,
        });
    }
    for (k, f) in [(2u64, "2"), (3, "3")] {
        let fact = if k == 2 { 2 } else { 6 };
        v.push(Cell {
            fixture: if f == "2" {
                "ex:naive/k2/enc1"
            } else {
                "ex:naive/k3/enc1"
            },
            stop: true,
            flat: [1, 0, 1, 0, 0, 0, 1, 1],
            sweeps: 1,
            sigma: fact,
            sizes: Some(vec![fact]),
            impl_graphs: 1,
        });
        v.push(Cell {
            fixture: if f == "2" {
                "ex:naive/k2/enc2"
            } else {
                "ex:naive/k3/enc2"
            },
            stop: true,
            flat: [1, 0, k + 1, 0, 0, 0, 1, k + 1],
            sweeps: 1,
            sigma: fact,
            sizes: Some(vec![fact]),
            impl_graphs: 1,
        });
    }
    v.push(Cell {
        fixture: "synth/width/w2",
        stop: false,
        flat: [2, 2, 9, 3, 2, 2, 1, 4],
        sweeps: 2,
        sigma: 3,
        sizes: range(2),
        impl_graphs: 2,
    });
    v.push(Cell {
        fixture: "synth/width/w8",
        stop: false,
        flat: [8, 8, 60, 36, 8, 8, 28, 4],
        sweeps: 8,
        sigma: 36,
        sizes: range(8),
        impl_graphs: 8,
    });
    v.push(Cell {
        fixture: "synth/chain/d2",
        stop: false,
        flat: [1, 1, 5, 0, 2, 2, 0, 5],
        sweeps: 1,
        sigma: 1,
        sizes: Some(vec![1]),
        impl_graphs: 1,
    });
    v.push(Cell {
        fixture: "synth/chain/d8",
        stop: false,
        flat: [1, 1, 17, 0, 8, 8, 0, 17],
        sweeps: 1,
        sigma: 1,
        sizes: Some(vec![1]),
        impl_graphs: 1,
    });
    v.push(Cell {
        fixture: "synth/share/m2c0",
        stop: false,
        flat: [1, 1, 5, 0, 2, 2, 0, 5],
        sweeps: 1,
        sigma: 1,
        sizes: Some(vec![1]),
        impl_graphs: 1,
    });
    for (j, nd, sk, visits) in [
        (0u64, 96u64, 32u64, 272u64),
        (2, 112, 40, 320),
        (4, 272, 120, 656),
    ] {
        let fx = match j {
            0 => "synth/commit/n4j0",
            2 => "synth/commit/n4j2",
            _ => "synth/commit/n4j4",
        };
        v.push(Cell {
            fixture: fx,
            stop: false,
            flat: [16, 16, visits, nd, 80, 80, sk, 15],
            sweeps: 16,
            sigma: 136,
            sizes: range(16),
            impl_graphs: 16,
        });
    }
    v
}

const FLAT_COLS: [&str; 8] = [
    "flat_calls",
    "flat_witnesses",
    "flat_visits",
    "flat_nd_branches",
    "flat_source_branches",
    "flat_source_recursions",
    "flat_send_kills",
    "flat_max_depth",
];

fn sorted_sizes(r: &Rec, c: &str) -> Option<Vec<u64>> {
    let v = r.get(c)?.trim();
    let inner = v.strip_prefix('[')?.strip_suffix(']')?;
    let mut out: Vec<u64> = inner
        .split(',')
        .filter(|x| !x.trim().is_empty())
        .map(|x| x.trim().parse().ok())
        .collect::<Option<Vec<u64>>>()?;
    out.sort_unstable();
    Some(out)
}

/// Criterion 5 (`P4-FLAT` F7, criterion 6): the derived cells re-measured
/// through the runner's child — `Driver` with a 10 s tier into a temporary
/// `EVAL_OUT`, one process per row, hand-count sizes only, the complete-first
/// host (both arms under `Ltr`) and the gated host's Flat arm: every figure of
/// derived.md §5 (incl. `commit(4, j)`'s `Σ nd` 96/112/272), the read-time
/// checker clean on the pilot store, `precheck_wall_time_ms` present on every
/// Flat row, every Flat row `communication_flat = true`. With `X5_PILOT_OUT`
/// set the table is written there (`log/dev/P5-X5.pilot.md`'s body). Run
/// alone.
#[test]
#[ignore]
fn c05_the_derived_cells_through_the_runners_child() {
    let out = temp("pilot");
    let tier = Tier {
        name: "t10s".to_owned(),
        wall: Duration::from_secs(10),
        mem_kb: 4 * 1024 * 1024,
    };
    let grid: BTreeMap<String, SynthPoint> = synth_grid()
        .into_iter()
        .map(|p| (p.fixture.clone(), p))
        .collect();
    let cells = pilot_cells();
    let mut rows = Vec::new();
    for c in &cells {
        let p = &grid[c.fixture];
        for gated in [false, true] {
            if gated && c.stop {
                continue; // m2: X5G has no `stop = true` pairs
            }
            for cfg in [
                flat_cfg(gated, Selector::Ltr, c.stop),
                sweep_cfg(gated, Selector::Ltr, c.stop),
            ] {
                let mut r = p.row_spec(&cfg, &tier, RunKind::Timed, 0);
                r.twin_key.clear(); // T4: X5/X5G rows carry no twin key
                rows.push(r);
            }
        }
    }
    let n_rows = rows.len();
    let d = Driver {
        spec: Spec {
            name: "X5-pilot".to_owned(),
            rows,
        },
        specs: specs().clone(),
        out_dir: out.clone(),
        sample_period: Duration::from_millis(100),
        probes: clean_probes(),
        allow_mixed: true,
        only: None,
    };
    let sum = d
        .run()
        .unwrap_or_else(|e| panic!("conformance: the pilot: {}", e.text()));
    assert_eq!(sum.ran, n_rows, "conformance: one child per row");
    let recs: Vec<Rec> = read_rows(&d.store_path())
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()))
        .into_iter()
        .collect();
    let pids: BTreeSet<String> = recs.iter().map(|r| r["pid"].clone()).collect();
    assert_eq!(pids.len(), n_rows, "conformance: one process per row");
    let (findings, labels) = check_store(&recs);
    assert!(
        findings.is_empty() && labels.is_empty(),
        "conformance: the pilot store: {findings:#?} {labels:#?}"
    );
    let mut bad = Vec::new();
    let mut table = String::from(
        "| point | host | stop | flat calls / w / visits / nd / src / rec / send kills / max depth | sweep: sweeps, Σ sizes, sizes | impl_graphs | executions (F / S) | max_paper_events (F / S) | outer ms (F / S) | sweep ms (F / S) | precheck ms (F) | proc ms (F / S) | rss kB (F / S) |\n|---|---|---|---|---|---|---|---|---|---|---|---|---|\n",
    );
    for c in &cells {
        for gated in [false, true] {
            if gated && c.stop {
                continue;
            }
            let host = if gated {
                "gated Exh/Never"
            } else {
                "complete-first"
            };
            let pick = |flat: bool| {
                recs.iter()
                    .find(|r| {
                        r["key"].starts_with(&format!("{}|", c.fixture))
                            && is_flat_key(&r["key"]) == flat
                            && is_gated_key(&r["key"]) == gated
                    })
                    .unwrap_or_else(|| panic!("conformance: no pilot row {}", c.fixture))
            };
            let (f, s) = (pick(true), pick(false));
            let what = format!("{} {host}", c.fixture);
            let got: Vec<u64> = FLAT_COLS
                .iter()
                .map(|k| num(f, k).unwrap_or(u64::MAX))
                .collect();
            if got != c.flat {
                bad.push(format!("{what}: flat {got:?}, derived {:?}", c.flat));
            }
            for k in ["flat_slot_kills", "flat_source_kills", "flat_done_kills"] {
                if num(f, k) != Some(0) {
                    bad.push(format!("{what}: {k} {:?}", f[k]));
                }
            }
            if f["communication_flat"] != "true" || f["precheck_wall_time_ms"].is_empty() {
                bad.push(format!("{what}: eligibility / precheck column"));
            }
            let (sw, sizes_col) = if gated {
                ("completion_sweeps", "completion_sweep_sizes")
            } else {
                ("sweeps", "sweep_sizes")
            };
            let sizes = sorted_sizes(s, sizes_col);
            if num(s, sw) != Some(c.sweeps)
                || list_sum(s, sizes_col) != Some(c.sigma)
                || (c.sizes.is_some() && sizes != c.sizes)
            {
                bad.push(format!("{what}: sweep {:?} {:?}", s[sw], s[sizes_col]));
            }
            if num(f, "impl_graphs") != Some(c.impl_graphs) {
                bad.push(format!("{what}: impl_graphs {:?}", f["impl_graphs"]));
            }
            table.push_str(&format!(
                "| `{}` | {host} | {} | {} | {}, {}, `{}` | {} | {} / {} | {} / {} | {} / {} | {} / {} | {} | {} / {} | {} / {} |\n",
                c.fixture,
                c.stop,
                got.iter().map(u64::to_string).collect::<Vec<_>>().join(" / "),
                s[sw],
                list_sum(s, sizes_col).unwrap_or(0),
                s[sizes_col],
                f["impl_graphs"],
                f["executions"],
                s["executions"],
                f["max_paper_events"],
                s["max_paper_events"],
                f["outer_wall_time_ms"],
                s["outer_wall_time_ms"],
                f["sweep_wall_time_ms"],
                s["sweep_wall_time_ms"],
                f["precheck_wall_time_ms"],
                f["proc_wall_ms"],
                s["proc_wall_ms"],
                f["rss_child_hwm_kb"],
                s["rss_child_hwm_kb"],
            ));
        }
    }
    // `commit(4, j)`'s per-call `nd` is not a column: the run totals above
    // carry it (derived.md §5's function summed); the gated host equals the
    // complete-first host (`Never`: every completion is a `W` miss or hit as
    // in complete-first).
    if let Some(p) = std::env::var_os("X5_PILOT_OUT") {
        fs::write(&p, &table).expect("conformance: writing the pilot table");
    }
    // m4: a copy of the pilot's store for `c09_the_campaign_store_passes_check_store`.
    if let Some(p) = std::env::var_os("X5_PILOT_STORE") {
        fs::copy(d.store_path(), &p).expect("conformance: copying the pilot store");
    }
    note!("c05: {} rows, profile {}\n{table}", n_rows, prof());
    assert!(bad.is_empty(), "conformance: criterion 5: {bad:#?}");
}

// =========================================================================
// Criterion 9 (gate 4 round 01 m4) — the route to the campaign store
// =========================================================================

/// m4: the read-time checker over a stored campaign generation. Reads the
/// store named by `EVAL_STORE` (a campaign directory's `rows.csv`; the
/// pilot's `rows-test.csv` works too), runs [`check_store`] and fails, listing
/// every finding, if there is any (a finding fails the build and is filed,
/// criterion 3); labels (censored pairs, eligibility cost, skipped rows) are
/// printed, not failed. Fails if `EVAL_STORE` is unset. Run alone.
#[test]
#[ignore]
fn c09_the_campaign_store_passes_check_store() {
    let path = std::env::var_os("EVAL_STORE")
        .map(PathBuf::from)
        .expect("conformance: EVAL_STORE names the store to check");
    let rows: Vec<Rec> = read_rows(&path)
        .unwrap_or_else(|e| panic!("conformance: {}: {}", path.display(), e.text()));
    let (findings, labels) = check_store(&rows);
    let pairs = rows.iter().filter(|r| is_flat_key(&r["key"])).count();
    note!(
        "c09: {} rows, {pairs} Flat rows, {} findings, labels {labels:#?}",
        rows.len(),
        findings.len()
    );
    assert!(
        findings.is_empty(),
        "conformance: the store {} fails the read-time checks: {findings:#?}",
        path.display()
    );
}
