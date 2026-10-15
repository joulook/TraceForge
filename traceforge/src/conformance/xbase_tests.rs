//! `P5-XBASE` gate 3: the tester's tests (criteria `P5-XBASE.md` rev 1.10,
//! criteria 1–6).
//!
//! Tester-owned. Every expected figure was derived **before** the lead's diff
//! was read: `plan/traceForge/log/dev/P5-XBASE.derived.md` (sha256 in
//! `backlog/changes.md`); the counts are `cfirst-1`'s (read-only). Tests that
//! spawn child processes are `#[ignore]`d and run one per invocation, writing
//! only under the system temporary directory; the real stores are only read.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use crate::conformance::eval::{
    builtin_specs, eval_row_of, fixture_by_name, header, parse_engine, parse_key, parse_label,
    profile_name, read_rows, record_of, run_row_in_process, xbase_config, xbase_spec, Driver,
    Probes, RowMeta, RowSpec, RunKind, Series, Spec, Tier, LABEL_PIN, SCHEMA_VERSION,
};
use crate::conformance::grid::{
    run_grid, stack_mib_for, ApptabPair, Fixture, GridConfig, GridEnd, GridEngine, GridRaw,
};

macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

type Rec = BTreeMap<String, String>;

const PLAN: &str = "../../plan/traceForge/";
/// derived.md §3.
const XBASE_LABEL: &str = "Explore/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep";

fn plan(rel: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(PLAN).join(rel)
}

fn fx(name: &str) -> Fixture {
    fixture_by_name(name).unwrap_or_else(|e| panic!("conformance: {name}: {}", e.text()))
}

/// The fixture with a specification closure that records a call (criterion 1).
fn spied(name: &str) -> (Fixture, Arc<AtomicBool>) {
    let mut f = fx(name);
    let called = Arc::new(AtomicBool::new(false));
    let c = called.clone();
    f.specification = Arc::new(move || {
        c.store(true, Ordering::SeqCst);
    });
    (f, called)
}

/// The configuration F1 says the arm passes: the fixture's own, plus
/// `keep_going_after_error = true`.
fn f1_config(f: &Fixture) -> crate::Config {
    let mut c = f.config.clone();
    c.keep_going_after_error = true;
    c
}

fn stats_of(end: &GridEnd) -> (usize, usize) {
    match end {
        GridEnd::Ok(r) => match &r.raw {
            GridRaw::Explore(s) => (s.execs, s.block),
            other => panic!("conformance: not an Explore result: {other:?}"),
        },
        other => panic!("conformance: the run did not complete: {other:?}"),
    }
}

fn rec(end: &GridEnd, f: &Fixture) -> Rec {
    let rs = RowSpec {
        fixture: f.name.clone(),
        config: xbase_config(),
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
    let row = eval_row_of(end, &RowMeta::of(&rs, profile_name(), "xbase-tests", ""));
    header()
        .iter()
        .map(|h| (*h).to_owned())
        .zip(record_of(&row))
        .collect()
}

// =========================================================================
// Criterion 1 — the implementation alone; the count
// =========================================================================

/// C1 (F1, F2): on the four pinned fixtures (derived.md §1), the `Explore`
/// run through the runner's path (`run_row_in_process`) never calls the
/// specification closure, returns `GridRaw::Explore`, and its `(execs,
/// block)` equals a direct `crate::verify(fixture.config + keep_going,
/// implementation)` and the pin; the row's `executions` is `execs + block`
/// and equals `cfirst-1`'s for the fixture; `outer_graphs(execs+block)` is
/// `Some(sum)`. The two smallest also go through `run_grid` (grid.rs's
/// `call`, hand-count sizes).
#[test]
fn c01_the_implementation_alone_and_the_count() {
    let pins: [(&str, (usize, usize), u64); 4] = [
        ("apps/a4/hash/a4a/k2q2m2", (0, 6), 6),
        ("2pc/leader/split/n3", (0, 882), 882),
        ("2pc/leader/conf/n2", (6, 0), 6),
        ("apps/a2/pb/spec/k2q2", (6, 0), 6),
    ];
    let mut bad = Vec::new();
    for (name, want, cfirst) in pins {
        let (f, called) = spied(name);
        let end = run_row_in_process(&f, &xbase_config(), false);
        let got = stats_of(&end);
        let s = crate::verify(f1_config(&f), {
            let imp = f.implementation.clone();
            move || imp()
        });
        let direct = (s.execs, s.block);
        let r = rec(&end, &f);
        note!(
            "c01 {name}: explore {got:?} direct {direct:?} executions {} outer {:?}",
            r["executions"],
            r["outer_graphs(execs+block)"]
        );
        if called.load(Ordering::SeqCst) {
            bad.push(format!("{name}: the specification closure was called"));
        }
        if got != want || direct != want {
            bad.push(format!(
                "{name}: explore {got:?} direct {direct:?} pin {want:?}"
            ));
        }
        let sum = (want.0 + want.1) as u64;
        if r["executions"] != sum.to_string() || sum != cfirst {
            bad.push(format!(
                "{name}: executions {} (sum {sum}, cfirst-1 {cfirst})",
                r["executions"]
            ));
        }
        if r["outer_graphs(execs+block)"] != format!("Some({sum})") {
            bad.push(format!(
                "{name}: outer_graphs {:?}",
                r["outer_graphs(execs+block)"]
            ));
        }
        if r["engine"] != "Explore" || r["end_class"] != "ok" {
            bad.push(format!(
                "{name}: engine {} end {}",
                r["engine"], r["end_class"]
            ));
        }
    }
    for name in ["apps/a4/hash/a4a/k2q2m2", "2pc/leader/conf/n2"] {
        let (f, called) = spied(name);
        let end = run_grid(&f, &xbase_config(), None);
        let got = stats_of(&end);
        let want = if name.starts_with("apps") {
            (0, 6)
        } else {
            (6, 0)
        };
        if got != want || called.load(Ordering::SeqCst) {
            bad.push(format!(
                "run_grid {name}: {got:?} called {}",
                called.load(Ordering::SeqCst)
            ));
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 1: {bad:#?}");
}

/// C1: a specification closure that **panics** does not disturb the run (it
/// is never called), on the blocking A4 fixture.
#[test]
fn c01_a_panicking_specification_is_never_called() {
    let mut f = fx("apps/a4/hash/a4a/k2q2m2");
    f.specification = Arc::new(|| panic!("conformance: the specification was called"));
    let end = run_row_in_process(&f, &xbase_config(), false);
    assert_eq!(stats_of(&end), (0, 6), "conformance: the count");
}

// =========================================================================
// Criterion 2 — the configuration as passed
// =========================================================================

fn arm_text(file: &str, start: &str) -> String {
    let src = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/conformance")
            .join(file),
    )
    .unwrap();
    let i = src
        .find(start)
        .unwrap_or_else(|| panic!("conformance: no `{start}` in {file}"));
    let tail = &src[i..];
    let j = tail
        .find("GridRaw::Explore(")
        .expect("conformance: the arm's result");
    let k = tail[j..].find('\n').unwrap() + j;
    tail[..k].to_owned()
}

/// C2 (F1). `Config` exposes no hook on the configuration the arm builds, so
/// three checks together:
/// (a) both `Explore` arms (`grid.rs::call`, `eval.rs::call_with`) build it as
///     exactly `fixture.config.clone()` + `keep_going_after_error = true` and
///     pass it to `crate::verify(cfg, move || imp())`, with no other
///     statement touching `cfg`;
/// (b) on an A1–A4 fixture and a leader fixture, the serde JSON of that
///     configuration (`f1_config`) equals `fixture.config`'s in every field
///     but `keep_going_after_error`, and carries `parallel = false`,
///     `partitioned_parallelization = false`, `parallel_workers = None`,
///     `thread_threshold` 1 000 / 65 536, `seed = 0`, `cons_type = FIFO`,
///     `progress_report = 0`, `mode = Verification`, `schedule_policy = LTR`,
///     `max_iterations = None`, no dot/trace file;
/// (c) behaviourally, c01's `(execs, block)` equals `verify(f1_config)`.
#[test]
fn c02_the_configuration_as_passed() {
    let mut bad = Vec::new();
    for (file, start) in [
        ("grid.rs", "        GridEngine::Explore => {\n            // `P5-XBASE` F1: the fixture's own `Config`"),
        ("eval.rs", "        GridEngine::Explore => {\n            // `P5-XBASE` F1: the fixture's own `Config`"),
    ] {
        let t = arm_text(file, start);
        let code: Vec<&str> = t
            .lines()
            .map(str::trim)
            .filter(|l| !l.starts_with("//") && !l.is_empty())
            .collect();
        let touching: Vec<&&str> = code.iter().filter(|l| l.contains("cfg")).collect();
        let want = [
            "let mut cfg = fixture.config.clone();",
            "cfg.keep_going_after_error = true;",
        ];
        if !touching.iter().take(2).map(|l| **l).eq(want) {
            bad.push(format!("{file}: the arm's cfg lines {touching:?}"));
        }
        let calls = touching
            .iter()
            .filter(|l| l.contains("crate::verify(cfg, move || imp())"))
            .count();
        if touching.len() != 3 || calls != 1 {
            bad.push(format!("{file}: cfg used {} times, verify(cfg, imp) {calls}", touching.len()));
        }
        if code.iter().any(|l| l.contains("spec()") || l.contains("specification")) {
            bad.push(format!("{file}: the arm mentions the specification"));
        }
    }
    for (name, threshold) in [
        ("apps/a4/hash/a4a/k2q2m2", 1000u64),
        ("2pc/leader/split/n3", 65536),
    ] {
        let f = fx(name);
        let mut a = serde_json::to_value(&f.config).unwrap();
        let b = serde_json::to_value(f1_config(&f)).unwrap();
        if b["keep_going_after_error"] != serde_json::json!(true) {
            bad.push(format!(
                "{name}: keep_going {}",
                b["keep_going_after_error"]
            ));
        }
        a["keep_going_after_error"] = serde_json::json!(true);
        if a != b {
            bad.push(format!("{name}: a field other than keep_going differs"));
        }
        let checks: [(&str, serde_json::Value); 13] = [
            ("parallel", serde_json::json!(false)),
            ("partitioned_parallelization", serde_json::json!(false)),
            ("parallel_workers", serde_json::Value::Null),
            ("thread_threshold", serde_json::json!(threshold)),
            ("seed", serde_json::json!(0)),
            ("cons_type", serde_json::json!("FIFO")),
            ("progress_report", serde_json::json!(0)),
            ("mode", serde_json::json!("Verification")),
            ("schedule_policy", serde_json::json!("LTR")),
            ("max_iterations", serde_json::Value::Null),
            ("dot_file", serde_json::Value::Null),
            ("trace_file", serde_json::Value::Null),
            ("error_trace_file", serde_json::Value::Null),
        ];
        for (k, v) in checks {
            if b[k] != v {
                bad.push(format!("{name}: {k} = {} (want {v})", b[k]));
            }
        }
        for k in ["symmetry", "vr", "warnings_as_errors"] {
            if b[k] != serde_json::json!(false) {
                bad.push(format!("{name}: {k} = {}", b[k]));
            }
        }
        for k in ["lossy_budget", "verbose"] {
            if b[k] != serde_json::json!(0) {
                bad.push(format!("{name}: {k} = {}", b[k]));
            }
        }
        note!(
            "c02 {name}: thread_threshold {} cons {} mode {} policy {}",
            b["thread_threshold"],
            b["cons_type"],
            b["mode"],
            b["schedule_policy"]
        );
    }
    assert!(bad.is_empty(), "conformance: criterion 2: {bad:#?}");
}

// =========================================================================
// Criterion 3 — the label and the key
// =========================================================================

/// C3 (F1, F3): the label pin, eleven fields, `parse_label` the identity,
/// `parse_engine("Explore")`; every `XBASE` key is distinct from every key of
/// `cfirst-1` and `apptab-1` (read-only scans) and every old key still parses.
#[test]
fn c03_the_label_and_the_key() {
    let l = xbase_config().label();
    assert_eq!(l, XBASE_LABEL, "conformance: the label");
    assert_eq!(l.split('/').count(), 11, "conformance: eleven fields");
    assert_eq!(
        parse_label(&l).map(|c| c.label()),
        Some(l.clone()),
        "conformance: identity"
    );
    assert_eq!(parse_engine("Explore"), Some(GridEngine::Explore));
    assert_eq!(
        GridConfig::new(GridEngine::Enumerator).label(),
        LABEL_PIN,
        "conformance: LABEL_PIN"
    );
    let prof = profile_name();
    let xk: BTreeSet<String> = xbase_spec().rows.iter().map(|r| r.key(prof)).collect();
    let xr: BTreeSet<String> = xbase_spec().rows.iter().map(|r| r.key("release")).collect();
    let mut bad = Vec::new();
    for store in ["log/eval/cfirst-1/rows.csv", "log/eval/apptab-1/rows.csv"] {
        let rows = read_rows(&plan(store)).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
        for r in &rows {
            let k = &r["key"];
            if xk.contains(k) || xr.contains(k) {
                bad.push(format!("{store}: collides {k}"));
            }
            if parse_key(k).is_none() {
                bad.push(format!("{store}: no longer parses {k}"));
            }
        }
        note!("c03: {store} {} keys scanned", rows.len());
    }
    for k in &xr {
        let (_, c, ..) = parse_key(k).unwrap_or_else(|| panic!("conformance: {k}"));
        if c.engine != GridEngine::Explore || c.label() != XBASE_LABEL {
            bad.push(format!("key {k}"));
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 3: {bad:#?}");
}

// =========================================================================
// Criterion 4 — the row and the split line
// =========================================================================

/// C4 (F2): the header is schema 3's (185 columns; the byte pin is
/// `eval_tests::pin_the_label_format_and_the_header_beside_the_schema_version`,
/// unchanged), and the stack is 32 MiB for an APPTAB fixture under `Explore`.
#[test]
fn c04_the_header_and_the_stack() {
    assert_eq!(SCHEMA_VERSION, 3, "conformance: schema");
    assert_eq!(header().len(), 185, "conformance: header width");
    for name in [
        "apps/a4/hash/a4a/k2q2m2",
        "2pc/leader/conf/n2",
        "apps/a1/correct/spec/n2r2",
    ] {
        let f = fx(name);
        assert_eq!(
            stack_mib_for(&f, &xbase_config()),
            32,
            "conformance: stack {name}"
        );
        assert_eq!(
            stack_mib_for(&f, &xbase_config()),
            stack_mib_for(&f, &GridConfig::new(GridEngine::CompleteFirst)),
            "conformance: the paired conformance row's stack"
        );
    }
}

/// The child: one row through the runner's child (`eval_row`); its stdout.
fn child_row(name: &str, dir: &Path) -> (String, Rec) {
    fs::create_dir_all(dir).unwrap();
    let rs = RowSpec {
        fixture: name.to_owned(),
        config: xbase_config(),
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
        .env("EVAL_COMMIT", "xbase-tests")
        .env("EVAL_RUN_DIR", dir)
        .env_remove("EVAL_EXPORT")
        .env_remove("EVAL_SCHEDULE")
        .env_remove("EVAL_OUT")
        .env_remove("EVAL_SPEC")
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
    (
        text,
        header()
            .iter()
            .map(|c| (*c).to_owned())
            .zip(cells)
            .collect(),
    )
}

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tf-xbase-tests-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).expect("conformance: a temp directory");
    d
}

/// C4 (F2) through the child, on the blocking A4 fixture, leader split n3 and
/// the non-blocking leader conf n2: exactly one `xbase: execs=<n> block=<n>
/// max_graph_events=<n>` line on stdout, not containing the sentinel, whose
/// `execs + block` equals the stored row's `executions`; the progress lines
/// are exactly Must's **default adaptive schedule**, which `progress_report =
/// 0` selects (`must.rs`, `should_report`: 1–9, 10–90, 100–900, …), the same
/// lines the outer conformance run prints (F1 as of rev 1.10; gate 3's T1
/// corrected the earlier "no progress lines"); the row's
/// `engine` `Explore`, `cache`/`carry` `n/a`, `stack_mib` 32,
/// `end_class` `ok`, `outer_graphs(execs+block)` `Some(sum)`.
#[test]
#[ignore]
fn c04_the_split_line_through_the_child() {
    let base = temp("c04");
    let mut bad = Vec::new();
    for (name, want) in [
        ("apps/a4/hash/a4a/k2q2m2", (0usize, 6usize)),
        ("2pc/leader/split/n3", (0, 882)),
        ("2pc/leader/conf/n2", (6, 0)),
    ] {
        let (text, r) = child_row(name, &base.join(name.replace('/', "_")));
        let lines: Vec<&str> = text.lines().filter(|l| l.contains("xbase:")).collect();
        note!("c04 {name}: {lines:?} executions {}", r["executions"]);
        if lines.len() != 1 {
            bad.push(format!("{name}: {} xbase lines", lines.len()));
            continue;
        }
        let l = lines[0];
        if l.contains(crate::conformance::eval::SENTINEL) || !l.starts_with("xbase: ") {
            bad.push(format!("{name}: the line {l:?}"));
        }
        let field = |k: &str| -> usize {
            l.split_whitespace()
                .find_map(|t| t.strip_prefix(&format!("{k}=")))
                .and_then(|v| v.parse().ok())
                .unwrap_or(usize::MAX)
        };
        let (e, b, m) = (field("execs"), field("block"), field("max_graph_events"));
        if (e, b) != want || m == usize::MAX || m == 0 {
            bad.push(format!(
                "{name}: execs {e} block {b} max {m}, want {want:?}"
            ));
        }
        if r["executions"] != (e + b).to_string()
            || r["outer_graphs(execs+block)"] != format!("Some({})", e + b)
        {
            bad.push(format!(
                "{name}: row executions {} outer {}",
                r["executions"], r["outer_graphs(execs+block)"]
            ));
        }
        let progress: Vec<u64> = text
            .lines()
            .filter_map(|l| l.split("Executions attempted so far: ").nth(1))
            .filter_map(|t| t.split_whitespace().next()?.parse().ok())
            .collect();
        let schedule: Vec<u64> = (1..=(e + b) as u64)
            .filter(|n| {
                let mut p = *n;
                while p % 10 == 0 {
                    p /= 10;
                }
                p < 10
            })
            .collect();
        note!("c04 {name}: {} progress lines", progress.len());
        if progress != schedule {
            bad.push(format!(
                "{name}: progress {progress:?}, the default schedule {schedule:?}"
            ));
        }
        for (c, v) in [
            ("engine", "Explore"),
            ("cache", "n/a"),
            ("carry", "n/a"),
            ("stack_mib", "32"),
            ("end_class", "ok"),
        ] {
            if r[c] != v {
                bad.push(format!("{name}: {c} = {}", r[c]));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 4: {bad:#?}");
}

// =========================================================================
// Criterion 5 — the spec
// =========================================================================

/// derived.md §5, re-derived from `cfirst-1` by the rule (read-only): the
/// largest size with an `ok` or `capped_*` row in any configuration.
fn max_from_cfirst() -> BTreeMap<String, usize> {
    let rows = read_rows(&plan("log/eval/cfirst-1/rows.csv"))
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let mut m = BTreeMap::new();
    for r in &rows {
        let ec = &r["end_class"];
        if ec != "ok" && !ec.starts_with("capped_") {
            continue;
        }
        let fxn = r["key"].split('|').next().unwrap();
        let (pair, s) = crate::conformance::grid::apptab_pair_of(fxn)
            .unwrap_or_else(|| panic!("conformance: {fxn}"));
        let e = m
            .entry(pair.label().to_owned() + "@" + pair.family())
            .or_insert(0);
        *e = (*e).max(s);
    }
    m
}

/// C5 (F3): 114 keys = `ApptabPair::ALL × 2..=max(pair) × {0,1,2}`; the
/// `max` table equals the rule on `cfirst-1` (derived.md §5); the vector is
/// size → benchmark → pair → rep; every row `timed`, `default`, `Explore`,
/// the series scope `<family>|<variant>|diag|<label>|default|timed` at the
/// row's size; `XBASE` absent from `builtin_specs` and no built-in spec holds
/// an `Explore` row.
#[test]
fn c05_the_spec() {
    let spec = xbase_spec();
    let mut bad = Vec::new();
    assert_eq!(spec.name, "XBASE");
    let derived: BTreeMap<(&str, &str), usize> = [
        (("a1", "correct"), 4),
        (("a1", "eager"), 3),
        (("a1", "silent"), 3),
        (("a2", "pb"), 4),
        (("a2", "stale-get"), 4),
        (("a2", "silent-put"), 4),
        (("a3", "fifo"), 3),
        (("a3", "double-grant"), 3),
        (("a3", "never-grant"), 3),
        (("a4", "hash"), 3),
        (("a4", "rr"), 3),
        (("a4", "hash-drop"), 3),
        (("le", "conf"), 5),
        (("le", "split"), 4),
        (("le", "silent"), 4),
    ]
    .into_iter()
    .collect();
    let rule = max_from_cfirst();
    for p in ApptabPair::ALL {
        let d = derived[&(p.family(), p.label())];
        let r = rule
            .get(&(p.label().to_owned() + "@" + p.family()))
            .copied();
        if r != Some(d) {
            bad.push(format!(
                "{} {}: derived {d} rule {r:?}",
                p.family(),
                p.label()
            ));
        }
    }
    let mut want = Vec::new();
    for s in 2..=5usize {
        for p in ApptabPair::ALL {
            if s <= derived[&(p.family(), p.label())] {
                for rep in 0..3u32 {
                    want.push((p.name(s), rep, s, p));
                }
            }
        }
    }
    let got: Vec<(String, u32)> = spec
        .rows
        .iter()
        .map(|r| (r.fixture.clone(), r.rep))
        .collect();
    let wantk: Vec<(String, u32)> = want.iter().map(|(f, r, ..)| (f.clone(), *r)).collect();
    if got != wantk {
        bad.push(format!(
            "the vector: {} rows, want {}",
            got.len(),
            wantk.len()
        ));
    }
    if spec.rows.len() != 114 {
        bad.push(format!("{} rows", spec.rows.len()));
    }
    let keys: BTreeSet<String> = spec.rows.iter().map(|r| r.key("release")).collect();
    if keys.len() != 114 {
        bad.push(format!("{} distinct keys", keys.len()));
    }
    for (r, (_, _, s, p)) in spec.rows.iter().zip(&want) {
        let scope = format!(
            "{}|{}|diag|{XBASE_LABEL}|default|timed",
            p.family(),
            p.variant()
        );
        let ok = r.run_kind == RunKind::Timed
            && r.tier.name == "default"
            && r.config.engine == GridEngine::Explore
            && r.config.label() == XBASE_LABEL
            && r.series.as_ref().map(|x| (x.scope.as_str(), x.size))
                == Some((scope.as_str(), *s as i64));
        if !ok {
            bad.push(format!(
                "{}: {:?} {} series {:?}",
                r.fixture,
                r.run_kind,
                r.tier.name,
                r.series.as_ref().map(|x| (&x.scope, x.size))
            ));
        }
        if !r
            .key("release")
            .ends_with(&format!("|{XBASE_LABEL}|{}|default|timed|release", r.rep))
        {
            bad.push(format!("key {}", r.key("release")));
        }
    }
    let names: Vec<String> = builtin_specs().into_iter().map(|s| s.name).collect();
    if names.iter().any(|n| n == "XBASE") {
        bad.push("XBASE is built in".to_owned());
    }
    if names
        != [
            "X0", "CAL", "CALX", "X1", "X1V", "X2", "X2P", "X2S", "X1P", "X3A", "X5", "X5G",
        ]
    {
        bad.push(format!("builtin_specs {names:?}"));
    }
    for s in builtin_specs() {
        if s.rows
            .iter()
            .any(|r| r.config.engine == GridEngine::Explore)
        {
            bad.push(format!("{} holds an Explore row", s.name));
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 5: {bad:#?}");
}

// =========================================================================
// Criterion 6 — the rep and series rules (child processes)
// =========================================================================

fn clean_probes() -> Probes {
    Probes {
        git: Box::new(|| ("xbase-tests".to_owned(), false)),
        host: Box::new(|| "xbase-tests-host".to_owned()),
    }
}

/// The rows of c06: `XBASE`'s rows of leader conf at sizes 4 and 5 (reps
/// 0–2), moved to a 2 s tier (their series rebuilt for that tier).
fn c06_rows() -> Vec<RowSpec> {
    let t2 = Tier {
        name: "t2s".to_owned(),
        wall: Duration::from_secs(2),
        mem_kb: 4 * 1024 * 1024,
    };
    xbase_spec()
        .rows
        .into_iter()
        .filter(|r| r.fixture == "2pc/leader/conf/n4" || r.fixture == "2pc/leader/conf/n5")
        .map(|mut r| {
            let size = r.series.as_ref().unwrap().size;
            r.tier = t2.clone();
            r.series = Some(Series::of(
                "le|conforming",
                "diag",
                &r.config,
                &t2,
                RunKind::Timed,
                size,
            ));
            r
        })
        .collect()
}

/// The child of the driver tests (`XBASE_CASE`): `from_env` runs
/// `Driver::from_env()` and prints the spec names it built; `rules` runs
/// c06's rows under the spec name `XBASE` into `XBASE_CASE_OUT`.
#[test]
#[ignore]
fn xbase_child() {
    let Ok(case) = std::env::var("XBASE_CASE") else {
        return;
    };
    let line = match case.as_str() {
        "from_env" => match Driver::from_env() {
            Err(e) => format!("from_env: {}", e.text()),
            Ok(d) => format!(
                "spec {} rows {} specs {}",
                d.spec.name,
                d.spec.rows.len(),
                d.specs
                    .iter()
                    .map(|s| s.name.as_str())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        },
        "rules" => {
            let d = Driver {
                spec: Spec {
                    name: "XBASE".to_owned(),
                    rows: c06_rows(),
                },
                specs: builtin_specs(),
                out_dir: PathBuf::from(std::env::var("XBASE_CASE_OUT").unwrap()),
                sample_period: Duration::from_millis(100),
                probes: clean_probes(),
                allow_mixed: true,
                only: std::env::var("XBASE_CASE_ONLY").ok(),
            };
            match d.run() {
                Ok(s) => format!(
                    "ran {} present {} skipped_rep {} skipped_after_censor {}",
                    s.ran, s.skipped_present, s.skipped_rep, s.skipped_after_censor
                ),
                Err(e) => e.text(),
            }
        }
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
        "conformance::xbase_tests::xbase_child",
        "--nocapture",
        "--test-threads=1",
    ]);
    for k in ["EVAL_SCHEDULE", "EVAL_OUT", "EVAL_SPEC", "EVAL_ONLY"] {
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
                    .filter(|l| l.contains("panicked"))
                    .take(2)
                    .collect::<Vec<_>>()
                    .join(" / ")
            )
        })
}

/// C5 (F3) through `from_env` (child): `EVAL_SPEC=XBASE` builds the 114-row
/// spec; `EVAL_SPEC=X0` builds no `XBASE` (absent unless named). Run alone.
#[test]
#[ignore]
fn c05_xbase_is_reachable_only_by_name() {
    let base = temp("c05");
    let x = child_case(&[
        ("XBASE_CASE", "from_env".into()),
        ("EVAL_SPEC", "XBASE".into()),
        ("EVAL_OUT", base.join("x").display().to_string()),
        ("EVAL_ALLOW_MIXED", "1".into()),
    ]);
    let o = child_case(&[
        ("XBASE_CASE", "from_env".into()),
        ("EVAL_SPEC", "X0".into()),
        ("EVAL_OUT", base.join("o").display().to_string()),
        ("EVAL_ALLOW_MIXED", "1".into()),
    ]);
    note!("c05: XBASE → {x}\nc05: X0 → {o}");
    assert!(x.starts_with("spec XBASE rows 114 "), "conformance: {x}");
    assert!(
        o.starts_with("spec X0 ") && !o.contains("XBASE"),
        "conformance: {o}"
    );
}

/// C6 (F4) through the driver as F5's runner drives it: one invocation per
/// (pair, size) glob, leader conf under a 2 s tier.
/// 1. `only = 2pc/leader/conf/n4|*`: rep 0 `capped_wall`, reps 1–2
///    `skipped_rep` (`ran 1 present 0 skipped_rep 2 skipped_after_censor 0`).
/// 2. `only = 2pc/leader/conf/n5|*`, a fresh process: the series end is
///    **rebuilt from the store** — the three n5 rows `skipped_after_censor`
///    (`ran 0 present 0 skipped_rep 0 skipped_after_censor 3`), no wall.
/// 3. Everything: nothing runs (`ran 0 present 6`), the store byte-identical
///    to the one invocation 2 left.
///
/// Only rep 0 of n4 carries a wall. Run alone.
#[test]
#[ignore]
fn c06_the_rep_and_series_rules() {
    let base = temp("c06");
    let out = base.join("out");
    let run = |only: Option<&str>| {
        let mut env = vec![
            ("XBASE_CASE", "rules".to_owned()),
            ("XBASE_CASE_OUT", out.display().to_string()),
        ];
        if let Some(o) = only {
            env.push(("XBASE_CASE_ONLY", o.to_owned()));
        }
        child_case(&env)
    };
    let store = out.join(if profile_name() == "release" {
        "rows.csv"
    } else {
        "rows-test.csv"
    });
    let first = run(Some("2pc/leader/conf/n4|*"));
    let rows1 = read_rows(&store).unwrap_or_default().len();
    let second = run(Some("2pc/leader/conf/n5|*"));
    let after2 = fs::read(&store).unwrap_or_default();
    let third = run(None);
    let after3 = fs::read(&store).unwrap_or_default();
    note!("c06: {first} / {second} / {third}");
    let rows = read_rows(&store).unwrap_or_default();
    let mut got: Vec<(String, String, String, String)> = rows
        .iter()
        .map(|r| {
            let p: Vec<&str> = r["key"].split('|').collect();
            (
                p[0].to_owned(),
                p[2].to_owned(),
                r["end_class"].clone(),
                r["proc_wall_ms"].clone(),
            )
        })
        .collect();
    got.sort();
    note!("c06 rows: {got:?}");
    let mut bad = Vec::new();
    for (f, rep, class, wall) in &got {
        let want = match (f.as_str(), rep.as_str()) {
            ("2pc/leader/conf/n4", "0") => "capped_wall",
            ("2pc/leader/conf/n4", _) => "skipped_rep",
            _ => "skipped_after_censor",
        };
        if class != want {
            bad.push(format!("{f} rep {rep}: {class}, want {want}"));
        }
        if (want == "capped_wall") == wall.is_empty() {
            bad.push(format!("{f} rep {rep}: wall {wall:?}"));
        }
    }
    if got.len() != 6 || rows1 != 3 {
        bad.push(format!("{} rows ({rows1} after invocation 1)", got.len()));
    }
    if !first.starts_with("ran 1 present 0 skipped_rep 2 skipped_after_censor 0") {
        bad.push(format!("invocation 1: {first}"));
    }
    if !second.starts_with("ran 0 present 0 skipped_rep 0 skipped_after_censor 3") {
        bad.push(format!("invocation 2 (the rebuild): {second}"));
    }
    if !third.starts_with("ran 0 present 6") || after2 != after3 {
        bad.push(format!(
            "invocation 3: {third} (store changed: {})",
            after2 != after3
        ));
    }
    assert!(bad.is_empty(), "conformance: criterion 6: {bad:#?}");
}
