//! `P5-APPTAB` gate 3: the tester's tests (criteria `P5-APPTAB.md` rev 3.4,
//! the landing errata E-AT-1..5).
//!
//! Tester-owned (the module lines in `mod.rs` are the lead's). Every expected
//! figure was derived **before** the lead's APPTAB code was read:
//! `plan/traceForge/log/dev/P5-APPTAB.derived.md` (sha256 in
//! `backlog/changes.md`). Tests are named by criterion (`c01_…` … `c12_…`); a
//! test reproducing a defect of the lead's code is `t<N>_…`, `#[ignore]`d with
//! both values in its rustdoc. Tests that spawn child processes (the driver,
//! the schedule, the exports) are `#[ignore]`d and run one per invocation
//! (`--ignored --exact … --test-threads=1`); they write only under the system
//! temporary directory, never into a real store (`log/eval/*`).
//!
//! The schedule files here are written by the tester's own generator
//! ([`sched_rows`], [`sched_profiling`]) from criteria T6's text, not by the
//! lead's (the scratchpad script), so the parser is checked against an
//! independent expansion.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use crate::conformance::eval::{
    all_fixtures, apptab_spec, apptab_specs, apptabp_spec, apptabs_spec, apptabw_spec,
    builtin_specs, csv_line, edprobe_spec, eval_row_of, experiments_of, exports_of,
    fixture_by_name, fixture_domain, header, parse_csv_line, profile_name, read_rows, record_of,
    row_json, run_row_in_process, schedule, x1_config, x2_config, Driver, Probes, RowMeta, RowSpec,
    RunKind, Schedule, Series, Spec, Store, Tier, LABEL_PIN, SCHEMA_VERSION, SENTINEL,
};
use crate::conformance::grid::{
    apptab_build, apptab_fixtures, apptab_pair_of, ApptabPair, Fixture, GridConfig, GridEnd,
    GridEngine, Group, APPTAB_MAX_SIZE, CONF_THREAD_THRESHOLD,
};
use crate::conformance::selector::Selector;
use crate::ConsType;

/// Writes a line to stderr (the closed `s5_tests` emission scan forbids the
/// print macros in every file under `conformance/` outside its test-only list).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

type Rec = BTreeMap<String, String>;

const ENGINES: [GridEngine; 4] = [
    GridEngine::Enumerator,
    GridEngine::Stateful,
    GridEngine::CompleteFirst,
    GridEngine::Gated,
];
const ALL_REPORTS: [GridEngine; 3] = [
    GridEngine::Stateful,
    GridEngine::CompleteFirst,
    GridEngine::Gated,
];

fn prof() -> &'static str {
    profile_name()
}

fn plan() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../plan/traceForge")
}

/// The pairs of T2's table, from the criteria's text (family, label,
/// variant, conforming).
const PAIRS: [(&str, &str, &str); 15] = [
    ("a1", "correct", "conforming"),
    ("a1", "eager", "mutant:eager"),
    ("a1", "silent", "mutant:silent"),
    ("a2", "pb", "conforming"),
    ("a2", "stale-get", "mutant:stale-get"),
    ("a2", "silent-put", "mutant:silent-put"),
    ("a3", "fifo", "conforming"),
    ("a3", "double-grant", "mutant:double-grant"),
    ("a3", "never-grant", "mutant:never-grant"),
    ("a4", "hash", "conforming"),
    ("a4", "rr", "mutant:rr-a4a"),
    ("a4", "hash-drop", "mutant:hash-drop-a4a"),
    ("le", "conf", "conforming"),
    ("le", "split", "mutant:split"),
    ("le", "silent", "mutant:silent"),
];

/// T2's names.
fn pname(fam: &str, label: &str, s: usize) -> String {
    match fam {
        "a1" => format!("apps/a1/{label}/spec/n{s}r{s}"),
        "a2" | "a3" => format!("apps/{fam}/{label}/spec/k{s}q{s}"),
        "a4" => format!("apps/a4/{label}/a4a/k{s}q{s}m{s}"),
        _ => format!("2pc/leader/{label}/n{s}"),
    }
}

fn cfg_of(e: GridEngine, mode: &str) -> GridConfig {
    if mode == "first" {
        x2_config(e, Selector::Ltr)
    } else {
        x1_config(e, Selector::Ltr)
    }
}

fn timed_key(fixture: &str, cfg: &GridConfig, profile: &str) -> String {
    format!("{fixture}|{}|0|default|timed|{profile}", cfg.label())
}

fn series_of(fam: &str, variant: &str, cfg: &GridConfig) -> String {
    format!("{fam}|{variant}|diag|{}|default|timed", cfg.label())
}

/// The run conditions T6 requires verbatim (copied from the criteria's
/// constants as landed: `COND_W`, `COND_S`, `COND_P`).
const COND_W: &str = "no dependency; runs before size 2 (plan §7 item 5)";
const COND_S: &str = "runs after the (benchmark, size) timed block whatever its outcomes; \
certifies the block's complete first reports (plan §3)";
const COND_P: &str = "runs only when its timed row completed (end_class ok) with reports >= 1; \
a missing, failed, censored or budget-skipped twin leaves the report unclassified (plan §7 item 5)";

/// T6's rows for `s = 2..=max`, in the balanced order (size, benchmark, the
/// three pairs, each mutant's first-report then all-reports rows), with the
/// keys at `profile`.
fn sched_rows(max: usize, profile: &str) -> Vec<serde_json::Value> {
    let mut out = Vec::new();
    for s in 2..=max {
        for fam in ["a1", "a2", "a3", "a4", "le"] {
            for (f, label, variant) in PAIRS.iter().filter(|p| p.0 == fam) {
                let name = pname(f, label, s);
                let modes: Vec<(&str, &[GridEngine])> = if *variant == "conforming" {
                    vec![("exhaustive", &ENGINES[..])]
                } else {
                    vec![("first", &ENGINES[..]), ("exhaustive", &ALL_REPORTS[..])]
                };
                for (mode, engines) in modes {
                    for e in engines {
                        let cfg = cfg_of(*e, mode);
                        out.push(serde_json::json!({
                            "key": timed_key(&name, &cfg, profile),
                            "benchmark": fam,
                            "pair": label,
                            "engine": format!("{e:?}"),
                            "mode": mode,
                            "size": s,
                            "series": series_of(fam, variant, &cfg),
                        }));
                    }
                }
            }
        }
    }
    out
}

/// T6's profiling list, derived from the rows: the five `APPTABW` rows (rep
/// 1, size 2), then per row in order the `APPTABS` row of each first-seen
/// (conforming pair, size) and the `APPTABP` twin of each runnable
/// first-report row.
fn sched_profiling(
    rows: &[serde_json::Value],
    reused: &BTreeSet<String>,
    ended: &[(String, usize)],
    profile: &str,
) -> Vec<serde_json::Value> {
    let st = x1_config(GridEngine::Stateful, Selector::Ltr).label();
    let mut out = Vec::new();
    for fam in ["a1", "a2", "a3", "a4", "le"] {
        let conf = PAIRS
            .iter()
            .find(|p| p.0 == fam && p.2 == "conforming")
            .unwrap();
        out.push(serde_json::json!({
            "spec": "APPTABW",
            "key": format!("{}|{st}|1|default|profiling|{profile}", pname(fam, conf.1, 2)),
            "depends_on": [],
            "condition": COND_W,
        }));
    }
    let mut seen = BTreeSet::new();
    for r in rows {
        let fam = r["benchmark"].as_str().unwrap();
        let s = r["size"].as_u64().unwrap() as usize;
        let conf = PAIRS
            .iter()
            .find(|p| p.0 == fam && p.2 == "conforming")
            .unwrap();
        if seen.insert((fam.to_owned(), s)) {
            out.push(serde_json::json!({
                "spec": "APPTABS",
                "key": format!("{}|{st}|0|default|profiling|{profile}", pname(fam, conf.1, s)),
                "depends_on": [],
                "condition": COND_S,
            }));
        }
        let key = r["key"].as_str().unwrap();
        let series = r["series"].as_str().unwrap();
        let ended_before = ended.iter().any(|(se, z)| se == series && s > *z);
        if r["mode"] == "first" && !reused.contains(key) && !ended_before {
            out.push(serde_json::json!({
                "spec": "APPTABP",
                "key": key.replacen("|timed|", "|profiling|", 1),
                "depends_on": [key],
                "condition": COND_P,
            }));
        }
    }
    out
}

/// A complete schedule text (T6) for `max` with the given reuse and ended
/// lists; `reuse_store` names the fake campaign store.
fn sched_text(
    max: usize,
    reused: &[serde_json::Value],
    ended: &[(String, usize)],
    reuse_store: &str,
) -> String {
    // Gate 4 round 01 m1: the file **omits** the rows an `ended` series drops
    // (sizes above the end).
    let rows: Vec<serde_json::Value> = sched_rows(max, "release")
        .into_iter()
        .filter(|r| {
            let series = r["series"].as_str().unwrap();
            let s = r["size"].as_u64().unwrap() as usize;
            !ended.iter().any(|(se, z)| se == series && s > *z)
        })
        .collect();
    let rk: BTreeSet<String> = reused
        .iter()
        .map(|r| r["key"].as_str().unwrap().to_owned())
        .collect();
    let profiling = sched_profiling(&rows, &rk, ended, "release");
    serde_json::json!({
        "date": "2026-10-14",
        "source": "apptab_tests",
        "commit": "8f19f0f",
        "max_size": max,
        "limits": { "wall_ms": 600000, "mem_kb": 4194304, "budget_h": 60 },
        "reuse_store": reuse_store,
        "rows": rows,
        "reused": reused,
        "ended": ended
            .iter()
            .map(|(s, z)| serde_json::json!({ "series": s, "size": z, "reason": "campaign row censored at 600 s" }))
            .collect::<Vec<_>>(),
        "extension_reuse": [],
        "profiling": profiling,
    })
    .to_string()
}

fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tf-apptab-tests-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).expect("conformance: a temp directory");
    d
}

fn clean_probes() -> Probes {
    Probes {
        git: Box::new(|| ("apptab-tests".to_owned(), false)),
        host: Box::new(|| "apptab-tests-host".to_owned()),
    }
}

fn specs() -> &'static Vec<Spec> {
    static S: OnceLock<Vec<Spec>> = OnceLock::new();
    S.get_or_init(builtin_specs)
}

fn by_name() -> &'static BTreeMap<String, Fixture> {
    static F: OnceLock<BTreeMap<String, Fixture>> = OnceLock::new();
    F.get_or_init(|| {
        fixture_domain()
            .into_iter()
            .map(|f| (f.name.clone(), f))
            .collect()
    })
}

/// The stored record of one in-process run (`run_row_in_process(.., false)`).
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
    let row = eval_row_of(end, &RowMeta::of(&rs, prof(), "apptab-tests", ""));
    header()
        .iter()
        .map(|h| (*h).to_owned())
        .zip(record_of(&row))
        .collect()
}

/// The same row through the runner's child (`eval_row`, `EVAL_EXPORT`, a run
/// directory), a 60 s tier enforced here; the record by column.
fn child(spec: &RowSpec, export: &str, run_dir: &Path) -> Result<Rec, String> {
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
        .env("EVAL_COMMIT", "apptab-tests")
        .env("EVAL_RUN_DIR", run_dir)
        .env("EVAL_EXPORT", export)
        .env_remove("EVAL_SCHEDULE")
        .env_remove("EVAL_OUT")
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
        if t.elapsed() > Duration::from_secs(60) {
            let _ = c.kill();
            let _ = c.wait();
            return Err(format!("{}: over 60 s", spec.fixture));
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    let text = fs::read_to_string(run_dir.join("stdout")).unwrap();
    let Some(i) = text.find(SENTINEL) else {
        let err = fs::read_to_string(run_dir.join("stderr")).unwrap_or_default();
        return Err(format!(
            "no sentinel; stderr: {}",
            err.lines().take(3).collect::<Vec<_>>().join(" / ")
        ));
    };
    let cells = parse_csv_line(text[i + SENTINEL.len()..].lines().next().unwrap()).unwrap();
    Ok(header()
        .iter()
        .map(|c| (*c).to_owned())
        .zip(cells)
        .collect())
}

fn plain_row(fixture: &str, cfg: GridConfig, kind: RunKind, rep: u32) -> RowSpec {
    RowSpec {
        fixture: fixture.to_owned(),
        config: cfg,
        rep,
        tier: Tier::default_tier(),
        run_kind: kind,
        family: String::new(),
        knobs: String::new(),
        k: [None; 4],
        variant: String::new(),
        twin_key: String::new(),
        series: None,
    }
}

fn json_at(dir: &Path, file: &str) -> Option<serde_json::Value> {
    let t = fs::read_to_string(dir.join(file)).ok()?;
    Some(serde_json::from_str(&t).expect("conformance: valid JSON"))
}

/// Runs this test binary's `apptab_child` with the given environment; the
/// `CASE\t…` line it prints.
fn child_case(env: &[(&str, String)], remove: &[&str]) -> String {
    let mut c = std::process::Command::new(std::env::current_exe().unwrap());
    c.args([
        "--ignored",
        "--exact",
        "conformance::apptab_tests::apptab_child",
        "--nocapture",
        "--test-threads=1",
    ]);
    for k in [
        "EVAL_SCHEDULE",
        "EVAL_OUT",
        "EVAL_FROZEN",
        "APPTAB_CASE_ONLY",
    ] {
        c.env_remove(k);
    }
    for k in remove {
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
                    .take(4)
                    .collect::<Vec<_>>()
                    .join(" / ")
            )
        })
}

// =========================================================================
// Criterion 1 — the tier
// =========================================================================

/// C1 (rev 3.4): no `table` tier in the source; every row of the companion
/// specs at `default_tier()` (600 000 ms / 4 194 304 kB); a schedule whose
/// `limits` are not the default tier's is refused; a schedule row at another
/// tier is refused by name.
#[test]
fn c01_every_apptab_row_is_at_the_default_tier() {
    let src =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/eval.rs"))
            .expect("conformance: reading eval.rs");
    assert!(
        !src.contains("fn table("),
        "conformance: a `table` tier exists"
    );
    let d = Tier::default_tier();
    assert_eq!(
        (d.name.as_str(), d.wall.as_millis(), d.mem_kb),
        ("default", 600_000, 4_194_304),
        "conformance: the default tier"
    );
    for s in [apptabw_spec(), edprobe_spec()] {
        for r in &s.rows {
            assert_eq!(r.tier, d, "conformance: {} {}", s.name, r.fixture);
        }
    }
    let ok = sched_text(2, &[], &[], "/nonexistent");
    Schedule::parse(&ok).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let mut v: serde_json::Value = serde_json::from_str(&ok).unwrap();
    v["limits"]["wall_ms"] = serde_json::json!(1_800_000);
    let e = Schedule::parse(&v.to_string()).expect_err("conformance: 1800 s limits");
    assert!(
        e.text().contains("are not the default tier's"),
        "conformance: {}",
        e.text()
    );
    let mut v: serde_json::Value = serde_json::from_str(&ok).unwrap();
    let k = v["rows"][0]["key"].as_str().unwrap().to_owned();
    let bad = k.replace("|default|", "|extension|");
    v["rows"][0]["key"] = serde_json::json!(bad);
    let e = Schedule::parse(&v.to_string()).expect_err("conformance: an extension-tier row");
    assert!(
        e.text().contains(&bad) && e.text().contains("not `default`"),
        "conformance: {}",
        e.text()
    );
}

// =========================================================================
// Criterion 2 — the fixtures
// =========================================================================

/// C2 (E-AT-4): `apptab_fixtures` over `all_fixtures()`'s names adds exactly
/// the 83 derived names (105 T2 names minus the 22 `all_fixtures()` holds);
/// `fixture_domain()` is duplicate-free and resolves every T2 name; the new
/// fixtures carry the source citing this part, A1–A4 `apps_config()` (FIFO,
/// seed 0, thread bound 1 000) and `Group::Apps`, the leader FIFO, seed 0,
/// 65 536 and `Group::TwoPc`, `table = None`; `all_fixtures()` holds none of
/// them; `ApptabPair` matches T2's table (names, variants, the parser).
#[test]
fn c02_the_fixtures() {
    let all = all_fixtures();
    let names: BTreeSet<String> = all.iter().map(|f| f.name.clone()).collect();
    let t2: BTreeSet<String> = (2..=8)
        .flat_map(|s| PAIRS.iter().map(move |p| pname(p.0, p.1, s)))
        .collect();
    assert_eq!(t2.len(), 105, "conformance: T2's names");
    let held: BTreeSet<String> = t2.intersection(&names).cloned().collect();
    let want_held: BTreeSet<String> = [
        "apps/a1/correct/spec/n2r2",
        "apps/a1/eager/spec/n2r2",
        "apps/a1/silent/spec/n2r2",
        "apps/a1/correct/spec/n3r3",
        "apps/a1/eager/spec/n3r3",
        "apps/a1/silent/spec/n3r3",
        "apps/a2/pb/spec/k2q2",
        "apps/a2/stale-get/spec/k2q2",
        "apps/a2/silent-put/spec/k2q2",
        "apps/a2/pb/spec/k3q3",
        "apps/a2/stale-get/spec/k3q3",
        "apps/a2/silent-put/spec/k3q3",
        "apps/a3/fifo/spec/k2q2",
        "apps/a3/double-grant/spec/k2q2",
        "apps/a3/never-grant/spec/k2q2",
        "apps/a4/hash/a4a/k2q2m2",
        "apps/a4/rr/a4a/k2q2m2",
        "2pc/leader/conf/n2",
        "2pc/leader/conf/n3",
        "2pc/leader/split/n2",
        "2pc/leader/split/n3",
        "2pc/leader/split/n4",
    ]
    .iter()
    .map(|s| (*s).to_owned())
    .collect();
    assert_eq!(held, want_held, "conformance: the 22 held names");
    let added = apptab_fixtures(&names);
    let added_names: BTreeSet<String> = added.iter().map(|f| f.name.clone()).collect();
    assert_eq!(added.len(), 83, "conformance: the added fixtures");
    assert_eq!(
        added_names,
        t2.difference(&held).cloned().collect::<BTreeSet<_>>(),
        "conformance: exactly the missing names"
    );
    // `fixture_domain` = `all_fixtures` ∪ the added, duplicate-free.
    let dom = fixture_domain();
    let dom_names: BTreeSet<String> = dom.iter().map(|f| f.name.clone()).collect();
    assert_eq!(dom.len(), dom_names.len(), "conformance: duplicate names");
    assert_eq!(dom.len(), all.len() + 83, "conformance: the domain's size");
    assert!(
        names.is_disjoint(&added_names),
        "conformance: all_fixtures() holds an APPTAB-only name"
    );
    for n in [
        "apps/a4/hash-drop/a4a/k2q2m2",
        "2pc/leader/silent/n8",
        "apps/a3/fifo/spec/k8q8",
    ] {
        let f = fixture_by_name(n).unwrap_or_else(|e| panic!("conformance: {n}: {}", e.text()));
        assert_eq!(f.name, n, "conformance: resolved");
    }
    for f in &added {
        let (pair, s) =
            apptab_pair_of(&f.name).unwrap_or_else(|| panic!("conformance: {}", f.name));
        assert!(
            f.source.contains("P5-APPTAB"),
            "conformance: {} source {}",
            f.name,
            f.source
        );
        assert!(f.table.is_none(), "conformance: {} table", f.name);
        assert_eq!(
            f.config.cons_type,
            ConsType::FIFO,
            "conformance: {}",
            f.name
        );
        assert_eq!(f.config.seed, 0, "conformance: {} seed", f.name);
        if pair.family() == "le" {
            assert_eq!(f.group, Group::TwoPc, "conformance: {}", f.name);
            assert_eq!(
                f.config.thread_threshold, CONF_THREAD_THRESHOLD,
                "conformance: {}",
                f.name
            );
            assert_eq!(
                f.visible,
                (0..s).map(|i| format!("p{i}")).collect::<Vec<_>>(),
                "conformance: {}",
                f.name
            );
        } else {
            assert_eq!(f.group, Group::Apps, "conformance: {}", f.name);
            assert_eq!(f.config.thread_threshold, 1000, "conformance: {}", f.name);
            let want: Vec<String> = if pair.family() == "a1" {
                vec!["p0".into(), "p1".into()]
            } else {
                (0..s).map(|i| format!("c{i}")).collect()
            };
            assert_eq!(f.visible, want, "conformance: {}", f.name);
        }
    }
    // `ApptabPair` against T2's table.
    assert_eq!(ApptabPair::ALL.len(), 15, "conformance: the pairs");
    for (p, (fam, label, variant)) in ApptabPair::ALL.iter().zip(PAIRS.iter()) {
        assert_eq!(
            (p.family(), p.label(), p.variant().as_str()),
            (*fam, *label, *variant),
            "conformance: {p:?}"
        );
        for s in 2..=8 {
            assert_eq!(p.name(s), pname(fam, label, s), "conformance: {p:?}");
            assert_eq!(
                apptab_pair_of(&pname(fam, label, s)),
                Some((*p, s)),
                "conformance: parser {p:?} {s}"
            );
        }
        assert!(p.conforming_of().is_conforming(), "conformance: {p:?}");
    }
    // Off-diagonal and unknown names are not diagonal fixtures.
    for n in [
        "apps/a1/correct/spec/n2r3",
        "apps/a4/hash/a4b/k2q2m2",
        "apps/a2/pb-br/spec/k2q2",
        "2pc/leader/conf/n",
        "apps/a3/fifo/spec/k2q2x",
    ] {
        assert_eq!(apptab_pair_of(n), None, "conformance: {n}");
    }
    assert_eq!(APPTAB_MAX_SIZE, 8, "conformance: APPTAB_MAX_SIZE");
}

// =========================================================================
// Criterion 3 — overlap validation
// =========================================================================

/// Counters that must agree between the built and the registry fixture.
const C3_COUNTERS: [&str; 6] = [
    "executions",
    "reports",
    "impl_graphs",
    "sweep_graphs",
    "spec_graphs",
    "spec_visit_calls",
];

fn overlap_check(pair: ApptabPair, s: usize, engines: &[GridEngine]) -> Vec<String> {
    let reg = all_fixtures()
        .into_iter()
        .find(|f| f.name == pair.name(s))
        .unwrap_or_else(|| panic!("conformance: no registry {}", pair.name(s)));
    let built = apptab_build(pair, s);
    let mut bad = Vec::new();
    let what = pair.name(s);
    if built.visible != reg.visible
        || built.group != reg.group
        || built.config.cons_type != reg.config.cons_type
        || built.config.seed != reg.config.seed
        || built.config.thread_threshold != reg.config.thread_threshold
    {
        bad.push(format!("{what}: visible/group/config differ"));
    }
    for e in engines {
        let cfg = x1_config(*e, Selector::Ltr);
        let (a, b) = (run_rec(&built, &cfg), run_rec(&reg, &cfg));
        for c in C3_COUNTERS {
            if a[c] != b[c] {
                bad.push(format!(
                    "{what} {e:?}: {c} built {:?} registry {:?}",
                    a[c], b[c]
                ));
            }
        }
        if a["end_class"] != "ok" || b["end_class"] != "ok" {
            bad.push(format!(
                "{what} {e:?}: {} / {}",
                a["end_class"], b["end_class"]
            ));
        }
    }
    bad
}

/// C3 at `s = 2` (in process, every engine, X1's configuration): the 13
/// pairs the registry holds on the diagonal at `s = 2` — `apptab_build` and
/// the registry fixture agree on `visible`, `group`, `config` and on the
/// counters of one run.
#[test]
fn c03_overlap_validation_at_s2() {
    let mut bad = Vec::new();
    for pair in ApptabPair::ALL {
        if matches!(pair, ApptabPair::A4HashDrop | ApptabPair::LeSilent) {
            continue;
        }
        bad.extend(overlap_check(pair, 2, &ENGINES));
    }
    assert!(bad.is_empty(), "conformance: criterion 3: {bad:#?}");
}

/// C3 at `s = 3` (ignored, heavy): `APPTAB_C3_PAIR` names one pair (its
/// `Debug` name) and `APPTAB_C3_ENGINE` one engine; the enumerator on `a2
/// k3q3` is never run (the campaign censored it at 600 s). One per process
/// under `timeout 1200`.
#[test]
#[ignore]
fn c03_overlap_validation_at_s3() {
    let pair_name = std::env::var("APPTAB_C3_PAIR").expect("conformance: APPTAB_C3_PAIR");
    let engine_name = std::env::var("APPTAB_C3_ENGINE").expect("conformance: APPTAB_C3_ENGINE");
    let pair = ApptabPair::ALL
        .into_iter()
        .find(|p| format!("{p:?}") == pair_name)
        .expect("conformance: a pair");
    let engine = ENGINES
        .into_iter()
        .find(|e| format!("{e:?}") == engine_name)
        .expect("conformance: an engine");
    assert!(
        !(pair.family() == "a2" && engine == GridEngine::Enumerator),
        "conformance: the enumerator on a2 k3q3 is not run"
    );
    let bad = overlap_check(pair, 3, &[engine]);
    note!("c03 s=3 {pair:?} {engine:?}: {bad:?}");
    assert!(
        bad.is_empty(),
        "conformance: criterion 3 at s = 3: {bad:#?}"
    );
}

// =========================================================================
// Criterion 4 — the two new pairs at s = 2
// =========================================================================

/// C4 (derived.md §1–§2): at `s = 2`, every engine, in process — the
/// all-reports rows (X1's configuration on stateful, complete-first, gated):
/// `reports = executions` = **6** (A4 `hash-drop`) and **3** (leader
/// `silent`, (β)); the first-report rows (X2's, four engines): `reports = 1`,
/// `executions = 1` on complete-first and gated; and the first report
/// exported through the child (`EVAL_EXPORT=first_report`): a complete report,
/// statuses `{c0: Done, c1: Blocked}` / `{p0: Blocked, p1: Blocked}`, the words
/// of derived.md. The lead's expectation (`expected.md`: 6, 3; 196 at `n = 3`
/// — mine agrees) is the same.
#[test]
fn c04_the_two_new_pairs_at_s2() {
    let a4 = by_name()["apps/a4/hash-drop/a4a/k2q2m2"].clone();
    let le = by_name()["2pc/leader/silent/n2"].clone();
    let mut bad = Vec::new();
    for (f, n) in [(&a4, 6u64), (&le, 3u64)] {
        for e in ALL_REPORTS {
            let r = run_rec(f, &x1_config(e, Selector::Ltr));
            let got = (
                r["reports"].clone(),
                r["executions"].clone(),
                r["end_class"].clone(),
            );
            note!("c04 {} {e:?} all reports: {got:?}", f.name);
            if got != (n.to_string(), n.to_string(), "ok".to_owned()) {
                bad.push(format!(
                    "{} {e:?} all reports: {got:?}, derived {n}/{n}",
                    f.name
                ));
            }
        }
        for e in ENGINES {
            let r = run_rec(f, &x2_config(e, Selector::Ltr));
            note!(
                "c04 {} {e:?} first report: reports {} executions {}",
                f.name,
                r["reports"],
                r["executions"]
            );
            if r["reports"] != "1" || r["end_class"] != "ok" {
                bad.push(format!(
                    "{} {e:?} first report: reports {}",
                    f.name, r["reports"]
                ));
            }
            if matches!(e, GridEngine::CompleteFirst | GridEngine::Gated) && r["executions"] != "1"
            {
                bad.push(format!(
                    "{} {e:?} first report: executions {}",
                    f.name, r["executions"]
                ));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 4: {bad:#?}");
}

/// C4's export half (child processes): the first-report profiling twin of
/// each new pair at `s = 2` on every engine, `EVAL_EXPORT=first_report`.
#[test]
#[ignore]
fn c04_the_exported_first_reports() {
    let base = temp("c04");
    let want = [
        (
            "apps/a4/hash-drop/a4a/k2q2m2",
            serde_json::json!({ "c0": "Done", "c1": "Blocked" }),
            serde_json::json!({
                "c0": ["⟨snd, A4Req(0, 0)⟩", "⟨rcv, A4Reply(0, 0)⟩", "⟨snd, A4Req(0, 1)⟩", "⟨rcv, A4Reply(0, 1)⟩"],
            }),
        ),
        (
            "2pc/leader/silent/n2",
            serde_json::json!({ "p0": "Blocked", "p1": "Blocked" }),
            serde_json::Value::Null,
        ),
    ];
    let mut bad = Vec::new();
    for (fx, statuses, _) in &want {
        for e in ENGINES {
            let dir = base.join(format!("{}-{e:?}", fx.replace('/', "_")));
            let spec = plain_row(fx, x2_config(e, Selector::Ltr), RunKind::Profiling, 0);
            match child(&spec, "first_report", &dir) {
                Err(err) => bad.push(format!("{fx} {e:?}: {err}")),
                Ok(rec) => {
                    let j = json_at(&dir, "first_report.json");
                    note!("c04 export {fx} {e:?}: reports {} {j:?}", rec["reports"]);
                    match j {
                        None => bad.push(format!("{fx} {e:?}: no first_report.json")),
                        Some(j) => {
                            if j["growth"] != "complete" || &j["statuses"] != statuses {
                                bad.push(format!(
                                    "{fx} {e:?}: growth {} statuses {}",
                                    j["growth"], j["statuses"]
                                ));
                            }
                            if fx.starts_with("2pc") {
                                let p0 = j["words"]["p0"].as_array().map(Vec::len);
                                let p1 = j["words"]["p1"].as_array().map(Vec::len);
                                if (p0, p1) != (Some(2), Some(1)) {
                                    bad.push(format!("{fx} {e:?}: words {}", j["words"]));
                                }
                            } else {
                                let c0 = j["words"]["c0"].as_array().map(Vec::len);
                                let c1 = j["words"]["c1"].as_array().map(Vec::len);
                                if (c0, c1) != (Some(4), Some(3)) {
                                    bad.push(format!("{fx} {e:?}: words {}", j["words"]));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 4 (export): {bad:#?}"
    );
}

// =========================================================================
// Criterion 5 — the witnesses (value-based)
// =========================================================================

/// C5 (child processes, `s = 2`, stateful `Ltr` profiling, graphs kept,
/// `EVAL_EXPORT=flat_witness`): each `APPTABW` fixture's file holds at least
/// one witness (a visible receive of a non-⊥ value with an empty
/// `visible_sends_of_value`), the derived one first; every witness's scan list
/// is empty; negatives: `relay/paper` — the receive of `9` has an invisible
/// source **and** a listed visible send, so no witness; `ex:naive/k2/enc1` — no
/// witness.
#[test]
#[ignore]
fn c05_the_flat_witnesses() {
    let base = temp("c05");
    let st = x1_config(GridEngine::Stateful, Selector::Ltr);
    let cases: [(&str, &str, &str); 5] = [
        ("apps/a1/correct/spec/n2r2", "p0", "Prepare"),
        ("apps/a2/pb/spec/k2q2", "c0", "Ack"),
        ("apps/a3/fifo/spec/k2q2", "c0", "Grant(0, 0)"),
        ("apps/a4/hash/a4a/k2q2m2", "c0", "A4Reply(0, 0)"),
        ("2pc/leader/conf/n2", "p0", "BeFollower"),
    ];
    let mut bad = Vec::new();
    let run = |fx: &str| -> Option<serde_json::Value> {
        let dir = base.join(fx.replace(['/', ':'], "_"));
        let spec = plain_row(fx, st.clone(), RunKind::Profiling, 1);
        match child(&spec, "flat_witness", &dir) {
            Err(e) => {
                note!("c05 {fx}: {e}");
                None
            }
            Ok(_) => json_at(&dir, "flat_witness.json"),
        }
    };
    for (fx, thread, value) in cases {
        let Some(j) = run(fx) else {
            bad.push(format!("{fx}: no file"));
            continue;
        };
        note!(
            "c05 {fx}: first {} ; receives {}",
            j["first_witness"],
            j["receives"]
        );
        let recs = j["receives"].as_array().cloned().unwrap_or_default();
        let witnesses: Vec<&serde_json::Value> =
            recs.iter().filter(|r| r["witness"] == true).collect();
        if witnesses.is_empty() {
            bad.push(format!("{fx}: no witness"));
        }
        for w in &witnesses {
            if w["visible_sends_of_value"] != serde_json::json!([]) {
                bad.push(format!("{fx}: a witness with a non-empty scan {w}"));
            }
        }
        for r in &recs {
            let empty = r["visible_sends_of_value"] == serde_json::json!([]);
            if (r["witness"] == true) != empty {
                bad.push(format!("{fx}: witness flag against the scan {r}"));
            }
        }
        let first = &j["first_witness"];
        let fv = first["value"].as_str().unwrap_or_default();
        if first["thread"] != thread || !fv.contains(value) {
            bad.push(format!(
                "{fx}: first witness {first}, derived {thread} {value}"
            ));
        }
        if fx.starts_with("2pc") {
            // The votes and decisions are not witnesses (visible senders).
            for r in &recs {
                let v = r["value"].as_str().unwrap_or_default();
                if (v.contains("Vote") || v.contains("Decision")) && r["witness"] == true {
                    bad.push(format!("{fx}: a vote/decision witness {r}"));
                }
            }
        }
    }
    // Negatives.
    match run("relay/paper") {
        None => bad.push("relay/paper: no file".to_owned()),
        Some(j) => {
            note!("c05 relay/paper: {}", j["receives"]);
            let recs = j["receives"].as_array().cloned().unwrap_or_default();
            if recs.is_empty() || !j["first_witness"].is_null() {
                bad.push(format!("relay/paper: {j}"));
            }
            for r in &recs {
                if r["witness"] == true
                    || r["source_visible"] != false
                    || r["visible_sends_of_value"] == serde_json::json!([])
                {
                    bad.push(format!("relay/paper: {r}"));
                }
            }
        }
    }
    match run("ex:naive/k2/enc1") {
        None => bad.push("ex:naive/k2/enc1: no file".to_owned()),
        Some(j) => {
            let recs = j["receives"].as_array().cloned().unwrap_or_default();
            if !j["first_witness"].is_null() || recs.iter().any(|r| r["witness"] == true) {
                bad.push(format!("ex:naive/k2/enc1: {j}"));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: criterion 5: {bad:#?}");
}

// =========================================================================
// Criterion 6 — the specs as data
// =========================================================================

fn parse_err(text: &str) -> String {
    match Schedule::parse(text) {
        Ok(_) => "accepted".to_owned(),
        Err(e) => e.text(),
    }
}

/// C6 (in process, `Schedule::parse` on the tester's own expansion): the
/// `max_size = 3` file is accepted with 180 rows and 95 profiling entries; each
/// malformed shape is refused **by name** (unknown key, `max_size` 9, a bad
/// key, a wrong label, an unknown fixture, a reused key not among the rows, a
/// row out of the balanced order, a wrong series string, an enumerator
/// all-reports row, a first-report row on a conforming pair, a non-empty
/// `extension_reuse` (E-AT-5), a `profiling` list with an entry missing, extra,
/// out of order, with another key, another dependency or another condition, an
/// `ended` entry without its reused batch and the converse).
#[test]
fn c06_the_schedule_parser() {
    let ok = sched_text(3, &[], &[], "/nonexistent");
    let s = Schedule::parse(&ok).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    assert_eq!(
        (s.rows.len(), s.profiling.len(), s.max_size),
        (180, 95, 3),
        "conformance: rows, profiling"
    );
    assert_eq!(s.runnable().len(), 180, "conformance: runnable");
    let base: serde_json::Value = serde_json::from_str(&ok).unwrap();
    let mut cases: Vec<(String, serde_json::Value, String)> = Vec::new();
    let mut push = |what: &str, v: serde_json::Value, needle: &str| {
        cases.push((what.to_owned(), v, needle.to_owned()));
    };
    let mut v = base.clone();
    v["frozen"] = serde_json::json!(1);
    push("unknown key", v, "unknown key `frozen`");
    let mut v = base.clone();
    v["max_size"] = serde_json::json!(9);
    push("max_size 9", v, "max_size 9 outside 2..=8");
    let mut v = base.clone();
    v["rows"][3]["key"] = serde_json::json!("not|a|key");
    push("bad key", v, "not|a|key");
    let row0 = base["rows"][0]["key"].as_str().unwrap().to_owned();
    let mut v = base.clone();
    v["rows"][0]["key"] = serde_json::json!(row0.replace("memo=true", "memo=false"));
    push("wrong label", v, "the label is not");
    let mut v = base.clone();
    v["rows"][0]["key"] = serde_json::json!(row0.replace("n2r2", "n2r3"));
    push("off-diagonal fixture", v, "is not a diagonal fixture");
    let mut v = base.clone();
    v["rows"][0]["series"] = serde_json::json!("a1|conforming|diag|x|default|timed");
    push(
        "wrong series",
        v,
        "series `a1|conforming|diag|x|default|timed`",
    );
    // Out of order: the first size-3 row before the last size-2 row.
    let mut v = base.clone();
    let rows = v["rows"].as_array_mut().unwrap();
    let r = rows.remove(90);
    rows.insert(0, r);
    push("out of order", v, "out of the balanced order");
    // An enumerator all-reports row on a mutant.
    let mut v = base.clone();
    let i = (0..180)
        .find(|i| base["rows"][*i]["mode"] == "exhaustive" && base["rows"][*i]["pair"] == "eager")
        .unwrap();
    let k = base["rows"][i]["key"].as_str().unwrap();
    // `MIN-ENGINES` E1 (2026-10-26, tester re-pin at gate 3): the stateful key
    // prints `Plain`, the enumerator's names its selector (`Ltr`).
    // `MIN-ENGINES` E7b (the tester's re-pin at gate 3): the stateful key's
    // `Set` suffix goes too — the enumerator's key does not print the index.
    let ek = k
        .replace("Stateful/Plain/", "Enumerator/Ltr/")
        .replace("memo=false/Default", "memo=true/Unlimited")
        .replace("/w=inf/quiet=false/index=set", "");
    v["rows"][i]["key"] = serde_json::json!(ek);
    v["rows"][i]["engine"] = serde_json::json!("Enumerator");
    v["rows"][i]["series"] = serde_json::json!(series_of(
        "a1",
        "mutant:eager",
        &x1_config(GridEngine::Enumerator, Selector::Ltr)
    ));
    push(
        "enumerator all-reports",
        v,
        "an all-reports row on the enumerator",
    );
    // A first-report row on a conforming pair.
    let mut v = base.clone();
    let cf = x2_config(GridEngine::Stateful, Selector::Ltr);
    v["rows"][1]["key"] = serde_json::json!(timed_key("apps/a1/correct/spec/n2r2", &cf, "release"));
    v["rows"][1]["mode"] = serde_json::json!("first");
    v["rows"][1]["series"] = serde_json::json!(series_of("a1", "conforming", &cf));
    push(
        "first report on conforming",
        v,
        "a first-report row on a conforming pair",
    );
    // A reused key not among the rows.
    let mut v = base.clone();
    v["reused"] = serde_json::json!([{ "key": "apps/a1/correct/spec/n9r9|x|0|default|timed|release", "batch": ["a"], "reps": 1 }]);
    push("reused not a row", v, "is not a row of the schedule");
    // E-AT-5.
    let mut v = base.clone();
    v["extension_reuse"] = serde_json::json!([{ "source": "a", "target": "b" }]);
    push("extension_reuse", v, "extension_reuse lists 1 entries");
    // The profiling list.
    let mut v = base.clone();
    v["profiling"].as_array_mut().unwrap().remove(7);
    push(
        "profiling missing",
        v,
        "profiling[7] is not the derivation's",
    );
    let mut v = base.clone();
    let extra = v["profiling"][5].clone();
    v["profiling"].as_array_mut().unwrap().push(extra);
    push(
        "profiling extra",
        v,
        "profiling[95] is not the derivation's",
    );
    let mut v = base.clone();
    v["profiling"].as_array_mut().unwrap().swap(6, 7);
    push("profiling order", v, "profiling[6] is not the derivation's");
    let mut v = base.clone();
    v["profiling"][7]["key"] = serde_json::json!("x|y");
    push("profiling key", v, "profiling[7] is not the derivation's");
    let mut v = base.clone();
    v["profiling"][7]["depends_on"] = serde_json::json!([]);
    push(
        "profiling dependency",
        v,
        "profiling[7] is not the derivation's",
    );
    let mut v = base.clone();
    v["profiling"][0]["condition"] = serde_json::json!("whenever");
    push(
        "profiling condition",
        v,
        "profiling[0] is not the derivation's",
    );
    // `ended` without its reused batch.
    let mut v = base.clone();
    v["ended"] =
        serde_json::json!([{ "series": base["rows"][0]["series"], "size": 2, "reason": "x" }]);
    push("ended alone", v, "names no reused batch censored there");
    // A reused batch that ends its series without an `ended` entry.
    let mut v = base.clone();
    v["reused"] =
        serde_json::json!([{ "key": row0, "batch": ["a"], "reps": 1, "ends_series": true }]);
    push(
        "ends_series alone",
        v,
        "ends its series but `ended` has no entry",
    );
    // Gate 4 round 01 m1: an engine outside the four.
    let mut v = base.clone();
    let vc = x1_config(GridEngine::Verify, Selector::Ltr);
    v["rows"][1]["key"] = serde_json::json!(timed_key("apps/a1/correct/spec/n2r2", &vc, "release"));
    v["rows"][1]["engine"] = serde_json::json!("Verify");
    v["rows"][1]["series"] = serde_json::json!(series_of("a1", "conforming", &vc));
    push(
        "engine Verify",
        v,
        "engine Verify is not one of the table's four",
    );
    // m1: a missing cell (the last row dropped, its twin re-derived away).
    let mut v = base.clone();
    let rows_less: Vec<serde_json::Value> = base["rows"].as_array().unwrap()[..179].to_vec();
    v["rows"] = serde_json::json!(rows_less);
    v["profiling"] = serde_json::json!(sched_profiling(
        &rows_less,
        &BTreeSet::new(),
        &[],
        "release"
    ));
    push(
        "a missing cell",
        v,
        "rows is incomplete: `2pc/leader/silent/n3|Gated/",
    );
    // m1: a row above its series' end listed beside the `ended` entry.
    {
        let rows = sched_rows(3, "release");
        let i = rows
            .iter()
            .position(|r| r["benchmark"] == "a2" && r["engine"] == "Enumerator")
            .unwrap();
        let k = rows[i]["key"].as_str().unwrap().to_owned();
        let se = rows[i]["series"].as_str().unwrap().to_owned();
        let batch: Vec<String> = (0..3)
            .map(|r| k.replacen("|0|default|", &format!("|{r}|default|"), 1))
            .collect();
        let entry = serde_json::json!({ "key": k, "batch": batch, "reps": 3, "ends_series": true });
        let ended = vec![(se.clone(), 2usize)];
        let mut v: serde_json::Value =
            serde_json::from_str(&sched_text(3, &[entry], &ended, "/nonexistent")).unwrap();
        // Put the dropped size-3 row back in its balanced place.
        let dropped = rows
            .iter()
            .find(|r| r["series"] == se.as_str() && r["size"] == 3)
            .unwrap()
            .clone();
        let pos = rows.iter().position(|r| *r == dropped).unwrap();
        let reused_keys: BTreeSet<String> = [k].into();
        let arr = v["rows"].as_array_mut().unwrap();
        arr.insert(pos, dropped);
        let listed = arr.clone();
        v["profiling"] =
            serde_json::json!(sched_profiling(&listed, &reused_keys, &ended, "release"));
        push(
            "a row above its series' end",
            v,
            "lies above its series' end at 2",
        );
    }
    // n1: the budget.
    let mut v = base.clone();
    v["limits"]["budget_h"] = serde_json::json!(59);
    push(
        "budget_h 59",
        v,
        "limits budget_h 59 is not D-T6's hard cap of 60 h",
    );
    // n2: one row at another build profile.
    let mut v = base.clone();
    let k5 = base["rows"][5]["key"]
        .as_str()
        .unwrap()
        .replace("|release", "|test");
    v["rows"][5]["key"] = serde_json::json!(k5);
    push(
        "profile mismatch",
        v,
        "build profile `test` differs from rows[0]'s `release`",
    );
    // n3: `note` is no longer a row key.
    let mut v = base.clone();
    v["rows"][0]["note"] = serde_json::json!("x");
    push("a note", v, "rows[0]: unknown key `note`");
    // n4: duplicate `reused` keys and duplicate `ended` entries.
    {
        let rows = sched_rows(3, "release");
        let k = rows[0]["key"].as_str().unwrap().to_owned();
        let batch: Vec<String> = (0..3)
            .map(|r| k.replacen("|0|default|", &format!("|{r}|default|"), 1))
            .collect();
        let e = serde_json::json!({ "key": k, "batch": batch, "reps": 3 });
        let mut v: serde_json::Value = serde_json::from_str(&sched_text(
            3,
            std::slice::from_ref(&e),
            &[],
            "/nonexistent",
        ))
        .unwrap();
        v["reused"] = serde_json::json!([e.clone(), e]);
        push("reused twice", v, "listed twice");
        let i = rows
            .iter()
            .position(|r| r["benchmark"] == "a2" && r["engine"] == "Enumerator")
            .unwrap();
        let k = rows[i]["key"].as_str().unwrap().to_owned();
        let se = rows[i]["series"].as_str().unwrap().to_owned();
        let batch: Vec<String> = (0..3)
            .map(|r| k.replacen("|0|default|", &format!("|{r}|default|"), 1))
            .collect();
        let entry = serde_json::json!({ "key": k, "batch": batch, "reps": 3, "ends_series": true });
        let mut v: serde_json::Value =
            serde_json::from_str(&sched_text(3, &[entry], &[(se, 2)], "/nonexistent")).unwrap();
        let e0 = v["ended"][0].clone();
        v["ended"] = serde_json::json!([e0.clone(), e0]);
        push("ended twice", v, "listed twice");
    }
    let mut bad = Vec::new();
    for (what, v, needle) in &cases {
        let e = parse_err(&v.to_string());
        if !e.contains(needle.as_str()) {
            bad.push(format!("{what}: {e}"));
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: criterion 6 refusals: {bad:#?}"
    );
    note!("c06: {} malformed shapes refused by name", cases.len());
}

/// `MIN-ENGINES` E1-2 (the tester, gate 3; derived §E1 item 14 (b)): an
/// APPTAB schedule row whose stateful or complete-first key spells a selector
/// in place of `Plain` (each of the three legacy spellings) is rejected at the
/// row's validation by name, the key quoted; the canonical file is accepted.
#[test]
fn e1_a_legacy_key_in_the_apptab_schedule_is_rejected() {
    let ok = sched_text(2, &[], &[], "/nonexistent");
    Schedule::parse(&ok).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let base: serde_json::Value = serde_json::from_str(&ok).unwrap();
    let mut bad = Vec::new();
    for engine in ["Stateful", "CompleteFirst"] {
        let plain = format!("|{engine}/Plain/");
        let i = (0..base["rows"].as_array().unwrap().len())
            .find(|i| base["rows"][*i]["key"].as_str().unwrap().contains(&plain))
            .unwrap_or_else(|| panic!("conformance: no {engine} row"));
        let k = base["rows"][i]["key"].as_str().unwrap().to_owned();
        for s in ["Ltr", "Reverse", "FewestEvents"] {
            let legacy = k.replace(&plain, &format!("|{engine}/{s}/"));
            let mut v = base.clone();
            v["rows"][i]["key"] = serde_json::json!(legacy);
            let e = parse_err(&v.to_string());
            if !(e.contains("a legacy key") && e.contains(&legacy) && e.contains("`Plain`")) {
                bad.push(format!("{engine} {s}: {e}"));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: E1-2: {bad:#?}");
}

/// The child of the schedule and driver tests (`APPTAB_CASE` selects):
/// - `specs`: the five specs under `EVAL_SCHEDULE`, checked against the
///   derivation, and their keys' overlaps with the builtin specs;
/// - `reuse`: `schedule().validate_reuse()` and `apptab_spec()`'s rows;
/// - `driver`: `Driver::run` on `APPTAB_CASE_SPEC` (a builtin/APPTAB spec, or
///   `custom:<name>` for the series rows) into `APPTAB_CASE_OUT`,
///   `APPTAB_CASE_ONLY` the glob.
///
/// A no-op without `APPTAB_CASE`.
#[test]
#[ignore]
fn apptab_child() {
    let Ok(case) = std::env::var("APPTAB_CASE") else {
        return;
    };
    let line = match case.as_str() {
        "specs" => case_specs(),
        "reuse" => case_reuse(),
        "driver" => case_driver(),
        "from_env" => case_from_env(),
        other => format!("unknown case {other}"),
    };
    use std::io::Write as _;
    let mut o = std::io::stdout().lock();
    writeln!(o, "CASE\t{line}").expect("conformance: writing the case line");
}

fn case_specs() -> String {
    let mut errors: Vec<String> = Vec::new();
    let sch = schedule();
    let a = apptab_spec();
    let p = apptabp_spec();
    let s = apptabs_spec();
    let w = apptabw_spec();
    let d = edprobe_spec();
    if let Some(sch) = sch {
        let runnable: Vec<String> = sch.runnable().iter().map(|r| r.key.clone()).collect();
        if runnable.len() != a.rows.len() {
            errors.push(format!(
                "{} runnable, {} rows",
                runnable.len(),
                a.rows.len()
            ));
        }
        for (r, k) in a.rows.iter().zip(&runnable) {
            let (pair, sz) = apptab_pair_of(&r.fixture).unwrap();
            let mode = if r.config.stop_at_first_report {
                "first"
            } else {
                "exhaustive"
            };
            let want_cfg = cfg_of(r.config.engine, mode);
            let want_series = Series {
                scope: series_of(pair.family(), &pair.variant(), &want_cfg),
                size: sz as i64,
            };
            let release = r.key("release");
            if &release != k
                || r.tier != Tier::default_tier()
                || r.run_kind != RunKind::Timed
                || r.rep != 0
                || r.config.selector != Selector::Ltr
                || r.config.label() != want_cfg.label()
                || r.series.as_ref() != Some(&want_series)
                || r.family != pair.family()
                || r.variant != pair.variant()
                || !r.twin_key.is_empty()
            {
                errors.push(format!("APPTAB row {release} against {k}"));
            }
        }
        // APPTABP: the profiling twins of the runnable first-report rows.
        let twins: Vec<String> = a
            .rows
            .iter()
            .filter(|r| r.config.stop_at_first_report)
            .map(|r| r.key(prof()).replacen("|timed|", "|profiling|", 1))
            .collect();
        let pk: Vec<String> = p.rows.iter().map(|r| r.key(prof())).collect();
        if pk != twins || p.rows.iter().any(|r| r.series.is_some()) {
            errors.push("APPTABP is not the twins".to_owned());
        }
        // The schedule's profiling list = APPTABW, then APPTABS/APPTABP.
        let listed: Vec<(String, String)> = sch
            .profiling
            .iter()
            .map(|e| {
                (
                    e.spec.clone(),
                    e.key.replace("|release", &format!("|{}", prof())),
                )
            })
            .collect();
        let mut from_specs: Vec<(String, String)> = w
            .rows
            .iter()
            .map(|r| ("APPTABW".to_owned(), r.key(prof())))
            .collect();
        let mut sk = s.rows.iter();
        let mut next_s = sk.next();
        let mut pk_iter = p.rows.iter();
        let mut next_p = pk_iter.next();
        for e in sch.profiling.iter().skip(5) {
            match e.spec.as_str() {
                "APPTABS" => {
                    if let Some(r) = next_s {
                        from_specs.push(("APPTABS".to_owned(), r.key(prof())));
                    }
                    next_s = sk.next();
                }
                "APPTABP" => {
                    if let Some(r) = next_p {
                        from_specs.push(("APPTABP".to_owned(), r.key(prof())));
                    }
                    next_p = pk_iter.next();
                }
                _ => errors.push(format!("profiling entry {e:?}")),
            }
        }
        if listed != from_specs || next_s.is_some() || next_p.is_some() {
            errors.push("the profiling list is not the three specs".to_owned());
        }
    }
    // APPTABS: stateful profiling rep 0 on the conforming pairs.
    for r in &s.rows {
        let (pair, _) = apptab_pair_of(&r.fixture).unwrap();
        if !pair.is_conforming()
            || r.run_kind != RunKind::Profiling
            || r.rep != 0
            || r.config.label() != x1_config(GridEngine::Stateful, Selector::Ltr).label()
            || r.tier != Tier::default_tier()
        {
            errors.push(format!("APPTABS row {}", r.key(prof())));
        }
    }
    // Overlaps with the builtin specs (keys).
    let mut over: BTreeMap<String, usize> = BTreeMap::new();
    let builtin = builtin_specs();
    let bkeys: BTreeMap<String, BTreeSet<String>> = builtin
        .iter()
        .map(|x| {
            (
                x.name.clone(),
                x.rows.iter().map(|r| r.key(prof())).collect(),
            )
        })
        .collect();
    let mut distinct_builtin = BTreeSet::new();
    for ks in bkeys.values() {
        distinct_builtin.extend(ks.iter().cloned());
    }
    let mut distinct_all = distinct_builtin.clone();
    for sp in [&a, &p, &s, &w, &d] {
        for r in &sp.rows {
            let k = r.key(prof());
            distinct_all.insert(k.clone());
            for (n, ks) in &bkeys {
                if ks.contains(&k) {
                    *over.entry(format!("{}∩{n}", sp.name)).or_default() += 1;
                }
            }
        }
    }
    let a_over: BTreeSet<String> = a
        .rows
        .iter()
        .map(|r| r.key(prof()))
        .filter(|k| distinct_builtin.contains(k))
        .collect();
    let a_over_fixtures: BTreeMap<String, usize> =
        a_over.iter().fold(BTreeMap::new(), |mut m, k| {
            *m.entry(k.split('|').next().unwrap().to_owned())
                .or_default() += 1;
            m
        });
    serde_json::json!({
        "errors": errors,
        "schedule": sch.is_some(),
        "rows": { "APPTAB": a.rows.len(), "APPTABP": p.rows.len(), "APPTABS": s.rows.len(),
                  "APPTABW": w.rows.len(), "EDPROBE": d.rows.len() },
        "overlaps": over,
        "apptab_overlap": a_over.len(),
        "apptab_overlap_fixtures": a_over_fixtures,
        "distinct_builtin": distinct_builtin.len(),
        "distinct_all": distinct_all.len(),
        "builtin_names": builtin.iter().map(|x| x.name.clone()).collect::<Vec<_>>(),
        "experiments_of_reused": sch.map(|sc| sc.reused.iter().map(|r| {
            let k = r.key.replace("|release", &format!("|{}", prof()));
            experiments_of(&k, &apptab_specs(), prof()).len()
        }).sum::<usize>()).unwrap_or(0),
    })
    .to_string()
}

fn case_reuse() -> String {
    let sch = schedule().expect("conformance: a schedule");
    let v = sch.validate_reuse();
    let keys: Vec<String> = apptab_spec()
        .rows
        .iter()
        .map(|r| r.key("release"))
        .collect();
    serde_json::json!({
        "validate": match v { Ok(()) => "ok".to_owned(), Err(e) => e.text() },
        "rows": keys,
    })
    .to_string()
}

/// The custom series spec of criterion 7: three series of size 1 and 2 on the
/// harness's test fixtures under a 2 s tier — `slow` (sleeps 3 s: capped at
/// size 1), `fast` (both sizes ok), `err` (`eval/panic` at size 1, then a fast
/// row at size 2) — plus a memory row (`eval/alloc256` under 64 MiB:
/// capped_memory, criterion 1's driver kill).
fn custom_rows() -> Vec<RowSpec> {
    let tier = Tier {
        name: "t2s".to_owned(),
        wall: Duration::from_secs(2),
        mem_kb: 64 * 1024,
    };
    let mk = |fx: &str, cfg: GridConfig, scope: &str, size: i64| RowSpec {
        fixture: fx.to_owned(),
        config: cfg.clone(),
        rep: 0,
        tier: tier.clone(),
        run_kind: RunKind::Timed,
        family: "custom".to_owned(),
        knobs: String::new(),
        k: [Some(size), None, None, None],
        variant: "conforming".to_owned(),
        twin_key: String::new(),
        series: Some(Series::of(scope, "diag", &cfg, &tier, RunKind::Timed, size)),
    };
    let st = x1_config(GridEngine::Stateful, Selector::Ltr);
    let ga = x1_config(GridEngine::Gated, Selector::Ltr);
    let cf = x1_config(GridEngine::CompleteFirst, Selector::Ltr);
    // `eval/series/slow/*` sleeps `EVAL_REP × 3 s` (the harness's
    // `trivial(Some(3))`): rep 1 sleeps 3 s, over the 2 s tier.
    let rep1 = |mut r: RowSpec| {
        r.rep = 1;
        r
    };
    vec![
        rep1(mk("eval/series/slow/k1", st.clone(), "slow", 1)),
        rep1(mk("eval/series/slow/k2", st.clone(), "slow", 2)),
        mk("eval/series/fast/k1", st.clone(), "fast", 1),
        mk("eval/series/fast/k2", st, "fast", 2),
        mk("eval/panic", ga.clone(), "err", 1),
        mk("eval/series/fast/k2", ga, "err", 2),
        mk("eval/alloc256", cf.clone(), "mem", 1),
        // Gate 4 round 01 n6: a `crashed(…)` row ends an APPTAB series too.
        mk("eval/abort", cf.clone(), "crash", 1),
        mk("eval/series/fast/k2", cf, "crash", 2),
    ]
}

fn case_driver() -> String {
    let name = std::env::var("APPTAB_CASE_SPEC").expect("conformance: APPTAB_CASE_SPEC");
    let out =
        PathBuf::from(std::env::var("APPTAB_CASE_OUT").expect("conformance: APPTAB_CASE_OUT"));
    let spec = if let Some(n) = name.strip_prefix("custom:") {
        Spec {
            name: n.to_owned(),
            rows: custom_rows(),
        }
    } else {
        apptab_specs()
            .into_iter()
            .find(|s| s.name == name)
            .unwrap_or_else(|| panic!("conformance: no spec {name}"))
    };
    let d = Driver {
        spec,
        specs: builtin_specs(),
        out_dir: out,
        sample_period: Duration::from_millis(100),
        probes: clean_probes(),
        allow_mixed: true,
        only: std::env::var("APPTAB_CASE_ONLY").ok(),
    };
    match d.run() {
        Ok(s) => format!(
            "ran {} skipped_after_censor {}",
            s.ran, s.skipped_after_censor
        ),
        Err(e) => e.text(),
    }
}

/// C6 through a child (`EVAL_SCHEDULE` = the tester's `max_size = 3` file, no
/// reuse): `APPTAB` 180 rows in the file's order, each at `default`, `Timed`,
/// rep 0, `Ltr`, X1's / X2's label, the T6 series scope and size, the meta;
/// `APPTABP` 80 twins (no series); `APPTABS` 10; `APPTABW` 5 (rep 1); `EDPROBE`
/// 6; the file's `profiling` list exactly the three specs' keys in the
/// runner's order. Overlaps with the builtin specs (derived from the reuse
/// table at `s ≤ 3`): `APPTAB` ∩ builtin = **56** keys (A1 `correct` 4,
/// `eager`/`silent` 4 + 2 each at `n2r2`; A2 `pb` `k3q3` 4; A3 `fifo` 4 and the
/// two mutants' first-report 4 each at `k2q2`; A4 `hash/a4a` 4 and `rr/a4a`
/// first-report 4 at `k2q2m2`; leader `conf` 4 + 4 and `split` 4 + 4 at `n2`,
/// `n3`), `APPTABP` ∩ `X2P` = **28**, the rest 0; `builtin_specs()`'s names
/// unchanged (no APPTAB spec). Then with one reused completed batch and one
/// ended series the rows are dropped and `experiments_of` the reused key is
/// empty; without a file the specs are empty and the driver refuses
/// `APPTAB`/`APPTABP`/`APPTABS`. Run alone.
#[test]
#[ignore]
fn c06_the_specs_through_a_child() {
    let base = temp("c06");
    let f = base.join("schedule.json");
    fs::write(&f, sched_text(3, &[], &[], "/nonexistent")).unwrap();
    let got = child_case(
        &[
            ("APPTAB_CASE", "specs".into()),
            ("EVAL_SCHEDULE", f.display().to_string()),
        ],
        &[],
    );
    note!("c06 specs: {got}");
    let v: serde_json::Value =
        serde_json::from_str(&got).unwrap_or_else(|e| panic!("conformance: {e}: {got}"));
    assert_eq!(
        v["errors"],
        serde_json::json!([]),
        "conformance: {}",
        v["errors"]
    );
    assert_eq!(
        v["rows"],
        serde_json::json!({ "APPTAB": 180, "APPTABP": 80, "APPTABS": 10, "APPTABW": 5, "EDPROBE": 6 }),
        "conformance: the rows"
    );
    assert_eq!(v["apptab_overlap"], 56, "conformance: APPTAB ∩ builtin");
    assert_eq!(
        v["apptab_overlap_fixtures"],
        serde_json::json!({
            "2pc/leader/conf/n2": 4, "2pc/leader/conf/n3": 4,
            "2pc/leader/split/n2": 4, "2pc/leader/split/n3": 4,
            "apps/a1/correct/spec/n2r2": 4, "apps/a1/eager/spec/n2r2": 6,
            "apps/a1/silent/spec/n2r2": 6, "apps/a2/pb/spec/k3q3": 4,
            "apps/a3/double-grant/spec/k2q2": 4, "apps/a3/fifo/spec/k2q2": 4,
            "apps/a3/never-grant/spec/k2q2": 4, "apps/a4/hash/a4a/k2q2m2": 4,
            "apps/a4/rr/a4a/k2q2m2": 4,
        }),
        "conformance: the overlapping cells"
    );
    let over = v["overlaps"].as_object().cloned().unwrap_or_default();
    let p_x2p = over
        .get("APPTABP∩X2P")
        .and_then(|x| x.as_u64())
        .unwrap_or(0);
    assert_eq!(p_x2p, 28, "conformance: APPTABP ∩ X2P: {over:?}");
    for (k, n) in &over {
        let allowed = k.starts_with("APPTAB∩") || k == "APPTABP∩X2P";
        assert!(allowed, "conformance: unexpected overlap {k} {n}");
    }
    let names: Vec<String> = serde_json::from_value(v["builtin_names"].clone()).unwrap();
    assert!(
        names
            .iter()
            .all(|n| !n.starts_with("APPTAB") && n != "EDPROBE"),
        "conformance: builtin_specs holds an APPTAB spec: {names:?}"
    );
    let distinct_builtin = v["distinct_builtin"].as_u64().unwrap();
    let distinct_all = v["distinct_all"].as_u64().unwrap();
    note!("c06 distinct: builtin {distinct_builtin}, with the five specs {distinct_all}");
    assert_eq!(
        distinct_all - distinct_builtin,
        180 + 80 + 10 + 5 + 6 - 56 - 28,
        "conformance: the five specs' new keys"
    );
    // Reuse and ended (a completed batch for A1 correct n2r2 Enumerator; the
    // A2 pb enumerator series ended at k2q2 by a censored batch).
    let rows = sched_rows(3, "release");
    let k_a1 = rows[0]["key"].as_str().unwrap().to_owned();
    let i_a2 = rows
        .iter()
        .position(|r| r["benchmark"] == "a2" && r["engine"] == "Enumerator")
        .unwrap();
    let k_a2 = rows[i_a2]["key"].as_str().unwrap().to_owned();
    let s_a2 = rows[i_a2]["series"].as_str().unwrap().to_owned();
    let batch = |k: &str, n: usize| -> Vec<String> {
        (0..n)
            .map(|r| k.replacen("|0|default|", &format!("|{r}|default|"), 1))
            .collect()
    };
    let reused = vec![
        serde_json::json!({ "key": k_a1, "batch": batch(&k_a1, 3), "reps": 3 }),
        serde_json::json!({ "key": k_a2, "batch": batch(&k_a2, 3), "reps": 3, "ends_series": true }),
    ];
    let f2 = base.join("schedule2.json");
    fs::write(
        &f2,
        sched_text(3, &reused, &[(s_a2.clone(), 2)], "/nonexistent"),
    )
    .unwrap();
    let got = child_case(
        &[
            ("APPTAB_CASE", "specs".into()),
            ("EVAL_SCHEDULE", f2.display().to_string()),
        ],
        &[],
    );
    let v: serde_json::Value =
        serde_json::from_str(&got).unwrap_or_else(|e| panic!("conformance: {e}: {got}"));
    note!("c06 reused: {}", v["rows"]);
    assert_eq!(
        v["errors"],
        serde_json::json!([]),
        "conformance: {}",
        v["errors"]
    );
    // The two reused rows and the ended series' larger size (`k3q3`'s
    // enumerator row): 180 − 2 − 1.
    assert_eq!(v["rows"]["APPTAB"], 177, "conformance: three rows dropped");
    assert_eq!(v["experiments_of_reused"], 0, "conformance: experiments_of");
    // No file.
    let got = child_case(&[("APPTAB_CASE", "specs".into())], &[]);
    let v: serde_json::Value =
        serde_json::from_str(&got).unwrap_or_else(|e| panic!("conformance: {e}: {got}"));
    assert_eq!(
        (
            v["rows"]["APPTAB"].clone(),
            v["rows"]["APPTABP"].clone(),
            v["rows"]["APPTABS"].clone()
        ),
        (
            serde_json::json!(0),
            serde_json::json!(0),
            serde_json::json!(0)
        ),
        "conformance: no file, no rows"
    );
    for sp in ["APPTAB", "APPTABP", "APPTABS"] {
        let got = child_case(
            &[
                ("APPTAB_CASE", "driver".into()),
                ("APPTAB_CASE_SPEC", sp.into()),
                (
                    "APPTAB_CASE_OUT",
                    base.join(format!("out-{sp}")).display().to_string(),
                ),
            ],
            &[],
        );
        assert_eq!(
            got,
            format!(
                "refused: {sp} is not runnable: no schedule file (EVAL_SCHEDULE, else EVAL_OUT/schedule.json)"
            ),
            "conformance: {sp}"
        );
    }
}

/// C6/T7: `exports_of`.
#[test]
fn c06_exports_of() {
    assert_eq!(exports_of("APPTAB"), None, "conformance: APPTAB");
    assert_eq!(
        exports_of("APPTABP"),
        Some("first_report"),
        "conformance: APPTABP"
    );
    assert_eq!(
        exports_of("APPTABS"),
        Some("spec_words"),
        "conformance: APPTABS"
    );
    assert_eq!(
        exports_of("APPTABW"),
        Some("flat_witness"),
        "conformance: APPTABW"
    );
    assert_eq!(exports_of("EDPROBE"), None, "conformance: EDPROBE");
    assert_eq!(exports_of("X2P"), Some("first_report"), "conformance: X2P");
    assert_eq!(exports_of("X2S"), Some("spec_words"), "conformance: X2S");
}

/// C6/E-AT-2: `APPTABW`'s five rows — the conforming pairs at `s = 2`,
/// stateful `Ltr` profiling, **rep 1**, default tier, no series; their keys
/// differ from the `APPTABS` keys of the same points (rep 0).
#[test]
fn c06_apptabw_rows() {
    let w = apptabw_spec();
    let fixtures: Vec<String> = w.rows.iter().map(|r| r.fixture.clone()).collect();
    assert_eq!(
        fixtures,
        vec![
            "apps/a1/correct/spec/n2r2",
            "apps/a2/pb/spec/k2q2",
            "apps/a3/fifo/spec/k2q2",
            "apps/a4/hash/a4a/k2q2m2",
            "2pc/leader/conf/n2",
        ],
        "conformance: the five"
    );
    for r in &w.rows {
        assert!(
            r.rep == 1
                && r.run_kind == RunKind::Profiling
                && r.tier == Tier::default_tier()
                && r.series.is_none()
                && r.config.label() == x1_config(GridEngine::Stateful, Selector::Ltr).label(),
            "conformance: {}",
            r.key(prof())
        );
    }
}

// =========================================================================
// Criterion 7 — the series rule; the record
// =========================================================================

/// C7 (+ C1's driver kills), child processes, fake probes, a valid schedule
/// file present: a custom spec named `APPTAB` with three series under a 2 s
/// tier, run in two invocations by size (`EVAL_ONLY`):
/// - invocation 1 (size 1): `slow` `capped_wall`, `fast` `ok`, `err`
///   `panicked`, the memory row `capped_memory`; `schedule.used.json` exists;
/// - invocation 2 (size 2): `slow` and `err` `skipped_after_censor`, `fast`
///   `ok`;
/// - the same under the name `X0` (not `APPTAB`): `err` at size 2 **runs**;
/// - a run stopped at its first append (a read-only store) has already written
///   `schedule.used.json`;
/// - a changed schedule file is refused.
///
/// Run alone.
#[test]
#[ignore]
fn c07_the_series_rule_across_invocations() {
    let base = temp("c07");
    let f = base.join("schedule.json");
    fs::write(&f, sched_text(2, &[], &[], "/nonexistent")).unwrap();
    let sched = f.display().to_string();
    let store_name = if prof() == "release" {
        "rows.csv"
    } else {
        "rows-test.csv"
    };
    let mut bad = Vec::new();
    for (name, err_runs) in [("APPTAB", false), ("X0", true)] {
        let out = base.join(format!("out-{name}"));
        let run = |only: &str| {
            child_case(
                &[
                    ("APPTAB_CASE", "driver".into()),
                    ("APPTAB_CASE_SPEC", format!("custom:{name}")),
                    ("APPTAB_CASE_OUT", out.display().to_string()),
                    ("APPTAB_CASE_ONLY", only.into()),
                    ("EVAL_SCHEDULE", sched.clone()),
                ],
                &[],
            )
        };
        // Size 1 in three invocations, then size 2 in a fourth: the censored
        // scopes are rebuilt from the store on every invocation.
        let r: Vec<String> = [
            "eval/series/*/k1|*",
            "eval/panic|*",
            "eval/alloc256|*",
            "eval/abort|*",
            "eval/series/*/k2|*",
        ]
        .iter()
        .map(|g| run(g))
        .collect();
        note!("c07 {name}: {r:?}");
        let rows = read_rows(&out.join(store_name)).unwrap_or_default();
        let class = |fx: &str, engine: &str| -> String {
            rows.iter()
                .find(|r| r["key"].starts_with(&format!("{fx}|{engine}/")))
                .map(|r| r["end_class"].clone())
                .unwrap_or_else(|| "absent".to_owned())
        };
        let got = [
            class("eval/series/slow/k1", "Stateful"),
            class("eval/series/slow/k2", "Stateful"),
            class("eval/series/fast/k1", "Stateful"),
            class("eval/series/fast/k2", "Stateful"),
            class("eval/panic", "Gated"),
            class("eval/series/fast/k2", "Gated"),
            class("eval/alloc256", "CompleteFirst"),
            class("eval/abort", "CompleteFirst"),
            class("eval/series/fast/k2", "CompleteFirst"),
        ];
        let got: Vec<String> = got
            .into_iter()
            .map(|c| {
                if c.starts_with("crashed") {
                    "crashed".to_owned()
                } else {
                    c
                }
            })
            .collect();
        let want = [
            "capped_wall",
            "skipped_after_censor",
            "ok",
            "ok",
            "panicked",
            if err_runs {
                "ok"
            } else {
                "skipped_after_censor"
            },
            "capped_memory",
            "crashed",
            if err_runs {
                "ok"
            } else {
                "skipped_after_censor"
            },
        ];
        if got.iter().map(String::as_str).collect::<Vec<_>>() != want {
            bad.push(format!("{name}: {got:?}, want {want:?}"));
        }
        let used = out.join("schedule.used.json").exists();
        if used != (name == "APPTAB") {
            bad.push(format!("{name}: schedule.used.json exists = {used}"));
        }
    }
    // The record before the first row: a read-only store.
    let out3 = base.join("out-stop");
    let store = out3.join(store_name);
    drop(
        Store::open(&store, "apptab-tests-host", "apptab-tests", true)
            .unwrap_or_else(|e| panic!("conformance: {}", e.text())),
    );
    let mut perm = fs::metadata(&store).unwrap().permissions();
    perm.set_readonly(true);
    fs::set_permissions(&store, perm).unwrap();
    let r = child_case(
        &[
            ("APPTAB_CASE", "driver".into()),
            ("APPTAB_CASE_SPEC", "custom:APPTAB".into()),
            ("APPTAB_CASE_OUT", out3.display().to_string()),
            ("APPTAB_CASE_ONLY", "eval/series/fast/k1|*".into()),
            ("EVAL_SCHEDULE", sched.clone()),
        ],
        &[],
    );
    note!("c07 stop: {r}");
    if !r.starts_with("refused: io") || !out3.join("schedule.used.json").exists() {
        bad.push(format!(
            "read-only store: {r}, record {}",
            out3.join("schedule.used.json").exists()
        ));
    }
    // A changed file.
    let f2 = base.join("schedule-changed.json");
    fs::write(&f2, sched_text(2, &[], &[], "/elsewhere")).unwrap();
    let r = child_case(
        &[
            ("APPTAB_CASE", "driver".into()),
            ("APPTAB_CASE_SPEC", "custom:APPTAB".into()),
            (
                "APPTAB_CASE_OUT",
                base.join("out-APPTAB").display().to_string(),
            ),
            ("APPTAB_CASE_ONLY", "eval/series/fast/k1|*".into()),
            ("EVAL_SCHEDULE", f2.display().to_string()),
        ],
        &[],
    );
    note!("c07 changed: {r}");
    if !r.starts_with("refused: the schedule changed under rows already run") {
        bad.push(format!("changed file: {r}"));
    }
    assert!(bad.is_empty(), "conformance: criterion 7: {bad:#?}");
}

// =========================================================================
// Criterion 8 — reuse validated before any row
// =========================================================================

/// A fake campaign store: the declared header, a host line, then one row per
/// `(key, end_class, executions)`.
fn fake_store(path: &Path, rows: &[(String, &str, &str)]) {
    let hdr = header();
    let mut text = format!(
        "{}\n#host: fake; schema={SCHEMA_VERSION}\n",
        csv_line(&hdr.iter().map(|h| (*h).to_owned()).collect::<Vec<_>>(),)
    );
    for (k, class, execs) in rows {
        let cells: Vec<String> = hdr
            .iter()
            .map(|h| match *h {
                "key" => k.clone(),
                "end_class" => (*class).to_owned(),
                "executions" | "reports" if class == &"ok" => (*execs).to_owned(),
                _ => String::new(),
            })
            .collect();
        text.push_str(&csv_line(&cells));
        text.push('\n');
    }
    fs::write(path, text).unwrap();
}

/// C8 (child processes): with a fake campaign store and one reused entry on
/// `A1 correct n2r2` (Enumerator), each bad batch is refused by
/// `validate_reuse` naming the key, and the driver refuses `APPTAB` before
/// `schedule.used.json` exists — an absent batch key, a label differing from
/// the key's, a batch of the wrong size, counters differing across the `ok`
/// reps, a rep before the censor not `ok`, a rep after it not `skipped_rep`,
/// two censored reps, a censored batch without `ends_series`, `ends_series` on
/// a completed batch; a completed batch, a batch censored at rep 0 and a mixed
/// batch (`ok`, `capped_wall`, `skipped_rep`) with `ends_series` pass and their
/// rows are absent (the censored ones with their larger sizes). Run alone.
#[test]
#[ignore]
fn c08_reuse_validation() {
    let base = temp("c08");
    let rows = sched_rows(3, "release");
    let key = rows[0]["key"].as_str().unwrap().to_owned();
    let series = rows[0]["series"].as_str().unwrap().to_owned();
    let k3 = rows
        .iter()
        .find(|r| r["series"] == series && r["size"] == 3)
        .unwrap()["key"]
        .as_str()
        .unwrap()
        .to_owned();
    let at = |r: usize| key.replacen("|0|default|", &format!("|{r}|default|"), 1);
    struct Case {
        what: &'static str,
        store: Vec<(String, &'static str, &'static str)>,
        batch: Vec<String>,
        ends: bool,
        ok: bool,
        needle: &'static str,
    }
    let three =
        |c: [(&'static str, &'static str); 3]| -> Vec<(String, &'static str, &'static str)> {
            c.iter()
                .enumerate()
                .map(|(i, (cl, ex))| (at(i), *cl, *ex))
                .collect()
        };
    let batch3 = vec![at(0), at(1), at(2)];
    let other_label = key.replace("memo=true", "memo=false");
    let cases = vec![
        Case {
            what: "absent",
            store: vec![(at(0), "ok", "5"), (at(1), "ok", "5")],
            batch: batch3.clone(),
            ends: false,
            ok: false,
            needle: "is absent from",
        },
        Case {
            what: "other label",
            store: vec![(other_label.clone(), "ok", "5")],
            batch: vec![other_label.clone()],
            ends: false,
            ok: false,
            needle: "is not that key at another rep",
        },
        Case {
            what: "wrong size",
            store: three([("ok", "5"), ("ok", "5"), ("ok", "5")]),
            batch: vec![at(0), at(2)],
            ends: false,
            ok: false,
            needle: "the batch's reps are",
        },
        Case {
            what: "counters differ",
            store: three([("ok", "5"), ("ok", "6"), ("ok", "5")]),
            batch: batch3.clone(),
            ends: false,
            ok: false,
            needle: "differs across the completed reps",
        },
        Case {
            what: "rep before censor not ok",
            store: three([("panicked", ""), ("capped_wall", ""), ("skipped_rep", "")]),
            batch: batch3.clone(),
            ends: true,
            ok: false,
            needle: "rep 0 did not complete",
        },
        Case {
            what: "rep after censor not skipped",
            store: three([("capped_wall", ""), ("ok", "5"), ("skipped_rep", "")]),
            batch: batch3.clone(),
            ends: true,
            ok: false,
            needle: "after the censored rep, not skipped_rep",
        },
        Case {
            what: "two censored",
            store: three([
                ("capped_wall", ""),
                ("capped_memory", ""),
                ("skipped_rep", ""),
            ]),
            batch: batch3.clone(),
            ends: true,
            ok: false,
            needle: "after an earlier censored rep",
        },
        Case {
            what: "censored without ends_series",
            store: three([
                ("capped_wall", ""),
                ("skipped_rep", ""),
                ("skipped_rep", ""),
            ]),
            batch: batch3.clone(),
            ends: false,
            ok: false,
            needle: "does not end its series",
        },
        Case {
            what: "ends_series on completed",
            store: three([("ok", "5"), ("ok", "5"), ("ok", "5")]),
            batch: batch3.clone(),
            ends: true,
            ok: false,
            needle: "the batch completed",
        },
        Case {
            what: "completed",
            store: three([("ok", "5"), ("ok", "5"), ("ok", "5")]),
            batch: batch3.clone(),
            ends: false,
            ok: true,
            needle: "",
        },
        Case {
            what: "censored at rep 0",
            store: three([
                ("capped_wall", ""),
                ("skipped_rep", ""),
                ("skipped_rep", ""),
            ]),
            batch: batch3.clone(),
            ends: true,
            ok: true,
            needle: "",
        },
        Case {
            what: "mixed",
            store: three([("ok", "5"), ("capped_wall", ""), ("skipped_rep", "")]),
            batch: batch3.clone(),
            ends: true,
            ok: true,
            needle: "",
        },
    ];
    let mut bad = Vec::new();
    for (i, c) in cases.iter().enumerate() {
        let dir = base.join(format!("case{i}"));
        fs::create_dir_all(&dir).unwrap();
        let store = dir.join("campaign.csv");
        fake_store(&store, &c.store);
        let mut entry = serde_json::json!({ "key": key, "batch": c.batch, "reps": c.batch.len() });
        if c.ends {
            entry["ends_series"] = serde_json::json!(true);
        }
        let ended: Vec<(String, usize)> = if c.ends {
            vec![(series.clone(), 2)]
        } else {
            vec![]
        };
        let f = dir.join("schedule.json");
        fs::write(
            &f,
            sched_text(3, &[entry], &ended, &store.display().to_string()),
        )
        .unwrap();
        let env = |case: &str| -> Vec<(&'static str, String)> {
            vec![
                ("APPTAB_CASE", case.to_owned()),
                ("EVAL_SCHEDULE", f.display().to_string()),
                ("APPTAB_CASE_SPEC", "APPTAB".to_owned()),
                ("APPTAB_CASE_OUT", dir.join("out").display().to_string()),
                (
                    "APPTAB_CASE_ONLY",
                    "campaign-tests: selects no key".to_owned(),
                ),
            ]
        };
        let got = child_case(&env("reuse"), &[]);
        let v: serde_json::Value = match serde_json::from_str(&got) {
            Ok(v) => v,
            Err(_) => {
                bad.push(format!("{}: {got}", c.what));
                continue;
            }
        };
        let val = v["validate"].as_str().unwrap_or_default().to_owned();
        let rows_now: Vec<String> = serde_json::from_value(v["rows"].clone()).unwrap();
        if c.ok {
            let mut expect_absent = vec![key.clone()];
            if c.ends {
                expect_absent.push(k3.clone());
            }
            let absent = expect_absent.iter().all(|k| !rows_now.contains(k));
            if val != "ok" || !absent {
                bad.push(format!("{}: {val}, absent {absent}", c.what));
            }
        } else {
            if !(val.contains(&key) && val.contains(c.needle)) {
                bad.push(format!("{}: {val}", c.what));
            }
            let d = child_case(&env("driver"), &[]);
            if d != val || dir.join("out/schedule.used.json").exists() {
                bad.push(format!(
                    "{}: driver {d}, record {}",
                    c.what,
                    dir.join("out/schedule.used.json").exists()
                ));
            }
        }
        note!("c08 {}: {val}", c.what);
    }
    assert!(bad.is_empty(), "conformance: criterion 8: {bad:#?}");
}

// =========================================================================
// Criterion 11 — EDPROBE
// =========================================================================

/// C11 / T10: `EDPROBE` holds six rows `ex:naive/k{2..7}/enc2`, the enumerator,
/// `Ltr`, `stop = true`, memo **off**, `Unlimited`, no precheck, not
/// instrumented, tier `default`, timed, rep 0, family `naive`, variant
/// `violating`, no series; its keys are in no builtin spec.
#[test]
fn c11_edprobe_rows() {
    let d = edprobe_spec();
    let want_label = "Enumerator/Ltr/stop=true/Exhaustive/Always/memo=false/Unlimited/precheck=false/instr=false/cut=false/cover=Sweep";
    let fixtures: Vec<String> = d.rows.iter().map(|r| r.fixture.clone()).collect();
    assert_eq!(
        fixtures,
        (2..=7)
            .map(|k| format!("ex:naive/k{k}/enc2"))
            .collect::<Vec<_>>(),
        "conformance: the six"
    );
    let builtin: BTreeSet<String> = specs()
        .iter()
        .flat_map(|s| s.rows.iter().map(|r| r.key(prof())))
        .collect();
    for r in &d.rows {
        assert_eq!(r.config.label(), want_label, "conformance: {}", r.fixture);
        assert!(
            r.tier == Tier::default_tier()
                && r.run_kind == RunKind::Timed
                && r.rep == 0
                && r.family == "naive"
                && r.variant == "violating"
                && r.series.is_none(),
            "conformance: {}",
            r.fixture
        );
        assert!(
            !builtin.contains(&r.key(prof())),
            "conformance: {} shared",
            r.fixture
        );
    }
}

// =========================================================================
// Criterion 12 — what is untouched
// =========================================================================

/// C12: the header's width, `SCHEMA_VERSION`, `LABEL_PIN`, `builtin_specs()`'s
/// names (no APPTAB spec), `all_fixtures()` free of the new names (c02), the
/// registry leader pairs built by `le_impl` exactly as `apptab_build` does
/// (c03) — the closed campaign tests (`campaign_tests.rs`, `x5_tests.rs`) run
/// beside this module in the full suites (E-AT-4's invariance check).
#[test]
fn c12_the_pins_that_must_not_move() {
    // P5-CFCFG re-pin (2026-10-14): schema 3, five columns after `witnesses`.
    // COMPACT-INDEX re-pin (2026-10-17, gate 3 F1): schema 4, seventeen
    // columns after `flat_wall_time_ms` (202).
    // COMPACT-INDEX phase 2 re-pin (2026-10-19): schema 5, 208 columns;
    // fix round P3 (`sig_aliases`): 209.
    assert_eq!(SCHEMA_VERSION, 5, "conformance: schema");
    assert_eq!(header().len(), 209, "conformance: header");
    assert_eq!(
        LABEL_PIN,
        GridConfig::new(GridEngine::Enumerator).label(),
        "conformance: LABEL_PIN"
    );
    let names: Vec<String> = specs().iter().map(|s| s.name.clone()).collect();
    assert_eq!(
        names,
        // As at `8f19f0f` (`git show HEAD:…/eval.rs`: `x0_spec(), cal_spec(),
        // calx_spec()` then `campaign_specs()`): no APPTAB spec (E-AT-4).
        vec!["X0", "CAL", "CALX", "X1", "X1V", "X2", "X2P", "X2S", "X1P", "X3A", "X5", "X5G"],
        "conformance: builtin_specs"
    );
}

/// Reads the plan's expected file to keep the citation live (its existence).
#[test]
fn c04_the_expected_file_exists() {
    assert!(
        plan().join("log/dev/P5-APPTAB.expected.md").exists()
            && plan().join("log/dev/P5-APPTAB.derived.md").exists(),
        "conformance: the expected and derived files"
    );
}

/// T1, **fixed** (2026-10-14, the lead's `eval.rs` `9e1dfe32…`: `Schedule::parse`
/// orders rows by `balanced_position` = (size, benchmark, pair, mode with
/// `first` before `exhaustive`, engine)). Found at gate 3 on `232f751e…`:
/// the parser checked (size, benchmark) only, and a block that listed a
/// mutant's all-reports row before the conforming pair's rows was accepted.
/// T6: within a benchmark "the three pairs with their modes (conforming, first
/// report, all reports)"; criterion 6: rows out of the balanced order are
/// refused by name. The test moves A1 `silent`'s last all-reports row to the
/// front of block (2, a1), re-derives the `profiling` list (nothing else
/// differs) and expects "out of the balanced order".
#[test]
fn t1_c06_rows_out_of_order_within_a_block_are_refused() {
    let mut rows = sched_rows(2, "release");
    // Block (2, a1): rows 0..18; move an all-reports row of `silent` to the front.
    let last = rows.remove(17);
    rows.insert(0, last);
    let profiling = sched_profiling(&rows, &BTreeSet::new(), &[], "release");
    let text = serde_json::json!({
        "date": "2026-10-14",
        "source": "apptab_tests",
        "commit": "8f19f0f",
        "max_size": 2,
        "limits": { "wall_ms": 600000, "mem_kb": 4194304, "budget_h": 60 },
        "reuse_store": "/nonexistent",
        "rows": rows,
        "reused": [],
        "ended": [],
        "extension_reuse": [],
        "profiling": profiling,
    })
    .to_string();
    let got = parse_err(&text);
    assert!(
        got.contains("out of the balanced order"),
        "conformance: T1: a within-block reordering is {got}"
    );
}

/// A schedule text for `max = 2` with the rows reordered by `f` and the
/// `profiling` list re-derived from the reordered rows.
fn reordered(f: impl Fn(&mut Vec<serde_json::Value>)) -> String {
    let mut rows = sched_rows(2, "release");
    f(&mut rows);
    let profiling = sched_profiling(&rows, &BTreeSet::new(), &[], "release");
    serde_json::json!({
        "date": "2026-10-14",
        "source": "apptab_tests",
        "commit": "8f19f0f",
        "max_size": 2,
        "limits": { "wall_ms": 600000, "mem_kb": 4194304, "budget_h": 60 },
        "reuse_store": "/nonexistent",
        "rows": rows,
        "reused": [],
        "ended": [],
        "extension_reuse": [],
        "profiling": profiling,
    })
    .to_string()
}

/// After T1's fix, the finer order (T6): inside block (2, a1), with the
/// `profiling` list re-derived each time — two engines of one (pair, mode)
/// swapped (the conforming pair's Enumerator and Stateful rows); a mutant's
/// all-reports rows before its first-report rows; the two mutants swapped
/// (`silent`'s rows before `eager`'s); and a row listed twice — each refused,
/// naming the row ("out of the balanced order"); the unmodified file is
/// accepted.
#[test]
fn c06_rows_finer_order_is_enforced() {
    assert_eq!(
        parse_err(&reordered(|_| {})),
        "accepted",
        "conformance: the balanced file"
    );
    // Block (2, a1): rows 0..4 correct (E, S, CF, G); 4..8 eager first
    // (E, S, CF, G); 8..11 eager all reports (S, CF, G); 11..15 silent
    // first; 15..18 silent all reports.
    let cases: Vec<(&str, String)> = vec![
        ("engines swapped", reordered(|r| r.swap(0, 1))),
        (
            "all reports before first report",
            reordered(|r| {
                let block: Vec<serde_json::Value> = r.drain(4..11).collect();
                let (first, all) = block.split_at(4);
                let mut v = all.to_vec();
                v.extend_from_slice(first);
                for (k, x) in v.into_iter().enumerate() {
                    r.insert(4 + k, x);
                }
            }),
        ),
        (
            "mutants swapped",
            reordered(|r| {
                let silent: Vec<serde_json::Value> = r.drain(11..18).collect();
                for (k, x) in silent.into_iter().enumerate() {
                    r.insert(4 + k, x);
                }
            }),
        ),
        (
            "a row twice",
            reordered(|r| {
                let x = r[5].clone();
                r.insert(6, x);
            }),
        ),
    ];
    let mut bad = Vec::new();
    for (what, text) in &cases {
        let e = parse_err(text);
        note!("c06 finer order, {what}: {e}");
        if !(e.contains("out of the balanced order") || e.contains("listed twice")) {
            bad.push(format!("{what}: {e}"));
        }
    }
    assert!(bad.is_empty(), "conformance: the finer order: {bad:#?}");
}

/// The `from_env` child case (gate 4 round 01 m4): `Driver::from_env()` under
/// the environment given (`EVAL_SPEC`, `EVAL_OUT`, `EVAL_SCHEDULE`,
/// `EVAL_ONLY`, `EVAL_ALLOW_MIXED`), then `run()`; the refusal text or the
/// run's counts. A panic would print no case line.
fn case_from_env() -> String {
    match Driver::from_env() {
        Err(e) => format!("from_env: {}", e.text()),
        Ok(d) => match d.run() {
            Ok(s) => format!("ran {}", s.ran),
            Err(e) => e.text(),
        },
    }
}

/// Gate 4 round 01 m4 (child processes): a **malformed** schedule in force
/// (`EVAL_SCHEDULE` naming a file with `budget_h` 59) — `EVAL_SPEC=APPTAB`
/// is refused by `Driver::from_env` with the parser's refusal by name, no
/// panic, no `schedule.used.json`; an unreadable path (a directory) is a
/// `Refusal::Io`; `EVAL_SPEC=X0` with the same malformed file present never
/// reads it and runs its one selected key (`ran 1`), writing no record. Run
/// alone.
#[test]
#[ignore]
fn c06_a_malformed_schedule_through_from_env() {
    let base = temp("m4");
    let mut v: serde_json::Value =
        serde_json::from_str(&sched_text(2, &[], &[], "/nonexistent")).unwrap();
    v["limits"]["budget_h"] = serde_json::json!(59);
    let f = base.join("schedule.json");
    fs::write(&f, v.to_string()).unwrap();
    let mut bad = Vec::new();
    let out_a = base.join("out-apptab");
    let got = child_case(
        &[
            ("APPTAB_CASE", "from_env".into()),
            ("EVAL_SPEC", "APPTAB".into()),
            ("EVAL_OUT", out_a.display().to_string()),
            ("EVAL_SCHEDULE", f.display().to_string()),
            ("EVAL_ALLOW_MIXED", "1".into()),
        ],
        &[],
    );
    note!("m4 APPTAB: {got}");
    if got
        != "from_env: refused: the schedule is malformed: limits budget_h 59 is not D-T6's hard cap of 60 h"
        || out_a.join("schedule.used.json").exists()
    {
        bad.push(format!("APPTAB: {got}"));
    }
    let got = child_case(
        &[
            ("APPTAB_CASE", "from_env".into()),
            ("EVAL_SPEC", "APPTABS".into()),
            ("EVAL_OUT", base.join("out-dir").display().to_string()),
            ("EVAL_SCHEDULE", base.display().to_string()),
            ("EVAL_ALLOW_MIXED", "1".into()),
        ],
        &[],
    );
    note!("m4 unreadable: {got}");
    if !got.starts_with("from_env: refused: io") {
        bad.push(format!("unreadable: {got}"));
    }
    let out_x = base.join("out-x0");
    let got = child_case(
        &[
            ("APPTAB_CASE", "from_env".into()),
            ("EVAL_SPEC", "X0".into()),
            ("EVAL_OUT", out_x.display().to_string()),
            ("EVAL_SCHEDULE", f.display().to_string()),
            // `MIN-ENGINES` E1 (gate 3 re-pin): the stateful key prints `Plain`.
            ("EVAL_ONLY", "ex:naive/k2/enc1|Stateful/Plain/*|0|*".into()),
            ("EVAL_ALLOW_MIXED", "1".into()),
        ],
        &[],
    );
    note!("m4 X0: {got}");
    if got != "ran 1" || out_x.join("schedule.used.json").exists() {
        bad.push(format!("X0: {got}"));
    }
    assert!(bad.is_empty(), "conformance: m4: {bad:#?}");
}
