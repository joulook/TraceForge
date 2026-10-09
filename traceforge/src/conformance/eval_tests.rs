//! `P5-HARNESS` gate 3: the tester's file (criteria revision 4).
//!
//! `test_fixtures()` is consulted by `eval::fixture_by_name` (criterion 9,
//! round 03 m5); it registers the test-only fixtures `eval/naive_self/k6`,
//! `eval/sleeper`, `eval/series/*`, `eval/alloc256`, `eval/panic` and
//! `eval/abort`. The tests are named by criterion (`c01_…` … `c10_…`), the
//! label pinning test is `pin_…`, and a test that reproduces a defect of the
//! lead's runner is named `t<N>_…` after its T-finding in
//! `plan/traceForge/log/dev/P5-HARNESS.report.md`; a failing one is
//! `#[ignore]`d with the expected and measured values in its rustdoc.
//!
//! **Every expected value was derived from the criteria and Part 6's records
//! before `eval.rs` was read** (the report's Part 0). In-process tests run in
//! the default suite; every test that spawns a child process is `#[ignore]`d
//! (it reruns this test binary once per row) and is run one per invocation
//! with `--ignored --exact … --test-threads=1`. Those tests write their stores
//! under `plan/traceForge/log/eval/` (or `EVAL_TEST_OUT`): `t/<test>-<profile>/`
//! for the tests' private stores (recreated by each run), the main store
//! `rows.csv` / `rows-test.csv` for criteria 5–7 only.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::conformance::config::{CompletionCover, GatePolicy, GatedMode};
use crate::conformance::eval::{
    child_row, csv_line, escape_value, experiments_of, fixture_by_name, header, mixed_of,
    parse_csv_line, parse_key, parse_label, profile_name, read_rows, record_of, row_from_json,
    row_json, run_row_in_process, unescape_value, x0_spec, Driver, Probes, Refusal, RowSpec,
    RunKind, Series, Spec, Store, Summary, Tier, LABEL_PIN, SCHEMA_VERSION,
};
use crate::conformance::grid::{
    cfg, corpus_fixtures, naive_d, naive_e2_fixture, naive_fixture, naive_visible, paper_fixtures,
    prog, row_of, run_grid, two_pc_fixtures, Budget, Fixture, GridConfig, GridEnd, GridEngine,
    Group, Prog, Row, TableEntry,
};
use crate::conformance::selector::Selector;
use crate::{thread, ConsType};

/// Writes a line to stderr (the closed `s5_tests` emission scan forbids the
/// print macros in every file under `conformance/` but its test-only list).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

// =========================================================================
// Test-only fixtures (criterion 9: the tester's registration table)
// =========================================================================

thread_local! {
    /// Set by `c04_fixture_by_name_rejects_a_duplicate_name` on its own
    /// thread only: `test_fixtures()` then registers `eval/dup` twice.
    static INJECT_DUPLICATE: Cell<bool> = const { Cell::new(false) };
}

fn test_fixture(name: &str, visible: &[&str], imp: Prog, spec: Prog) -> Fixture {
    Fixture {
        name: name.to_owned(),
        source: "eval_tests.rs (P5-HARNESS tester)",
        group: Group::Paper,
        implementation: imp,
        specification: spec,
        visible: visible.iter().map(|s| (*s).to_owned()).collect(),
        config: cfg(ConsType::Bag),
        k: None,
        encoding: None,
        big_stack: false,
        table: None,
    }
}

/// `EVAL_REP` as the driver passes it (H5); 0 in process.
fn eval_rep() -> u64 {
    std::env::var("EVAL_REP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0)
}

/// `main` spawns one visible thread `a` that does nothing, after sleeping
/// `EVAL_REP × secs_per_rep` seconds when asked to.
fn trivial(secs_per_rep: Option<u64>) -> Prog {
    prog(move || {
        if let Some(s) = secs_per_rep {
            let n = eval_rep() * s;
            if n > 0 {
                std::thread::sleep(Duration::from_secs(n));
            }
        }
        let _a = thread::Builder::new()
            .name("a".to_string())
            .spawn(|| {})
            .unwrap();
    })
}

/// Sleeps 3 s on rep 2 only.
fn late() -> Prog {
    prog(|| {
        if eval_rep() == 2 {
            std::thread::sleep(Duration::from_secs(3));
        }
        let _a = thread::Builder::new()
            .name("a".to_string())
            .spawn(|| {})
            .unwrap();
    })
}

/// 256 MiB, every page written, held ≥ 5 sample periods (800 ms at 100 ms).
fn alloc256() -> Prog {
    prog(|| {
        const N: usize = 256 << 20;
        let mut v = vec![0u8; N];
        let mut i = 0;
        while i < N {
            v[i] = 1;
            i += 4096;
        }
        std::hint::black_box(&mut v);
        std::thread::sleep(Duration::from_millis(800));
        let touched: usize = v.iter().step_by(4096).map(|b| *b as usize).sum();
        assert_eq!(
            touched,
            N / 4096,
            "conformance: eval/alloc256: every page written"
        );
        let _a = thread::Builder::new()
            .name("a".to_string())
            .spawn(|| {})
            .unwrap();
    })
}

/// The panic fixture's payload: multi-line on purpose (H2's escape).
pub(super) const PANIC_TEXT: &str = "eval/panic: a deliberate panic\nsecond line, \"quoted\", \\n";

/// The test-only fixtures `fixture_by_name` resolves besides the registries.
pub(super) fn test_fixtures() -> Vec<Fixture> {
    let mut v = vec![
        // Criterion 3: the self-conformance pair `naive_d(6, 1, false, None)`.
        {
            let mut f = test_fixture(
                "eval/naive_self/k6",
                &[],
                naive_d(6, 1, false, None),
                naive_d(6, 1, false, None),
            );
            f.visible = naive_visible(6);
            f.k = Some(6);
            f.encoding = Some(2);
            f
        },
        // Criterion 4: rep-dependent (`EVAL_REP × 3 s`).
        test_fixture("eval/sleeper", &["a"], trivial(Some(3)), trivial(None)),
        // Criterion 4's two-size series: one scope censored at size 1.
        test_fixture(
            "eval/series/slow/k1",
            &["a"],
            trivial(Some(3)),
            trivial(None),
        ),
        test_fixture(
            "eval/series/slow/k2",
            &["a"],
            trivial(Some(3)),
            trivial(None),
        ),
        test_fixture("eval/series/fast/k1", &["a"], trivial(None), trivial(None)),
        test_fixture("eval/series/fast/k2", &["a"], trivial(None), trivial(None)),
        // T3: censored at its last rep only (o, o, c).
        test_fixture("eval/series/late/k1", &["a"], late(), trivial(None)),
        test_fixture("eval/series/late/k2", &["a"], late(), trivial(None)),
        // Criterion 2.
        test_fixture("eval/alloc256", &["a"], alloc256(), alloc256()),
        test_fixture(
            "eval/panic",
            &["a"],
            prog(|| panic!("conformance: {}", PANIC_TEXT)),
            prog(|| panic!("conformance: {}", PANIC_TEXT)),
        ),
        test_fixture(
            "eval/abort",
            &["a"],
            prog(|| std::process::abort()),
            prog(|| std::process::abort()),
        ),
    ];
    if INJECT_DUPLICATE.with(Cell::get) {
        v.push(test_fixture(
            "eval/dup",
            &["a"],
            trivial(None),
            trivial(None),
        ));
        v.push(test_fixture(
            "eval/dup",
            &["a"],
            trivial(None),
            trivial(None),
        ));
    }
    v
}

// =========================================================================
// Helpers
// =========================================================================

fn cell<'a>(row: &'a Row, k: &str) -> Option<&'a str> {
    row.iter().find(|(c, _)| *c == k).map(|(_, v)| v.as_str())
}

fn get<'a>(row: &'a BTreeMap<String, String>, k: &str) -> &'a str {
    row.get(k)
        .map(String::as_str)
        .unwrap_or_else(|| panic!("conformance: eval_tests: the store has no column {k}"))
}

/// Criterion 1's exclusion list: `*_ms`, `vm_hwm_*`, `stack_mib`, `pid`,
/// `kept_*`.
fn excluded_c1(col: &str) -> bool {
    col.ends_with("_ms")
        || col.starts_with("vm_hwm_")
        || col == "stack_mib"
        || col == "pid"
        || col.starts_with("kept_")
}

fn tier(name: &str, wall_ms: u64, mem_kb: u64) -> Tier {
    Tier {
        name: name.to_owned(),
        wall: Duration::from_millis(wall_ms),
        mem_kb,
    }
}

const FOUR_GIB_KB: u64 = 4 * 1024 * 1024;

fn row_spec(fixture: &str, config: GridConfig, rep: u32, t: &Tier, kind: RunKind) -> RowSpec {
    RowSpec {
        fixture: fixture.to_owned(),
        config,
        rep,
        tier: t.clone(),
        run_kind: kind,
        family: fixture
            .rsplit_once('/')
            .map_or(fixture, |(a, _)| a)
            .to_owned(),
        knobs: String::new(),
        k: [None; 4],
        variant: "conforming".to_owned(),
        twin_key: String::new(),
        series: None,
    }
}

fn spec(name: &str, rows: Vec<RowSpec>) -> Spec {
    Spec {
        name: name.to_owned(),
        rows,
    }
}

fn fake_probes(commit: &str, dirty: bool, host: &str) -> Probes {
    let (c, h) = (commit.to_owned(), host.to_owned());
    Probes {
        git: Box::new(move || (c.clone(), dirty)),
        host: Box::new(move || h.clone()),
    }
}

fn driver_with(s: Spec, specs: Vec<Spec>, out: &Path, period: Duration, probes: Probes) -> Driver {
    Driver {
        spec: s,
        specs,
        out_dir: out.to_path_buf(),
        sample_period: period,
        probes,
        allow_mixed: false,
        only: None,
    }
}

/// The real probes with `allow_mixed` (the gate-3 tree is dirty).
fn real_driver(s: Spec, specs: Vec<Spec>, out: &Path) -> Driver {
    let mut d = driver_with(s, specs, out, Duration::from_millis(100), Probes::real());
    d.allow_mixed = true;
    d
}

fn run_ok(d: &Driver) -> Summary {
    d.run()
        .unwrap_or_else(|e| panic!("conformance: eval_tests: driver refused: {}", e.text()))
}

/// Where the process tests keep their stores (`EVAL_TEST_OUT` overrides).
fn out_root() -> PathBuf {
    std::env::var_os("EVAL_TEST_OUT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../plan/traceForge/log/eval")
        })
}

/// A recreated private directory under `out_root()/t/`.
fn fresh(name: &str) -> PathBuf {
    let d = out_root()
        .join("t")
        .join(format!("{name}-{}", profile_name()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).expect("conformance: eval_tests: creating the store directory");
    d
}

/// A recreated directory under the system temp dir (in-process tests).
fn temp(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tf-eval-tests-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).expect("conformance: eval_tests: creating a temp directory");
    d
}

fn store_of(d: &Driver) -> Vec<BTreeMap<String, String>> {
    read_rows(&d.store_path()).unwrap_or_else(|e| panic!("conformance: {}", e.text()))
}

fn data_lines(path: &Path) -> usize {
    fs::read_to_string(path)
        .map(|t| t.lines().count().saturating_sub(2))
        .unwrap_or(0)
}

/// The settings columns of `row_of` (Part 6's table key, `cover` aside).
const SETTINGS: [&str; 10] = [
    "fixture",
    "engine",
    "selector",
    "stop",
    "gated_mode",
    "policy",
    "memo",
    "budget",
    "precheck",
    "instrumented",
];

fn settings_key(get: impl Fn(&str) -> String) -> String {
    SETTINGS.map(&get).join("|")
}

/// Split one Markdown table row of `grid::Tables` on unescaped `|`.
fn md_cells(line: &str) -> Vec<String> {
    let inner = line
        .trim()
        .strip_prefix('|')
        .and_then(|s| s.strip_suffix('|'))
        .unwrap_or("");
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut prev_backslash = false;
    for c in inner.chars() {
        if c == '|' && !prev_backslash {
            out.push(cur.trim().replace("\\|", "|"));
            cur.clear();
        } else {
            cur.push(c);
        }
        prev_backslash = c == '\\';
    }
    out.push(cur.trim().replace("\\|", "|"));
    out
}

/// Part 6's full-grid rows ("criterion 8/11: every run under …" in
/// `log/dev/P4-DIFF.tables.md`), keyed by the settings columns; a blank cell
/// is an absent column.
fn part6_grid_rows() -> BTreeMap<String, BTreeMap<String, String>> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../plan/traceForge/log/dev/P4-DIFF.tables.md");
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("conformance: eval_tests: {}: {e}", path.display()));
    let mut out: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    let mut in_grid = false;
    let mut hdr: Vec<String> = Vec::new();
    for l in text.lines() {
        if let Some(t) = l.strip_prefix("### ") {
            in_grid = t.starts_with("criterion 8/11");
            hdr.clear();
            continue;
        }
        if !in_grid || !l.starts_with('|') || l.starts_with("|---") {
            continue;
        }
        let cells = md_cells(l);
        if cells.first().map(String::as_str) == Some("fixture") {
            hdr = cells;
            continue;
        }
        assert_eq!(cells.len(), hdr.len(), "conformance: a Part 6 row: {l}");
        let m: BTreeMap<String, String> = hdr
            .iter()
            .cloned()
            .zip(cells)
            .filter(|(_, v)| !v.is_empty())
            .collect();
        let key = settings_key(|c| m.get(c).cloned().unwrap_or_default());
        if let Some(prev) = out.get(&key) {
            assert_eq!(prev, &m, "conformance: Part 6 holds two rows for {key}");
        }
        out.insert(key, m);
    }
    out
}

/// Compare a store row to Part 6's row by column name (exclusions applied):
/// `(compared, mismatches, Part 6 columns absent from the store)`.
fn compare_to_part6(
    got: &BTreeMap<String, String>,
    want: &BTreeMap<String, String>,
) -> (usize, Vec<String>, Vec<String>) {
    let mut compared = 0;
    let mut bad = Vec::new();
    let mut absent = Vec::new();
    for (c, w) in want {
        if excluded_c1(c) {
            continue;
        }
        match got.get(c) {
            None => absent.push(c.clone()),
            Some(g) => {
                compared += 1;
                if g != w {
                    bad.push(format!("{c}: Part 6 {w:?}, runner {g:?}"));
                }
            }
        }
    }
    (compared, bad, absent)
}

fn parse_u64(s: &str) -> Option<u64> {
    s.parse().ok()
}

// =========================================================================
// The label pinning test (round 03 m1)
// =========================================================================

/// The declared header at schema version 2 (180 columns: 30 runner, `run_dir`
/// included, and every `row_of`/`row_of_end` name but `ended`; gate-3 T1's fix).
/// Version 1's 148-column header was the defect T1. A change to the header or to `GridConfig::label()` fails here
/// until `SCHEMA_VERSION` is bumped and this pin updated with it.
const HEADER_PIN_V2: &str = "key,run_kind,profile,commit,rep,tier,end_class,censor_via,censored,proc_wall_ms,pid,rss_sampled_hwm_kb,rss_child_hwm_kb,run_dir,diag_keys,diag_bytes_est,family,knobs,k1,k2,k3,k4,variant,twin_key,cut,inner_order,comm_model,cache,carry,direction,fixture,engine,selector,stop,gated_mode,policy,memo,budget,precheck,instrumented,cover,flat_calls,flat_visits,flat_nd_branches,wall_ms,vm_hwm_kb_before,vm_hwm_kb_after,tainted_at_start,stack_mib,reports,exhaustions,diagnostics,end,skipped_gates,inert_gates,seed,spec_error,outer_graphs(execs+block),gate_invocations,gate_skipped_inert,gate_skipped_replay,gate_skipped_pruned,gate_skipped_disabled,gate_skipped_aborted,cover_calls,cover_exhaustions,rebuilds_taken,rebuilds_skipped_initial_seed,rebuilds_skipped_exhausted_seed,spec_visit_calls,spec_visit_calls_extend,spec_visit_calls_rebuild,memo_hits,per_cover,distinct_keys_run_wide,f63_distinct_run_wide,explored_complete_keys,report_keys,max_paper_events_per_execution,paper_events_at_first_report,executions,engine_wall_time_ms,per_cover_detail,impl_end,spec_end,spec_errors,impl_notes,max_paper_events,kept_impl_graphs,kept_spec_graphs,spec_graphs,impl_graphs,sig_key_buckets,signatures,orders_held,lookups,lookups_signature_miss,lookups_containment_tested,lookups_succeeded,lookups_failed_after_tests,containment_tests,counter_reports,spec_wall_time_ms,impl_wall_time_ms,cut_reports_list,aborted,witness_cache_len,sweep_ends,paper_events_at_first_report(grid),cache_probes,cache_hits,cache_tests,sweeps,sweeps_successful,sweeps_failing,sweeps_aborted,sweep_sizes,sweep_graphs,sweep_graphs_max,witnesses,witness_duplicates,cut_reports,precheck_ran,precheck_wall_time_ms,outer_wall_time_ms,sweep_wall_time_ms,reports_at_gates,reports_at_completion,abort_gate_at,first_failure_mode,gates,gates_inert,gates_skipped_replay,gates_skipped_certified,gates_declined,c1_tests_carried,carried_hits,c1_tests_cache,gate_cache_hits,c1_tests_sweep,gate_sweeps,gate_sweeps_successful,gate_sweeps_failing,gate_sweeps_budgeted,gate_sweeps_aborted,gate_sweep_sizes,certificates_set,certificate_resets,states_pushed,certified_states_revisited,reports_certified,reports_by_completion_test,completion_probes,completion_cache_hits,completion_cache_tests,completion_sweeps,completion_sweeps_successful,completion_sweeps_failing,completion_sweeps_aborted,completion_sweep_sizes,verdict,notes,rendered_engine,spec_errfree,communication_flat,thread_flat,spec_graphs_scanned,first_invisible,refused_at,payload,cap_ms,flat_source_branches,flat_source_recursions,flat_send_kills,flat_slot_kills,flat_source_kills,flat_done_kills,flat_witnesses,flat_max_depth,flat_wall_time_ms";

/// **Label pinning** (H1, round 03 m1): `LABEL_PIN` is today's
/// `GridConfig::new(GridEngine::Enumerator).label()`, and `header()` is the
/// pinned list, both beside `SCHEMA_VERSION == 2`.
#[test]
fn pin_the_label_format_and_the_header_beside_the_schema_version() {
    assert_eq!(
        SCHEMA_VERSION, 2,
        "conformance: bump the pins with the version"
    );
    assert_eq!(
        GridConfig::new(GridEngine::Enumerator).label(),
        LABEL_PIN,
        "conformance: the label format changed; bump SCHEMA_VERSION"
    );
    assert_eq!(
        LABEL_PIN,
        "Enumerator/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep"
    );
    assert_eq!(
        header().join(","),
        HEADER_PIN_V2,
        "conformance: the header changed; bump SCHEMA_VERSION"
    );
    assert_eq!(header().len(), 180);
}

/// H1: every label the grid builds parses back to the same configuration
/// (the key format the resume check relies on).
#[test]
fn h1_every_grid_label_parses_back() {
    let mut configs = Vec::new();
    for s in [Selector::Ltr, Selector::FewestEvents, Selector::Reverse] {
        for e in [
            GridEngine::Enumerator,
            GridEngine::Stateful,
            GridEngine::CompleteFirst,
            GridEngine::Gated,
            GridEngine::Verify,
        ] {
            for p in [
                GatePolicy::Never,
                GatePolicy::Always,
                GatePolicy::Budget(1),
                GatePolicy::Budget(12),
            ] {
                for m in [GatedMode::Exhaustive, GatedMode::FirstFailure] {
                    for b in [Budget::Default, Budget::Unlimited, Budget::Exact(12_082)] {
                        let c = GridConfig::new(e)
                            .selector(s)
                            .gated(m, p)
                            .budget(b)
                            .memo(true)
                            .stop(true)
                            .precheck(true)
                            .instrumented(true)
                            .cover(CompletionCover::Flat);
                        configs.push(c.clone());
                        configs.push(GridConfig {
                            early_error_cut: true,
                            ..c
                        });
                    }
                }
            }
        }
    }
    for c in &configs {
        assert_eq!(
            parse_label(&c.label()).as_ref(),
            Some(c),
            "conformance: {}",
            c.label()
        );
        let k = row_spec(
            "ex:naive/k2/enc1",
            c.clone(),
            2,
            &Tier::extension(),
            RunKind::Baseline,
        )
        .key("release");
        let (f, pc, rep, t, rk, prof) = parse_key(&k).expect("conformance: a key parses");
        assert_eq!(
            (f.as_str(), &pc, rep, t.as_str(), rk, prof.as_str()),
            (
                "ex:naive/k2/enc1",
                c,
                2,
                "extension",
                RunKind::Baseline,
                "release"
            )
        );
    }
    assert!(parse_label("Enumerator/Ltr/stop=false").is_none());
    assert!(parse_key("a|b|c").is_none());
}

// =========================================================================
// Criterion 1 (in process): the runner's columns on X0's rows
// =========================================================================

/// **Criterion 1 / H7, in process**: `child_row` on each `X0` row — the
/// runner's constant columns (`run_kind`, `profile`, `rep`, `tier`,
/// `end_class`, `inner_order = Recorded`, `comm_model = NoOrder` for the
/// `Bag` fixture, `cache`/`carry` by engine, `direction = none`, `cut`),
/// `rss_child_hwm_kb` = the run's post-call `vm_hwm_kb_after`.
#[test]
fn c01_the_runner_columns_of_x0_in_process() {
    for r in x0_spec().rows {
        let row = child_row(&r, "c0+dirty").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
        let c = |k: &str| cell(&row, k).unwrap_or("<absent>").to_owned();
        let engine = r.config.engine;
        let sweeping = matches!(engine, GridEngine::CompleteFirst | GridEngine::Gated);
        assert_eq!(c("key"), r.key(profile_name()));
        assert_eq!(
            (
                c("run_kind"),
                c("profile"),
                c("commit"),
                c("rep"),
                c("tier"),
                c("end_class"),
                c("censor_via"),
                c("censored"),
            ),
            (
                "timed".to_owned(),
                profile_name().to_owned(),
                "c0+dirty".to_owned(),
                "0".to_owned(),
                "default".to_owned(),
                "ok".to_owned(),
                String::new(),
                "false".to_owned()
            ),
            "conformance: c01 {}",
            r.config.label()
        );
        assert_eq!(
            (
                c("inner_order"),
                c("comm_model"),
                c("cache"),
                c("carry"),
                c("direction"),
                c("cut"),
                c("family"),
                c("knobs"),
                c("k1"),
                c("k2"),
                c("k3"),
                c("variant"),
            ),
            (
                "Recorded".to_owned(),
                "NoOrder".to_owned(),
                if sweeping { "on" } else { "n/a" }.to_owned(),
                if engine == GridEngine::Gated {
                    "on"
                } else {
                    "n/a"
                }
                .to_owned(),
                "none".to_owned(),
                "false".to_owned(),
                "ex:naive".to_owned(),
                "k=2,enc=1".to_owned(),
                "2".to_owned(),
                "1".to_owned(),
                String::new(),
                "violating".to_owned()
            )
        );
        let after = c("vm_hwm_kb_after");
        assert_eq!(
            Some(c("rss_child_hwm_kb")),
            after
                .strip_prefix("Some(")
                .and_then(|s| s.strip_suffix(')'))
                .map(str::to_owned),
            "conformance: rss_child_hwm_kb is vm_hwm_kb_after"
        );
        assert!(
            cell(&row, "ended").is_none(),
            "conformance: n2: ended is mapped"
        );
        assert_eq!(c("diag_keys"), "", "conformance: uninstrumented");
    }
}

// =========================================================================
// Criterion 1b: `keep_graphs` off on the three sites
// =========================================================================

/// **Criterion 1b, in process** (M2; round 03 m6): `ex:naive/k3/enc2`, `Ltr`,
/// stateful, complete-first and gated exhaustive. With `keep_graphs = false`
/// (timed) the kept columns are 0/0; with `true` (profiling) they are Part
/// 6's 6/6, 6/36 (= Σ `sweep_sizes` `[6; 6]`), 6/7 (= Σ `gate_sweep_sizes`
/// `[1, 6]`); every other column is equal (criterion 1's exclusions,
/// `kept_*`, `instrumented`).
#[test]
fn c01b_keep_graphs_off_on_the_three_sites_in_process() {
    let f = naive_fixture(3, 2);
    for (engine, kept_true) in [
        (GridEngine::Stateful, ("6", "6")),
        (GridEngine::CompleteFirst, ("6", "36")),
        (GridEngine::Gated, ("6", "7")),
    ] {
        let c = GridConfig::new(engine);
        let rows: Vec<Row> = [false, true]
            .into_iter()
            .map(|keep| match run_row_in_process(&f, &c, keep) {
                GridEnd::Ok(r) => row_of(&r),
                other => panic!("conformance: c01b {engine:?}: {other:?}"),
            })
            .collect();
        let kept = |r: &Row| {
            (
                cell(r, "kept_impl_graphs").unwrap_or("").to_owned(),
                cell(r, "kept_spec_graphs").unwrap_or("").to_owned(),
            )
        };
        assert_eq!(
            kept(&rows[0]),
            ("0".to_owned(), "0".to_owned()),
            "conformance: c01b {engine:?} timed"
        );
        assert_eq!(
            kept(&rows[1]),
            (kept_true.0.to_owned(), kept_true.1.to_owned()),
            "conformance: c01b {engine:?} profiling"
        );
        let other = |r: &Row| -> Vec<(String, String)> {
            r.iter()
                .filter(|(k, _)| !excluded_c1(k) && *k != "instrumented")
                .map(|(k, v)| ((*k).to_owned(), v.clone()))
                .collect()
        };
        assert_eq!(
            other(&rows[0]),
            other(&rows[1]),
            "conformance: c01b {engine:?}"
        );
        assert!(other(&rows[0]).len() > 20);
    }
}

// =========================================================================
// Criterion 2 (in process): the panic row
// =========================================================================

/// **Criterion 2 / H2, in process**: `eval/panic` gives `end_class =
/// panicked`, `censored = false`, the multi-line payload in `payload`, and
/// the payload survives the sentinel encoding (`csv_line` →
/// `parse_csv_line`) byte for byte.
#[test]
fn c02_the_panic_row_carries_its_multiline_payload() {
    let r = row_spec(
        "eval/panic",
        GridConfig::new(GridEngine::Stateful),
        0,
        &Tier::default_tier(),
        RunKind::Timed,
    );
    let row = child_row(&r, "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    assert_eq!(cell(&row, "end_class"), Some("panicked"));
    assert_eq!(cell(&row, "censored"), Some("false"));
    let payload = cell(&row, "payload")
        .expect("conformance: a payload")
        .to_owned();
    assert!(
        payload.contains(PANIC_TEXT),
        "conformance: payload {payload:?}"
    );
    assert!(payload.contains('\n'));
    let line = csv_line(&record_of(&row));
    assert!(!line.contains('\n') && !line.contains('\r'));
    let back = parse_csv_line(&line).expect("conformance: the record parses");
    let idx = header().iter().position(|c| *c == "payload").unwrap();
    assert_eq!(back[idx], payload);
    assert_eq!(back, record_of(&row));
}

/// H2: the child's JSON row round-trips every field the child reads.
#[test]
fn h2_the_row_json_round_trips() {
    let mut r = row_spec(
        "eval/sleeper",
        GridConfig::new(GridEngine::Gated)
            .selector(Selector::Reverse)
            .gated(GatedMode::FirstFailure, GatePolicy::Budget(3))
            .budget(Budget::Exact(7)),
        2,
        &tier("t2s", 2000, 65_536),
        RunKind::Profiling,
    );
    r.k = [Some(3), None, Some(-1), Some(9)];
    r.knobs = "k=3,\"x\"=y".to_owned();
    r.variant = "mutant:m1".to_owned();
    r.twin_key = "a|b".to_owned();
    let back = row_from_json(&row_json(&r)).expect("conformance: the JSON parses");
    assert_eq!(back.key("test"), r.key("test"));
    assert_eq!(
        (
            &back.fixture,
            &back.config,
            back.rep,
            &back.tier,
            back.run_kind,
            &back.family,
            &back.knobs,
            back.k,
            &back.variant,
            &back.twin_key
        ),
        (
            &r.fixture,
            &r.config,
            r.rep,
            &r.tier,
            r.run_kind,
            &r.family,
            &r.knobs,
            r.k,
            &r.variant,
            &r.twin_key
        )
    );
}

// =========================================================================
// Criterion 4 (in process): refusals, truncation, experiments, mixed
// =========================================================================

fn write_store(
    dir: &Path,
    header_cells: &[String],
    host_line: &str,
    rows: &[Vec<String>],
) -> PathBuf {
    let p = dir.join("rows-test.csv");
    let p = if profile_name() == "release" {
        dir.join("rows.csv")
    } else {
        p
    };
    let mut s = format!("{}\n{host_line}\n", csv_line(header_cells));
    for r in rows {
        s.push_str(&csv_line(r));
        s.push('\n');
    }
    fs::write(&p, s).expect("conformance: writing a crafted store");
    p
}

fn declared() -> Vec<String> {
    header().iter().map(|s| (*s).to_owned()).collect()
}

fn record_with(key: &str, commit: &str) -> Vec<String> {
    record_of(&vec![
        ("key", key.to_owned()),
        ("commit", commit.to_owned()),
    ])
}

fn refusal_of(d: &Driver) -> Option<Refusal> {
    d.run().err()
}

/// **Criterion 4, every `Refusal` reason through the injected probes** (H7,
/// m5). Each driver has an empty spec, so nothing is spawned.
#[test]
fn c04_every_refusal_reason_through_the_injected_probes() {
    let dir = temp("refusals");
    let empty = || spec("E", Vec::new());
    let host_line = |h: &str, v: &str| format!("#host: {h}; schema={v}");
    let x0_key = x0_spec().rows[0].key(profile_name());
    let cur = SCHEMA_VERSION.to_string();
    let mk = |probes: Probes, allow: bool| {
        let mut d = driver_with(
            empty(),
            vec![empty()],
            &dir,
            Duration::from_millis(100),
            probes,
        );
        d.allow_mixed = allow;
        d
    };
    // Dirty, with a valid store and with no store; and before a bad header (L6).
    let _ = fs::remove_file(dir.join("rows-test.csv"));
    let _ = fs::remove_file(dir.join("rows.csv"));
    assert_eq!(
        refusal_of(&mk(fake_probes("c1", true, "H"), false)),
        Some(Refusal::Dirty("c1+dirty".to_owned()))
    );
    let mut renamed = declared();
    renamed[3] = "commit_".to_owned();
    write_store(&dir, &renamed, &host_line("H", &cur), &[]);
    assert_eq!(
        refusal_of(&mk(fake_probes("c1", true, "H"), false)),
        Some(Refusal::Dirty("c1+dirty".to_owned())),
        "conformance: L6, Dirty precedes Header"
    );
    // Header: same length, one column renamed; refused even with the override.
    for allow in [false, true] {
        assert_eq!(
            refusal_of(&mk(fake_probes("c1", false, "H"), allow)),
            Some(Refusal::Header),
            "conformance: Header, allow_mixed = {allow}"
        );
    }
    // Header: a missing column.
    write_store(&dir, &declared()[1..], &host_line("H", &cur), &[]);
    assert_eq!(
        refusal_of(&mk(fake_probes("c1", false, "H"), true)),
        Some(Refusal::Header)
    );
    // Schema, even with the override.
    write_store(&dir, &declared(), &host_line("H", "1"), &[]);
    assert_eq!(
        refusal_of(&mk(fake_probes("c1", false, "H"), true)),
        Some(Refusal::Schema("1".to_owned()))
    );
    // Host: refused without the override, accepted with it.
    write_store(&dir, &declared(), &host_line("H-other", &cur), &[]);
    assert_eq!(
        refusal_of(&mk(fake_probes("c1", false, "H"), false)),
        Some(Refusal::Host("H-other".to_owned()))
    );
    assert_eq!(refusal_of(&mk(fake_probes("c1", false, "H"), true)), None);
    // KeyFormat, even with the override: an old label format (no `cover=`).
    let old = x0_key.replace("/cover=Sweep", "");
    write_store(
        &dir,
        &declared(),
        &host_line("H", &cur),
        &[record_with(&old, "c1")],
    );
    for allow in [false, true] {
        assert_eq!(
            refusal_of(&mk(fake_probes("c1", false, "H"), allow)),
            Some(Refusal::KeyFormat(old.clone())),
            "conformance: KeyFormat, allow_mixed = {allow}"
        );
    }
    // T4 (follow-up): a header-only store is created afresh, not refused.
    let hdr_only = write_store(&dir, &declared(), "", &[]);
    fs::write(&hdr_only, format!("{}\n", csv_line(&declared()))).unwrap();
    assert_eq!(refusal_of(&mk(fake_probes("c1", false, "H"), false)), None);
    // Commit: refused without the override, accepted with it.
    write_store(
        &dir,
        &declared(),
        &host_line("H", &cur),
        &[record_with(&x0_key, "c0")],
    );
    assert_eq!(
        refusal_of(&mk(fake_probes("c1", false, "H"), false)),
        Some(Refusal::Commit("c0".to_owned()))
    );
    assert_eq!(refusal_of(&mk(fake_probes("c1", false, "H"), true)), None);
    assert_eq!(refusal_of(&mk(fake_probes("c0", false, "H"), false)), None);
    // Every reason's text is distinct.
    let texts: BTreeSet<String> = [
        Refusal::Header,
        Refusal::Schema("x".into()),
        Refusal::KeyFormat("x".into()),
        Refusal::Host("x".into()),
        Refusal::Commit("x".into()),
        Refusal::Dirty("x".into()),
        Refusal::DuplicateName("x".into()),
    ]
    .iter()
    .map(|r| r.text().replace('x', ""))
    .collect();
    assert_eq!(texts.len(), 7);
    let _ = fs::remove_dir_all(&dir);
}

/// **Criterion 4 / H2**: `fixture_by_name` rejects a duplicate name over its
/// whole domain (`Refusal::DuplicateName`), and so does a driver run before
/// it spawns anything; without the duplicate every test-only fixture
/// resolves.
#[test]
fn c04_fixture_by_name_rejects_a_duplicate_name() {
    for n in [
        "eval/naive_self/k6",
        "eval/sleeper",
        "eval/alloc256",
        "eval/panic",
        "eval/abort",
        "ex:naive/k7/enc2",
        "ndk3/bad_A",
        "2pc/leader/split/n4",
    ] {
        assert_eq!(fixture_by_name(n).map(|f| f.name).ok().as_deref(), Some(n));
    }
    assert!(matches!(
        fixture_by_name("eval/no-such"),
        Err(Refusal::UnknownFixture(_))
    ));
    INJECT_DUPLICATE.with(|c| c.set(true));
    let got = fixture_by_name("ex:naive/k2/enc1").map(|f| f.name);
    let dir = temp("dup");
    let d = driver_with(
        spec("D", vec![x0_spec().rows[0].clone()]),
        Vec::new(),
        &dir,
        Duration::from_millis(100),
        fake_probes("c", false, "H"),
    );
    let refused = d.run().err();
    INJECT_DUPLICATE.with(|c| c.set(false));
    assert_eq!(got, Err(Refusal::DuplicateName("eval/dup".to_owned())));
    assert_eq!(refused, Some(Refusal::DuplicateName("eval/dup".to_owned())));
    assert!(!dir.join("runs").exists() || fs::read_dir(dir.join("runs")).unwrap().count() == 0);
    let _ = fs::remove_dir_all(&dir);
}

/// **Criterion 4, a truncated last line is dropped** (in process): a store
/// whose last record was cut mid-cell opens, without that key, and the file
/// is rewritten without the line.
#[test]
fn c04_a_truncated_last_line_is_dropped() {
    let dir = temp("trunc");
    let rows = x0_spec().rows;
    let a = child_row(&rows[0], "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let b = child_row(&rows[1], "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let ka = rows[0].key(profile_name());
    let kb = rows[1].key(profile_name());
    let path = {
        let mut s = Store::open(&dir.join("s.csv"), "H", "c", false).unwrap();
        s.append(&a).unwrap();
        s.append(&b).unwrap();
        dir.join("s.csv")
    };
    let text = fs::read_to_string(&path).unwrap();
    let last_len = text.lines().last().unwrap().len();
    let good_prefix = text.as_bytes()[..text.len() - last_len - 1].to_vec();
    let cut = text.len() - last_len / 2;
    fs::write(&path, &text[..cut]).unwrap();
    let s =
        Store::open(&path, "H", "c", false).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    assert!(s.has(&ka) && !s.has(&kb));
    assert_eq!(s.rows().len(), 1);
    // Round 01 m2: truncated in place — the good prefix byte for byte.
    assert_eq!(
        fs::read(&path).unwrap(),
        good_prefix,
        "conformance: the store is cut at the end of its last good line"
    );
    let _ = fs::remove_dir_all(&dir);
}

/// **Fixed in the gate-3 follow-up** (`eval.rs` `a4f36b81…`); kept as a
/// regression test. **T-finding T5** (H7's truncation rule). A last line cut **right after
/// its final comma** parses to the full cell count (the missing last cell
/// reads as an empty unquoted cell), so it is kept as a complete row.
/// Expected: dropped (`!has(kb)`); measured: kept, with the last column
/// (`cap_ms`) silently blank.
///
/// Measured runtime: 0.01 s (gate 3).
#[test]
fn t5_a_line_cut_after_its_last_comma_is_kept_as_complete() {
    let dir = temp("trunc-comma");
    let rows = x0_spec().rows;
    let a = child_row(&rows[0], "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let kb = rows[1].key(profile_name());
    let mut b = child_row(&rows[1], "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    b.push(("cap_ms", "1234".to_owned()));
    let path = dir.join("s.csv");
    {
        let mut s = Store::open(&path, "H", "c", false).unwrap();
        s.append(&a).unwrap();
        s.append(&b).unwrap();
    }
    let text = fs::read_to_string(&path).unwrap();
    let cut = text.trim_end().rfind(',').unwrap() + 1;
    fs::write(&path, &text[..cut]).unwrap();
    let s =
        Store::open(&path, "H", "c", false).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let kept = s.has(&kb);
    let _ = fs::remove_dir_all(&dir);
    assert!(
        !kept,
        "conformance: T5: a line cut after its last comma was accepted as a complete row"
    );
}

/// **Fixed in the gate-3 follow-up** (`eval.rs` `a4f36b81…`); kept as a
/// regression test. **T-finding T4** (H7's crash window at creation). `Store::open` writes
/// the header and the `#host` line with two `writeln!`s; a driver killed
/// before or between them leaves a file that every later run refuses — an
/// empty file as `Refusal::Header`, a header-only file as
/// `Refusal::Schema("missing")` — although it holds no row. Expected: the
/// store reopens (or is recreated) with no rows. Measured: `Err(Header)` and
/// `Err(Schema("missing"))`.
///
/// Measured runtime: 0.00 s (gate 3).
#[test]
fn t4_a_store_cut_during_creation_refuses_forever() {
    let dir = temp("t4-create");
    let empty = dir.join("empty.csv");
    fs::write(&empty, "").unwrap();
    let header_only = dir.join("header-only.csv");
    fs::write(&header_only, format!("{}\n", csv_line(&declared()))).unwrap();
    let got: Vec<Option<Refusal>> = [&empty, &header_only]
        .iter()
        .map(|p| Store::open(p, "H", "c", false).err())
        .collect();
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(got, vec![None, None], "conformance: T4");
}

/// **Round 01 m1**: `Series::of` builds H5's scope — the configuration minus
/// its size (family and the other knobs), plus the label (engine, selector,
/// every knob), the tier and the run kind: equal across sizes, different
/// whenever any of those differs.
#[test]
fn m1_series_of_yields_the_h5_scope() {
    let c = GridConfig::new(GridEngine::Stateful);
    let t = tier("t2s", 2000, FOUR_GIB_KB);
    let base = Series::of("fam", "enc=1", &c, &t, RunKind::Timed, 3);
    assert_eq!(
        base.scope,
        format!("fam|enc=1|{}|t2s|timed", c.label()),
        "conformance: the H5 scope"
    );
    assert_eq!(base.size, 3);
    assert_eq!(
        Series::of("fam", "enc=1", &c, &t, RunKind::Timed, 4).scope,
        base.scope
    );
    let others = [
        Series::of("fam2", "enc=1", &c, &t, RunKind::Timed, 3),
        Series::of("fam", "enc=2", &c, &t, RunKind::Timed, 3),
        Series::of(
            "fam",
            "enc=1",
            &GridConfig::new(GridEngine::Gated),
            &t,
            RunKind::Timed,
            3,
        ),
        Series::of(
            "fam",
            "enc=1",
            &c.clone().selector(Selector::Reverse),
            &t,
            RunKind::Timed,
            3,
        ),
        Series::of("fam", "enc=1", &c.clone().memo(true), &t, RunKind::Timed, 3),
        Series::of("fam", "enc=1", &c, &Tier::default_tier(), RunKind::Timed, 3),
        Series::of("fam", "enc=1", &c, &t, RunKind::Profiling, 3),
    ];
    for o in others {
        assert_ne!(o.scope, base.scope, "conformance: {}", o.scope);
    }
}

/// **Round 01 M2**: an `EVAL_ONLY` glob that selects no key of the spec is
/// refused before anything runs.
#[test]
fn m2_eval_only_selecting_nothing_is_refused() {
    let dir = temp("only-none");
    let mut d = driver_with(
        x0_spec(),
        Vec::new(),
        &dir,
        Duration::from_millis(100),
        fake_probes("c", false, "H"),
    );
    d.only = Some("*|NoSuchEngine/*".to_owned());
    let got = d.run().err();
    let ran = fs::read_dir(dir.join("runs"))
        .map(|r| r.count())
        .unwrap_or(0);
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(
        got,
        Some(Refusal::Spec(
            "EVAL_ONLY=*|NoSuchEngine/* selects no key of X0".to_owned()
        ))
    );
    assert_eq!(ran, 0, "conformance: nothing spawned");
}

// =========================================================================
// Gate-4 round-02 minors: m1 (unterminated last record), m2 (`Series::of_row`)
// =========================================================================

/// **Round 02 m1** (expected values derived from the verdict before running):
/// a store whose last line is a **complete, well-formed** record without its
/// trailing `\n` (a writer killed between the record and its newline) opens
/// without that key, and the file is cut in place to the end of the previous
/// good line, byte for byte; the next `append`s start on lines of their own,
/// so a reopen holds every key and every data line parses to the header's
/// width.
#[test]
fn r2m1_an_unterminated_complete_record_is_dropped_and_appends_do_not_fuse() {
    let dir = temp("r2m1-unterminated");
    let rows = x0_spec().rows;
    let row =
        |i: usize| child_row(&rows[i], "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let (a, b, c) = (row(0), row(1), row(2));
    let (ka, kb, kc) = (
        rows[0].key(profile_name()),
        rows[1].key(profile_name()),
        rows[2].key(profile_name()),
    );
    let width = declared().len();
    let path = dir.join("s.csv");
    {
        let mut s = Store::open(&path, "H", "c", false).unwrap();
        s.append(&a).unwrap();
        s.append(&b).unwrap();
    }
    let text = fs::read_to_string(&path).unwrap();
    assert!(
        text.ends_with('\n'),
        "conformance: append terminates its record"
    );
    let last = text.lines().last().unwrap().to_owned();
    // The precondition that makes this m1's case and not a cut mid-cell: the
    // unterminated line is itself a full-width record.
    assert_eq!(parse_csv_line(&last).map(|c| c.len()), Some(width));
    let good_prefix = text.as_bytes()[..text.len() - last.len() - 1].to_vec();
    fs::write(&path, &text[..text.len() - 1]).unwrap();
    let mut s =
        Store::open(&path, "H", "c", false).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let held = (s.has(&ka), s.has(&kb), s.rows().len());
    let after_open = fs::read(&path).unwrap();
    s.append(&b).unwrap();
    s.append(&c).unwrap();
    drop(s);
    let reopened = Store::open(&path, "H", "c", false)
        .map(|s| (s.has(&ka), s.has(&kb), s.has(&kc), s.rows().len()));
    let final_text = fs::read_to_string(&path).unwrap();
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(
        held,
        (true, false, 1),
        "conformance: the unterminated record is dropped"
    );
    assert_eq!(
        after_open, good_prefix,
        "conformance: the store is cut in place at the end of its last good line"
    );
    assert_eq!(
        reopened,
        Ok((true, true, true, 3)),
        "conformance: no fused records"
    );
    assert!(final_text.ends_with('\n'));
    let data: Vec<&str> = final_text.lines().skip(2).collect();
    assert_eq!(data.len(), 3, "conformance: one line per record");
    for l in data {
        assert_eq!(
            parse_csv_line(l).map(|c| c.len()),
            Some(width),
            "conformance: {l}"
        );
    }
}

/// A row of family `fam` with knobs `k` (size axis first by default), the
/// stateful engine, a 2 s tester tier and the timed run kind.
fn of_row_base(fixture: &str, k: [Option<i64>; 4]) -> RowSpec {
    let t = tier("t2s", 2000, FOUR_GIB_KB);
    let mut r = row_spec(
        fixture,
        GridConfig::new(GridEngine::Stateful),
        0,
        &t,
        RunKind::Timed,
    );
    r.family = "fam".to_owned();
    r.k = k;
    r.knobs = k
        .iter()
        .enumerate()
        .filter_map(|(i, v)| v.map(|x| format!("k{}={x}", i + 1)))
        .collect::<Vec<_>>()
        .join(",");
    r
}

/// **Round 02 m2, equality across the size axis** (derived from H5 before
/// running): two rows that differ only in the size-axis knob — and hence in
/// everything that is a function of it and not of the configuration: the
/// fixture name, the free `knobs` label, `rep` and `twin_key` — get the
/// same scope and their own sizes. The scope string is pinned to the
/// rustdoc's composition: `family|variant|k1..k4 (axis = "_", absent = "")`
/// then label, tier, run kind.
#[test]
fn r2m2_of_row_is_equal_across_the_size_axis_only() {
    let n3 = of_row_base("fam/n3", [Some(3), Some(1), None, None]);
    let mut n4 = of_row_base("fam/n4", [Some(4), Some(1), None, None]);
    n4.rep = 2;
    n4.twin_key = "some|twin".to_owned();
    assert_ne!(n3.knobs, n4.knobs, "conformance: precondition");
    let (s3, s4) = (Series::of_row(&n3, 0), Series::of_row(&n4, 0));
    assert_eq!(
        s3.scope,
        format!(
            "fam|conforming|_,1,,|{}|t2s|timed",
            GridConfig::new(GridEngine::Stateful).label()
        ),
        "conformance: the H5 scope of a row"
    );
    assert_eq!(s3.scope, s4.scope, "conformance: same series across sizes");
    assert_eq!((s3.size, s4.size), (3, 4));
}

/// **Round 02 m2, inequality on every component** (derived from H5 and the
/// verdict before running): changing exactly one of `variant` (round 02 m2's
/// addition to round 01 m1's list), a non-axis knob (including absent vs
/// `0`), the family, the engine, the selector, a knob carried in the label,
/// the tier or the run kind gives a different scope.
#[test]
fn r2m2_of_row_differs_on_every_scope_component() {
    let base = of_row_base("fam/n3", [Some(3), Some(1), None, None]);
    let scope = Series::of_row(&base, 0).scope;
    let vary: Vec<(&str, Box<dyn Fn(&mut RowSpec)>)> = vec![
        (
            "variant mutant",
            Box::new(|r| r.variant = "mutant:m1".to_owned()),
        ),
        (
            "variant violating",
            Box::new(|r| r.variant = "violating".to_owned()),
        ),
        (
            "variant control",
            Box::new(|r| r.variant = "control:c1".to_owned()),
        ),
        ("non-axis knob", Box::new(|r| r.k[1] = Some(2))),
        ("absent knob vs 0", Box::new(|r| r.k[2] = Some(0))),
        ("family", Box::new(|r| r.family = "fam2".to_owned())),
        (
            "engine",
            Box::new(|r| r.config = GridConfig::new(GridEngine::Gated)),
        ),
        (
            "selector",
            Box::new(|r| r.config = r.config.clone().selector(Selector::Reverse)),
        ),
        (
            "knob in the label",
            Box::new(|r| r.config = r.config.clone().memo(true)),
        ),
        ("tier", Box::new(|r| r.tier = Tier::default_tier())),
        ("run kind", Box::new(|r| r.run_kind = RunKind::Profiling)),
    ];
    for (what, f) in vary {
        let mut r = base.clone();
        f(&mut r);
        let s = Series::of_row(&r, 0);
        assert_ne!(s.scope, scope, "conformance: {what}: {}", s.scope);
        assert_eq!(s.size, 3, "conformance: {what}");
    }
}

/// **Round 02 m2, a size axis other than `k1`** (derived before running): with
/// `size_axis = 1` the size is `k2`, rows differing only in `k2` share a
/// scope, and rows differing in `k1` (now an ordinary knob) do not.
#[test]
fn r2m2_of_row_honours_a_size_axis_other_than_k1() {
    let base = of_row_base("fam/a", [Some(3), Some(5), None, None]);
    let s = Series::of_row(&base, 1);
    assert_eq!(s.size, 5, "conformance: the size is k2");
    assert!(
        s.scope.starts_with("fam|conforming|3,_,,|"),
        "conformance: {}",
        s.scope
    );
    let same = Series::of_row(&of_row_base("fam/b", [Some(3), Some(6), None, None]), 1);
    assert_eq!((same.scope.as_str(), same.size), (s.scope.as_str(), 6));
    let other = Series::of_row(&of_row_base("fam/c", [Some(4), Some(5), None, None]), 1);
    assert_ne!(other.scope, s.scope, "conformance: k1 is not the axis");
}

/// **T-finding T8, fixed** (`eval.rs` `9acfa4d4…`; kept as a positive test
/// of the fix; expected derived before running). Before the fix, `Store::open`
/// wrote the header and the `#host` line with two `writeln!`s, so a driver
/// killed between the host line and its newline left `header\n#host: …;
/// schema=2` with no final newline; `open` accepted it and the first `append`
/// fused onto the host line (measured on `b6c17489…`: every reopen refused
/// with `Refusal::Schema("2<the record>")`). Fixed: such a file holds no row
/// and is recreated like T4's header-only file. Expected now: `open` gives an
/// empty store and the file is exactly `header\n#host: H; schema=2\n`; the
/// append lands on its own line; a reopen holds exactly that 1 key; the file
/// has 3 newline-terminated lines.
#[test]
fn t8_a_host_line_without_its_newline_fuses_with_the_first_record() {
    let dir = temp("t8-host");
    let path = dir.join("s.csv");
    let head = format!(
        "{}\n#host: H; schema={SCHEMA_VERSION}",
        csv_line(&declared())
    );
    fs::write(&path, &head).unwrap();
    let rows = x0_spec().rows;
    let a = child_row(&rows[0], "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let ka = rows[0].key(profile_name());
    let opened = Store::open(&path, "H", "c", false).map(|s| (s.rows().len(), s));
    let after_open = fs::read_to_string(&path).unwrap();
    let opened_rows = opened.as_ref().map(|(n, _)| *n).map_err(|e| e.clone());
    let appended_ok = match opened {
        Ok((_, mut s)) => s.append(&a),
        Err(e) => Err(e),
    };
    let reopened = Store::open(&path, "H", "c", false).map(|s| (s.has(&ka), s.rows().len()));
    let final_text = fs::read_to_string(&path).unwrap();
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(opened_rows, Ok(0), "conformance: T8: the store opens empty");
    assert_eq!(
        after_open,
        format!("{head}\n"),
        "conformance: T8: recreated"
    );
    assert_eq!(appended_ok, Ok(()), "conformance: T8: append");
    match reopened {
        Ok(got) => assert_eq!(got, (true, 1), "conformance: T8: one key held"),
        Err(e) => {
            let t: String = e.text().chars().take(80).collect();
            panic!("conformance: T8: the reopen is refused: {t}")
        }
    }
    assert!(final_text.ends_with('\n'));
    let lines: Vec<&str> = final_text.lines().collect();
    assert_eq!(lines.len(), 3, "conformance: T8: header, host, one record");
    assert_eq!(
        parse_csv_line(lines[2]).map(|c| c.len()),
        Some(declared().len())
    );
}

/// **Criterion 4 / H1, `experiments` at read time**: a key shared by `X0`
/// and a tester spec `X0b` reads `X0,X0b`; a key of `X0b` alone reads
/// `X0b`; with the caller's profile in the key (L7), a key of the other
/// profile reads nothing.
#[test]
fn c04_experiments_of_a_shared_key() {
    let (x0, x0b) = (x0_spec(), x0b_spec());
    let specs = vec![x0.clone(), x0b.clone()];
    let p = profile_name();
    for r in &x0b.rows {
        let names = experiments_of(&r.key(p), &specs, p);
        let shared = x0.rows.iter().any(|q| q.key(p) == r.key(p));
        assert_eq!(
            names,
            if shared {
                vec!["X0".to_owned(), "X0b".to_owned()]
            } else {
                vec!["X0b".to_owned()]
            }
        );
    }
    assert_eq!(
        experiments_of(&x0.rows[0].key(p), &specs, p),
        vec!["X0".to_owned(), "X0b".to_owned()]
    );
    let other = if p == "test" { "release" } else { "test" };
    assert!(experiments_of(&x0.rows[0].key(other), &specs, p).is_empty());
}

/// **Criterion 4 / round 03 D4**: `mixed` over the four rule-(1) sequences.
#[test]
fn c04_mixed_truth_table() {
    let r = row_spec(
        "eval/sleeper",
        GridConfig::new(GridEngine::Stateful),
        0,
        &tier("t2s", 2000, FOUR_GIB_KB),
        RunKind::Timed,
    );
    let mk = |rep: u32, class: &str| -> BTreeMap<String, String> {
        let mut q = r.clone();
        q.rep = rep;
        let censored = class.starts_with("capped");
        [
            ("key", q.key("test")),
            ("end_class", class.to_owned()),
            ("censored", censored.to_string()),
        ]
        .into_iter()
        .map(|(a, b)| (a.to_owned(), b))
        .collect()
    };
    for (seq, want) in [
        (["capped_wall", "skipped_rep", "skipped_rep"], false),
        (["ok", "capped_wall", "skipped_rep"], true),
        (["ok", "ok", "capped_memory"], true),
        (["ok", "ok", "ok"], false),
    ] {
        let rows: Vec<_> = seq
            .iter()
            .enumerate()
            .map(|(i, c)| mk(i as u32, c))
            .collect();
        assert_eq!(
            mixed_of(&rows, &r.rep_set()),
            want,
            "conformance: D4 {seq:?}"
        );
    }
}

/// **Fixed in the gate-3 follow-up** (`eval.rs` `a4f36b81…`); kept as a
/// regression test. **T-finding T6** (H4: "`timed` rows carry lightweight counters only
/// (`instrumented = false`)"; plan §0). The runner accepts a `timed` row
/// whose configuration is instrumented and runs it instrumented. Expected: a
/// refusal or an uninstrumented run; measured: `instrumented = true` and a
/// filled `diag_keys` on a `timed` row.
///
/// Measured runtime: 0.01 s (gate 3).
#[test]
fn t6_a_timed_row_runs_instrumented() {
    let r = row_spec(
        "ex:naive/k2/enc2",
        GridConfig::new(GridEngine::Enumerator).instrumented(true),
        0,
        &Tier::default_tier(),
        RunKind::Timed,
    );
    let key = r.key(profile_name());
    let dir = temp("t6");
    let d = driver_with(
        spec("T6", vec![r]),
        Vec::new(),
        &dir,
        Duration::from_millis(100),
        fake_probes("c", false, "H"),
    );
    let got = d.run().err();
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(
        got,
        Some(Refusal::Spec(format!("timed row instrumented: {key}"))),
        "conformance: T6"
    );
}

// =========================================================================
// Criterion 5 (in process): the header and RFC 4180
// =========================================================================

/// **Criterion 5 / H7, the runner's columns**: every H7 runner column is in
/// the header except `experiments` (H1: computed at read time by
/// `experiments_of`, never stored — round 03 m7); no column twice; `ended`
/// is not a column (n2).
#[test]
fn c05_the_header_has_the_runner_columns_once() {
    let h = header();
    let set: BTreeSet<&str> = h.iter().copied().collect();
    assert_eq!(set.len(), h.len(), "conformance: a column twice");
    let runner = [
        "key",
        "run_kind",
        "profile",
        "commit",
        "rep",
        "tier",
        "end_class",
        "censor_via",
        "censored",
        "payload",
        "proc_wall_ms",
        "pid",
        "rss_sampled_hwm_kb",
        "rss_child_hwm_kb",
        "diag_keys",
        "diag_bytes_est",
        "family",
        "knobs",
        "k1",
        "k2",
        "k3",
        "k4",
        "variant",
        "twin_key",
        "cut",
        "inner_order",
        "comm_model",
        "cache",
        "carry",
        "direction",
    ];
    let missing: Vec<&str> = runner
        .iter()
        .copied()
        .filter(|c| !set.contains(c))
        .collect();
    assert!(
        missing.is_empty(),
        "conformance: runner columns missing: {missing:?}"
    );
    assert!(!set.contains("experiments") && !set.contains("ended"));
    assert_eq!(h[0], "key");
}

/// Every column name `grid.rs::row_of` (every arm, `flat_columns`) and
/// `row_of_end` push, extracted from `grid.rs` by reading its `push`/`push_d`
/// calls between `fn flat_columns` and the end of `fn row_of_end`.
fn row_of_columns_from_grid_source() -> Vec<String> {
    let src = include_str!("grid.rs");
    let start = src
        .find("fn settings_columns")
        .expect("conformance: settings_columns");
    // End at `fn row_of_end`'s closing brace (round 01 n2), not at a banner
    // another part owns.
    let roe = start
        + src[start..]
            .find("pub(super) fn row_of_end")
            .expect("conformance: row_of_end");
    let end = roe
        + src[roe..]
            .find("\n}\n")
            .expect("conformance: the end of row_of_end")
        + 3;
    let body: String = src[start..end]
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let mut out: Vec<String> = Vec::new();
    for pat in [
        "push(&mutrow,\"",
        "push_d(&mutrow,\"",
        "push(row,\"",
        "push_d(row,\"",
    ] {
        let mut rest = body.as_str();
        while let Some(i) = rest.find(pat) {
            rest = &rest[i + pat.len()..];
            let name = &rest[..rest.find('"').unwrap()];
            if !out.iter().any(|c| c == name) {
                out.push(name.to_owned());
            }
        }
    }
    out
}

/// **Fixed in the gate-3 follow-up** (`eval.rs` `a4f36b81…`); kept as a
/// regression test. **T-finding T1** (criterion 5, H7: "every `row_of` column of every arm is
/// present by name"). Expected: every name `row_of`/`flat_columns` push (148
/// over the arms, by script and by this extraction) and `row_of_end`'s
/// `payload`, `cap_ms` in `header()`. Measured: **31 absent** — the twelve
/// `flat_*` columns, `outer_graphs(execs+block)`,
/// `rebuilds_skipped_initial_seed`, `rebuilds_skipped_exhausted_seed`,
/// `spec_visit_calls_extend`, `spec_visit_calls_rebuild`,
/// `explored_complete_keys`, `max_paper_events_per_execution`,
/// `paper_events_at_first_report`, `lookups_containment_tested`,
/// `lookups_failed_after_tests`, `paper_events_at_first_report(grid)`,
/// `reports_at_completion`, `gates_skipped_certified`,
/// `certified_states_revisited`, `reports_by_completion_test`,
/// `completion_sweeps_{successful,failing,aborted}`,
/// `completion_sweep_sizes`. `record_of` drops them silently, so no store
/// row carries them (criterion 7's 2PC outer-graph figure among them).
///
/// Measured runtime: 0.00 s (gate 3).
#[test]
fn t1_every_row_of_column_is_in_the_header() {
    let cols = row_of_columns_from_grid_source();
    assert!(
        cols.len() >= 150,
        "conformance: extraction found {}",
        cols.len()
    );
    let h = header();
    let missing: Vec<&String> = cols
        .iter()
        .filter(|c| c.as_str() != "ended" && !h.contains(&c.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "conformance: T1: {} row_of columns are not in the header: {missing:?}",
        missing.len()
    );
}

/// An RFC 4180 reader written for this test (not `eval::parse_csv_line`):
/// fields separated by `,`, a quoted field ends at a `"` not followed by
/// `"`, `""` inside quotes is one `"`.
fn rfc4180(line: &str) -> Vec<String> {
    let b: Vec<char> = line.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    loop {
        let mut f = String::new();
        if i < b.len() && b[i] == '"' {
            i += 1;
            loop {
                assert!(i < b.len(), "conformance: an unterminated quoted field");
                if b[i] == '"' {
                    if i + 1 < b.len() && b[i + 1] == '"' {
                        f.push('"');
                        i += 2;
                    } else {
                        i += 1;
                        break;
                    }
                } else {
                    f.push(b[i]);
                    i += 1;
                }
            }
        } else {
            while i < b.len() && b[i] != ',' {
                f.push(b[i]);
                i += 1;
            }
        }
        out.push(f);
        if i >= b.len() {
            return out;
        }
        assert_eq!(b[i], ',', "conformance: a field is followed by a comma");
        i += 1;
    }
}

/// H2's reversible escape, inverted here independently: `\\` → `\`, `\n` →
/// newline, `\r` → carriage return.
fn my_unescape(s: &str) -> String {
    let mut out = String::new();
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match it.next() {
            Some('\\') => out.push('\\'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            other => panic!("conformance: an escape the writer never emits: {other:?}"),
        }
    }
    out
}

/// **Criterion 5, RFC 4180 round trip** (H2, H7, n3): `sweep_sizes` and
/// `per_cover_detail` (commas, brackets, semicolons) from real rows, and
/// adversarial values (newlines, carriage returns, quotes, backslashes before
/// `n`, a trailing backslash, an empty value), each written by `csv_line`
/// and read back by this test's own RFC 4180 reader plus the inverse escape,
/// and by `parse_csv_line`. Every value is quoted; no line breaks.
#[test]
fn c05_rfc4180_round_trip() {
    let cf = match run_row_in_process(
        &naive_fixture(3, 2),
        &GridConfig::new(GridEngine::CompleteFirst),
        false,
    ) {
        GridEnd::Ok(r) => row_of(&r),
        other => panic!("conformance: {other:?}"),
    };
    let en = match run_row_in_process(
        &naive_fixture(3, 2),
        &GridConfig::new(GridEngine::Enumerator)
            .budget(Budget::Unlimited)
            .instrumented(true),
        false,
    ) {
        GridEnd::Ok(r) => row_of(&r),
        other => panic!("conformance: {other:?}"),
    };
    let sizes = cell(&cf, "sweep_sizes").unwrap().to_owned();
    let detail = cell(&en, "per_cover_detail").unwrap().to_owned();
    assert_eq!(
        sizes, "[6, 6, 6, 6, 6, 6]",
        "conformance: Part 6's k3/enc2 sweep sizes"
    );
    assert!(detail.contains(", ") && detail.contains("per_attempt=["));
    let values: Vec<String> = vec![
        sizes,
        detail,
        PANIC_TEXT.to_owned(),
        "a\r\nb\rc\nd".to_owned(),
        "\\n is not a newline, \\\\n neither".to_owned(),
        "ends with a backslash \\".to_owned(),
        "\"\"\"".to_owned(),
        String::new(),
        ",,,".to_owned(),
        "EVALROW\tinside".to_owned(),
    ];
    let line = csv_line(&values);
    assert!(!line.contains('\n') && !line.contains('\r'));
    let fields = rfc4180(&line);
    assert_eq!(fields.len(), values.len());
    for (f, v) in fields.iter().zip(&values) {
        assert_eq!(&my_unescape(f), v);
        assert_eq!(f, &escape_value(v));
        assert_eq!(&unescape_value(f), v);
    }
    let requote = |fs: &[String]| -> String {
        fs.iter()
            .map(|f| format!("\"{}\"", f.replace('"', "\"\"")))
            .collect::<Vec<_>>()
            .join(",")
    };
    assert_eq!(requote(&fields), line, "conformance: every value quoted");
    assert_eq!(parse_csv_line(&line).as_deref(), Some(&values[..]));
    // A whole record of a real row, both readers.
    let rec = record_of(&en);
    let l2 = csv_line(&rec);
    assert_eq!(
        requote(&rfc4180(&l2)),
        l2,
        "conformance: every value quoted"
    );
    let mine: Vec<String> = rfc4180(&l2).iter().map(|f| my_unescape(f)).collect();
    assert_eq!(mine, rec);
    assert_eq!(parse_csv_line(&l2), Some(rec));
}

// =========================================================================
// Criterion 8: the rustdoc fix
// =========================================================================

/// **Criterion 8** (m8): `CompletionCover`'s rustdoc no longer calls the sweep
/// "directed" (it says "undirected"); `flat.rs` line 14 still says "the
/// directed sweep" — recorded for a later docs pass, not edited (closed).
#[test]
fn c08_completion_cover_rustdoc_no_longer_says_directed() {
    let src = include_str!("config.rs");
    let at = src.find("pub enum CompletionCover").unwrap();
    let doc_start = src[..at].rfind("\n\n").unwrap();
    let doc: Vec<&str> = src[doc_start..at]
        .lines()
        .filter(|l| l.trim_start().starts_with("///"))
        .collect();
    let text = doc.join(" ");
    assert!(
        text.contains("undirected, unpruned sweep"),
        "conformance: {text}"
    );
    let stripped = text.replace("undirected", "");
    assert!(!stripped.contains("directed"), "conformance: {text}");
    let flat14 = include_str!("flat.rs").lines().nth(13).unwrap();
    assert!(
        flat14.contains("the directed sweep"),
        "conformance: flat.rs l. 14 changed: {flat14}"
    );
}

// =========================================================================
// Specs (criteria 1, 4)
// =========================================================================

/// `X0b`: two of `X0`'s keys (Ltr enumerator and stateful) plus one of its
/// own (`ex:naive/k2/enc2`, Ltr enumerator).
fn x0b_spec() -> Spec {
    let mut rows: Vec<RowSpec> = x0_spec()
        .rows
        .into_iter()
        .filter(|r| {
            r.config.selector == Selector::Ltr
                && matches!(
                    r.config.engine,
                    GridEngine::Enumerator | GridEngine::Stateful
                )
        })
        .collect();
    assert_eq!(rows.len(), 2);
    let mut own = rows[0].clone();
    own.fixture = "ex:naive/k2/enc2".to_owned();
    own.knobs = "k=2,enc=2".to_owned();
    own.k = [Some(2), Some(2), None, None];
    rows.push(own);
    spec("X0b", rows)
}

/// `X0` at three repetitions.
fn x0_reps_spec() -> Spec {
    let mut rows = Vec::new();
    for r in x0_spec().rows {
        for rep in 0..3 {
            rows.push(RowSpec { rep, ..r.clone() });
        }
    }
    spec("X0r", rows)
}

// =========================================================================
// Process tests (`#[ignore]`d): every one spawns children through the driver
// =========================================================================

/// **Criterion 1, the driver and the child** (H1–H3): `X0`'s 12 rows, each
/// from its own process (`pid` distinct), `end_class = ok`; every Part 6
/// column (criterion 1's exclusions) equal to Part 6's table row
/// (`log/dev/P4-DIFF.tables.md`), and every header column equal to the
/// in-process `run_grid` row (`cover`, `per_cover_detail` included). Part 6
/// columns absent from the store are T1's and listed, not failed here.
///
/// Measured runtime: 0.31 s test profile, 0.25 s release (gate 3).
#[test]
#[ignore]
fn c01_x0_twelve_rows_each_from_its_own_process() {
    let dir = fresh("c01");
    let d = real_driver(x0_spec(), vec![x0_spec()], &dir);
    let s = run_ok(&d);
    assert_eq!((s.ran, s.skipped_present, s.censored), (12, 0, 0));
    let rows = store_of(&d);
    assert_eq!(rows.len(), 12);
    let pids: BTreeSet<&str> = rows.iter().map(|r| get(r, "pid")).collect();
    assert_eq!(pids.len(), 12, "conformance: one process per row");
    assert!(!pids.contains(std::process::id().to_string().as_str()));
    let part6 = part6_grid_rows();
    let mut absent_all = BTreeSet::new();
    let mut compared_total = 0;
    for r in &rows {
        assert_eq!(get(r, "end_class"), "ok");
        assert_eq!(get(r, "censored"), "false");
        assert_eq!(get(r, "run_kind"), "timed");
        assert_eq!(get(r, "comm_model"), "NoOrder");
        let key = settings_key(|c| get(r, c).to_owned());
        let want = part6
            .get(&key)
            .unwrap_or_else(|| panic!("conformance: no Part 6 row for {key}"));
        let (n, bad, absent) = compare_to_part6(r, want);
        assert!(bad.is_empty(), "conformance: c01 {key}: {bad:?}");
        assert!(n >= 20, "conformance: c01 {key}: only {n} columns compared");
        compared_total += n;
        absent_all.extend(absent);
        // The in-process run, every header column but the clocks and memory.
        let (_, cfgn, ..) = parse_key(get(r, "key")).unwrap();
        let f = fixture_by_name(get(r, "fixture")).unwrap();
        let inproc = match run_grid(&f, &cfgn, None) {
            GridEnd::Ok(x) => row_of(&x),
            other => panic!("conformance: {other:?}"),
        };
        for (c, v) in &inproc {
            if excluded_c1(c) || !header().contains(c) {
                continue;
            }
            assert_eq!(
                get(r, c),
                v.as_str(),
                "conformance: c01 {key}: {c} in process"
            );
        }
    }
    note!(
        "c01: {compared_total} cells compared; Part 6 columns absent from the store (T1): {absent_all:?}"
    );
    assert!(
        absent_all.is_empty(),
        "conformance: c01 absent: {absent_all:?}"
    );
}

/// **Criterion 1b through the driver**: the same three engines as `timed`
/// and `profiling` rows; timed kept 0/0, profiling Part 6's kept figures,
/// every other column equal (criterion 1's exclusions plus `run_kind`,
/// `rss_*`, `kept_*`, `instrumented`, and the per-row `key`, `pid`).
///
/// Measured runtime: 0.09 s test profile (gate 3).
#[test]
#[ignore]
fn c01b_keep_graphs_through_the_driver() {
    let dir = fresh("c01b");
    let t = Tier::default_tier();
    let mut rows = Vec::new();
    for e in [
        GridEngine::Stateful,
        GridEngine::CompleteFirst,
        GridEngine::Gated,
    ] {
        for k in [RunKind::Timed, RunKind::Profiling] {
            rows.push(row_spec("ex:naive/k3/enc2", GridConfig::new(e), 0, &t, k));
        }
    }
    let s = spec("C1b", rows);
    let d = real_driver(s.clone(), vec![s], &dir);
    assert_eq!(run_ok(&d).ran, 6);
    let rows = store_of(&d);
    for (e, want) in [
        ("Stateful", ("6", "6")),
        ("CompleteFirst", ("6", "36")),
        ("Gated", ("6", "7")),
    ] {
        let of = |k: &str| {
            rows.iter()
                .find(|r| get(r, "engine") == e && get(r, "run_kind") == k)
                .unwrap()
        };
        let (t, p) = (of("timed"), of("profiling"));
        assert_eq!(
            (get(t, "kept_impl_graphs"), get(t, "kept_spec_graphs")),
            ("0", "0")
        );
        assert_eq!(
            (get(p, "kept_impl_graphs"), get(p, "kept_spec_graphs")),
            want
        );
        for (c, v) in t {
            if excluded_c1(c)
                || ["run_kind", "instrumented", "key", "pid", "run_dir"].contains(&c.as_str())
                || c.starts_with("rss_")
            {
                continue;
            }
            assert_eq!(get(p, c), v.as_str(), "conformance: c01b {e} {c}");
        }
    }
}

/// **Criterion 2, the wall kill** (H3, H5): complete-first exhaustive on the
/// violating `ex:naive/k7/enc2` under a tester tier of 2 s (derived margin
/// ≈ 1474× in the test profile) is `capped_wall`, `censored`, `censor_via =
/// kill`, `proc_wall_ms = 2000`, every counter empty; the next key in the
/// driver's order (`ndk2/conf`, enumerator) runs and is `ok`.
///
/// Measured runtime: 2.06 s test profile (gate 3).
#[test]
#[ignore]
fn c02_the_wall_kill_and_the_next_key() {
    let dir = fresh("c02-wall");
    let t2 = tier("t2s", 2000, FOUR_GIB_KB);
    let s = spec(
        "C2w",
        vec![
            row_spec(
                "ex:naive/k7/enc2",
                GridConfig::new(GridEngine::CompleteFirst),
                0,
                &t2,
                RunKind::Timed,
            ),
            row_spec(
                "ndk2/conf",
                GridConfig::new(GridEngine::Enumerator),
                0,
                &t2,
                RunKind::Timed,
            ),
        ],
    );
    let d = real_driver(s.clone(), vec![s], &dir);
    let started = std::time::Instant::now();
    let sum = run_ok(&d);
    let took = started.elapsed();
    let rows = store_of(&d);
    assert_eq!((sum.ran, sum.censored, rows.len()), (2, 1, 2));
    let k = rows
        .iter()
        .find(|r| get(r, "fixture") == "ex:naive/k7/enc2")
        .unwrap();
    assert_eq!(
        (
            get(k, "end_class"),
            get(k, "censored"),
            get(k, "censor_via"),
            get(k, "proc_wall_ms"),
            get(k, "tier")
        ),
        ("capped_wall", "true", "kill", "2000", "t2s")
    );
    for c in [
        "reports",
        "executions",
        "sweeps",
        "sweep_graphs",
        "impl_graphs",
        "wall_ms",
        "rss_child_hwm_kb",
    ] {
        assert_eq!(get(k, c), "", "conformance: c02 a killed row has no {c}");
    }
    let cap: u64 = get(k, "cap_ms").parse().unwrap();
    assert!((2000..3000).contains(&cap), "conformance: cap_ms {cap}");
    let n = rows
        .iter()
        .find(|r| get(r, "fixture") == "ndk2/conf")
        .unwrap();
    assert_eq!((get(n, "end_class"), get(n, "reports")), ("ok", "0"));
    note!("c02 wall: the driver took {took:?}");
}

fn alloc_spec(name: &str, t: &Tier) -> Spec {
    spec(
        name,
        vec![row_spec(
            "eval/alloc256",
            GridConfig::new(GridEngine::Stateful),
            0,
            t,
            RunKind::Timed,
        )],
    )
}

/// **Criterion 2, the memory kill** (H3, H6): `eval/alloc256` (256 MiB, every
/// page written, held 800 ms ≥ 5 periods) under a 64 MiB tester tier at the
/// default 100 ms period is `capped_memory`, `censor_via = kill`,
/// `censored`, with `rss_sampled_hwm_kb > 65 536`, `proc_wall_ms` the
/// elapsed time at the kill, every counter empty.
///
/// Measured runtime: 0.14 s test profile (gate 3).
#[test]
#[ignore]
fn c02_the_memory_kill() {
    let dir = fresh("c02-mem");
    let t = tier("t64m", 60_000, 65_536);
    let s = alloc_spec("C2m", &t);
    let d = real_driver(s.clone(), vec![s], &dir);
    run_ok(&d);
    let rows = store_of(&d);
    let r = &rows[0];
    assert_eq!(
        (
            get(r, "end_class"),
            get(r, "censor_via"),
            get(r, "censored")
        ),
        ("capped_memory", "kill", "true")
    );
    let sampled: u64 = get(r, "rss_sampled_hwm_kb").parse().unwrap();
    let wall: u64 = get(r, "proc_wall_ms").parse().unwrap();
    assert!(sampled > 65_536, "conformance: sampled {sampled}");
    assert!(wall < 60_000, "conformance: proc_wall_ms {wall}");
    assert_eq!(get(r, "executions"), "");
    assert_eq!(get(r, "cap_ms"), wall.to_string().as_str());
    note!("c02 memory kill: sampled {sampled} kB at {wall} ms");
}

/// **Criterion 2, the post-hoc memory rule** (H3, round 03 m2): the same
/// fixture and tier with the sampling period set to 10 s — the child exits
/// before the first periodic sample — is `capped_memory` with `censor_via =
/// post_hoc`, `censored`, through `rss_child_hwm_kb > 65 536`; its counters
/// are kept (it completed) and `proc_wall_ms` is the measured time.
///
/// Measured runtime: 1.80 s test profile (gate 3).
#[test]
#[ignore]
fn c02_the_post_hoc_memory_rule() {
    let dir = fresh("c02-posthoc");
    let t = tier("t64m", 60_000, 65_536);
    let s = alloc_spec("C2p", &t);
    let mut d = real_driver(s.clone(), vec![s], &dir);
    d.sample_period = Duration::from_secs(10);
    run_ok(&d);
    let rows = store_of(&d);
    let r = &rows[0];
    assert_eq!(
        (
            get(r, "end_class"),
            get(r, "censor_via"),
            get(r, "censored")
        ),
        ("capped_memory", "post_hoc", "true")
    );
    let child: u64 = get(r, "rss_child_hwm_kb").parse().unwrap();
    assert!(child > 262_144, "conformance: rss_child_hwm_kb {child}");
    let wall: u64 = get(r, "proc_wall_ms").parse().unwrap();
    assert!(
        (800..10_000).contains(&wall),
        "conformance: proc_wall_ms {wall}"
    );
    assert_eq!(get(r, "reports"), "0");
    assert!(!get(r, "executions").is_empty());
    let sampled = get(r, "rss_sampled_hwm_kb");
    assert!(
        sampled.is_empty() || parse_u64(sampled).unwrap() < 65_536,
        "conformance: no periodic sample saw the allocation: {sampled}"
    );
    note!("c02 post hoc: child {child} kB, sampled {sampled:?}, {wall} ms");
}

/// **Criterion 2, panic and abort** (H3, m9): `eval/panic` is `panicked`,
/// not censored, with the multi-line payload in the row and the message in
/// the child's stderr file; `eval/abort` is `crashed(signal 6)`, not
/// censored.
///
/// Measured runtime: 0.03 s test profile (gate 3).
#[test]
#[ignore]
fn c02_panic_and_abort() {
    let dir = fresh("c02-crash");
    let t = Tier::default_tier();
    let s = spec(
        "C2c",
        vec![
            row_spec(
                "eval/panic",
                GridConfig::new(GridEngine::Stateful),
                0,
                &t,
                RunKind::Timed,
            ),
            row_spec(
                "eval/abort",
                GridConfig::new(GridEngine::Stateful),
                0,
                &t,
                RunKind::Timed,
            ),
        ],
    );
    let d = real_driver(s.clone(), vec![s], &dir);
    run_ok(&d);
    let rows = store_of(&d);
    let p = rows
        .iter()
        .find(|r| get(r, "fixture") == "eval/panic")
        .unwrap();
    assert_eq!(
        (get(p, "end_class"), get(p, "censored")),
        ("panicked", "false")
    );
    assert!(
        get(p, "payload").contains(PANIC_TEXT),
        "conformance: {:?}",
        get(p, "payload")
    );
    let a = rows
        .iter()
        .find(|r| get(r, "fixture") == "eval/abort")
        .unwrap();
    assert_eq!(
        (
            get(a, "end_class"),
            get(a, "censored"),
            get(a, "censor_via")
        ),
        ("crashed(signal 6)", "false", "")
    );
    // The message in a stderr file of this test's run directories.
    let mut found = Vec::new();
    for e in fs::read_dir(dir.join("runs")).unwrap() {
        let p = e.unwrap().path().join("stderr");
        if fs::read_to_string(&p)
            .unwrap_or_default()
            .contains("eval/panic: a deliberate panic")
        {
            found.push(p);
        }
    }
    assert_eq!(
        found.len(),
        1,
        "conformance: the panic message in one stderr file"
    );
}

/// **Criterion 3, the memory columns** (H6): `eval/naive_self/k6`,
/// complete-first exhaustive (derived: 720 sweeps, Σ = 259 560 Spec graphs,
/// conforming, no cache hit) is a row of seconds;
/// `rss_sampled_hwm_kb ≤ rss_child_hwm_kb + slack` and within 5 % of it (the
/// slack is printed); on `X0`'s sub-100 ms rows the child's column is present
/// and the sampled one empty or ≤ the child's.
///
/// Measured runtime: 25.9 s test profile, 27.8 s release (gate 3).
#[test]
#[ignore]
fn c03_the_memory_columns() {
    let dir = fresh("c03");
    let t = Tier::default_tier();
    let mut rows = vec![row_spec(
        "eval/naive_self/k6",
        GridConfig::new(GridEngine::CompleteFirst),
        0,
        &t,
        RunKind::Timed,
    )];
    rows.extend(x0_spec().rows);
    let s = spec("C3", rows);
    let d = real_driver(s.clone(), vec![s], &dir);
    run_ok(&d);
    let rows = store_of(&d);
    let r = rows
        .iter()
        .find(|r| get(r, "fixture") == "eval/naive_self/k6")
        .unwrap();
    assert_eq!(get(r, "end_class"), "ok");
    assert_eq!(
        (
            get(r, "reports"),
            get(r, "impl_graphs"),
            get(r, "sweeps"),
            get(r, "sweeps_successful"),
            get(r, "sweep_graphs"),
            get(r, "sweep_graphs_max"),
            get(r, "cache_hits"),
            get(r, "kept_spec_graphs"),
        ),
        ("0", "720", "720", "720", "259560", "720", "0", "0"),
        "conformance: D-3"
    );
    let sampled: u64 = get(r, "rss_sampled_hwm_kb").parse().unwrap();
    let child: u64 = get(r, "rss_child_hwm_kb").parse().unwrap();
    let wall: u64 = get(r, "proc_wall_ms").parse().unwrap();
    let slack = sampled as i64 - child as i64;
    note!(
        "c03: proc_wall_ms {wall}, wall_ms {}, sampled {sampled} kB, child {child} kB, sampled − child {slack} kB ({:.3} %)",
        get(r, "wall_ms"),
        100.0 * slack as f64 / child as f64
    );
    assert!(
        wall >= 2000,
        "conformance: c03 not a row of seconds: {wall} ms"
    );
    assert!(
        (slack.unsigned_abs() as f64) <= 0.05 * child as f64,
        "conformance: c03: sampled {sampled} vs child {child}"
    );
    for r in rows
        .iter()
        .filter(|r| get(r, "fixture") == "ex:naive/k2/enc1")
    {
        let c = parse_u64(get(r, "rss_child_hwm_kb")).expect("conformance: the child's column");
        let s = get(r, "rss_sampled_hwm_kb");
        assert!(
            s.is_empty() || parse_u64(s).unwrap() <= c,
            "conformance: {s} > {c}"
        );
    }
}

/// **Criterion 4, repetitions, deduplication, resumption** (H1, H5, H7):
/// `X0` at three reps has `rep` 0..2 and identical counters across reps; a
/// second invocation (and `X0` itself) adds no row; `X0b` overlapping `X0`
/// computes once and its shared rows read `X0,X0b` after either run order; a
/// store with a truncated last line resumes, rerunning exactly that key.
///
/// Measured runtime: 0.37 s test profile (gate 3).
#[test]
#[ignore]
fn c04_repetitions_deduplication_and_resumption() {
    let dir = fresh("c04-reps");
    let specs = vec![x0_spec(), x0b_spec(), x0_reps_spec()];
    let d = real_driver(x0_reps_spec(), specs.clone(), &dir);
    assert_eq!(run_ok(&d).ran, 36);
    let rows = store_of(&d);
    assert_eq!(rows.len(), 36);
    let mut sets: BTreeMap<String, Vec<&BTreeMap<String, String>>> = BTreeMap::new();
    for r in &rows {
        let (f, c, ..) = parse_key(get(r, "key")).unwrap();
        sets.entry(format!("{f}|{}", c.label()))
            .or_default()
            .push(r);
    }
    assert_eq!(sets.len(), 12);
    let volatile = |c: &str| {
        excluded_c1(c)
            || c.starts_with("rss_")
            || ["key", "rep", "pid", "proc_wall_ms", "run_dir"].contains(&c)
    };
    for (k, v) in &sets {
        let reps: BTreeSet<&str> = v.iter().map(|r| get(r, "rep")).collect();
        assert_eq!(
            reps,
            ["0", "1", "2"].into_iter().collect(),
            "conformance: {k}"
        );
        for r in &v[1..] {
            for (c, x) in v[0].iter() {
                if !volatile(c) {
                    assert_eq!(
                        get(r, c),
                        x.as_str(),
                        "conformance: c04 {k}: {c} differs across reps"
                    );
                }
            }
        }
    }
    // Second invocations add nothing.
    let s = run_ok(&d);
    assert_eq!((s.ran, s.skipped_present), (0, 36));
    let s = run_ok(&real_driver(x0_spec(), specs.clone(), &dir));
    assert_eq!((s.ran, s.skipped_present), (0, 12));
    let runs = fs::read_dir(dir.join("runs")).unwrap().count();
    assert_eq!(runs, 36, "conformance: one run directory per row run");
    // X0b after X0: only its own key runs.
    let s = run_ok(&real_driver(x0b_spec(), specs.clone(), &dir));
    assert_eq!((s.ran, s.skipped_present), (1, 2));
    // The other order in a second store.
    let dir2 = fresh("c04-reps-order");
    assert_eq!(
        run_ok(&real_driver(x0b_spec(), specs.clone(), &dir2)).ran,
        3
    );
    assert_eq!(
        run_ok(&real_driver(x0_spec(), specs.clone(), &dir2)).ran,
        10
    );
    let names = [x0_spec(), x0b_spec()];
    for store_dir in [&dir, &dir2] {
        let rows = store_of(&real_driver(x0_spec(), specs.clone(), store_dir));
        for r in x0b_spec().rows {
            let k = r.key(profile_name());
            assert_eq!(rows.iter().filter(|x| get(x, "key") == k).count(), 1);
            let got = experiments_of(&k, &names, profile_name()).join(",");
            let want = if r.fixture == "ex:naive/k2/enc2" {
                "X0b"
            } else {
                "X0,X0b"
            };
            assert_eq!(got, want);
        }
    }
    // A truncated last line (`X0b`'s own row, appended last): dropped, its
    // key rerun, nothing else.
    let path = d.store_path();
    let text = fs::read_to_string(&path).unwrap();
    let last = text.lines().last().unwrap().to_owned();
    let last_key = parse_csv_line(&last).unwrap()[0].clone();
    assert!(
        last_key.starts_with("ex:naive/k2/enc2|"),
        "conformance: {last_key}"
    );
    fs::write(&path, &text[..text.len() - last.len() / 2 - 1]).unwrap();
    let before = data_lines(&path);
    let s = run_ok(&real_driver(x0b_spec(), specs.clone(), &dir));
    assert_eq!((s.ran, s.skipped_present), (1, 2));
    assert_eq!(data_lines(&path), before);
    let rows = store_of(&d);
    assert_eq!(rows.len(), 37);
    assert_eq!(rows.iter().filter(|r| get(r, "key") == last_key).count(), 1);
}

const T2: u64 = 2000;

fn sleeper_rows(t: &Tier) -> Vec<RowSpec> {
    (0..3)
        .map(|rep| {
            row_spec(
                "eval/sleeper",
                GridConfig::new(GridEngine::Stateful),
                rep,
                t,
                RunKind::Timed,
            )
        })
        .collect()
}

/// The two-size series: `eval/series/slow/k{1,2}` (sleeping on reps ≥ 1) and
/// `eval/series/fast/k{1,2}` (no sleep), each scope built by `Series::of`
/// (H5's scope; round 01 m1). The driver orders `fast` before `slow`, which
/// the rules do not depend on.
fn series_rows(t: &Tier) -> Vec<RowSpec> {
    let mut v = Vec::new();
    for fam in ["eval/series/slow", "eval/series/fast"] {
        for size in 1..=2 {
            for rep in 0..3 {
                let c = GridConfig::new(GridEngine::Stateful);
                let mut r = row_spec(&format!("{fam}/k{size}"), c.clone(), rep, t, RunKind::Timed);
                r.family = fam.to_owned();
                r.k = [Some(size), None, None, None];
                r.knobs = format!("k={size}");
                r.series = Some(Series::of(fam, "k=*", &c, t, RunKind::Timed, size));
                v.push(r);
            }
        }
    }
    v
}

fn classes(rows: &[BTreeMap<String, String>], fixture: &str) -> Vec<String> {
    let mut v: Vec<(u32, String)> = rows
        .iter()
        .filter(|r| get(r, "fixture") == fixture)
        .map(|r| {
            (
                get(r, "rep").parse().unwrap(),
                get(r, "end_class").to_owned(),
            )
        })
        .collect();
    v.sort();
    v.into_iter().map(|(_, c)| c).collect()
}

/// **Criterion 4, rules (1)–(4)** (H5): with a 2 s tier, `eval/sleeper` gives
/// rep 0 `ok`, rep 1 `capped_wall`, rep 2 `skipped_rep` (written, never run);
/// `mixed` is true; counters come from the first completed rep (rule 3, at
/// read time) and no median is formed (rule 4: the set is incomplete). On
/// the two-size series the censored scope's size 2 is written
/// `skipped_after_censor` (3 rows) and the survivors complete both sizes. A
/// second invocation runs nothing.
///
/// Measured runtime: 4.1 s test profile (gate 3).
#[test]
#[ignore]
fn c04_rules_one_to_four_on_the_sleeper_and_a_series() {
    let dir = fresh("c04-rules");
    let t = tier("t2s", T2, FOUR_GIB_KB);
    let mut rows = sleeper_rows(&t);
    rows.extend(series_rows(&t));
    let s = spec("C4r", rows);
    let d = real_driver(s.clone(), vec![s.clone()], &dir);
    let sum = run_ok(&d);
    let rows = store_of(&d);
    assert_eq!(
        classes(&rows, "eval/sleeper"),
        ["ok", "capped_wall", "skipped_rep"],
        "conformance: rule (1)"
    );
    assert_eq!(
        classes(&rows, "eval/series/slow/k1"),
        ["ok", "capped_wall", "skipped_rep"]
    );
    assert_eq!(
        classes(&rows, "eval/series/slow/k2"),
        [
            "skipped_after_censor",
            "skipped_after_censor",
            "skipped_after_censor"
        ],
        "conformance: rule (2)"
    );
    for f in ["eval/series/fast/k1", "eval/series/fast/k2"] {
        assert_eq!(
            classes(&rows, f),
            ["ok", "ok", "ok"],
            "conformance: survivors {f}"
        );
    }
    assert_eq!(
        (
            sum.ran,
            sum.skipped_rep,
            sum.skipped_after_censor,
            sum.censored
        ),
        (10, 2, 3, 2)
    );
    for r in rows
        .iter()
        .filter(|r| get(r, "end_class").starts_with("skipped"))
    {
        assert_eq!(
            (
                get(r, "censored"),
                get(r, "pid"),
                get(r, "proc_wall_ms"),
                get(r, "executions"),
                get(r, "cap_ms")
            ),
            ("false", "", "", "", ""),
            "conformance: a skipped row is written without running"
        );
    }
    let sleeper = sleeper_rows(&t);
    assert!(mixed_of(&rows, &sleeper[0].rep_set()), "conformance: mixed");
    let fast = series_rows(&t)
        .into_iter()
        .find(|r| r.fixture == "eval/series/fast/k1")
        .unwrap();
    assert!(!mixed_of(&rows, &fast.rep_set()));
    // Rule (3): counters from the first completed rep; rule (4): no median.
    let set: Vec<&BTreeMap<String, String>> = rows
        .iter()
        .filter(|r| get(r, "fixture") == "eval/sleeper")
        .collect();
    let first_ok = set.iter().find(|r| get(r, "end_class") == "ok").unwrap();
    assert_eq!(get(first_ok, "rep"), "0");
    assert!(!get(first_ok, "executions").is_empty());
    let complete = set.iter().filter(|r| get(r, "end_class") == "ok").count();
    assert!(complete < 3, "conformance: rule (4) forms no median here");
    // A second invocation runs nothing.
    let runs = fs::read_dir(dir.join("runs")).unwrap().count();
    let again = run_ok(&d);
    assert_eq!(
        (
            again.ran,
            again.skipped_rep,
            again.skipped_after_censor,
            again.skipped_present
        ),
        (0, 0, 0, 15)
    );
    assert_eq!(fs::read_dir(dir.join("runs")).unwrap().count(), runs);
    assert_eq!(store_of(&d).len(), 15);
}

/// **Fixed in the gate-3 follow-up** (`eval.rs` `a4f36b81…`); kept as a
/// regression test. **T-finding T3** (H5 rules (1)–(2) across invocations). The driver
/// rebuilds its censored sets from **this** invocation's runs only, never
/// from the store. A driver killed after appending a censored row and before
/// writing the `skipped_*` rows is simulated by removing those rows; the
/// resume must write them without running anything. Two scopes: the sleeper
/// (o, c, s) and a series whose size 1 is censored at its last rep (o, o, c)
/// with size 2 `skipped_after_censor` ×3. Expected: `ran = 0`, sleeper rep 2
/// `skipped_rep`, late size 2 `skipped_after_censor` ×3. Measured (gate 3,
/// test profile): `ran = 4` — sleeper rep 2 is **run** (`capped_wall`, a
/// second censored rep: 2 s here, 600 s under the default tier) and the late
/// series' size 2 is **run** (`ok, ok, capped_wall`), rule (2) lost.
///
/// Measured runtime: 8.1 s (gate 3).
#[test]
#[ignore]
fn t3_a_resumed_driver_forgets_rules_one_and_two() {
    let dir = fresh("t3-resume");
    let t = tier("t2s", T2, FOUR_GIB_KB);
    let mut rows = sleeper_rows(&t);
    for size in 1..=2 {
        for rep in 0..3 {
            let c = GridConfig::new(GridEngine::Stateful);
            let series = Series::of("eval/series/late", "k=*", &c, &t, RunKind::Timed, size);
            let mut r = row_spec(
                &format!("eval/series/late/k{size}"),
                c,
                rep,
                &t,
                RunKind::Timed,
            );
            r.k = [Some(size), None, None, None];
            r.series = Some(series);
            rows.push(r);
        }
    }
    let s = spec("T3", rows);
    let d = real_driver(s.clone(), vec![s], &dir);
    run_ok(&d);
    let first = store_of(&d);
    assert_eq!(
        classes(&first, "eval/sleeper"),
        ["ok", "capped_wall", "skipped_rep"]
    );
    assert_eq!(
        classes(&first, "eval/series/late/k1"),
        ["ok", "ok", "capped_wall"]
    );
    assert_eq!(
        classes(&first, "eval/series/late/k2"),
        [
            "skipped_after_censor",
            "skipped_after_censor",
            "skipped_after_censor"
        ]
    );
    let path = d.store_path();
    let text = fs::read_to_string(&path).unwrap();
    let kept: Vec<&str> = text
        .lines()
        .filter(|l| !l.contains("\"skipped_rep\"") && !l.contains("\"skipped_after_censor\""))
        .collect();
    fs::write(&path, kept.join("\n") + "\n").unwrap();
    let again = run_ok(&d);
    let rows = store_of(&d);
    let got = (
        again.ran,
        classes(&rows, "eval/sleeper"),
        classes(&rows, "eval/series/late/k2"),
    );
    note!("t3: measured {got:?}");
    assert_eq!(
        got,
        (
            0,
            vec![
                "ok".to_owned(),
                "capped_wall".to_owned(),
                "skipped_rep".to_owned()
            ],
            vec!["skipped_after_censor".to_owned(); 3]
        ),
        "conformance: T3"
    );
}

/// **Fixed in the gate-3 follow-up** (`eval.rs` `a4f36b81…`); kept as a
/// regression test. **T-finding T2** (H2: "the driver parses from the sentinel prefix"). The
/// driver looks for `EVALROW\t` at the **start** of a stdout line, but
/// libtest under `--nocapture` prints `test conformance::eval::eval_row ... `
/// without a newline before the test body runs, so the sentinel lands on a
/// line of its own only when the engine happened to print something first
/// (TraceForge's progress line, or its panic hook's thread name). A row
/// whose run prints nothing — here `run_grid`'s own `Flat` refusal, which the
/// copy keeps (round 03 n8) and which returns before any engine runs — is
/// lost. Expected: `end_class = panicked` with the refusal payload (as
/// `run_grid` gives in process). Measured: `crashed(status 0)`, payload
/// `crashed: status 0`.
///
/// Measured runtime: 0.07 s (gate 3).
#[test]
#[ignore]
fn t2_a_row_that_prints_nothing_loses_its_sentinel() {
    let dir = fresh("t2-sentinel");
    let c = GridConfig::new(GridEngine::Enumerator).cover(CompletionCover::Flat);
    let r = row_spec(
        "ex:naive/k2/enc1",
        c,
        0,
        &Tier::default_tier(),
        RunKind::Timed,
    );
    let in_process = child_row(&r, "c").unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    assert_eq!(cell(&in_process, "end_class"), Some("panicked"));
    let s = spec("T2", vec![r]);
    let d = real_driver(s.clone(), vec![s], &dir);
    run_ok(&d);
    let rows = store_of(&d);
    let got = (
        get(&rows[0], "end_class").to_owned(),
        get(&rows[0], "payload").to_owned(),
    );
    assert_eq!(
        got.0, "panicked",
        "conformance: T2: the driver classified the row {got:?}"
    );
}

/// **Fixed in the gate-3 follow-up** (`eval.rs` `a4f36b81…`); kept as a
/// regression test. **T-finding T7** (H2: "restricting by `EVAL_ONLY=<glob>` on row keys").
/// `Driver.only` is a **substring** filter (`key.contains(only)`), so a glob
/// selects nothing. Expected: `EVAL_ONLY=*|Stateful/*` runs `X0`'s three
/// stateful rows. Measured: `ran = 0`, no row written, no refusal.
///
/// Measured runtime: 0.02 s (gate 3).
#[test]
#[ignore]
fn t7_eval_only_is_a_glob() {
    let dir = fresh("t7-only");
    let mut d = real_driver(x0_spec(), vec![x0_spec()], &dir);
    d.only = Some("*|Stateful/*".to_owned());
    let s = run_ok(&d);
    assert_eq!(
        (s.ran, s.skipped_present),
        (3, 0),
        "conformance: T7: the glob selected {} rows",
        s.ran
    );
}

/// **Criterion 4, the dirty-tree refusal through the real git probe** (the
/// gate-3 tree is dirty): without `allow_mixed` the driver refuses with
/// `Refusal::Dirty("<HEAD>+dirty")` and writes nothing. Not a process test,
/// but it shells out to `git`, so it is `#[ignore]`d with the others.
///
/// Measured runtime: 0.01 s (gate 3).
#[test]
#[ignore]
fn c04_the_real_tree_is_dirty_and_refuses() {
    let dir = fresh("c04-dirty");
    let d = driver_with(
        x0_spec(),
        vec![x0_spec()],
        &dir,
        Duration::from_millis(100),
        Probes::real(),
    );
    match d.run() {
        Err(Refusal::Dirty(c)) => assert!(
            c.ends_with("+dirty") && c.len() == 40 + 6,
            "conformance: {c}"
        ),
        other => panic!("conformance: {:?}", other.map(|s| s.ran)),
    }
    assert!(!d.store_path().exists());
}

/// The default subset of Part 6 (`grid_tests.rs::default_fixtures` and
/// `all_configs`, copied): `ex:naive` k 2–3 (three encodings), the paper
/// pairs, `corpus(7, 3)`; 16 configurations under each of three selectors.
fn default_subset_spec() -> Spec {
    let mut fixtures = Vec::new();
    for k in 2..=3 {
        fixtures.push(naive_fixture(k, 1).name);
        fixtures.push(naive_fixture(k, 2).name);
        fixtures.push(naive_e2_fixture(k).name);
    }
    fixtures.extend(paper_fixtures().into_iter().map(|f| f.name));
    fixtures.extend(corpus_fixtures(7, 3).into_iter().map(|f| f.name));
    let policies = [
        GatePolicy::Never,
        GatePolicy::Always,
        GatePolicy::Budget(1),
        GatePolicy::Budget(2),
    ];
    let mut configs = Vec::new();
    for s in [Selector::Ltr, Selector::FewestEvents, Selector::Reverse] {
        let base = GridConfig::new(GridEngine::Enumerator)
            .selector(s)
            .budget(Budget::Unlimited);
        configs.push(base.clone().memo(true));
        configs.push(base.clone().memo(true).stop(true));
        configs.push(base.memo(false));
        configs.push(GridConfig::new(GridEngine::Stateful).selector(s));
        configs.push(GridConfig::new(GridEngine::Stateful).selector(s).stop(true));
        configs.push(GridConfig::new(GridEngine::CompleteFirst).selector(s));
        configs.push(
            GridConfig::new(GridEngine::CompleteFirst)
                .selector(s)
                .stop(true),
        );
        for p in policies {
            configs.push(
                GridConfig::new(GridEngine::Gated)
                    .selector(s)
                    .gated(GatedMode::Exhaustive, p),
            );
        }
        configs.push(
            GridConfig::new(GridEngine::Gated)
                .selector(s)
                .gated(GatedMode::Exhaustive, GatePolicy::Always)
                .stop(true),
        );
        for p in policies {
            configs.push(
                GridConfig::new(GridEngine::Gated)
                    .selector(s)
                    .gated(GatedMode::FirstFailure, p),
            );
        }
    }
    let t = Tier::default_tier();
    let mut rows = Vec::new();
    for f in &fixtures {
        for c in &configs {
            rows.push(row_spec(f, c.clone(), 0, &t, RunKind::Contract));
        }
    }
    spec("C5", rows)
}

/// **Criterion 5, Part 6's default-subset rows in the test profile**
/// (`run_kind = contract`, into the main store `rows-test.csv`): every row
/// `ok` and equal, column by column (criterion 1's exclusions), to Part 6's
/// table row for the same settings. Test profile only.
///
/// Measured runtime: 14.9 s test profile (2 064 children) (gate 3).
#[test]
#[ignore]
fn c05_part6_default_subset_as_contract_rows() {
    assert_eq!(
        profile_name(),
        "test",
        "conformance: c05 runs in the test profile"
    );
    let s = default_subset_spec();
    let d = real_driver(s.clone(), vec![s.clone()], &out_root());
    let sum = run_ok(&d);
    let part6 = part6_grid_rows();
    let keys: BTreeSet<String> = s.rows.iter().map(|r| r.key("test")).collect();
    let rows: Vec<_> = store_of(&d)
        .into_iter()
        .filter(|r| keys.contains(get(r, "key")))
        .collect();
    assert_eq!(rows.len(), s.rows.len());
    let (mut cells, mut bad, mut no_part6, mut absent) =
        (0, Vec::new(), Vec::new(), BTreeSet::new());
    for r in &rows {
        assert_eq!(get(r, "end_class"), "ok", "conformance: {}", get(r, "key"));
        let key = settings_key(|c| get(r, c).to_owned());
        match part6.get(&key) {
            None => no_part6.push(key),
            Some(w) => {
                let (n, b, a) = compare_to_part6(r, w);
                cells += n;
                bad.extend(b.into_iter().map(|x| format!("{key}: {x}")));
                absent.extend(a);
            }
        }
    }
    note!(
        "c05: ran {}, present {}; {} rows, {} cells compared, {} rows without a Part 6 row, Part 6 columns absent (T1): {absent:?}",
        sum.ran,
        sum.skipped_present,
        rows.len(),
        cells,
        no_part6.len()
    );
    assert!(no_part6.is_empty(), "conformance: c05 {no_part6:?}");
    assert!(absent.is_empty(), "conformance: c05 absent: {absent:?}");
    assert!(
        bad.is_empty(),
        "conformance: c05 {} mismatches: {bad:?}",
        bad.len()
    );
}

/// **Criterion 6**: `X0` rows of the two profiles' main stores (`rows.csv`
/// release, `rows-test.csv` test — written by the H9 command) agree on every
/// column but criterion 1's exclusions and the per-run columns; the release
/// `wall_ms` is printed beside the test-profile one, labelled.
///
/// Measured runtime: 0.07 s (reads the two stores) (gate 3).
#[test]
#[ignore]
fn c06_x0_under_both_profiles() {
    let rel = read_rows(&out_root().join("rows.csv"))
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let tst = read_rows(&out_root().join("rows-test.csv"))
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let x0 = x0_spec();
    let mut lines = vec![
        "| X0 row (fixture ex:naive/k2/enc1) | wall_ms release | wall_ms test | proc_wall_ms release | proc_wall_ms test |".to_owned(),
        "|---|---|---|---|---|".to_owned(),
    ];
    for r in &x0.rows {
        let a = rel
            .iter()
            .find(|x| get(x, "key") == r.key("release"))
            .expect("conformance: a release X0 row");
        let b = tst
            .iter()
            .find(|x| get(x, "key") == r.key("test"))
            .expect("conformance: a test X0 row");
        for (c, v) in a {
            if excluded_c1(c)
                || c.starts_with("rss_")
                || ["key", "profile", "pid", "commit", "run_dir"].contains(&c.as_str())
            {
                continue;
            }
            assert_eq!(
                get(b, c),
                v.as_str(),
                "conformance: c06 {} {c}",
                r.config.label()
            );
        }
        assert_eq!((get(a, "profile"), get(b, "profile")), ("release", "test"));
        lines.push(format!(
            "| {} | {} | {} | {} | {} |",
            r.config.label(),
            get(a, "wall_ms"),
            get(b, "wall_ms"),
            get(a, "proc_wall_ms"),
            get(b, "proc_wall_ms")
        ));
    }
    let table = lines.join("\n");
    fs::write(out_root().join("c06-x0-profiles.md"), format!("{table}\n")).unwrap();
    note!("{table}");
}

// --- criterion 7 ----------------------------------------------------------

/// The baseline keys of criterion 7 (P4-DIFF criterion 7) and their timed
/// twins (uninstrumented, three reps).
fn baseline_spec() -> Spec {
    let t = Tier::default_tier();
    let f63 = || GridConfig::new(GridEngine::Enumerator).budget(Budget::Exact(10_000));
    let unl = || GridConfig::new(GridEngine::Enumerator).budget(Budget::Unlimited);
    let mut base: Vec<(String, GridConfig)> = vec![
        ("ndk2/conf".into(), f63().instrumented(true)),
        ("ndk3/bad_A".into(), f63().instrumented(true)),
        ("ndk3/bad_A".into(), f63()),
        ("ndk2/conf".into(), unl()),
        ("ndk3/conf".into(), unl()),
        ("ndk3/bad_A".into(), unl()),
        (
            "ndk3/bad_A".into(),
            GridConfig::new(GridEngine::Enumerator).budget(Budget::Exact(12_081)),
        ),
        (
            "ndk3/bad_A".into(),
            GridConfig::new(GridEngine::Enumerator).budget(Budget::Exact(12_082)),
        ),
    ];
    for f in two_pc_fixtures(4) {
        let tr = f.table.clone().expect("conformance: a 2PC row");
        let c = if tr.entry == TableEntry::VerifyStopTriage {
            GridConfig::new(GridEngine::Verify)
                .stop(true)
                .budget(Budget::Exact(tr.budget))
                .precheck(true)
        } else {
            GridConfig::new(GridEngine::Enumerator).budget(Budget::Exact(tr.budget))
        };
        base.push((f.name.clone(), c));
    }
    assert_eq!(base.len(), 8 + 17);
    let mut rows = Vec::new();
    let mut timed = BTreeSet::new();
    for (f, c) in &base {
        rows.push(row_spec(f, c.clone(), 0, &t, RunKind::Baseline));
        let tc = c.clone().instrumented(false);
        if timed.insert((f.clone(), tc.label())) {
            for rep in 0..3 {
                rows.push(row_spec(f, tc.clone(), rep, &t, RunKind::Timed));
            }
        }
    }
    spec("X7t", rows)
}

/// `per_cover_detail` → per Cover `(extend, rebuild, distinct, per_attempt,
/// f63)`.
type CoverFig = (usize, usize, usize, [usize; 2], [usize; 2]);

fn covers_of(detail: &str) -> Vec<CoverFig> {
    let pair = |s: &str| -> [usize; 2] {
        let v: Vec<usize> = s
            .trim_start_matches('[')
            .trim_end_matches(']')
            .split(", ")
            .map(|x| x.parse().unwrap())
            .collect();
        [v[0], v[1]]
    };
    detail
        .split("; ")
        .filter(|s| !s.is_empty())
        .map(|c| {
            let field = |name: &str| -> &str {
                let i = c
                    .find(&format!("{name}="))
                    .unwrap_or_else(|| panic!("conformance: {name} in {c}"));
                let rest = &c[i + name.len() + 1..];
                if rest.starts_with('[') {
                    &rest[..=rest.find(']').unwrap()]
                } else {
                    rest.split(' ').next().unwrap()
                }
            };
            let calls: Vec<usize> = field("calls")
                .split('/')
                .map(|x| x.parse().unwrap())
                .collect();
            (
                calls[1],
                calls[2],
                field("distinct").parse().unwrap(),
                pair(field("per_attempt")),
                pair(field("f63")),
            )
        })
        .collect()
}

fn median(v: &mut [u64]) -> u64 {
    v.sort_unstable();
    v[v.len() / 2]
}

/// **Criterion 7, baselines under the runner** (release; P4-DIFF criterion 7
/// compare-or-record). F63 arm (`baseline`, instrumented): `ndk2` 0/0, 26
/// covers, 177 nodes, Σ f63 169, Σ canonical 155, run-wide 31, **1.05×**;
/// `bad_A` 15/11, 126 covers, 175 968 nodes, Σ f63 11 160, Σ canonical 5 830,
/// run-wide 322 / 649, per-Cover Σ 5 785, largest (10 000, 536, 267) →
/// 15.77, 18.66, 17.20, 30.18, 18.11, per-Cover 30.4; the uninstrumented
/// twin agrees but for the instrumented-only fields. Unlimited arm: minima
/// 33 / 981 / 12 082, no exhaustion; 12 081 exhausts, 12 082 does not. 2PC:
/// the 17 verdicts (outer graphs: T1, not in the store). Timed medians (3
/// reps) written to `log/eval/c07-medians.md` beside Part 6's and the
/// DEMO-2PC documents' figures.
///
/// Measured runtime: 271 s release (97 children) (gate 3).
#[test]
#[ignore]
fn c07_baselines_under_the_runner() {
    let s = baseline_spec();
    let d = real_driver(s.clone(), vec![s.clone()], &out_root());
    let sum = run_ok(&d);
    let p = profile_name();
    let keys: BTreeSet<String> = s.rows.iter().map(|r| r.key(p)).collect();
    let rows: Vec<_> = store_of(&d)
        .into_iter()
        .filter(|r| keys.contains(get(r, "key")))
        .collect();
    assert_eq!(rows.len(), s.rows.len());
    for r in &rows {
        assert_eq!(get(r, "end_class"), "ok", "conformance: {}", get(r, "key"));
    }
    let find = |f: &str, kind: &str, budget: &str, instr: &str| {
        rows.iter()
            .find(|r| {
                get(r, "fixture") == f
                    && get(r, "run_kind") == kind
                    && get(r, "budget") == budget
                    && get(r, "instrumented") == instr
            })
            .unwrap_or_else(|| panic!("conformance: no {f} {kind} {budget} {instr}"))
    };
    let num = |r: &BTreeMap<String, String>, c: &str| -> usize { get(r, c).parse().unwrap() };
    let ratio = |a: usize, b: usize| a as f64 / b as f64;
    // ndk2, F63 settings.
    let n2 = find("ndk2/conf", "baseline", "Exact(10000)", "true");
    let cv = covers_of(get(n2, "per_cover_detail"));
    let sum_f63: usize = cv.iter().map(|c| c.4[0] + c.4[1]).sum();
    let sum_canon: usize = cv.iter().map(|c| c.3[0] + c.3[1]).sum();
    assert_eq!(
        (
            num(n2, "reports"),
            num(n2, "exhaustions"),
            num(n2, "cover_calls"),
            num(n2, "spec_visit_calls"),
            sum_f63,
            sum_canon,
            num(n2, "distinct_keys_run_wide")
        ),
        (0, 0, 26, 177, 169, 155, 31)
    );
    assert_eq!(format!("{:.2}", ratio(177, sum_f63)), "1.05");
    // bad_A, F63 settings.
    let b = find("ndk3/bad_A", "baseline", "Exact(10000)", "true");
    let cv = covers_of(get(b, "per_cover_detail"));
    assert_eq!(cv.len(), num(b, "per_cover"));
    let mut largest = (0, 0, 0);
    for c in &cv {
        for (i, n) in [c.0, c.1].into_iter().enumerate() {
            if n > largest.0 {
                largest = (n, c.4[i], c.3[i]);
            }
        }
    }
    let nodes = num(b, "spec_visit_calls");
    let sum_f63: usize = cv.iter().map(|c| c.4[0] + c.4[1]).sum();
    let sum_canon: usize = cv.iter().map(|c| c.3[0] + c.3[1]).sum();
    let per_cover: usize = cv.iter().map(|c| c.2).sum();
    let (rw_canon, rw_f63) = (
        num(b, "distinct_keys_run_wide"),
        num(b, "f63_distinct_run_wide"),
    );
    assert_eq!(
        (
            num(b, "reports"),
            num(b, "exhaustions"),
            num(b, "cover_calls"),
            nodes,
            sum_f63,
            sum_canon,
            rw_canon,
            rw_f63,
            per_cover,
            largest
        ),
        (
            15,
            11,
            126,
            175_968,
            11_160,
            5_830,
            322,
            649,
            5_785,
            (10_000, 536, 267)
        )
    );
    let figures = [
        ratio(nodes, sum_f63),
        ratio(largest.0, largest.1),
        ratio(sum_f63, rw_f63),
        ratio(nodes, sum_canon),
        ratio(sum_canon, rw_canon),
    ]
    .map(|x| format!("{x:.2}"));
    assert_eq!(
        figures,
        ["15.77", "18.66", "17.20", "30.18", "18.11"].map(String::from)
    );
    assert_eq!(format!("{:.1}", ratio(nodes, per_cover)), "30.4");
    assert_eq!(get(b, "diag_keys"), (322 + 649).to_string());
    // The uninstrumented twin: equal but for the instrumented-only fields.
    let bt = find("ndk3/bad_A", "baseline", "Exact(10000)", "false");
    let strip =
        |d: &str| -> Vec<(usize, usize)> { covers_of(d).iter().map(|c| (c.0, c.1)).collect() };
    for c in [
        "reports",
        "exhaustions",
        "end",
        "skipped_gates",
        "inert_gates",
        "gate_invocations",
        "gate_skipped_inert",
        "gate_skipped_replay",
        "gate_skipped_pruned",
        "cover_calls",
        "cover_exhaustions",
        "rebuilds_taken",
        "spec_visit_calls",
        "memo_hits",
        "per_cover",
        "executions",
    ] {
        assert_eq!(get(bt, c), get(b, c), "conformance: c07 twin {c}");
    }
    assert_eq!(
        strip(get(bt, "per_cover_detail")),
        strip(get(b, "per_cover_detail"))
    );
    assert_eq!(
        (get(bt, "distinct_keys_run_wide"), get(bt, "diag_keys")),
        ("0", "")
    );
    // The unlimited arm.
    for (f, want) in [
        ("ndk2/conf", 33usize),
        ("ndk3/conf", 981),
        ("ndk3/bad_A", 12_082),
    ] {
        let r = find(f, "baseline", "Unlimited", "false");
        let m = covers_of(get(r, "per_cover_detail"))
            .iter()
            .map(|c| c.0.max(c.1))
            .max()
            .unwrap();
        assert_eq!(
            (m, num(r, "exhaustions")),
            (want, 0),
            "conformance: D-B* {f}"
        );
    }
    assert!(
        num(
            find("ndk3/bad_A", "baseline", "Exact(12081)", "false"),
            "exhaustions"
        ) > 0
    );
    assert_eq!(
        num(
            find("ndk3/bad_A", "baseline", "Exact(12082)", "false"),
            "exhaustions"
        ),
        0
    );
    // 2PC verdicts; the seeded rows' outer graphs recorded (compared, never
    // failed: P4-DIFF criterion 7, round 05 m3).
    let mut outer = Vec::new();
    for f in two_pc_fixtures(4) {
        if let Some(rec) = match f.name.as_str() {
            "2pc/coord/conf/n2" => Some("Some(8)"),
            "2pc/coord/conf/n3" => Some("Some(48)"),
            "2pc/coord/conf/n4" => Some("Some(384)"),
            "2pc/ring/conf/n2" => Some("Some(4)"),
            "2pc/ring/conf/n3" => Some("Some(24)"),
            "2pc/ring/conf/n4" => Some("Some(192)"),
            _ => None,
        } {
            let r = rows
                .iter()
                .find(|r| get(r, "fixture") == f.name && get(r, "run_kind") == "baseline")
                .unwrap();
            outer.push(format!(
                "{}: recorded {rec}, measured {}",
                f.name,
                get(r, "outer_graphs(execs+block)")
            ));
        }
    }
    note!("c07 outer graphs (seeded 2PC rows): {outer:?}");
    for f in two_pc_fixtures(4) {
        let r = rows
            .iter()
            .find(|r| get(r, "fixture") == f.name && get(r, "run_kind") == "baseline")
            .unwrap();
        if f.table.as_ref().unwrap().entry == TableEntry::VerifyStopTriage {
            assert_eq!(get(r, "verdict"), "Reported", "conformance: {}", f.name);
        } else {
            assert_eq!(
                (get(r, "reports"), get(r, "exhaustions")),
                ("0", "0"),
                "conformance: {}",
                f.name
            );
        }
    }
    // Timed medians beside Part 6's and the DEMO-2PC documents' figures.
    let part6_ms: BTreeMap<(&str, &str), &str> = [
        (("ndk2/conf", "Exact(10000)"), "22 (instr.)"),
        (
            ("ndk3/bad_A", "Exact(10000)"),
            "13552 (uninstr.); 17645 (instr.)",
        ),
        (("ndk2/conf", "Unlimited"), "18"),
        (("ndk3/conf", "Unlimited"), "656"),
        (("ndk3/bad_A", "Unlimited"), "11059"),
        (("ndk3/bad_A", "Exact(12081)"), "16798"),
        (("ndk3/bad_A", "Exact(12082)"), "—"),
        (("2pc/coord/conf/n2", ""), "22"),
        (("2pc/coord/conf/n3", ""), "169"),
        (("2pc/coord/conf/n4", ""), "968"),
        (("2pc/coord/eager/n2", ""), "349"),
        (("2pc/coord/eager/n3", ""), "334"),
        (("2pc/coord/eager/n4", ""), "399"),
        (("2pc/leader/conf/n2", ""), "16"),
        (("2pc/leader/conf/n3", ""), "2247"),
        (("2pc/leader/split/n2", ""), "12"),
        (("2pc/leader/split/n3", ""), "22"),
        (("2pc/leader/split/n4", ""), "44"),
        (("2pc/ring/conf/n2", ""), "18"),
        (("2pc/ring/conf/n3", ""), "199"),
        (("2pc/ring/conf/n4", ""), "1250"),
        (("2pc/ring/split/n2", ""), "7"),
        (("2pc/ring/split/n3", ""), "32"),
        (("2pc/ring/split/n4", ""), "58"),
    ]
    .into_iter()
    .collect();
    let demo_s: BTreeMap<&str, &str> = [
        ("2pc/coord/conf/n2", "0.025"),
        ("2pc/coord/conf/n3", "0.142"),
        ("2pc/coord/conf/n4", "0.818"),
        ("2pc/coord/eager/n2", "0.262"),
        ("2pc/coord/eager/n3", "0.262"),
        ("2pc/coord/eager/n4", "0.279"),
        ("2pc/leader/conf/n2", "0.009"),
        ("2pc/leader/conf/n3", "2.034"),
        ("2pc/leader/split/n2", "0.018"),
        ("2pc/leader/split/n3", "0.031"),
        ("2pc/leader/split/n4", "0.038"),
        ("2pc/ring/conf/n2", "0.010"),
        ("2pc/ring/conf/n3", "0.141"),
        ("2pc/ring/conf/n4", "1.128"),
        ("2pc/ring/split/n2", "0.008"),
        ("2pc/ring/split/n3", "0.019"),
        ("2pc/ring/split/n4", "0.033"),
    ]
    .into_iter()
    .collect();
    let mut sets: BTreeMap<(String, String), Vec<&BTreeMap<String, String>>> = BTreeMap::new();
    for r in rows.iter().filter(|r| get(r, "run_kind") == "timed") {
        sets.entry((get(r, "fixture").to_owned(), get(r, "budget").to_owned()))
            .or_default()
            .push(r);
    }
    let mut lines = vec![
        format!("Criterion 7 timed rows, profile `{p}`, commit `{}`, one process per row, 3 reps each. Part 6: in-process `wall_ms`, test profile, `bd793be` + tree (`log/dev/P4-DIFF.tables.md`). DEMO-2PC: seconds as printed at `ae3ab15`, test profile, in-process.", get(&rows[0], "commit")),
        String::new(),
        "| fixture | budget | proc_wall_ms median [min, max] | wall_ms median | Part 6 wall_ms | DEMO-2PC s |".to_owned(),
        "|---|---|---|---|---|---|".to_owned(),
    ];
    for ((f, budget), v) in &sets {
        assert_eq!(v.len(), 3, "conformance: three reps of {f}");
        let mut pw: Vec<u64> = v
            .iter()
            .map(|r| get(r, "proc_wall_ms").parse().unwrap())
            .collect();
        let mut ew: Vec<u64> = v
            .iter()
            .map(|r| get(r, "wall_ms").parse().unwrap())
            .collect();
        let (lo, hi) = (*pw.iter().min().unwrap(), *pw.iter().max().unwrap());
        let two_pc = f.starts_with("2pc/");
        let p6 = part6_ms
            .get(&(f.as_str(), if two_pc { "" } else { budget.as_str() }))
            .copied()
            .unwrap_or("?");
        lines.push(format!(
            "| {f} | {budget} | {} [{lo}, {hi}] | {} | {p6} | {} |",
            median(&mut pw),
            median(&mut ew),
            demo_s.get(f.as_str()).copied().unwrap_or("—")
        ));
    }
    let table = lines.join("\n");
    fs::write(
        out_root().join(format!("c07-medians-{p}.md")),
        format!("{table}\n"),
    )
    .unwrap();
    note!(
        "c07: ran {}, present {}\n{table}",
        sum.ran,
        sum.skipped_present
    );
}
