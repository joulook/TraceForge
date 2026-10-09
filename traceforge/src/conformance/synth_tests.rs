//! `P5-SYNTH` gate 3: the tester's tests (criteria `P5-SYNTH.md` revision 5.1).
//!
//! Tester-owned; the lead created the stub (the module lines in `mod.rs` are
//! the lead's, criterion 10).
//!
//! **How the expectations were made.** Every figure asserted here was derived
//! from the criteria's programs and the engine facts N1–N7 **before** the
//! lead's `P5-SYNTH.expected.md` was read, and recorded in
//! `plan/traceForge/log/dev/P5-SYNTH.derived.md` (sha256 in
//! `backlog/changes.md` before the first run). The figures are formulas in the
//! knobs ([`derived`], [`g5`]); the reconciliation with the lead's
//! expectations is in `P5-SYNTH.report.md`.
//!
//! **Resource rule** (`P5-README.md`). The default subset is the hand-count
//! sizes only ([`hand_count`]), one worker, in process, every engine on the
//! lean path (`eval::run_row_in_process(.., false)`); the stateful oracle keeps
//! its two families (`(.., true)`) — at every pilot size here those are at
//! most 48 graphs (`ex:naive` `k = 4`). Everything larger is `#[ignore]`d and
//! run one test (or one fixture, `SYNTH_FIXTURE`) per process. Nothing goes
//! through `grid::run_grid`.
//!
//! Tests are named by criterion (`c02_…` … `c10_…`); a test reproducing a
//! defect of the lead's code would be `t<N>_…` after its T-finding.
//!
//! Conventions kept because the closed source scans read this file: no print
//! macro anywhere, and every panic-family message starts with `conformance:`.

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use crate::conformance::config::{GatePolicy, GatedMode};
use crate::conformance::ctx::ReportKind;
use crate::conformance::eval::{
    fixture_by_name, key_of, profile_name, read_rows, run_row_in_process, Driver, Probes, RunKind,
    Spec, Tier,
};
use crate::conformance::gated::ReportSite;
use crate::conformance::grid::{
    paper_events_total, registry, row_of, synth_fixtures, synth_grid, Budget, Fixture, GridConfig,
    GridEnd, GridEngine, GridRaw, GridResult, Group, Row, SynthPoint, Tables,
};
use crate::conformance::grid_oracle::{canon_key, certify, thread_named, Cause, Claim, Families};
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::wobs;
use crate::conformance::report::{
    obs_text, ReplaySnapshot, ReportCause, ReportGate, ReportTag, SearchEnd,
};
use crate::conformance::selector::Selector;
use crate::conformance::sig::{covered, Summary};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;

/// Writes a line to stderr (the closed `s5_tests` emission scan forbids the
/// print macros under `conformance/`).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

const SELECTORS: [Selector; 3] = [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];

// =========================================================================
// The derivation as formulas (`P5-SYNTH.derived.md`)
// =========================================================================

fn fact(n: usize) -> usize {
    (1..=n).product()
}

fn pow2(n: usize) -> usize {
    1usize << n
}

/// The derived figures of one fixture: complete Impl and Spec graphs, Spec
/// signatures (stateful's `signatures`), uncovered Impl graphs, and `|W|` on
/// the two sweeping engines where the derivation fixes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Exp {
    imp: usize,
    spec: usize,
    sig: usize,
    unc: usize,
    witnesses: Option<usize>,
}

/// The knob values of a `synth/<family>/<knobs>` or `ex:naive/k{k}/enc{e}`
/// name, in order of appearance.
fn knobs_of(name: &str) -> (String, Vec<usize>) {
    let (family, knobs) = if let Some(rest) = name.strip_prefix("ex:naive/") {
        ("ex:naive".to_owned(), rest.to_owned())
    } else {
        let rest = name
            .strip_prefix("synth/")
            .unwrap_or_else(|| panic!("conformance: `{name}` is not a synthetic name"));
        let (f, k) = rest
            .split_once('/')
            .unwrap_or_else(|| panic!("conformance: `{name}` has no knobs"));
        (f.to_owned(), k.to_owned())
    };
    let mut vals = Vec::new();
    let mut cur = String::new();
    for ch in knobs.chars() {
        if ch.is_ascii_digit() {
            cur.push(ch);
        } else if !cur.is_empty() {
            vals.push(cur.parse().expect("conformance: a knob value"));
            cur.clear();
        }
    }
    if !cur.is_empty() {
        vals.push(cur.parse().expect("conformance: a knob value"));
    }
    (family, vals)
}

/// `derived.md`'s per-family counts.
fn derived(name: &str) -> Exp {
    let (family, v) = knobs_of(name);
    let e = |imp, spec, sig, unc, witnesses| Exp {
        imp,
        spec,
        sig,
        unc,
        witnesses,
    };
    match family.as_str() {
        // `ex:naive`: `c` sends 0 against 1 — every Impl graph uncovered;
        // one signature (the graphs differ in rf only).
        "ex:naive" => e(fact(v[0]), fact(v[0]), 1, fact(v[0]), None),
        // T3 (my derivation corrected): the `k!` graphs share one word but
        // differ in `vo` (`b_{π(j)}.s < c.r_j`); `ord(M) ⊆ ord(G)` forces
        // `σ = π`, so every graph needs its own witness: `|W| = k!`.
        "naive-self" => e(fact(v[0]), fact(v[0]), 1, 0, Some(fact(v[0]))),
        "share" => e(pow2(v[1]), 1, 1, 0, Some(1)),
        "share-ctl" => e(pow2(v[1]), pow2(v[1]), pow2(v[1]), 0, Some(pow2(v[1]))),
        "commit" => e(pow2(v[0]), pow2(v[0]), pow2(v[0]), 0, Some(pow2(v[0]))),
        "chain" => e(1, 1, 1, 0, Some(1)),
        "reset" | "reset-ctl" => e(pow2(v[0]), fact(v[1]), 1, pow2(v[0]) - 1, Some(1)),
        "reset-twin" => e(fact(v[1]), fact(v[1]), 1, 0, Some(1)),
        "width" => e(v[0], v[0], v[0], 0, Some(v[0])),
        _ => panic!("conformance: no derivation for `{name}`"),
    }
}

/// Criterion 4's list: the smallest sizes of the criteria table, every
/// family, control and twin (rebuilt from the criteria's text).
fn pilot_names() -> Vec<String> {
    let mut out = Vec::new();
    for k in 2..=4 {
        for e in 1..=2 {
            out.push(format!("ex:naive/k{k}/enc{e}"));
            out.push(format!("synth/naive-self/k{k}enc{e}"));
        }
    }
    for m in [2, 4] {
        for c in [0, m / 2, m] {
            out.push(format!("synth/share/m{m}c{c}"));
            out.push(format!("synth/share-ctl/m{m}c{c}"));
        }
    }
    for n in [2, 4] {
        for j in [0, n / 2, n] {
            out.push(format!("synth/commit/n{n}j{j}"));
        }
    }
    for d in [2, 8, 32] {
        out.push(format!("synth/chain/d{d}"));
    }
    for (k, s) in [(1, 1), (2, 1), (3, 1), (1, 2), (2, 3)] {
        for f in ["reset", "reset-ctl", "reset-twin"] {
            out.push(format!("synth/{f}/k{k}s{s}"));
        }
    }
    for w in [2, 8, 32] {
        out.push(format!("synth/width/w{w}"));
    }
    out
}

/// The hand-count sizes (the default subset): each family's smallest point,
/// S5 at `k ≤ 2` with `s = 1` and the pad's `(1, 2)`.
fn hand_count(name: &str) -> bool {
    let (family, v) = knobs_of(name);
    match family.as_str() {
        "ex:naive" | "naive-self" => v[0] == 2,
        "share" | "share-ctl" => v[0] == 2,
        "commit" => v[0] == 2,
        "chain" | "width" => v[0] == 2,
        "reset" | "reset-ctl" | "reset-twin" => matches!((v[0], v[1]), (1, 1) | (2, 1) | (1, 2)),
        _ => false,
    }
}

// =========================================================================
// Harness (copied in shape from `apps_tests.rs`, P5-APPS gate 3)
// =========================================================================

fn fx(name: &str) -> Fixture {
    fixture_by_name(name).unwrap_or_else(|e| panic!("conformance: `{name}`: {}", e.text()))
}

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

/// One engine run on the lean path (`keep_graphs = false`).
fn grun(f: &Fixture, c: &GridConfig) -> GridResult {
    ok(run_row_in_process(f, c, false))
}

fn cell<'a>(row: &'a Row, k: &str) -> &'a str {
    row.iter()
        .find(|(c, _)| *c == k)
        .map(|(_, v)| v.as_str())
        .unwrap_or_else(|| panic!("conformance: the row has no column `{k}`"))
}

fn num(row: &Row, k: &str) -> usize {
    cell(row, k).parse().unwrap_or_else(|_| {
        panic!(
            "conformance: column `{k}` = `{}` is not a count",
            cell(row, k)
        )
    })
}

fn sizes(v: &[usize]) -> String {
    format!("{v:?}")
}

/// The pilot's configurations under one selector (criterion 4): the
/// enumerator at `Budget::Unlimited` with the memo on (the contract's row),
/// stateful, complete-first, gated `Exhaustive`/`Always`.
fn engines(s: Selector) -> [GridConfig; 4] {
    [
        GridConfig::new(GridEngine::Enumerator)
            .selector(s)
            .budget(Budget::Unlimited)
            .memo(true),
        GridConfig::new(GridEngine::Stateful).selector(s),
        GridConfig::new(GridEngine::CompleteFirst).selector(s),
        gated_cfg(s),
    ]
}

fn gated_cfg(s: Selector) -> GridConfig {
    GridConfig::new(GridEngine::Gated)
        .selector(s)
        .gated(GatedMode::Exhaustive, GatePolicy::Always)
}

fn cf_cfg(s: Selector) -> GridConfig {
    GridConfig::new(GridEngine::CompleteFirst).selector(s)
}

/// One report of a grid run, engine-independently (`apps_tests.rs`).
struct Rep<'a> {
    graph: &'a ExecutionGraph,
    tag: ReportTag,
    cause: Cause,
    serialized: bool,
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
                Rep {
                    graph: &rep.graph,
                    tag: ReportTag::of(&rc, ReportGate::of(rep.gate)),
                    cause,
                    serialized: serialized(&rep.replay),
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
                    }
                })
                .collect();
            v.extend(o.reports.iter().map(|(g, s)| Rep {
                graph: g,
                tag: ReportTag::CompleteCoverage,
                cause: Cause::NoCover,
                serialized: serialized(s),
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
            })
            .collect(),
        GridRaw::Verdict(_) => Vec::new(),
    }
}

/// What the contract reads of a run.
struct St {
    reports: usize,
    exhaustions: usize,
    end: SearchEnd,
    failure: Option<String>,
}

fn st(r: &GridResult) -> St {
    match &r.raw {
        GridRaw::Enumerator(o) => St {
            reports: o.reports.len(),
            exhaustions: o.exhaustions.len(),
            end: o.end,
            failure: o
                .spec_error
                .as_ref()
                .map(|(t, e)| format!("spec_error on `{t}` at {e}")),
        },
        GridRaw::Stateful(o) => St {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (!o.spec_errors.is_empty()).then(|| format!("{:?}", o.spec_errors)),
        },
        GridRaw::CompleteFirst(o) => St {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (o.aborted || !o.spec_errors.is_empty())
                .then(|| format!("aborted={} {:?}", o.aborted, o.spec_errors)),
        },
        GridRaw::Gated(o) => St {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (o.aborted || !o.spec_errors.is_empty())
                .then(|| format!("aborted={} {:?}", o.aborted, o.spec_errors)),
        },
        GridRaw::Verdict(_) => St {
            reports: 0,
            exhaustions: 0,
            end: SearchEnd::Unknown,
            failure: Some("a Verdict route in the pilot".to_owned()),
        },
    }
}

/// The oracle run (stateful, report-and-continue, `Ltr`, families kept).
struct Oracle {
    imp: Vec<ExecutionGraph>,
    spec: Vec<ExecutionGraph>,
    families: Families,
    row: Row,
}

fn oracle(f: &Fixture) -> Oracle {
    let r = ok(run_row_in_process(
        f,
        &GridConfig::new(GridEngine::Stateful),
        true,
    ));
    let row = row_of(&r);
    let GridRaw::Stateful(o) = r.raw else {
        unreachable!("conformance: the oracle run is stateful")
    };
    assert!(
        o.spec_errors.is_empty(),
        "conformance: `{}`: Spec errors {:?}",
        f.name,
        o.spec_errors
    );
    assert_eq!(
        (o.impl_end, o.spec_end),
        (
            SearchEnd::StateSpaceExhausted,
            SearchEnd::StateSpaceExhausted
        ),
        "conformance: `{}`: the oracle run is not exhaustive",
        f.name
    );
    let families = Families::new(&o.kept_spec_graphs, &o.kept_impl_graphs, 0, &f.visible);
    Oracle {
        imp: o.kept_impl_graphs,
        spec: o.kept_spec_graphs,
        families,
        row,
    }
}

// =========================================================================
// Reading programs off graphs (criterion 2's conventions, observed)
// =========================================================================

fn tname(g: &ExecutionGraph, t: crate::thread::ThreadId) -> String {
    g.get_thread_tclab(t)
        .name()
        .clone()
        .unwrap_or_else(|| "main".to_owned())
}

/// Thread names in spawn order (`ThreadId` order), `main` dropped.
fn spawn_order(g: &ExecutionGraph) -> Vec<String> {
    g.thread_ids()
        .into_iter()
        .skip(1)
        .map(|t| tname(g, t))
        .collect()
}

fn int(v: &crate::msg::Val) -> i32 {
    *v.as_any_ref()
        .downcast_ref::<i32>()
        .expect("conformance: every synthetic message is an i32")
}

/// The communication shape of thread `name` in `g`: `S<v>` a send of `v`;
/// `R<t:v>` a blocking receive reading `v` from `t`; `N<t:v>` / `N<⊥` a
/// non-blocking receive; `C<a..=b>=x` a `Choice`; `T` a `CToss`. Begin, End,
/// spawns and the rest are dropped.
fn shape(g: &ExecutionGraph, name: &str) -> Vec<String> {
    let t = thread_named(g, name);
    let mut out = Vec::new();
    for i in 0..g.thread_size(t) {
        let e = Event::new(t, i as u32);
        match g.label(e) {
            LabelEnum::SendMsg(s) => out.push(format!("S{}", int(s.val()))),
            LabelEnum::RecvMsg(r) => {
                let k = if r.is_non_blocking() { "N" } else { "R" };
                match r.rf() {
                    Some(rf) => out.push(format!(
                        "{k}<{}:{}",
                        tname(g, rf.thread),
                        int(g.val(e).expect("conformance: a read value"))
                    )),
                    None => out.push(format!("{k}<\u{22a5}")),
                }
            }
            LabelEnum::Choice(c) => out.push(format!(
                "C<{}..={}>={}",
                c.range().start(),
                c.range().end(),
                c.result()
            )),
            LabelEnum::CToss(_) => out.push("T".to_owned()),
            _ => {}
        }
    }
    out
}

fn shapes(gs: &[ExecutionGraph], name: &str) -> BTreeSet<Vec<String>> {
    gs.iter().map(|g| shape(g, name)).collect()
}

fn set(xs: &[&[&str]]) -> BTreeSet<Vec<String>> {
    xs.iter()
        .map(|x| x.iter().map(|s| (*s).to_owned()).collect())
        .collect()
}

fn owned(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|s| (*s).to_owned()).collect()
}

fn same_order_everywhere(gs: &[ExecutionGraph], want: &[String], what: &str) {
    assert!(!gs.is_empty(), "conformance: {what}: no graph");
    for g in gs {
        assert_eq!(&spawn_order(g), want, "conformance: {what}: spawn order");
    }
}

/// The visible projection of a complete graph: every visible thread's word.
fn projection(g: &ExecutionGraph, vis: &[String]) -> Vec<(String, Vec<String>)> {
    let w = wobs(g, vis).unwrap_or_else(|e| panic!("conformance: no words: {e:?}"));
    let mut out: Vec<(String, Vec<String>)> = vis
        .iter()
        .map(|n| {
            (
                n.clone(),
                w.of(n).iter().map(|(_, o)| obs_text(o)).collect(),
            )
        })
        .collect();
    out.sort();
    out
}

fn summary(g: &ExecutionGraph, vis: &[String]) -> Summary {
    let w = wobs(g, vis).unwrap_or_else(|e| panic!("conformance: no words: {e:?}"));
    Summary::of(CompleteExecution::assume_finished_at_gate(g), &w, vis)
        .unwrap_or_else(|e| panic!("conformance: no summary: {e:?}"))
}

/// **N6's offline minimal-basis size**: the minimum number of Spec graphs
/// covering every Impl graph under `covered` (`lem:sig`), exact by exhaustive
/// subset search (Spec family ≤ 20 graphs); `None` when some Impl graph is
/// covered by no Spec graph.
fn min_basis(imp: &[ExecutionGraph], spec: &[ExecutionGraph], vis: &[String]) -> Option<usize> {
    assert!(spec.len() <= 20, "conformance: min_basis is exhaustive");
    let ss: Vec<Summary> = spec.iter().map(|g| summary(g, vis)).collect();
    let masks: Vec<u32> = imp
        .iter()
        .map(|g| {
            let s = summary(g, vis);
            ss.iter()
                .enumerate()
                .filter(|(_, m)| covered(&s, m))
                .fold(0u32, |a, (i, _)| a | (1 << i))
        })
        .collect();
    if masks.contains(&0) {
        return None;
    }
    (0u32..(1u32 << ss.len()))
        .filter(|sub| masks.iter().all(|m| m & sub != 0))
        .map(|sub| sub.count_ones() as usize)
        .min()
}

// =========================================================================
// Criterion 2 / 9 / 10 — the generators and the grid as data
// =========================================================================

/// **Criterion 2.** `synth_fixtures()`: unique names under `synth/`, every one
/// `Group::Synth`, seed 0, the family's communication model (N7: S1 and S5
/// `Bag`, the rest FIFO); the criteria's example names present; 173 fixtures
/// (S1 twins 12, S2 36, S3 18, S4 7, S5 31 points × 3 = 93, S6 7 — derived
/// from the grid table and the validation list before the code was read);
/// `registry()` holds no synthetic fixture.
#[test]
fn c02_synth_fixtures_names_groups_models() {
    let all = synth_fixtures();
    let names: BTreeSet<&str> = all.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names.len(), all.len(), "conformance: duplicate names");
    let count = |p: &str| all.iter().filter(|f| f.name.starts_with(p)).count();
    assert_eq!(
        [
            count("synth/naive-self/"),
            count("synth/share/"),
            count("synth/share-ctl/"),
            count("synth/commit/"),
            count("synth/chain/"),
            count("synth/reset/"),
            count("synth/reset-ctl/"),
            count("synth/reset-twin/"),
            count("synth/width/"),
        ],
        [12, 18, 18, 18, 7, 31, 31, 31, 7],
        "conformance: per-family fixture counts"
    );
    assert_eq!(all.len(), 173, "conformance: synth_fixtures() size");
    for f in &all {
        assert!(f.name.starts_with("synth/"), "conformance: {}", f.name);
        assert_eq!(f.group, Group::Synth, "conformance: {}", f.name);
        assert_eq!(f.config.seed, 0, "conformance: {} seed", f.name);
        let (family, _) = knobs_of(&f.name);
        let want = match family.as_str() {
            "naive-self" | "reset" | "reset-ctl" | "reset-twin" => "Bag",
            _ => "FIFO",
        };
        assert_eq!(
            format!("{:?}", f.config.cons_type),
            want,
            "conformance: {} communication model (N7)",
            f.name
        );
    }
    for n in [
        "synth/share/m4c2",
        "synth/commit/n4j2",
        "synth/chain/d8",
        "synth/reset/k3s1",
        "synth/reset-ctl/k3s1",
        "synth/reset-twin/k3s1",
        "synth/width/w8",
        "synth/naive-self/k3enc2",
        "synth/share-ctl/m4c2",
    ] {
        assert!(names.contains(n), "conformance: criterion 2 names `{n}`");
    }
    let reg = registry(2..=7, 4, 10);
    assert!(
        reg.iter()
            .all(|f| f.group != Group::Synth && !f.name.starts_with("synth/")),
        "conformance: registry() holds a synthetic fixture"
    );
    // S1's violating pair is the registry's, Bag, `Group::Paper`.
    for k in 2..=7 {
        for e in 1..=2 {
            let f = fx(&format!("ex:naive/k{k}/enc{e}"));
            assert_eq!(f.group, Group::Paper, "conformance: {}", f.name);
            assert_eq!(format!("{:?}", f.config.cons_type), "Bag");
        }
    }
}

/// **Criterion 9 / L2(g).** `synth_grid()`: 182 `in_grid` points (S1 24, S2
/// 36, S3 18, S4 7, S5 90, S6 7), 3 validation points (`reset*` at `(1, 2)`),
/// every point's fixture resolvable by `eval::fixture_by_name`, every point
/// once; the grid's synthetic fixtures are exactly `synth_fixtures()`; twins
/// point at each other (S1's pair, S5's `reset`/`reset-twin`), the control
/// has none; variants as criterion 2 names them.
#[test]
fn c09_the_grid_shape() {
    let g = synth_grid();
    let ing: Vec<&SynthPoint> = g.iter().filter(|p| p.in_grid).collect();
    let val: Vec<&SynthPoint> = g.iter().filter(|p| !p.in_grid).collect();
    assert_eq!(ing.len(), 182, "conformance: in_grid points");
    let fam = |f: &str| ing.iter().filter(|p| p.family == f).count();
    assert_eq!(
        [
            fam("naive"),
            fam("share"),
            fam("commit"),
            fam("chain"),
            fam("reset"),
            fam("width")
        ],
        [24, 36, 18, 7, 90, 7],
        "conformance: in_grid points per family"
    );
    let mut vnames: Vec<&str> = val.iter().map(|p| p.fixture.as_str()).collect();
    vnames.sort();
    assert_eq!(
        vnames,
        [
            "synth/reset-ctl/k1s2",
            "synth/reset-twin/k1s2",
            "synth/reset/k1s2"
        ],
        "conformance: the validation-only points"
    );
    let fixtures: BTreeSet<&str> = g.iter().map(|p| p.fixture.as_str()).collect();
    assert_eq!(fixtures.len(), g.len(), "conformance: a point listed twice");
    let synth: BTreeSet<String> = synth_fixtures().into_iter().map(|f| f.name).collect();
    let grid_synth: BTreeSet<String> = fixtures
        .iter()
        .filter(|n| n.starts_with("synth/"))
        .map(|n| (*n).to_owned())
        .collect();
    assert_eq!(
        grid_synth, synth,
        "conformance: grid fixtures vs synth_fixtures()"
    );
    let by_name: BTreeMap<&str, &SynthPoint> = g.iter().map(|p| (p.fixture.as_str(), p)).collect();
    for p in &g {
        let f = fx(&p.fixture);
        assert_eq!(f.name, p.fixture);
        let (family, v) = knobs_of(&p.fixture);
        let (want_variant, want_twin): (&str, Option<String>) = match family.as_str() {
            "ex:naive" => (
                "violating",
                Some(format!("synth/naive-self/k{}enc{}", v[0], v[1])),
            ),
            "naive-self" => (
                "conforming",
                Some(format!("ex:naive/k{}/enc{}", v[0], v[1])),
            ),
            "share" | "commit" | "chain" | "width" => ("conforming", None),
            "share-ctl" => ("control:share-ctl", None),
            "reset" => (
                "violating",
                Some(format!("synth/reset-twin/k{}s{}", v[0], v[1])),
            ),
            "reset-ctl" => ("control:reset-ctl", None),
            "reset-twin" => (
                "conforming",
                Some(format!("synth/reset/k{}s{}", v[0], v[1])),
            ),
            _ => panic!("conformance: unexpected family `{family}`"),
        };
        assert_eq!(
            p.variant, want_variant,
            "conformance: {} variant",
            p.fixture
        );
        assert_eq!(p.twin, want_twin, "conformance: {} twin", p.fixture);
        if let Some(t) = &p.twin {
            let back = by_name
                .get(t.as_str())
                .unwrap_or_else(|| panic!("conformance: twin `{t}` is not a point"));
            assert_eq!(back.twin.as_deref(), Some(p.fixture.as_str()));
            assert_eq!(
                back.in_grid, p.in_grid,
                "conformance: {} twin in_grid",
                p.fixture
            );
        }
    }
}

/// The 24 declared lines, written from the criteria's "Knob lines" paragraph
/// and the label rule (round 05 m2), independently of `grid.rs`.
fn declared_lines() -> BTreeSet<(String, String)> {
    let mut out = BTreeSet::new();
    for e in 1..=2 {
        for v in ["violating", "conforming"] {
            out.insert(("naive".to_owned(), format!("naive/enc={e}/{v}")));
        }
    }
    for r in ["0", "m/2", "m"] {
        for v in ["family", "control"] {
            out.insert(("share".to_owned(), format!("share/c={r}/{v}")));
        }
    }
    for r in ["0", "n/2", "n"] {
        out.insert(("commit".to_owned(), format!("commit/j={r}")));
    }
    out.insert(("chain".to_owned(), "chain".to_owned()));
    for s in [1, 3, 4] {
        for v in ["family", "control", "twin"] {
            out.insert(("reset".to_owned(), format!("reset/s={s}/{v}")));
        }
    }
    out.insert(("width".to_owned(), "width".to_owned()));
    out
}

/// The non-axis knobs of a point with the tied knob written as its ratio
/// (S2 `c/m`, S3 `j/n`) — what must be constant along a line.
fn fixed_coordinates(p: &SynthPoint) -> String {
    let (family, v) = knobs_of(&p.fixture);
    let ratio = |part: usize, whole: usize| part as f64 / whole as f64;
    match family.as_str() {
        "ex:naive" | "naive-self" => format!("enc={}", v[1]),
        "share" | "share-ctl" => format!("c/m={}", ratio(v[1], v[0])),
        "commit" => format!("j/n={}", ratio(v[1], v[0])),
        "chain" | "width" => String::new(),
        "reset" | "reset-ctl" | "reset-twin" => format!("s={}", v[1]),
        _ => panic!("conformance: unexpected family `{family}`"),
    }
}

/// **Criterion 10, the partition check** (round 05 m2). For one fixed
/// `(config, tier, run_kind)`, grouping `synth_grid()`'s `in_grid` rows (built
/// by `SynthPoint::row_spec`) by `series.scope` gives exactly the 24 declared
/// lines (S1 4, S2 6, S3 3, S4 1, S5 9, S6 1) with 6/6/6/7/10/7 points each;
/// within a group the sizes are distinct and equal the axis knob, and the
/// family, the variant and every non-axis knob (ratios applied) are
/// identical; the validation points' scopes are none of the 24. Repeated for
/// two configurations, two tiers and two run kinds: a scope never spans two.
#[test]
fn c10_the_partition_check() {
    let g = synth_grid();
    let configs = [cf_cfg(Selector::Ltr), gated_cfg(Selector::Reverse)];
    let tiers = [Tier::default_tier(), Tier::extension()];
    let mut all_scopes: BTreeSet<String> = BTreeSet::new();
    for c in &configs {
        for t in &tiers {
            for rk in [RunKind::Timed, RunKind::Profiling] {
                let mut groups: BTreeMap<String, Vec<&SynthPoint>> = BTreeMap::new();
                for p in g.iter().filter(|p| p.in_grid) {
                    let r = p.row_spec(c, t, rk, 0);
                    let s = r
                        .series
                        .clone()
                        .expect("conformance: a synthetic row has a series");
                    assert_eq!(s.size, p.size, "conformance: {} size", p.fixture);
                    groups.entry(s.scope).or_default().push(p);
                }
                assert_eq!(groups.len(), 24, "conformance: lines under {}", c.label());
                let mut lines = BTreeSet::new();
                let mut per_family: BTreeMap<&str, usize> = BTreeMap::new();
                for (scope, ps) in &groups {
                    assert!(
                        all_scopes.insert(scope.clone()),
                        "conformance: scope reused"
                    );
                    let first = ps[0];
                    *per_family.entry(first.family).or_default() += 1;
                    lines.insert((first.family.to_owned(), first.line.to_owned()));
                    let mut seen = BTreeSet::new();
                    for p in ps {
                        assert!(
                            seen.insert(p.size),
                            "conformance: `{scope}`: size {} twice",
                            p.size
                        );
                        assert_eq!(
                            (p.family, p.line, p.variant, fixed_coordinates(p)),
                            (
                                first.family,
                                first.line,
                                first.variant,
                                fixed_coordinates(first)
                            ),
                            "conformance: `{scope}` mixes {} and {}",
                            p.fixture,
                            first.fixture
                        );
                        assert_eq!(
                            knobs_of(&p.fixture).1[0] as i64,
                            p.size,
                            "conformance: {}: size is not the axis knob",
                            p.fixture
                        );
                    }
                    let want_points = match first.family {
                        "chain" | "width" => 7,
                        "reset" => 10,
                        _ => 6,
                    };
                    assert_eq!(ps.len(), want_points, "conformance: `{scope}` points");
                }
                assert_eq!(lines, declared_lines(), "conformance: the 24 line labels");
                assert_eq!(
                    per_family,
                    BTreeMap::from([
                        ("chain", 1),
                        ("commit", 3),
                        ("naive", 4),
                        ("reset", 9),
                        ("share", 6),
                        ("width", 1)
                    ]),
                    "conformance: lines per family"
                );
                for p in g.iter().filter(|p| !p.in_grid) {
                    let s = p.row_spec(c, t, rk, 0).series.unwrap();
                    assert!(!groups.contains_key(&s.scope), "conformance: {}", p.fixture);
                }
            }
        }
    }
}

/// **Criterion 2 / 10, `SynthPoint::row_spec`** maps one to one onto the
/// runner's `RowSpec`: fixture, family, knobs, `k`, variant carried over;
/// `rep`, tier, run kind and configuration as passed; keys distinct across
/// points; `twin_key` the twin's own row key under the same configuration,
/// tier, run kind and repetition (empty without a twin); the scope names the
/// configuration label, the tier and the run kind.
#[test]
fn c10_row_spec_maps_one_to_one() {
    let g = synth_grid();
    let t = Tier::default_tier();
    for c in [gated_cfg(Selector::FewestEvents), cf_cfg(Selector::Ltr)] {
        for rep in [0u32, 2] {
            let mut keys = BTreeSet::new();
            let rows: BTreeMap<&str, _> = g
                .iter()
                .map(|p| (p.fixture.as_str(), p.row_spec(&c, &t, RunKind::Timed, rep)))
                .collect();
            for p in &g {
                let r = &rows[p.fixture.as_str()];
                assert_eq!(
                    (
                        r.fixture.as_str(),
                        r.family.as_str(),
                        r.knobs.as_str(),
                        r.k,
                        r.variant.as_str(),
                        r.rep,
                        r.run_kind,
                        r.tier.name.as_str()
                    ),
                    (
                        p.fixture.as_str(),
                        p.family,
                        p.knobs.as_str(),
                        p.k,
                        p.variant,
                        rep,
                        RunKind::Timed,
                        "default"
                    ),
                    "conformance: {}",
                    p.fixture
                );
                assert_eq!(r.config.label(), c.label());
                assert!(keys.insert(r.key(profile_name())), "conformance: key twice");
                let want_twin = match &p.twin {
                    Some(tw) => {
                        let k = key_of(
                            tw,
                            &c.label(),
                            rep,
                            "default",
                            RunKind::Timed,
                            profile_name(),
                        );
                        assert_eq!(k, rows[tw.as_str()].key(profile_name()));
                        k
                    }
                    None => String::new(),
                };
                assert_eq!(r.twin_key, want_twin, "conformance: {} twin_key", p.fixture);
                let scope = &r.series.as_ref().unwrap().scope;
                assert!(
                    scope.contains(&c.label()) && scope.ends_with("|default|timed"),
                    "conformance: scope `{scope}`"
                );
                assert!(
                    scope.starts_with(&format!("{}|{}|", p.family, p.line)),
                    "conformance: scope `{scope}` is not (family, line)"
                );
            }
        }
    }
}

// =========================================================================
// Criterion 2 / L2(a) — every program against its encoding
// =========================================================================

/// **S1** (`naive-self` and the registry's `ex:naive`): spawn order `c, b1,
/// b2, a` (enc 1) / `b1, b2, a, c` (enc 2) on both sides; `c` sends 1 to `a`
/// on the twin (0 on the violating Impl) then receives one 1 from each `b_i`
/// (both rf orders occur, `Bag`); `a` never receives; no nondeterminism.
#[test]
fn c02_programs_s1() {
    for (enc, order) in [(1, ["c", "b1", "b2", "a"]), (2, ["b1", "b2", "a", "c"])] {
        let o = oracle(&fx(&format!("synth/naive-self/k2enc{enc}")));
        let order = owned(&order);
        same_order_everywhere(&o.imp, &order, "naive-self Impl");
        same_order_everywhere(&o.spec, &order, "naive-self Spec");
        let want = set(&[&["S1", "R<b1:1", "R<b2:1"], &["S1", "R<b2:1", "R<b1:1"]]);
        assert_eq!(shapes(&o.imp, "c"), want, "conformance: naive-self c");
        assert_eq!(shapes(&o.spec, "c"), want);
        for b in ["b1", "b2"] {
            assert_eq!(shapes(&o.imp, b), set(&[&["S1"]]));
        }
        assert_eq!(shapes(&o.imp, "a"), set(&[&[]]));
        let v = fx(&format!("ex:naive/k2/enc{enc}"));
        let ov = oracle(&v);
        assert_eq!(
            shapes(&ov.imp, "c"),
            set(&[&["S0", "R<b1:1", "R<b2:1"], &["S0", "R<b2:1", "R<b1:1"]]),
            "conformance: ex:naive Impl c sends 0"
        );
        assert_eq!(shapes(&ov.spec, "c"), want);
        same_order_everywhere(&ov.imp, &order, "ex:naive Impl");
    }
}

/// **S2** `share(2, 1)` / `share-ctl(2, 1)`: per module spawn order `c_i, r_i,
/// a_i` (Spec `c_i, a_i`); `r_i` invisible, `a_i`, `c_i` visible; module 0's
/// relay has the **non-blocking** receive (⊥ then a blocking read, or a
/// direct read), module 1's one blocking receive; `c_i` reads from `r_i` on
/// the Impl and from `a_i` on the Spec; the control's `r_0` chooses with a
/// `Choice<0..=1>` **after** its blocking receive and sends `0 + b`, `r_1`
/// sends the fixed 10; no `CToss` anywhere.
#[test]
fn c02_programs_s2() {
    let f = fx("synth/share/m2c1");
    assert_eq!(
        f.visible,
        owned(&["a0", "a1", "c0", "c1"]),
        "conformance: share visible"
    );
    let o = oracle(&f);
    same_order_everywhere(
        &o.imp,
        &owned(&["c0", "r0", "a0", "c1", "r1", "a1"]),
        "share Impl",
    );
    same_order_everywhere(&o.spec, &owned(&["c0", "a0", "c1", "a1"]), "share Spec");
    assert_eq!(
        shapes(&o.imp, "r0"),
        set(&[&["N<a0:9", "S9"], &["N<\u{22a5}", "R<a0:9", "S9"]]),
        "conformance: r0 is the non-blocking relay"
    );
    assert_eq!(shapes(&o.imp, "r1"), set(&[&["R<a1:9", "S9"]]));
    assert_eq!(shapes(&o.imp, "c0"), set(&[&["R<r0:9"]]));
    assert_eq!(shapes(&o.imp, "c1"), set(&[&["R<r1:9"]]));
    assert_eq!(shapes(&o.spec, "c0"), set(&[&["R<a0:9"]]));
    assert_eq!(shapes(&o.imp, "a0"), set(&[&["S9"]]));
    let f = fx("synth/share-ctl/m2c1");
    assert_eq!(f.visible, owned(&["a0", "a1", "c0", "c1"]));
    let o = oracle(&f);
    for side in [&o.imp, &o.spec] {
        same_order_everywhere(
            side,
            &owned(&["c0", "r0", "a0", "c1", "r1", "a1"]),
            "share-ctl",
        );
        assert_eq!(
            shapes(side, "r0"),
            set(&[
                &["R<a0:9", "C<0..=1>=0", "S0"],
                &["R<a0:9", "C<0..=1>=1", "S1"]
            ]),
            "conformance: share-ctl r0 chooses after its receive"
        );
        assert_eq!(shapes(side, "r1"), set(&[&["R<a1:9", "S10"]]));
        assert_eq!(shapes(side, "c0"), set(&[&["R<r0:0"], &["R<r0:1"]]));
    }
}

/// **S3** `commit(2, j)`: spawn order `c, p`; `p` sends −1 then the bits; the
/// Impl chooses each bit (`Choice<0..=1>`) immediately before its send; the
/// Spec chooses `b_1..b_j` before the prefix send, the rest before each send;
/// `c` reads the `n + 1` values from `p` in order (FIFO).
#[test]
fn c02_programs_s3() {
    for j in 0..=2usize {
        let o = oracle(&fx(&format!("synth/commit/n2j{j}")));
        for side in [&o.imp, &o.spec] {
            same_order_everywhere(side, &owned(&["c", "p"]), "commit");
        }
        let mut imp = BTreeSet::new();
        let mut spec = BTreeSet::new();
        let mut cw = BTreeSet::new();
        for b1 in 0..=1 {
            for b2 in 0..=1 {
                let c1 = format!("C<0..=1>={b1}");
                let c2 = format!("C<0..=1>={b2}");
                let (s1, s2) = (format!("S{b1}"), format!("S{b2}"));
                imp.insert(vec![
                    "S-1".into(),
                    c1.clone(),
                    s1.clone(),
                    c2.clone(),
                    s2.clone(),
                ]);
                spec.insert(match j {
                    0 => vec!["S-1".into(), c1.clone(), s1.clone(), c2.clone(), s2.clone()],
                    1 => vec![c1.clone(), "S-1".into(), s1.clone(), c2.clone(), s2.clone()],
                    _ => vec![c1.clone(), c2.clone(), "S-1".into(), s1.clone(), s2.clone()],
                });
                cw.insert(vec![
                    "R<p:-1".to_owned(),
                    format!("R<p:{b1}"),
                    format!("R<p:{b2}"),
                ]);
            }
        }
        assert_eq!(
            shapes(&o.imp, "p"),
            imp,
            "conformance: commit Impl p, j = {j}"
        );
        assert_eq!(
            shapes(&o.spec, "p"),
            spec,
            "conformance: commit Spec p, j = {j}"
        );
        assert_eq!(shapes(&o.imp, "c"), cw);
        assert_eq!(shapes(&o.spec, "c"), cw);
    }
}

/// **S4** `chain(2)`: Impl spawn order `v2, r2, v1, r1, v0`, Spec `v2, v1,
/// v0`; `v0` sends 1, `v1` reads 1 then sends 2, `v2` reads 2; on the Impl
/// every hop goes through the invisible relay `r_i`.
#[test]
fn c02_programs_s4() {
    let f = fx("synth/chain/d2");
    assert_eq!(f.visible, owned(&["v0", "v1", "v2"]));
    let o = oracle(&f);
    same_order_everywhere(
        &o.imp,
        &owned(&["v2", "r2", "v1", "r1", "v0"]),
        "chain Impl",
    );
    same_order_everywhere(&o.spec, &owned(&["v2", "v1", "v0"]), "chain Spec");
    let one = |gs: &[ExecutionGraph], n: &str| shapes(gs, n).into_iter().collect::<Vec<_>>();
    assert_eq!(one(&o.imp, "v0"), [owned(&["S1"])]);
    assert_eq!(one(&o.imp, "r1"), [owned(&["R<v0:1", "S1"])]);
    assert_eq!(one(&o.imp, "v1"), [owned(&["R<r1:1", "S2"])]);
    assert_eq!(one(&o.imp, "r2"), [owned(&["R<v1:2", "S2"])]);
    assert_eq!(one(&o.imp, "v2"), [owned(&["R<r2:2"])]);
    assert_eq!(one(&o.spec, "v1"), [owned(&["R<v0:1", "S2"])]);
    assert_eq!(one(&o.spec, "v2"), [owned(&["R<v1:2"])]);
}

/// **S5** `reset(2, s)`, `reset-ctl(2, s)`, `reset-twin(2, s)` for `s ∈ {1,
/// 3}` (the grid's `s` values at `k = 2`; `s = 2` exists only at `k = 1`):
/// copy `i`'s spawn order `a_i, c_i, b_i` (family, twin) / `a_i, b_i, c_i`
/// (control, **both sides**); the pad `s0..s{s-1}, d` spawned after every
/// copy **on the Spec side only** (and on both sides of the twin, which is
/// the Spec against itself); the pad invisible (not in `visible`), its
/// senders' values distinct, `d` receiving `s` times; Impl `c_i` reads from
/// `a_i` (1) or `b_i` (2), Spec `c_i` only from `b_i`.
#[test]
fn c02_programs_s5() {
    for s in [1usize, 3] {
        let pad: Vec<String> = (0..s)
            .map(|j| format!("s{j}"))
            .chain(std::iter::once("d".to_owned()))
            .collect();
        for (fam, acb) in [("reset", true), ("reset-ctl", false), ("reset-twin", true)] {
            let f = fx(&format!("synth/{fam}/k2s{s}"));
            assert_eq!(
                f.visible,
                owned(&["a0", "b0", "c0", "a1", "b1", "c1"]),
                "conformance: {fam} visible (the pad is not)"
            );
            let o = oracle(&f);
            let copies: Vec<String> = (0..2)
                .flat_map(|i| {
                    if acb {
                        [format!("a{i}"), format!("c{i}"), format!("b{i}")]
                    } else {
                        [format!("a{i}"), format!("b{i}"), format!("c{i}")]
                    }
                })
                .collect();
            let mut with_pad = copies.clone();
            with_pad.extend(pad.iter().cloned());
            let imp_order = if fam == "reset-twin" {
                &with_pad
            } else {
                &copies
            };
            same_order_everywhere(&o.imp, imp_order, &format!("{fam} Impl"));
            same_order_everywhere(&o.spec, &with_pad, &format!("{fam} Spec"));
            let spec_c = set(&[&["R<b0:2"]]);
            assert_eq!(shapes(&o.spec, "c0"), spec_c, "conformance: {fam} Spec c0");
            let imp_c = if fam == "reset-twin" {
                spec_c.clone()
            } else {
                set(&[&["R<a0:1"], &["R<b0:2"]])
            };
            assert_eq!(shapes(&o.imp, "c0"), imp_c, "conformance: {fam} Impl c0");
            assert_eq!(shapes(&o.imp, "a1"), set(&[&["S1"]]));
            assert_eq!(shapes(&o.imp, "b1"), set(&[&["S2"]]));
            let vals: BTreeSet<Vec<String>> = (0..s)
                .map(|j| shape(&o.spec[0], &format!("s{j}")))
                .collect();
            assert_eq!(vals.len(), s, "conformance: the pad's values are distinct");
            assert_eq!(
                shape(&o.spec[0], "d").len(),
                s,
                "conformance: the pad's receiver receives s times"
            );
        }
    }
}

/// **S6** `width(2)`: spawn order `c, v`; `v` makes one `Choice<0..=1>` and
/// sends the value; `c` receives it.
#[test]
fn c02_programs_s6() {
    let f = fx("synth/width/w2");
    assert_eq!(f.visible, owned(&["v", "c"]));
    let o = oracle(&f);
    for side in [&o.imp, &o.spec] {
        same_order_everywhere(side, &owned(&["c", "v"]), "width");
        assert_eq!(
            shapes(side, "v"),
            set(&[&["C<0..=1>=0", "S0"], &["C<0..=1>=1", "S1"]])
        );
        assert_eq!(shapes(side, "c"), set(&[&["R<v:0"], &["R<v:1"]]));
    }
}

// =========================================================================
// Criterion 3 / 4 — the derived table and the validation pilot
// =========================================================================

/// **Criterion 3.** The derivation covers every pilot fixture and every name
/// resolves; the pilot has 51 fixtures (S1 12, S2 12, S3 6, S4 3, S5 15, S6 3).
#[test]
fn c03_the_derived_table_covers_every_pilot_size() {
    let names = pilot_names();
    assert_eq!(names.len(), 51, "conformance: pilot size");
    for n in &names {
        let _ = derived(n);
        assert_eq!(fx(n).name, *n);
    }
    assert_eq!(
        names.iter().filter(|n| hand_count(n)).count(),
        4 + 6 + 3 + 1 + 9 + 1
    );
}

/// One pilot fixture: the oracle's counts against the derivation, then the
/// four engines × three selectors — conclusive, verdict agreement, report-key
/// equality with the oracle's uncovered set on the deciding engines,
/// certification of every report of every engine, `impl_graphs`, stateful's
/// `signatures`, `|W|` on the sweeping engines.
fn check_fixture(name: &str, selectors: &[Selector]) -> (Vec<String>, Vec<Row>) {
    let f = fx(name);
    let e = derived(name);
    let mut fail = Vec::new();
    let vis = &f.visible;
    let want_group = if name.starts_with("ex:naive") {
        Group::Paper
    } else {
        Group::Synth
    };
    if f.group != want_group {
        fail.push(format!("{name}: group {:?}", f.group));
    }
    let t0 = Instant::now();
    let o = oracle(&f);
    if (o.imp.len(), o.spec.len()) != (e.imp, e.spec) {
        fail.push(format!(
            "{name}: Impl/Spec complete graphs {}/{}, derived {}/{}",
            o.imp.len(),
            o.spec.len(),
            e.imp,
            e.spec
        ));
    }
    if num(&o.row, "signatures") != e.sig {
        fail.push(format!(
            "{name}: {} Spec signatures, derived {}",
            num(&o.row, "signatures"),
            e.sig
        ));
    }
    let want = o.families.uncovered_keys();
    if want.len() != e.unc {
        fail.push(format!(
            "{name}: {} uncovered, derived {}",
            want.len(),
            e.unc
        ));
    }
    let oracle_secs = t0.elapsed().as_secs_f64();
    let mut rows = Vec::new();
    for s in selectors.iter().copied() {
        for c in engines(s) {
            let r = grun(&f, &c);
            let x = st(&r);
            let row = row_of(&r);
            let label = format!("{name} {}", c.label());
            if let Some(why) = &x.failure {
                fail.push(format!("{label}: failure: {why}"));
            }
            if x.exhaustions != 0 || x.end != SearchEnd::StateSpaceExhausted {
                fail.push(format!(
                    "{label}: exhaustions {} end {:?}",
                    x.exhaustions, x.end
                ));
            }
            if (x.reports > 0) != (e.unc > 0) {
                fail.push(format!(
                    "{label}: {} reports, derived {} uncovered",
                    x.reports, e.unc
                ));
            }
            let reps = reports_of(&r);
            if c.engine != GridEngine::Enumerator {
                let keys: Vec<String> = reps.iter().map(|x| canon_key(x.graph, vis)).collect();
                let got: BTreeSet<String> = keys.iter().cloned().collect();
                if got.len() != keys.len() {
                    fail.push(format!("{label}: a key reported twice"));
                }
                if got != want {
                    fail.push(format!(
                        "{label}: report-key set of {} differs from the oracle's uncovered {}",
                        got.len(),
                        want.len()
                    ));
                }
                if num(&row, "impl_graphs") != e.imp {
                    fail.push(format!(
                        "{label}: impl_graphs {}, derived {}",
                        num(&row, "impl_graphs"),
                        e.imp
                    ));
                }
            }
            if c.engine == GridEngine::Stateful && num(&row, "signatures") != e.sig {
                fail.push(format!("{label}: signatures {}", num(&row, "signatures")));
            }
            if matches!(c.engine, GridEngine::CompleteFirst | GridEngine::Gated) {
                if let Some(w) = e.witnesses {
                    if num(&row, "witnesses") != w {
                        fail.push(format!(
                            "{label}: witnesses {}, derived {w}",
                            num(&row, "witnesses")
                        ));
                    }
                }
            }
            for rep in &reps {
                if rep.cause != Cause::NoCover {
                    fail.push(format!("{label}: a report with cause {:?}", rep.cause));
                }
                if let Err(why) = certify(
                    &o.families,
                    &Claim {
                        graph: rep.graph,
                        tag: rep.tag,
                        cause: rep.cause.clone(),
                        serialized: rep.serialized,
                    },
                ) {
                    fail.push(format!("{label}: the oracle rejects a report: {why}"));
                }
            }
            let mut out: Row = vec![
                ("pilot_fixture", name.to_owned()),
                (
                    "derived_impl_spec_sig_unc",
                    format!("{}/{}/{}/{}", e.imp, e.spec, e.sig, e.unc),
                ),
            ];
            out.extend(row);
            rows.push(out);
        }
    }
    if let Some(first) = rows.first_mut() {
        first.push(("oracle_secs", format!("{oracle_secs:.2}")));
    }
    (fail, rows)
}

/// Runs [`check_fixture`] over `names` (one worker), fails with every failure,
/// and appends the rows to `P4_DIFF_TABLES` when it is set.
fn pilot(names: &[String], title: &str) {
    assert!(!names.is_empty(), "conformance: {title}: no fixture");
    let mut failures = Vec::new();
    let mut rows = Vec::new();
    let mut secs = Vec::new();
    for n in names {
        let t = Instant::now();
        let (f, r) = check_fixture(n, &SELECTORS);
        secs.push(format!("{n} {:.1}s", t.elapsed().as_secs_f64()));
        failures.extend(f);
        rows.extend(r);
    }
    if std::env::var_os("P4_DIFF_TABLES").is_some() {
        let mut t = Tables::open();
        t.table(title, &rows);
        t.note(&format!(
            "Per-fixture wall time (oracle + 12 runs): {}",
            secs.join("; ")
        ));
    }
    assert!(
        failures.is_empty(),
        "conformance: {title}: {} failures:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

/// **Criterion 4, the hand-count sizes** (the default subset): 24 fixtures,
/// the four engines × three selectors each.
#[test]
fn c04_pilot_hand_count() {
    let names: Vec<String> = pilot_names()
        .into_iter()
        .filter(|n| hand_count(n))
        .collect();
    pilot(&names, "P5-SYNTH pilot, hand-count sizes");
}

/// **Criterion 4, one fixture per process** (`SYNTH_FIXTURE`; a no-op without
/// it): the pilot sizes beyond the hand-count ones.
#[test]
#[ignore = "one fixture per process: SYNTH_FIXTURE"]
fn c04_one_fixture() {
    let Ok(name) = std::env::var("SYNTH_FIXTURE") else {
        return;
    };
    assert!(
        pilot_names().contains(&name),
        "conformance: `{name}` is not a pilot fixture"
    );
    pilot(
        std::slice::from_ref(&name),
        &format!("P5-SYNTH pilot, {name}"),
    );
}

// =========================================================================
// Criterion 5 — S5's premise, before any S5 measurement
// =========================================================================

/// The derived gated counters (`derived.md` §S5; `Exhaustive`/`Always`).
#[derive(Clone, Debug, PartialEq, Eq)]
struct G5 {
    impl_graphs: usize,
    reports: usize,
    reports_certified: usize,
    certificates_set: usize,
    certificate_resets: usize,
    states_pushed: usize,
    certified_states_revisited: usize,
    gate_sweep_sizes: String,
    gate_cache_hits: usize,
    carried_hits: usize,
    completion_cache_hits: usize,
    witnesses: usize,
}

/// `variant` is `reset` or `reset-ctl`; `rev` the `Reverse` selector.
fn g5(variant: &str, rev: bool, k: usize, s: usize) -> G5 {
    let unc = pow2(k) - 1;
    let failing = |n: usize| {
        let mut v = vec![1];
        v.extend(std::iter::repeat_n(fact(s), n));
        sizes(&v)
    };
    let base = G5 {
        impl_graphs: pow2(k),
        reports: unc,
        reports_certified: unc,
        certificates_set: unc,
        certificate_resets: 0,
        states_pushed: unc,
        certified_states_revisited: unc,
        gate_sweep_sizes: failing(unc),
        gate_cache_hits: k,
        carried_hits: k - 1,
        completion_cache_hits: 1,
        witnesses: 1,
    };
    match (variant, rev) {
        ("reset", false) => base,
        // `derived.md`'s `Reverse` rows (N5 extended to k copies) — refuted by
        // T2 (`Reverse` schedules as `Ltr` here); kept as the record of the
        // derivation, asserted nowhere.
        ("reset", true) | ("reset-ctl", true) => G5 {
            certified_states_revisited: unc - k,
            gate_cache_hits: 0,
            carried_hits: 3 * k - 1,
            ..base
        },
        ("reset-ctl", false) => G5 {
            certificates_set: k,
            certificate_resets: k,
            states_pushed: 0,
            certified_states_revisited: 0,
            gate_sweep_sizes: failing(k),
            gate_cache_hits: k,
            carried_hits: 2 * k - 1,
            ..base
        },
        _ => panic!("conformance: g5 knows reset and reset-ctl"),
    }
}

fn g5_of(row: &Row) -> G5 {
    G5 {
        impl_graphs: num(row, "impl_graphs"),
        reports: num(row, "reports"),
        reports_certified: num(row, "reports_certified"),
        certificates_set: num(row, "certificates_set"),
        certificate_resets: num(row, "certificate_resets"),
        states_pushed: num(row, "states_pushed"),
        certified_states_revisited: num(row, "certified_states_revisited"),
        gate_sweep_sizes: cell(row, "gate_sweep_sizes").to_owned(),
        gate_cache_hits: num(row, "gate_cache_hits"),
        carried_hits: num(row, "carried_hits"),
        completion_cache_hits: num(row, "completion_cache_hits"),
        witnesses: num(row, "witnesses"),
    }
}

fn gated_row(name: &str, s: Selector) -> Row {
    row_of(&grun(&fx(name), &gated_cfg(s)))
}

/// `FewestEvents`' measured gated counters on `reset(k, 1)` — **the record**
/// (criteria rev 5.2's erratum after T1: N5 holds at `k = 1` only; these are
/// measured, not derived; `k = 1` equals the `Ltr` derivation). Mechanism
/// (F83's replay window, diagnosed at gate 4 round 01):
/// [`m2_fewest_events_defers_the_revisited_prefix_behind_fresh_events`].
fn fe_record(k: usize) -> G5 {
    match k {
        1 => g5("reset", false, 1, 1),
        2 => G5 {
            reports_certified: 2,
            certificates_set: 2,
            certified_states_revisited: 2,
            gate_sweep_sizes: "[1, 1, 1]".to_owned(),
            carried_hits: 0,
            ..g5("reset", false, 2, 1)
        },
        3 => G5 {
            reports_certified: 5,
            certificates_set: 5,
            certified_states_revisited: 4,
            gate_sweep_sizes: "[1, 1, 1, 1, 1, 1]".to_owned(),
            carried_hits: 0,
            ..g5("reset", false, 3, 1)
        },
        _ => panic!("conformance: fe_record has k = 1, 2, 3"),
    }
}

/// **Criterion 5, the premise** (plan §2.1; N4; rev 5.2): on `reset(k, 1)`,
/// `k ∈ {1, 2, 3}`, gated `Exhaustive`/`Always`, under **`Ltr` and
/// `FewestEvents`**: a certificate is set before the backward revisit that
/// discards it — `certificates_set ≥ 1`, `certified_states_revisited ≥ 1`,
/// `certificate_resets = 0`, `states_pushed = 2^k − 1`. Under `Ltr` every
/// derived counter holds (`certificates_set = certified_states_revisited =
/// 2^k − 1`, `gate_sweep_sizes = [1, 1 × (2^k − 1)]`, `gate_cache_hits = k`,
/// `carried_hits = k − 1`, one completion cache hit, `|W| = 1`); under
/// `FewestEvents` the measured record [`fe_record`] (T1: at `k = 2` the
/// schedule departs from `Ltr`'s). **If the premise fails, P5-SYNTH stops**.
#[test]
fn c05_the_premise_under_ltr_and_fewest_events() {
    let mut fail = Vec::new();
    for s in [Selector::Ltr, Selector::FewestEvents] {
        for k in 1..=3 {
            let name = format!("synth/reset/k{k}s1");
            let got = g5_of(&gated_row(&name, s));
            if got.certificates_set < 1
                || got.certified_states_revisited < 1
                || got.certificate_resets != 0
                || got.states_pushed != pow2(k) - 1
            {
                fail.push(format!("{name} {s:?}: PREMISE FAILS: {got:?}"));
            }
            let want = if s == Selector::Ltr {
                g5("reset", false, k, 1)
            } else {
                fe_record(k)
            };
            if got != want {
                fail.push(format!(
                    "{name} {s:?}:\n    got  {got:?}\n    want {want:?}"
                ));
            }
        }
    }
    assert!(
        fail.is_empty(),
        "conformance: criterion 5:\n  {}",
        fail.join("\n  ")
    );
}

/// **T2 — criterion 5's labelled exception does not occur** (N5 says: under
/// `Reverse` at `k = 1` the certificate is set only after the revisit,
/// `certified_states_revisited = 0`; my derivation extended that to `csr =
/// 2^k − 1 − k`). Measured: `Reverse` gives **`Ltr`'s** counters exactly at
/// `k = 1, 2, 3` (`csr = 2^k − 1`). Mechanism (`selector.rs`): `Reverse` picks
/// the candidate with the largest origination vector, so every thread `main`
/// spawns runs **before `main` spawns the next one** — `a_i` sends, `c_i`
/// reads 1, `b_i` sends and backward-revisits, which is `Ltr`'s visible
/// order; N5 assumed `main` spawns every thread first. Pinned as measured.
#[test]
fn t2_reverse_schedules_as_ltr_on_reset() {
    let mut fail = Vec::new();
    for k in 1..=3 {
        let name = format!("synth/reset/k{k}s1");
        let got = g5_of(&gated_row(&name, Selector::Reverse));
        let want = g5("reset", false, k, 1);
        if got != want {
            fail.push(format!(
                "{name} Reverse:\n    got  {got:?}\n    want {want:?}"
            ));
        }
    }
    assert!(fail.is_empty(), "conformance: N5:\n  {}", fail.join("\n  "));
}

/// **Criterion 5, `reset(1, 2)`** (the Spec-only pad's first exercise on every
/// engine): Impl 2, Spec 2, one uncovered graph; gated `gate_sweep_sizes = [1,
/// 2]` under every selector (the successful sweep stops at rank 1, the failing
/// one tests both pad orders); every engine reports, every report certified
/// (the pilot's own check, here at this one point).
#[test]
fn c05_the_pad_at_reset_1_2() {
    let o = oracle(&fx("synth/reset/k1s2"));
    assert_eq!(
        (o.imp.len(), o.spec.len(), o.families.uncovered_keys().len()),
        (2, 2, 1),
        "conformance: reset(1, 2) counts"
    );
    for s in SELECTORS {
        let r = gated_row("synth/reset/k1s2", s);
        assert_eq!(cell(&r, "gate_sweep_sizes"), "[1, 2]", "conformance: {s:?}");
    }
    let (fail, _) = check_fixture("synth/reset/k1s2", &SELECTORS);
    assert!(
        fail.is_empty(),
        "conformance: reset(1, 2):\n  {}",
        fail.join("\n  ")
    );
}

/// The per-copy choice vectors of the uncovered Impl graphs (the visible
/// projection criterion 5 compares by).
fn uncovered_projections(o: &Oracle, vis: &[String]) -> BTreeSet<Vec<(String, Vec<String>)>> {
    o.imp
        .iter()
        .filter(|g| !o.families.is_covered(g))
        .map(|g| projection(g, vis))
        .collect()
}

/// **Criterion 5, the control** `reset-ctl(k, 1)`, `k ∈ {1, 2, 3}`: under
/// `Ltr` the derived `states_pushed = certified_states_revisited = 0`,
/// `certificates_set = certificate_resets = k`, `[1, 1 × k]`, `k` gate cache
/// hits; under `FewestEvents` no backward revisit (its counters on stderr,
/// rev 5.2; mechanism `m2_…`); the same `impl_graphs` and `reports` as the
/// family on the three **deciding** engines (stateful, complete-first, gated)
/// under every selector — the enumerator is skipped: its growing-prefix report
/// counts differ by construction (T5); the same uncovered set **by visible
/// projection**
/// while the canonical key sets differ (`main`'s spawn order).
#[test]
fn c05_the_control_matches_the_family_by_projection() {
    let mut fail = Vec::new();
    for k in 1..=3 {
        let fam = format!("synth/reset/k{k}s1");
        let ctl = format!("synth/reset-ctl/k{k}s1");
        let fe = g5_of(&gated_row(&ctl, Selector::FewestEvents));
        note!("{ctl} FewestEvents (measured, rev 5.2): {fe:?}");
        if fe.states_pushed != 0 || fe.certified_states_revisited != 0 {
            fail.push(format!("{ctl} FewestEvents: backward revisits {fe:?}"));
        }
        {
            let s = Selector::Ltr;
            let got = g5_of(&gated_row(&ctl, s));
            let want = g5("reset-ctl", false, k, 1);
            if got != want {
                fail.push(format!("{ctl} {s:?}:\n    got  {got:?}\n    want {want:?}"));
            }
        }
        let (ff, cf) = (fx(&fam), fx(&ctl));
        for s in SELECTORS {
            // The deciding engines: the enumerator's growing-prefix reports
            // are not report-key equal by construction and differ in number
            // (family 1, control k or more — measured, recorded in the report).
            for c in engines(s).into_iter().skip(1) {
                let (a, b) = (row_of(&grun(&ff, &c)), row_of(&grun(&cf, &c)));
                let pick = |r: &Row| {
                    (
                        r.iter()
                            .find(|(c, _)| *c == "impl_graphs")
                            .map(|(_, v)| v.clone()),
                        cell(r, "reports").to_owned(),
                    )
                };
                if pick(&a) != pick(&b) {
                    fail.push(format!(
                        "k = {k} {}: family {:?} vs control {:?}",
                        c.label(),
                        pick(&a),
                        pick(&b)
                    ));
                }
            }
        }
        let (of, oc) = (oracle(&ff), oracle(&cf));
        let (pf, pc) = (
            uncovered_projections(&of, &ff.visible),
            uncovered_projections(&oc, &cf.visible),
        );
        if pf != pc || pf.len() != pow2(k) - 1 {
            fail.push(format!("k = {k}: uncovered projections differ or miscount"));
        }
        if of.families.uncovered_keys() == oc.families.uncovered_keys() {
            fail.push(format!(
                "k = {k}: the canonical keys are equal (spawn order unrecorded?)"
            ));
        }
    }
    assert!(
        fail.is_empty(),
        "conformance: the control:\n  {}",
        fail.join("\n  ")
    );
}

/// **The control under `Reverse`** (the criteria state none). My derivation
/// (backward revisits, the family's `Reverse` structure) was wrong for T2's
/// reason: `Reverse` runs each spawned thread before `main`'s next spawn, so
/// both sends precede `c_i`'s receive and the control keeps its `Ltr`
/// counters — no backward revisit, `certificate_resets = k`. Pinned as
/// measured.
#[test]
fn c05_the_control_under_reverse() {
    let mut fail = Vec::new();
    for k in 1..=3 {
        let name = format!("synth/reset-ctl/k{k}s1");
        let got = g5_of(&gated_row(&name, Selector::Reverse));
        let want = g5("reset-ctl", false, k, 1);
        if got != want {
            fail.push(format!(
                "{name} Reverse:\n    got  {got:?}\n    want {want:?}"
            ));
        }
    }
    assert!(
        fail.is_empty(),
        "conformance: control/Reverse:\n  {}",
        fail.join("\n  ")
    );
}

/// **S5 at `s = 3`** (`reset(2, 3)`, criterion 4's point): every failing
/// sweep tests `3! = 6` Spec graphs, the successful one 1, under `Ltr`; the
/// control fails `k = 2` times. E2's contrast `gate_sweeps_failing` 3 vs 2.
#[test]
#[ignore = "beyond the hand-count sizes: one test per process"]
fn c05_the_pad_at_reset_2_3() {
    for (v, name) in [
        ("reset", "synth/reset/k2s3"),
        ("reset-ctl", "synth/reset-ctl/k2s3"),
    ] {
        let r = gated_row(name, Selector::Ltr);
        assert_eq!(g5_of(&r), g5(v, false, 2, 3), "conformance: {name}");
        let failing = if v == "reset" { 3 } else { 2 };
        assert_eq!(
            num(&r, "gate_sweeps_failing"),
            failing,
            "conformance: E2 {name}"
        );
    }
}

// =========================================================================
// Criterion 6 — S2's sharing
// =========================================================================

/// S2's derived complete-first and gated figures at `(m, c)` (`Ltr`).
fn s2_check(name: &str, fail: &mut Vec<String>) {
    let (family, v) = knobs_of(name);
    let n = pow2(v[1]);
    let ctl = family == "share-ctl";
    let f = fx(name);
    let cf = row_of(&grun(&f, &cf_cfg(Selector::Ltr)));
    let ranks: Vec<usize> = if ctl { (1..=n).collect() } else { vec![1] };
    let want_cf = (
        n,
        ranks.len(),
        ranks.len(),
        if ctl { 0 } else { n - 1 },
        sizes(&ranks),
    );
    let got_cf = (
        num(&cf, "impl_graphs"),
        num(&cf, "sweeps"),
        num(&cf, "witnesses"),
        num(&cf, "cache_hits"),
        cell(&cf, "sweep_sizes").to_owned(),
    );
    if got_cf != want_cf {
        fail.push(format!(
            "{name} CF (impl, sweeps, |W|, cache_hits, sizes): {got_cf:?} want {want_cf:?}"
        ));
    }
    let g = gated_row(name, Selector::Ltr);
    let want_g = (ranks.len(), n, ranks.len(), sizes(&ranks), 0);
    let got_g = (
        num(&g, "gate_sweeps"),
        num(&g, "completion_cache_hits"),
        num(&g, "witnesses"),
        cell(&g, "gate_sweep_sizes").to_owned(),
        num(&g, "certificates_set"),
    );
    if got_g != want_g {
        fail.push(format!(
            "{name} gated (gate_sweeps, ccache, |W|, sizes, certs): {got_g:?} want {want_g:?}"
        ));
    }
    let o = oracle(&f);
    let basis = min_basis(&o.imp, &o.spec, &f.visible);
    if basis != Some(ranks.len()) {
        fail.push(format!(
            "{name}: minimal basis {basis:?}, derived {}",
            ranks.len()
        ));
    }
    // Sharing = impl_graphs / |W|: 2^c on the family, 1 on the control.
    let sharing = num(&cf, "impl_graphs") / num(&cf, "witnesses").max(1);
    if sharing != if ctl { 1 } else { n } {
        fail.push(format!("{name}: sharing {sharing}"));
    }
}

/// **Criterion 6's cells**: `share(2, 1)`, `share(2, 2)`, `share-ctl(2, 2)`
/// under complete-first exhaustive `Ltr` — `impl_graphs` 2/4/4, `sweeps`
/// 1/1/4, `witnesses` 1/1/4, `cache_hits` 1/3/0, `sweep_sizes` `[1]`/`[1]`/`[1,
/// 2, 3, 4]`; gated `Always` — `gate_sweeps` 1/1/4, `completion_cache_hits`
/// 2/4/4, `witnesses` 1/1/4, no certificate; the offline minimal basis
/// 1/1/4; sharing 2/4/1.
#[test]
fn c06_the_share_cells() {
    let mut fail = Vec::new();
    for n in [
        "synth/share/m2c1",
        "synth/share/m2c2",
        "synth/share-ctl/m2c2",
    ] {
        s2_check(n, &mut fail);
    }
    assert!(
        fail.is_empty(),
        "conformance: criterion 6:\n  {}",
        fail.join("\n  ")
    );
}

/// **Criterion 6 over every S2 pilot point** (`m ∈ {2, 4}`, every `c`, both
/// variants): the control's sharing is 1 at every `(m, c)`, the family's
/// `2^c`; the minimal basis 1 / `2^c`.
#[test]
#[ignore = "beyond the hand-count sizes: one test per process"]
fn c06_sharing_at_every_pilot_point() {
    let mut fail = Vec::new();
    for n in pilot_names()
        .iter()
        .filter(|n| n.starts_with("synth/share"))
    {
        s2_check(n, &mut fail);
    }
    assert!(
        fail.is_empty(),
        "conformance: criterion 6:\n  {}",
        fail.join("\n  ")
    );
}

// =========================================================================
// Criterion 7 — S3's dial
// =========================================================================

/// `commit(n, j)` at every `j ∈ {0, n/2, n}`: conforms, `2^n` graphs both
/// sides; the witness ranks follow the pinned `Choice` order under `Ltr`
/// (both streams lexicographic in the bit vector, whatever `j`): complete-
/// first `sweep_sizes` and gated `gate_sweep_sizes` are `[1, 2, …, 2^n]`. The
/// enumerator's `rebuilds_taken`, `cover_calls`, `spec_visit_calls` per `j`
/// are returned (reported, not predicted).
/// `(j, rebuilds_taken, cover_calls, spec_visit_calls)` of the enumerator.
type DialRow = (usize, usize, usize, usize);

fn s3_dial(n: usize) -> (Vec<String>, Vec<DialRow>) {
    let mut fail = Vec::new();
    let mut en = Vec::new();
    let ranks = sizes(&(1..=pow2(n)).collect::<Vec<_>>());
    for j in [0, n / 2, n] {
        let name = format!("synth/commit/n{n}j{j}");
        let f = fx(&name);
        let o = oracle(&f);
        if (o.imp.len(), o.spec.len(), o.families.uncovered_keys().len()) != (pow2(n), pow2(n), 0) {
            fail.push(format!("{name}: counts"));
        }
        let cf = row_of(&grun(&f, &cf_cfg(Selector::Ltr)));
        if cell(&cf, "sweep_sizes") != ranks || num(&cf, "reports") != 0 {
            fail.push(format!(
                "{name}: CF sweep_sizes {}",
                cell(&cf, "sweep_sizes")
            ));
        }
        let g = gated_row(&name, Selector::Ltr);
        if cell(&g, "gate_sweep_sizes") != ranks || num(&g, "reports") != 0 {
            fail.push(format!(
                "{name}: gated gate_sweep_sizes {}",
                cell(&g, "gate_sweep_sizes")
            ));
        }
        let e = row_of(&grun(&f, &engines(Selector::Ltr)[0]));
        if num(&e, "reports") != 0 {
            fail.push(format!("{name}: the enumerator reports"));
        }
        en.push((
            j,
            num(&e, "rebuilds_taken"),
            num(&e, "cover_calls"),
            num(&e, "spec_visit_calls"),
        ));
    }
    (fail, en)
}

/// **Criterion 7 at the hand-count size** `n = 2` (the dial's shape).
#[test]
fn c07_the_commit_dial_at_n_2() {
    let (fail, en) = s3_dial(2);
    note!("commit n=2 (j, rebuilds_taken, cover_calls, spec_visit_calls): {en:?}");
    assert!(
        fail.is_empty(),
        "conformance: criterion 7:\n  {}",
        fail.join("\n  ")
    );
}

/// **Criterion 7** on `commit(4, j)`, `j ∈ {0, 2, 4}`: conforms with 16 graphs
/// both sides, witness ranks `[1..16]` on both sweeping engines; the
/// enumerator's `rebuilds_taken` per `j` reported on stderr. Monotonicity is
/// the next test.
#[test]
#[ignore = "beyond the hand-count sizes: one test per process"]
fn c07_the_commit_dial_at_n_4() {
    let (fail, en) = s3_dial(4);
    note!("commit n=4 (j, rebuilds_taken, cover_calls, spec_visit_calls): {en:?}");
    assert!(
        fail.is_empty(),
        "conformance: criterion 7:\n  {}",
        fail.join("\n  ")
    );
}

/// **Criterion 7's expectation** (not an engine fact): the enumerator's
/// `rebuilds_taken` is monotone non-decreasing in `j` at `n = 4`. A failure
/// is a finding against the family's design.
#[test]
#[ignore = "beyond the hand-count sizes: one test per process"]
fn c07_rebuilds_are_monotone_in_j() {
    let (_, en) = s3_dial(4);
    let r: Vec<usize> = en.iter().map(|x| x.1).collect();
    assert!(
        r.windows(2).all(|w| w[0] <= w[1]),
        "conformance: rebuilds_taken per j = 0, 2, 4: {r:?}"
    );
}

// =========================================================================
// Criterion 8 — S6 and S4 calibrate
// =========================================================================

/// `width(w)`: `w` complete graphs on every engine (`impl_graphs` on the three
/// deciding engines, conclusive enumerator), `|W| = w` on both sweeping
/// engines, ranks `[1..w]`.
fn s6_check(w: usize, fail: &mut Vec<String>) {
    let name = format!("synth/width/w{w}");
    let f = fx(&name);
    let ranks = sizes(&(1..=w).collect::<Vec<_>>());
    for c in engines(Selector::Ltr) {
        let row = row_of(&grun(&f, &c));
        let l = format!("{name} {}", c.label());
        if num(&row, "reports") != 0 {
            fail.push(format!("{l}: reports"));
        }
        match c.engine {
            GridEngine::Enumerator => {}
            GridEngine::Stateful => {
                if (num(&row, "impl_graphs"), num(&row, "spec_graphs")) != (w, w) {
                    fail.push(format!("{l}: graphs"));
                }
            }
            GridEngine::CompleteFirst => {
                if (num(&row, "impl_graphs"), num(&row, "witnesses")) != (w, w)
                    || cell(&row, "sweep_sizes") != ranks
                {
                    fail.push(format!("{l}: graphs/|W|/ranks"));
                }
            }
            _ => {
                if (num(&row, "impl_graphs"), num(&row, "witnesses")) != (w, w)
                    || cell(&row, "gate_sweep_sizes") != ranks
                {
                    fail.push(format!("{l}: graphs/|W|/ranks"));
                }
            }
        }
    }
}

/// `chain(d)`: 1 graph and 1 signature; `max_paper_events = 4d` on the
/// sweeping engines (and stateful), the enumerator's
/// `max_paper_events_per_execution = 4d`; the Spec graph has `2d` paper
/// events and its `ord` (the stateful index's `Summary`) is a strict total
/// order on its `2d` visible positions.
fn s4_check(d: usize, fail: &mut Vec<String>) {
    let name = format!("synth/chain/d{d}");
    let f = fx(&name);
    for c in engines(Selector::Ltr) {
        let row = row_of(&grun(&f, &c));
        let l = format!("{name} {}", c.label());
        let col = if c.engine == GridEngine::Enumerator {
            "max_paper_events_per_execution"
        } else {
            "max_paper_events"
        };
        if num(&row, col) != 4 * d {
            fail.push(format!("{l}: {col} {} (4d = {})", num(&row, col), 4 * d));
        }
        if c.engine != GridEngine::Enumerator && num(&row, "impl_graphs") != 1 {
            fail.push(format!("{l}: impl_graphs"));
        }
    }
    let o = oracle(&f);
    if (o.imp.len(), o.spec.len(), num(&o.row, "signatures")) != (1, 1, 1) {
        fail.push(format!("{name}: counts"));
    }
    if paper_events_total(&o.spec[0]) != 2 * d || paper_events_total(&o.imp[0]) != 4 * d {
        fail.push(format!(
            "{name}: paper events Impl {} Spec {}",
            paper_events_total(&o.imp[0]),
            paper_events_total(&o.spec[0])
        ));
    }
    for (side, g) in [("Spec", &o.spec[0]), ("Impl", &o.imp[0])] {
        let s = summary(g, &f.visible);
        let n = 2 * d;
        let pos: BTreeSet<_> = s
            .ord
            .iter()
            .flat_map(|(a, b)| [a.clone(), b.clone()])
            .collect();
        if pos.len() != n || s.ord.len() != n * (n - 1) / 2 {
            fail.push(format!(
                "{name} {side}: ord over {} positions with {} pairs, a chain of {n} has {}",
                pos.len(),
                s.ord.len(),
                n * (n - 1) / 2
            ));
        }
    }
}

/// **Criterion 8 at the hand-count sizes** (`w = 2`, `d = 2`).
#[test]
fn c08_width_and_chain_calibrate_at_2() {
    let mut fail = Vec::new();
    s6_check(2, &mut fail);
    s4_check(2, &mut fail);
    assert!(
        fail.is_empty(),
        "conformance: criterion 8:\n  {}",
        fail.join("\n  ")
    );
}

/// **Criterion 8** at the pilot sizes `w, d ∈ {2, 8, 32}`.
#[test]
#[ignore = "beyond the hand-count sizes: one test per process"]
fn c08_width_and_chain_calibrate_at_the_pilot_sizes() {
    let mut fail = Vec::new();
    for x in [2, 8, 32] {
        s6_check(x, &mut fail);
        s4_check(x, &mut fail);
    }
    assert!(
        fail.is_empty(),
        "conformance: criterion 8:\n  {}",
        fail.join("\n  ")
    );
}

// =========================================================================
// Criterion 10 — the line test (through `eval::Driver`, one process per row)
// =========================================================================

/// **Criterion 10, the line test** (round 04 M1(ii), round 05 m2). A spec of
/// two synthetic lines built from `SynthPoint::row_spec` — `share/c=m/family`
/// (`2^m` Impl graphs: censors within the line under a 2 s tier) and
/// `share/c=0/family` (one graph at every `m`) — complete-first `Ltr`, timed,
/// `rep = 0`, through `eval::Driver` (one child process per row). Expected: on
/// the first line some point is censored (`capped_*`), every smaller point is
/// `ok`, and **every** larger point is `skipped_after_censor`; on the other
/// line every point is `ok` and none is skipped.
#[test]
#[ignore = "spawns one child process per row (the runner's)"]
fn c10_the_line_test() {
    let tier = Tier {
        name: "t2s".to_owned(),
        wall: Duration::from_secs(2),
        mem_kb: 4 * 1024 * 1024,
    };
    let config = cf_cfg(Selector::Ltr);
    let lines = ["share/c=m/family", "share/c=0/family"];
    let rows: Vec<_> = synth_grid()
        .into_iter()
        .filter(|p| p.in_grid && lines.contains(&p.line))
        .map(|p| p.row_spec(&config, &tier, RunKind::Timed, 0))
        .collect();
    assert_eq!(rows.len(), 12, "conformance: two lines of six points");
    let spec = Spec {
        name: "SYNTH-LINES".to_owned(),
        rows,
    };
    let out = std::env::temp_dir().join(format!("tf-synth-line-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out);
    std::fs::create_dir_all(&out).expect("conformance: the store directory");
    let d = Driver {
        spec: spec.clone(),
        specs: vec![spec],
        out_dir: out.clone(),
        sample_period: Duration::from_millis(100),
        probes: Probes::real(),
        allow_mixed: true,
        only: None,
    };
    let sum = d
        .run()
        .unwrap_or_else(|e| panic!("conformance: the driver refused: {}", e.text()));
    let rows = read_rows(&d.store_path())
        .unwrap_or_else(|e| panic!("conformance: the store: {}", e.text()));
    let class = |m: usize, c: usize| -> String {
        let f = format!("synth/share/m{m}c{c}");
        rows.iter()
            .find(|r| r.get("fixture").map(String::as_str) == Some(f.as_str()))
            .and_then(|r| r.get("end_class").cloned())
            .unwrap_or_else(|| panic!("conformance: no row for {f}"))
    };
    let ms = [2usize, 4, 8, 12, 16, 24];
    let a: Vec<String> = ms.iter().map(|&m| class(m, m)).collect();
    let b: Vec<String> = ms.iter().map(|&m| class(m, 0)).collect();
    note!("line c=m: {a:?}\nline c=0: {b:?}\nsummary: {sum:?}");
    let first = a
        .iter()
        .position(|c| c.starts_with("capped_"))
        .unwrap_or_else(|| panic!("conformance: nothing censored on c=m: {a:?}"));
    for (i, c) in a.iter().enumerate() {
        let want = if i < first {
            "ok"
        } else if i == first {
            c.as_str()
        } else {
            "skipped_after_censor"
        };
        assert_eq!(c, want, "conformance: c=m line at m = {}: {a:?}", ms[i]);
    }
    assert!(
        b.iter().all(|c| c == "ok"),
        "conformance: the other line: {b:?}"
    );
    assert_eq!(sum.skipped_after_censor, ms.len() - first - 1);
    let _ = std::fs::remove_dir_all(&out);
}

// =========================================================================
// Gate-4 round 01 M2 — T1 diagnosed by installation order
// =========================================================================

/// Every event of `g` in installation (stamp) order, rendered `thread:label`
/// with the thread's origination vector and paper-event count *at that
/// point*: `S<v>`/`R<t:v>` as [`shape`], `TC>child`, `Begin`, `End`.
fn installation_order(g: &ExecutionGraph) -> Vec<String> {
    let mut evs: Vec<(usize, Event)> = Vec::new();
    for t in g.thread_ids() {
        for i in 0..g.thread_size(t) {
            let e = Event::new(t, i as u32);
            let l = g.label(e);
            if l.stamped() {
                evs.push((l.stamp(), e));
            }
        }
    }
    evs.sort();
    evs.into_iter()
        .filter_map(|(st, e)| {
            let who = tname(g, e.thread);
            let what = match g.label(e) {
                LabelEnum::SendMsg(s) => format!("S{}", int(s.val())),
                LabelEnum::RecvMsg(r) => match r.rf() {
                    Some(rf) => format!(
                        "R<{}:{}",
                        tname(g, rf.thread),
                        int(g.val(e).expect("conformance: a read value"))
                    ),
                    None => "R<\u{22a5}".to_owned(),
                },
                LabelEnum::TCreate(c) => format!("TC>{}", c.name().clone().unwrap_or_default()),
                LabelEnum::Begin(_) => "B".to_owned(),
                LabelEnum::End(_) => "E".to_owned(),
                LabelEnum::Block(_) => "Blk".to_owned(),
                _ => return None,
            };
            Some(format!("{st}:{who}:{what}"))
        })
        .collect()
}

/// The gated run of the fixture `name` under `s`, `Exhaustive`/`Always`, with
/// its kept Impl graphs (called on `reset(2, 1)` and `reset-ctl(2, 1)`:
/// hand-count size, 4 graphs each).
fn kept_gated(name: &str, s: Selector) -> Vec<ExecutionGraph> {
    let r = ok(run_row_in_process(&fx(name), &gated_cfg(s), true));
    let GridRaw::Gated(o) = r.raw else {
        unreachable!("conformance: a gated run")
    };
    o.kept_impl_graphs
}

/// The send and receive part of [`installation_order`], stamps dropped
/// (`thread:S<v>` / `thread:R<t:v>`).
fn visible_order(g: &ExecutionGraph) -> Vec<String> {
    installation_order(g)
        .into_iter()
        .filter_map(|x| {
            let (_, rest) = x.split_once(':')?;
            let (_, label) = rest.split_once(':')?;
            (label.starts_with('S') || label.starts_with("R<")).then(|| rest.to_owned())
        })
        .collect()
}

/// Position of `what` (`thread:label`) in [`installation_order`].
fn at(order: &[String], what: &str) -> usize {
    order
        .iter()
        .position(|x| x.split_once(':').map(|(_, r)| r) == Some(what))
        .unwrap_or_else(|| panic!("conformance: `{what}` not installed"))
}

/// **Gate-4 round 01 M2 — T1 diagnosed.** `reset(2, 1)`, gated
/// `Exhaustive`/`Always`, kept Impl graphs, `FewestEvents` against `Ltr`.
///
/// Measured (no engine change; installation order from the labels' stamps):
/// 1. The **visible** installation order (sends and receives) is identical
///    under the two selectors in all four kept graphs, in the same graph
///    order — the documented `(paper_events, orig)` key does give `Ltr`'s
///    event order, as every derivation said.
/// 2. They differ in when the **revisited prefix is re-executed**. In the
///    branch entered by `b0`'s backward revisit of `c0` (kept graph 2, `c0 ←
///    2, c1 ← 1`), `FewestEvents` installs `a1.s`, `c1.r`, `b1.s` before `b0`
///    and `c0` resume (their `End`s come after `b1.s`); `Ltr` resumes them
///    first (`End`s before `a1.s`). Every execution re-runs the program from
///    `main`; `initialize_for_execution` enters every restored label into
///    `unreplayed_events`, and the runtime drains them as threads re-execute
///    (`is_replay`). `Selector::pick` keys `FewestEvents` on
///    `paper_events(&current.graph, t)` — the restored labels included — so
///    after the revisit `c0` and `b0` already "have" one event each (their
///    receive and send, restored but not yet re-executed) and lose the tie to
///    the untouched `a1, c1, b1` (0 each); `main` (0 paper events, `orig =
///    []`) re-executes every spawn first, so all six threads compete at once.
///    `Ltr` keys on `orig` alone: copy 0's restored prefix (lower `orig`) is
///    re-executed first. `Reverse` runs each spawned thread before `main`'s
///    next spawn (T2), so copy 0 is re-executed before copy 1's threads exist.
/// 3. Every gate that fires while those restored events are unreplayed is
///    skipped by F49's replay-frontier rule (`ctx.rs`: `unreplayed_events`
///    non-empty): `gates_skipped_replay` = 3 under `FewestEvents` (`a1.s`,
///    `c1.r(1)`, `b1.s` of that branch), 0 under `Ltr`. So that branch sets no
///    certificate: its completion is reported by the completion test
///    (`reports_by_completion_test` 1, `completion_sweeps` 1) and `b1`'s
///    backward revisit from it leaves an uncertified slot — the measured
///    `certificates_set` 2, `certified_states_revisited` 2, `carried_hits` 0,
///    `gates` 9 = `Ltr`'s 12 − 3.
#[test]
fn m2_fewest_events_defers_the_revisited_prefix_behind_fresh_events() {
    let (ltr, fe) = (
        kept_gated("synth/reset/k2s1", Selector::Ltr),
        kept_gated("synth/reset/k2s1", Selector::FewestEvents),
    );
    assert_eq!((ltr.len(), fe.len()), (4, 4), "conformance: kept graphs");
    for (i, (a, b)) in ltr.iter().zip(&fe).enumerate() {
        assert_eq!(
            visible_order(a).len(),
            6,
            "conformance: graph {i}: six visible events"
        );
        assert_eq!(
            visible_order(a),
            visible_order(b),
            "conformance: graph {i}: the visible installation order differs"
        );
    }
    // Graph 2 is the branch entered by `b0`'s revisit of `c0`.
    for (s, g, resumed_first) in [("Ltr", &ltr[2], true), ("FewestEvents", &fe[2], false)] {
        let o = installation_order(g);
        assert_eq!(
            shape(g, "c0"),
            owned(&["R<b0:2"]),
            "conformance: {s}: graph 2 is the c0 <- b0 branch"
        );
        let c0_end = at(&o, "c0:E");
        let b0_end = at(&o, "b0:E");
        let a1_s = at(&o, "a1:S1");
        let b1_s = at(&o, "b1:S2");
        if resumed_first {
            assert!(c0_end < a1_s && b0_end < a1_s, "conformance: {s}: {o:?}");
        } else {
            assert!(c0_end > b1_s && b0_end > b1_s, "conformance: {s}: {o:?}");
        }
    }
    let pick = |s: Selector| {
        let r = gated_row("synth/reset/k2s1", s);
        [
            "gates",
            "gates_skipped_replay",
            "gate_sweeps_failing",
            "reports_by_completion_test",
            "completion_sweeps",
            "certified_states_revisited",
            "carried_hits",
        ]
        .map(|k| num(&r, k))
    };
    assert_eq!(
        pick(Selector::Ltr),
        [12, 0, 3, 0, 0, 3, 1],
        "conformance: Ltr"
    );
    assert_eq!(
        pick(Selector::FewestEvents),
        [9, 3, 2, 1, 1, 2, 0],
        "conformance: FewestEvents"
    );
}

/// The F83 window's counters of one gated row: `gates_skipped_replay`,
/// `gate_sweeps_failing`, `completion_sweeps_failing`, their sum,
/// `certificates_set`, `certificate_resets`.
fn window(name: &str, s: Selector) -> [usize; 6] {
    let r = gated_row(name, s);
    let (g, c) = (
        num(&r, "gate_sweeps_failing"),
        num(&r, "completion_sweeps_failing"),
    );
    [
        num(&r, "gates_skipped_replay"),
        g,
        c,
        g + c,
        num(&r, "certificates_set"),
        num(&r, "certificate_resets"),
    ]
}

/// **Gate-4 round 02 M1(c) — the F83 window on the control, measured.**
/// `reset-ctl(2, 1)` (spawn `a, b, c`: `c_i ← b_i` is a **forward** pop),
/// gated `Exhaustive`/`Always`, kept Impl graphs, and the window's counters
/// for the family and the control, `k = 1, 2, 3`, all three selectors.
///
/// Measured:
/// 1. The visible installation order of every kept control graph is the same
///    under `FewestEvents` and `Ltr`. In the branch entered by `c0`'s forward
///    pop to `b0` (kept graph 2, `c0 ← 2, c1 ← 1`), `FewestEvents` installs
///    `a1.s`, `b1.s`, `c1.r` before `c0` resumes (`c0:End` after `c1.r`);
///    `Ltr` resumes `c0` first (`c0:End` before `a1.s`). So **the window
///    opens after a forward revisit too** (restored by `cut_to_stamp`).
/// 2. `[gates_skipped_replay, gate_sweeps_failing, completion_sweeps_failing,
///    sum, certificates_set, certificate_resets]`:
///
///    | fixture | `Ltr` = `Reverse` | `FewestEvents` |
///    |---|---|---|
///    | `reset(1,1)` | `[0,1,0,1,1,0]` | `[0,1,0,1,1,0]` |
///    | `reset(2,1)` | `[0,3,0,3,3,0]` | `[3,2,1,3,2,0]` |
///    | `reset(3,1)` | `[0,7,0,7,7,0]` | `[12,5,2,7,5,0]` |
///    | `reset-ctl(1,1)` | `[0,1,0,1,1,1]` | `[0,1,0,1,1,1]` |
///    | `reset-ctl(2,1)` | `[0,2,0,2,2,2]` | `[3,1,1,2,1,1]` |
///    | `reset-ctl(3,1)` | `[0,3,0,3,3,3]` | `[12,2,2,4,2,2]` |
///
///    The family's total failing sweeps (gate + completion) are `2^k − 1`
///    under all three selectors: the window relocates them. The control's
///    total equals its `Ltr` value `k` at `k = 1, 2`, and is **4 against 3 at
///    `k = 3`**: there the window adds one failing sweep (not traced further).
#[test]
fn m2_the_window_opens_after_a_forward_revisit_on_the_control() {
    let n = "synth/reset-ctl/k2s1";
    let (ltr, fe) = (
        kept_gated(n, Selector::Ltr),
        kept_gated(n, Selector::FewestEvents),
    );
    assert_eq!((ltr.len(), fe.len()), (4, 4), "conformance: kept graphs");
    for (i, (a, b)) in ltr.iter().zip(&fe).enumerate() {
        assert_eq!(visible_order(a).len(), 6, "conformance: graph {i}");
        assert_eq!(visible_order(a), visible_order(b), "conformance: graph {i}");
    }
    for (s, g, resumed_first) in [("Ltr", &ltr[2], true), ("FewestEvents", &fe[2], false)] {
        assert_eq!(
            shape(g, "c0"),
            owned(&["R<b0:2"]),
            "conformance: {s}: graph 2"
        );
        let o = installation_order(g);
        let (c0_end, a1_s, c1_r) = (at(&o, "c0:E"), at(&o, "a1:S1"), at(&o, "c1:R<a1:1"));
        if resumed_first {
            assert!(c0_end < a1_s, "conformance: {s}: {o:?}");
        } else {
            assert!(c0_end > c1_r, "conformance: {s}: {o:?}");
        }
    }
    let ltr_rows: [(&str, [usize; 6]); 6] = [
        ("synth/reset/k1s1", [0, 1, 0, 1, 1, 0]),
        ("synth/reset/k2s1", [0, 3, 0, 3, 3, 0]),
        ("synth/reset/k3s1", [0, 7, 0, 7, 7, 0]),
        ("synth/reset-ctl/k1s1", [0, 1, 0, 1, 1, 1]),
        ("synth/reset-ctl/k2s1", [0, 2, 0, 2, 2, 2]),
        ("synth/reset-ctl/k3s1", [0, 3, 0, 3, 3, 3]),
    ];
    let fe_rows: [[usize; 6]; 6] = [
        [0, 1, 0, 1, 1, 0],
        [3, 2, 1, 3, 2, 0],
        [12, 5, 2, 7, 5, 0],
        [0, 1, 0, 1, 1, 1],
        [3, 1, 1, 2, 1, 1],
        [12, 2, 2, 4, 2, 2],
    ];
    let mut fail = Vec::new();
    for ((name, l), f) in ltr_rows.iter().zip(fe_rows) {
        for (s, want) in [
            (Selector::Ltr, *l),
            (Selector::Reverse, *l),
            (Selector::FewestEvents, f),
        ] {
            let got = window(name, s);
            if got != want {
                fail.push(format!("{name} {s:?}: {got:?} want {want:?}"));
            }
        }
    }
    assert!(
        fail.is_empty(),
        "conformance: the window:\n  {}",
        fail.join("\n  ")
    );
}
