//! P4-DIFF gate 3: the **tester's** tests for the differential grid (criteria
//! `P4-DIFF.md` revision 5.2). The lead's `grid.rs` runs configurations and
//! carries no judgement; every threshold, label, expected value and assertion
//! is here or in `grid_oracle.rs` (X1, criteria 13–14).
//!
//! Every expected value was derived from the criteria and the paper before
//! `grid.rs` was read; the derivations are in
//! `plan/traceForge/log/dev/P4-DIFF.report.md`, Part 0, under the labels
//! `D1`..`D8` cited on each test. Tests are named by criterion.
//!
//! **The default subset** (criterion 12): `corpus(7, 3)` (21 pairs), `ex:naive`
//! at `k ≤ 3` (both encodings and E2's revisit fixture), the paper pairs and
//! R1/R2, run once per process into a shared grid ([`grid`]) on one worker
//! thread, uncapped (round 05 n1). Every heavier run is `#[ignore]`d with its
//! measured runtime in its rustdoc; capped and memory configurations are one
//! `#[ignore]`d test each, to be run one per process (`--test-threads=1`).
//!
//! Conventions this file keeps because `s5_tests`' source scans read it: no
//! print macro anywhere (tables go through `grid::Tables`, which writes to the
//! file named by `P4_DIFF_TABLES`), and every panic-family message starts with
//! `conformance:`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, OnceLock};
use std::time::Duration;

use crate::conformance::config::{GatePolicy, GatedMode};
use crate::conformance::ctx::ReportKind;
use crate::conformance::gated::ReportSite;
use crate::conformance::generator;
use crate::conformance::grid::{
    corpus_fixtures, naive_e2_fixture, naive_fixture, paper_fixtures, row_of, row_of_end, run_grid,
    two_pc_fixtures, Budget, Fixture, GridConfig, GridEnd, GridEngine, GridRaw, GridResult, Group,
    Row, TableEntry, Tables,
};
use crate::conformance::grid_oracle::{
    begin_of, canon_key, certify, plan_key, restrict_to_porf, send_of, with_send_value, Cause,
    Claim, Families,
};
use crate::conformance::report::{
    ConfCounters, ConfVerdict, CoverCounters, ReplaySnapshot, ReportCause, ReportGate, ReportTag,
    SearchEnd,
};
use crate::conformance::selector::Selector;
use crate::exec_graph::ExecutionGraph;

// =========================================================================
// Harness
// =========================================================================

const SELECTORS: [Selector; 3] = [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];
const POLICIES: [GatePolicy; 4] = [
    GatePolicy::Never,
    GatePolicy::Always,
    GatePolicy::Budget(1),
    GatePolicy::Budget(2),
];

/// A completed run, or the test fails with the runner's own words: a panic
/// on a sanctioned fixture is a T-finding, verbatim (L1), and an uncapped
/// run cannot be capped.
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
        GridEnd::Capped {
            fixture,
            config,
            after,
        } => panic!(
            "conformance: `{fixture}` under {} was capped after {after:?}",
            config.label()
        ),
    }
}

fn run(f: &Fixture, c: &GridConfig) -> GridResult {
    ok(run_grid(f, c, None))
}

fn serialized(s: &ReplaySnapshot) -> bool {
    matches!(s, ReplaySnapshot::Serialized(_))
}

/// One report, engine-independent: what the oracle reads (X3's mapping).
struct Rep<'a> {
    graph: &'a ExecutionGraph,
    tag: ReportTag,
    cause: Cause,
    serialized: bool,
    site: String,
}

/// X3: the enumerator's tag is `ReportTag::of(cause, gate)`; completion
/// reports of the other engines are `CompleteCoverage`; a gated
/// `ReportSite::Gate(_)` is `GrowingExhaustion`.
///
/// **Exempt from X5 (d), stated (gate 4 round 01 m2):** a `GridRaw::Verdict`
/// — the `Verify` route of criterion 7's violating 2PC rows and the
/// precheck arm of criterion 9 — yields no report here. The rendered
/// `ConfReport` carries no `ExecutionGraph` (only a dump and a serialized
/// snapshot, whose deserialisation is out of scope: F80 and
/// `ReplaySnapshot`'s own disclaimer), so it cannot be certified on graphs.
/// The same pairs' reports are certified on the engine-only routes: the
/// precheck arm's engines through their `run_with` runs in the same grid,
/// and the 2PC violating pairs at N ≤ 3 through the full grid's enumerator,
/// stateful, complete-first and gated runs (`c08`), and the coordinator and
/// ring violating rows at N = 4 in `x6_two_pc_n4_outside_the_exhaustive_sweeps`.
/// The leader violating row at N = 4 has no oracle run within reach (its
/// capped oracle run: `cap_leader_conforming_n4_oracle_run`), so its reports
/// are certified nowhere — listed in the report.
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
                let gate = ReportGate::of(rep.gate);
                Rep {
                    graph: &rep.graph,
                    tag: ReportTag::of(&rc, gate),
                    cause,
                    serialized: serialized(&rep.replay),
                    site: format!("{gate:?}"),
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
                site: "Completion".to_owned(),
            })
            .collect(),
        GridRaw::CompleteFirst(o) => {
            assert!(
                o.cut_reports.is_empty(),
                "conformance: a cut report on a grid run with the cut off"
            );
            o.reports
                .iter()
                .map(|(g, s)| Rep {
                    graph: g,
                    tag: ReportTag::CompleteCoverage,
                    cause: Cause::NoCover,
                    serialized: serialized(s),
                    site: "Completion".to_owned(),
                })
                .collect()
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
                site: format!("{site:?}"),
            })
            .collect(),
        GridRaw::Verdict(_) => Vec::new(),
    }
}

/// The complete Impl graphs a sweeping run kept.
fn kept_impl(r: &GridResult) -> &[ExecutionGraph] {
    match &r.raw {
        GridRaw::Stateful(o) => &o.kept_impl_graphs,
        GridRaw::CompleteFirst(o) => &o.kept_impl_graphs,
        GridRaw::Gated(o) => &o.kept_impl_graphs,
        GridRaw::Enumerator(_) | GridRaw::Verdict(_) => &[],
    }
}

/// What X5 reads of a run.
#[derive(Clone, Debug)]
struct Status {
    reports: usize,
    exhaustions: usize,
    end: SearchEnd,
    /// X3/X5: a `spec_error` on the enumerator, or `aborted`/`spec_errors` on
    /// a `run_with` engine, on a pair the oracle run cleared.
    failure: Option<String>,
}

fn status(r: &GridResult) -> Status {
    match &r.raw {
        GridRaw::Enumerator(o) => Status {
            reports: o.reports.len(),
            exhaustions: o.exhaustions.len(),
            end: o.end,
            failure: o
                .spec_error
                .as_ref()
                .map(|(t, e)| format!("spec_error on `{t}` at {e}")),
        },
        GridRaw::Stateful(o) => Status {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (!o.spec_errors.is_empty()).then(|| format!("{:?}", o.spec_errors)),
        },
        GridRaw::CompleteFirst(o) => Status {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (o.aborted || !o.spec_errors.is_empty())
                .then(|| format!("aborted={} {:?}", o.aborted, o.spec_errors)),
        },
        GridRaw::Gated(o) => Status {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (o.aborted || !o.spec_errors.is_empty())
                .then(|| format!("aborted={} {:?}", o.aborted, o.spec_errors)),
        },
        GridRaw::Verdict(v) => match v {
            Ok(v) => {
                let o = v.outcome();
                Status {
                    reports: o.reports.len(),
                    exhaustions: o.exhaustions.len(),
                    end: o.end,
                    failure: None,
                }
            }
            Err(e) => Status {
                reports: 0,
                exhaustions: 0,
                end: SearchEnd::Unknown,
                failure: Some(format!("{e:?}")),
            },
        },
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Class {
    Conforms,
    Reported,
    Inconclusive,
}

/// `ConfVerdict::of`'s rule, written out (X3).
fn class(s: &Status) -> Class {
    if s.reports > 0 {
        Class::Reported
    } else if s.exhaustions == 0 && s.end == SearchEnd::StateSpaceExhausted {
        Class::Conforms
    } else {
        Class::Inconclusive
    }
}

/// X5 (a)'s bins, disjoint and exhaustive; `Unknown` is a failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Bin {
    InconclusiveReported,
    InconclusiveSilent,
    BoundedSilent,
    Conclusive,
}

fn bin(s: &Status) -> Bin {
    assert_ne!(
        s.end,
        SearchEnd::Unknown,
        "conformance: X5 a: a run ended `Unknown`"
    );
    if s.exhaustions > 0 {
        if s.reports > 0 {
            Bin::InconclusiveReported
        } else {
            Bin::InconclusiveSilent
        }
    } else if s.reports == 0
        && matches!(
            s.end,
            SearchEnd::MaxIterations(_) | SearchEnd::StoppedAtFirstReport
        )
    {
        Bin::BoundedSilent
    } else {
        Bin::Conclusive
    }
}

/// Which differential contract a configuration falls under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// Stateful, complete-first and gated `Exhaustive`, report-and-continue:
    /// the three enumerating engines (criterion 3).
    Enumerating,
    /// X5 e's first-report runs of the three sweeping engines (`stop` or
    /// gated first-failure).
    FirstReport,
    /// The enumerator, report-and-continue.
    Deciding,
    /// The enumerator under `stop_at_first_report`.
    DecidingStop,
}

fn kind(c: &GridConfig) -> Kind {
    match c.engine {
        GridEngine::Enumerator | GridEngine::Verify => {
            if c.stop_at_first_report {
                Kind::DecidingStop
            } else {
                Kind::Deciding
            }
        }
        GridEngine::Gated if c.gated_mode == GatedMode::FirstFailure => Kind::FirstReport,
        _ if c.stop_at_first_report => Kind::FirstReport,
        _ => Kind::Enumerating,
    }
}

/// The oracle run (X4): stateful, report-and-continue, `Ltr`, no bound.
fn oracle_config() -> GridConfig {
    GridConfig::new(GridEngine::Stateful)
}

/// The sweeping engines' configurations under one selector: stateful and
/// complete-first with and without the stop; gated exhaustive under every
/// policy, exhaustive with the stop, and first-failure under every policy.
fn sweep_configs(s: Selector) -> Vec<GridConfig> {
    let mut v = vec![
        GridConfig::new(GridEngine::Stateful).selector(s),
        GridConfig::new(GridEngine::Stateful).selector(s).stop(true),
        GridConfig::new(GridEngine::CompleteFirst).selector(s),
        GridConfig::new(GridEngine::CompleteFirst)
            .selector(s)
            .stop(true),
    ];
    for p in POLICIES {
        v.push(
            GridConfig::new(GridEngine::Gated)
                .selector(s)
                .gated(GatedMode::Exhaustive, p),
        );
    }
    v.push(
        GridConfig::new(GridEngine::Gated)
            .selector(s)
            .gated(GatedMode::Exhaustive, GatePolicy::Always)
            .stop(true),
    );
    for p in POLICIES {
        v.push(
            GridConfig::new(GridEngine::Gated)
                .selector(s)
                .gated(GatedMode::FirstFailure, p),
        );
    }
    v
}

/// The enumerator's configurations under one selector, all unlimited (the
/// differential contract is memo on; memo off is criterion 9's arm).
fn enum_configs(s: Selector) -> Vec<GridConfig> {
    let base = GridConfig::new(GridEngine::Enumerator)
        .selector(s)
        .budget(Budget::Unlimited);
    vec![
        base.clone().memo(true),
        base.clone().memo(true).stop(true),
        base.memo(false),
    ]
}

/// One pair's runs in the grid.
struct Pair {
    fixture: Fixture,
    oracle: GridResult,
    families: Option<Families>,
    excluded: Option<String>,
    /// Each run, with the enumerator's instrumented twin (X3).
    runs: Vec<(GridResult, Option<GridResult>)>,
}

fn compute_pair(f: Fixture, configs: &[GridConfig]) -> Pair {
    let oracle = run(&f, &oracle_config());
    let GridRaw::Stateful(o) = &oracle.raw else {
        unreachable!("conformance: the oracle run is stateful")
    };
    // X4: `spec_errors` first; then both ends must be exhaustive.
    if !o.spec_errors.is_empty() {
        let why = format!("Spec errors in the oracle run: {:?}", o.spec_errors);
        return Pair {
            fixture: f,
            oracle,
            families: None,
            excluded: Some(why),
            runs: Vec::new(),
        };
    }
    assert_eq!(
        (o.impl_end, o.spec_end),
        (
            SearchEnd::StateSpaceExhausted,
            SearchEnd::StateSpaceExhausted
        ),
        "conformance: X4: `{}`'s oracle run is not exhaustive",
        f.name
    );
    let families = Families::new(
        &o.kept_spec_graphs,
        &o.kept_impl_graphs,
        o.spec_errors.len(),
        &f.visible,
    );
    let mut runs = Vec::new();
    for c in configs {
        let r = run(&f, c);
        let twin =
            (c.engine == GridEngine::Enumerator).then(|| run(&f, &c.clone().instrumented(true)));
        runs.push((r, twin));
    }
    Pair {
        fixture: f,
        oracle,
        families: Some(families),
        excluded: None,
        runs,
    }
}

/// Run `fixtures` × `configs` on `workers` threads (each run on its own
/// grid thread).
fn compute(fixtures: Vec<Fixture>, configs: &[GridConfig], workers: usize) -> Vec<Pair> {
    let n = fixtures.len();
    let next = AtomicUsize::new(0);
    let out: Mutex<Vec<Option<Pair>>> = Mutex::new((0..n).map(|_| None).collect());
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= n {
                    break;
                }
                let p = compute_pair(fixtures[i].clone(), configs);
                out.lock().unwrap_or_else(|p| p.into_inner())[i] = Some(p);
            });
        }
    });
    out.into_inner()
        .unwrap_or_else(|p| p.into_inner())
        .into_iter()
        .map(|p| p.expect("conformance: a grid worker died"))
        .collect()
}

fn default_fixtures() -> Vec<Fixture> {
    let mut v = Vec::new();
    for k in 2..=3 {
        v.push(naive_fixture(k, 1));
        v.push(naive_fixture(k, 2));
        v.push(naive_e2_fixture(k));
    }
    v.extend(paper_fixtures());
    v.extend(corpus_fixtures(7, 3));
    v
}

fn all_configs() -> Vec<GridConfig> {
    let mut v = Vec::new();
    for s in SELECTORS {
        v.extend(enum_configs(s));
        v.extend(sweep_configs(s));
    }
    v
}

static GRID: OnceLock<Mutex<Vec<Pair>>> = OnceLock::new();

/// The default subset's grid, computed once per process.
fn grid() -> MutexGuard<'static, Vec<Pair>> {
    GRID.get_or_init(|| Mutex::new(compute(default_fixtures(), &all_configs(), 1)))
        .lock()
        .unwrap_or_else(|p| p.into_inner())
}

/// Fail with every collected failure. The text is also written to stderr
/// directly: `generator`'s `raw_cancel` swaps the process-wide panic hook
/// for a no-op and back without synchronisation, so after concurrent engine
/// runs a test's panic message can be lost (observation O1 of the report).
fn fail_if(failures: Vec<String>, what: &str) {
    if failures.is_empty() {
        return;
    }
    let text = format!(
        "{what}: {} failure(s):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    {
        use std::io::Write;
        let _ = std::io::stderr().write_all(format!("conformance: {text}\n").as_bytes());
    }
    panic!("conformance: {text}");
}

/// The verdicts the paper and the closed parts give the paper pairs (D4).
fn expected_paper_class(name: &str) -> Option<Class> {
    let conforms = [
        "relay/paper",
        "relay/paper/rev",
        "ex:nogate",
        "ex:sched",
        "ex:restart",
        "traces/self",
    ];
    let reports = [
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
    if name.starts_with("2pc/") {
        // Criterion 7's verdicts: the conforming tables conform, the eager
        // and split-brain tables report.
        return Some(if name.contains("/conf/") {
            Class::Conforms
        } else {
            Class::Reported
        });
    }
    match name {
        "ndk2/conf" | "ndk3/conf" => return Some(Class::Conforms),
        "ndk3/bad_A" => return Some(Class::Reported),
        _ => {}
    }
    if name.starts_with("ex:naive") || reports.contains(&name) {
        Some(Class::Reported)
    } else if conforms.contains(&name) {
        Some(Class::Conforms)
    } else {
        None
    }
}

/// The number of uncovered Impl graphs per paper pair (D4): the size of the
/// enumerating engines' report set.
fn expected_report_set_size(name: &str, k: Option<usize>) -> Option<usize> {
    let fact = |k: usize| (1..=k).product::<usize>();
    match name {
        n if n.starts_with("ex:naive") => k.map(fact),
        "ex:cone" | "relay/apparatus" | "ex:rebuild" | "blocking/apparatus" | "blocking/cfirst"
        | "reset-pair" | "forward-pop" | "R1" | "R2" => Some(1),
        "a27" => Some(2),
        "relay/paper" | "relay/paper/rev" | "ex:nogate" | "ex:sched" | "ex:restart"
        | "traces/self" => Some(0),
        _ => None,
    }
}

/// `generator::corpus(7, 3)`'s pinned expectations, by the grid's fixture
/// name.
fn corpus_expectations(per_mode: usize) -> BTreeMap<String, bool> {
    generator::corpus(7, per_mode)
        .into_iter()
        .map(|p| {
            (
                format!("corpus/{:?}/{:#x}", p.mode, p.seed),
                p.expect_inclusion,
            )
        })
        .collect()
}

// =========================================================================
// Criterion 1 — the plan key against canonical equality, across runs
// =========================================================================

/// **Criterion 1 (X2).** Over the kept Impl families of the oracle run and
/// of every stateful, complete-first and gated run (each selector, mode and
/// policy), matching complete graphs by canonical equality equals matching
/// them by the plan key: each plan key names exactly one canonical form and
/// vice versa, across runs. Every enumerating run's kept family equals the
/// oracle family under both keys, and each run holds each key once
/// (Must's optimality; no A9 pair is in the set — criterion 10).
fn check_c01(g: &[Pair]) -> Vec<String> {
    let mut failures = Vec::new();
    let mut graphs = 0usize;
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        let v = &p.fixture.visible;
        let mut plan_to_canon: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut canon_to_plan: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let family = |gs: &[ExecutionGraph]| -> (Vec<String>, Vec<String>) {
            (
                gs.iter().map(|x| canon_key(x, v)).collect(),
                gs.iter().map(|x| plan_key(x, v)).collect(),
            )
        };
        let (oc, op) = family(kept_impl(&p.oracle));
        let oc_set: BTreeSet<String> = oc.iter().cloned().collect();
        let op_set: BTreeSet<String> = op.iter().cloned().collect();
        let all = std::iter::once(&p.oracle).chain(p.runs.iter().map(|(r, _)| r));
        for r in all {
            let gs = kept_impl(r);
            if gs.is_empty() && !matches!(r.raw, GridRaw::Stateful(_)) {
                continue;
            }
            let (c, pk) = family(gs);
            graphs += gs.len();
            for (ck, pkk) in c.iter().zip(&pk) {
                plan_to_canon
                    .entry(pkk.clone())
                    .or_default()
                    .insert(ck.clone());
                canon_to_plan
                    .entry(ck.clone())
                    .or_default()
                    .insert(pkk.clone());
            }
            let cset: BTreeSet<String> = c.iter().cloned().collect();
            if cset.len() != c.len() {
                failures.push(format!(
                    "{} {}: multiplicity > 1 ({} graphs, {} keys)",
                    p.fixture.name,
                    r.config.label(),
                    c.len(),
                    cset.len()
                ));
            }
            if kind(&r.config) == Kind::Enumerating {
                let pset: BTreeSet<String> = pk.iter().cloned().collect();
                if cset != oc_set || pset != op_set {
                    failures.push(format!(
                        "{} {}: kept family differs from the oracle family ({} vs {} canonical, \
                         {} vs {} plan keys)",
                        p.fixture.name,
                        r.config.label(),
                        cset.len(),
                        oc_set.len(),
                        pset.len(),
                        op_set.len()
                    ));
                }
            }
        }
        for (k, cs) in &plan_to_canon {
            if cs.len() != 1 {
                failures.push(format!(
                    "{}: one plan key, {} canonical forms: {k}",
                    p.fixture.name,
                    cs.len()
                ));
            }
        }
        for (k, ps) in &canon_to_plan {
            if ps.len() != 1 {
                failures.push(format!(
                    "{}: one canonical form, {} plan keys: {k}",
                    p.fixture.name,
                    ps.len()
                ));
            }
        }
    }
    if graphs < 1000 {
        failures.push(format!("criterion 1 saw only {graphs} graphs"));
    }
    failures
}

#[test]
fn c01_the_plan_key_agrees_with_canonical_equality_across_runs() {
    fail_if(check_c01(&grid()), "criterion 1");
}

// =========================================================================
// Criterion 2 — verdict agreement, every selector
// =========================================================================

/// **Criterion 2 (X5 b), and X5 e on the first-report runs.** On every
/// conclusive run of a pair, "some violation exists" agrees across the four
/// engines, every mode, policy and selector; it equals the oracle family's
/// "some Impl graph is uncovered", D4's expectation on the paper pairs, and
/// `generator`'s pinned `expect_inclusion` on the corpus. First-report runs
/// report at most one graph, exactly one iff a violation exists, and end
/// `StoppedAtFirstReport` iff they reported; the enumerator under the stop
/// reports none on a conforming pair and at least one otherwise (F81
/// occurrences counted, not failed). Any `aborted`/`spec_errors` on an
/// included pair is a failure.
fn check_c02(
    g: &[Pair],
    corpus: &BTreeMap<String, bool>,
    runs_per_pair: usize,
) -> (Vec<String>, Vec<String>) {
    let mut failures = Vec::new();
    let mut f81 = Vec::new();
    let mut compared = 0usize;
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        let fam = p
            .families
            .as_ref()
            .expect("conformance: included pair has families");
        let violation = fam.some_impl_uncovered();
        if let Some(c) = expected_paper_class(&p.fixture.name) {
            if (c == Class::Reported) != violation {
                failures.push(format!(
                    "{}: D4 expects {c:?}, the oracle family says violation={violation}",
                    p.fixture.name
                ));
            }
        }
        if let Some(incl) = corpus.get(&p.fixture.name) {
            if *incl == violation {
                failures.push(format!(
                    "{}: generator pins expect_inclusion={incl}, the oracle family says \
                     violation={violation}",
                    p.fixture.name
                ));
            }
        }
        for (r, _) in &p.runs {
            let s = status(r);
            let label = format!("{} {}", p.fixture.name, r.config.label());
            if let Some(why) = &s.failure {
                failures.push(format!("{label}: failure on an included pair: {why}"));
                continue;
            }
            if bin(&s) != Bin::Conclusive {
                continue;
            }
            compared += 1;
            if (s.reports > 0) != violation {
                failures.push(format!(
                    "{label}: reports={} but violation={violation}",
                    s.reports
                ));
            }
            match kind(&r.config) {
                Kind::FirstReport => {
                    let want = usize::from(violation);
                    if s.reports != want {
                        failures.push(format!("{label}: first-report run reported {}", s.reports));
                    }
                    let want_end = if violation {
                        SearchEnd::StoppedAtFirstReport
                    } else {
                        SearchEnd::StateSpaceExhausted
                    };
                    if s.end != want_end {
                        failures.push(format!("{label}: end {:?}", s.end));
                    }
                }
                Kind::DecidingStop => {
                    if s.reports > 1 || (s.reports >= 1 && s.end == SearchEnd::StateSpaceExhausted)
                    {
                        f81.push(format!(
                            "{} {:?} reports={} end={:?}",
                            p.fixture.name, r.config.selector, s.reports, s.end
                        ));
                    }
                    if !violation && s.end != SearchEnd::StateSpaceExhausted {
                        failures.push(format!("{label}: conforming, end {:?}", s.end));
                    }
                }
                Kind::Enumerating | Kind::Deciding => {
                    if s.end != SearchEnd::StateSpaceExhausted {
                        failures.push(format!("{label}: end {:?}", s.end));
                    }
                }
            }
        }
    }
    // Every configuration of every included pair is conclusive on the sets
    // this is called on (criterion 5), so each one is compared.
    let included = g.iter().filter(|p| p.excluded.is_none()).count();
    if compared != runs_per_pair * included {
        failures.push(format!(
            "{compared} runs compared for {included} pairs, not {runs_per_pair} each"
        ));
    }
    (failures, f81)
}

/// The pairs a grid excluded (X4: Spec errors in the oracle run), pinned
/// against their measured value (round 01 m6).
fn excluded_names(g: &[Pair]) -> Vec<String> {
    g.iter()
        .filter(|p| p.excluded.is_some())
        .map(|p| p.fixture.name.clone())
        .collect()
}

#[test]
fn c02_verdict_agreement_every_selector() {
    let g = grid();
    // 3 selectors × (3 enumerator + 13 sweeping configurations) = 48.
    let (mut failures, f81) = check_c02(&g, &corpus_expectations(3), 48);
    // Round 01 m6: the default subset excludes nothing (measured).
    if !excluded_names(&g).is_empty() {
        failures.push(format!(
            "excluded pairs {:?}, pinned none",
            excluded_names(&g)
        ));
    }
    // F81 is counted, not failed (X5 e). Measured on the default subset:
    // exactly `ex:rebuild` under each selector — its one report is at
    // `RevisitApply` and the stopped run ends `StateSpaceExhausted` (F81's
    // second face). Pinned so that a change is seen.
    let want: Vec<String> = SELECTORS
        .iter()
        .map(|s| format!("ex:rebuild {s:?} reports=1 end=StateSpaceExhausted"))
        .collect();
    if f81 != want {
        failures.push(format!("F81 occurrences {f81:?}, pinned {want:?}"));
    }
    fail_if(failures, "criterion 2");
}

// =========================================================================
// Criterion 3 — report-key sets of the three enumerating engines
// =========================================================================

/// **Criterion 3 (X5 c).** The canonical report-key sets of stateful,
/// complete-first and gated exhaustive under each policy are equal, under
/// each selector, and equal to the oracle family's uncovered members
/// (`thm:stateful`/`thm:cfirst`/`thm:gated`); each key is reported once; D4's
/// set sizes hold on the paper pairs.
fn check_c03(g: &[Pair], sets_per_pair: usize) -> Vec<String> {
    let mut failures = Vec::new();
    let mut sets = 0usize;
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        let fam = p.families.as_ref().expect("conformance: families");
        let want = fam.uncovered_keys();
        if let Some(n) = expected_report_set_size(&p.fixture.name, p.fixture.k) {
            if want.len() != n {
                failures.push(format!(
                    "{}: D4 expects {n} uncovered graphs, the family has {}",
                    p.fixture.name,
                    want.len()
                ));
            }
        }
        for (r, _) in p
            .runs
            .iter()
            .filter(|(r, _)| kind(&r.config) == Kind::Enumerating)
        {
            let keys: Vec<String> = reports_of(r)
                .iter()
                .map(|x| canon_key(x.graph, &p.fixture.visible))
                .collect();
            let set: BTreeSet<String> = keys.iter().cloned().collect();
            sets += 1;
            if set.len() != keys.len() {
                failures.push(format!(
                    "{} {}: a key reported twice",
                    p.fixture.name,
                    r.config.label()
                ));
            }
            if set != want {
                failures.push(format!(
                    "{} {}: report set of {} differs from the uncovered family of {}",
                    p.fixture.name,
                    r.config.label(),
                    set.len(),
                    want.len()
                ));
            }
        }
    }
    // Three selectors × (stateful, complete-first, four gated policies).
    let included = g.iter().filter(|p| p.excluded.is_none()).count();
    if sets != sets_per_pair * included {
        failures.push(format!(
            "{sets} report sets for {included} pairs, not {sets_per_pair} each"
        ));
    }
    failures
}

#[test]
fn c03_report_key_sets_are_equal_every_selector() {
    fail_if(check_c03(&grid(), 18), "criterion 3");
}

// =========================================================================
// Criterion 4 — certification of every report, R1/R2, the oracle's audit
// =========================================================================

/// **Criterion 4 (X4, X5 d).** Every report of every completed run — every
/// engine, mode, policy and selector, the enumerator's memo arms and its
/// instrumented twins, and the oracle run's own reports — passes its tag's
/// case of the oracle.
/// `all_tags`: the set contains R1/R2-like visible-error pairs, so every
/// semantic tag must have been certified at least once.
fn check_c04(g: &[Pair], all_tags: bool) -> Vec<String> {
    let mut failures = Vec::new();
    let mut certified = 0usize;
    let mut by_tag: BTreeMap<String, usize> = BTreeMap::new();
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        let fam = p.families.as_ref().expect("conformance: families");
        let runs = std::iter::once(&p.oracle).chain(
            p.runs
                .iter()
                .flat_map(|(r, t)| std::iter::once(r).chain(t.iter())),
        );
        for r in runs {
            for rep in reports_of(r) {
                let claim = Claim {
                    graph: rep.graph,
                    tag: rep.tag,
                    cause: rep.cause.clone(),
                    serialized: rep.serialized,
                };
                match certify(fam, &claim) {
                    Ok(()) => {
                        certified += 1;
                        *by_tag.entry(format!("{:?}", rep.tag)).or_default() += 1;
                    }
                    Err(e) => failures.push(format!(
                        "{} {} report at {} ({:?}): {e}",
                        p.fixture.name,
                        r.config.label(),
                        rep.site,
                        rep.tag
                    )),
                }
            }
        }
    }
    for t in ["GrowingExhaustion", "CompleteCoverage", "VisibleError"] {
        if all_tags && by_tag.get(t).copied().unwrap_or(0) == 0 {
            failures.push(format!("no {t} report was certified: {by_tag:?}"));
        }
    }
    if certified < 1000 {
        failures.push(format!("only {certified} reports certified"));
    }
    failures
}

#[test]
fn c04_every_report_of_every_completed_run_is_certified() {
    fail_if(check_c04(&grid(), true), "criterion 4 (every report)");
}

/// The default subset's pair named `name`.
fn pair<'a>(g: &'a [Pair], name: &str) -> &'a Pair {
    g.iter()
        .find(|p| p.fixture.name == name)
        .unwrap_or_else(|| panic!("conformance: no pair `{name}` in the grid"))
}

/// The first run of `p` matching `pred`.
fn run_where(p: &Pair, pred: impl Fn(&GridConfig) -> bool) -> &GridResult {
    p.runs
        .iter()
        .map(|(r, _)| r)
        .find(|r| pred(&r.config))
        .unwrap_or_else(|| panic!("conformance: no such run of `{}`", p.fixture.name))
}

fn is_enum_unlimited_memo(c: &GridConfig, s: Selector) -> bool {
    c.engine == GridEngine::Enumerator
        && c.selector == s
        && c.memo
        && !c.stop_at_first_report
        && c.budget == Budget::Unlimited
}

/// **Criterion 4, R1 and R2 (i)–(ii)** (D3). The enumerator reports
/// `VisibleError` at `NotAGate`, naming `a`'s `Block{Assert}`; stateful,
/// complete-first and gated report `CompleteCoverage` at completion (errored
/// against done; the cut off); every report is accepted by the oracle. (iii)
/// is the md5 mutation audit of the report (two `VisibleError` mutations).
#[test]
fn c04_r1_and_r2_are_visible_error_reports_and_certify() {
    let g = grid();
    for name in ["R1", "R2"] {
        let p = pair(&g, name);
        let fam = p.families.as_ref().expect("conformance: families");
        for s in SELECTORS {
            let e = run_where(p, |c| is_enum_unlimited_memo(c, s));
            let reps = reports_of(e);
            assert_eq!(
                reps.len(),
                1,
                "conformance: {name} {s:?}: one enumerator report"
            );
            assert_eq!(reps[0].tag, ReportTag::VisibleError, "conformance: {name}");
            assert_eq!(reps[0].site, "NotAGate", "conformance: {name}");
            let Cause::VisibleError { thread, pos } = &reps[0].cause else {
                panic!("conformance: {name}: cause {:?}", reps[0].cause)
            };
            assert_eq!(thread, "a", "conformance: {name}");
            assert_eq!(
                *pos,
                format!(
                    "{}",
                    crate::event::Event::new(
                        crate::conformance::grid_oracle::thread_named(reps[0].graph, "a"),
                        1
                    )
                ),
                "conformance: {name}: the error is `a`'s event 1, after its Begin"
            );
            let claim = Claim {
                graph: reps[0].graph,
                tag: reps[0].tag,
                cause: reps[0].cause.clone(),
                serialized: reps[0].serialized,
            };
            certify(fam, &claim).unwrap_or_else(|e| {
                panic!("conformance: {name} {s:?}: the oracle rejects the enumerator's report: {e}")
            });
            for engine in [
                GridEngine::Stateful,
                GridEngine::CompleteFirst,
                GridEngine::Gated,
            ] {
                let r = run_where(p, |c| {
                    c.engine == engine && c.selector == s && kind(c) == Kind::Enumerating
                });
                let reps = reports_of(r);
                assert_eq!(reps.len(), 1, "conformance: {name} {engine:?}");
                assert_eq!(reps[0].tag, ReportTag::CompleteCoverage);
                assert_eq!(reps[0].site, "Completion");
                certify(
                    fam,
                    &Claim {
                        graph: reps[0].graph,
                        tag: reps[0].tag,
                        cause: Cause::NoCover,
                        serialized: reps[0].serialized,
                    },
                )
                .unwrap_or_else(|e| panic!("conformance: {name} {engine:?}: {e}"));
            }
        }
    }
}

/// The oracle's inputs for a pair of the grid.
fn fam_of(p: &Pair) -> &Families {
    p.families.as_ref().expect("conformance: families")
}

/// The oracle run's kept Impl graphs of a pair.
fn oracle_impl(p: &Pair) -> &[ExecutionGraph] {
    kept_impl(&p.oracle)
}

fn oracle_spec(p: &Pair) -> &[ExecutionGraph] {
    match &p.oracle.raw {
        GridRaw::Stateful(o) => &o.kept_spec_graphs,
        _ => unreachable!("conformance: the oracle run is stateful"),
    }
}

/// **N1** (criterion 4): a covered complete Impl graph of a conforming pair
/// (`traces/self`), tagged `CompleteCoverage`, is rejected. Killed mutant:
/// "`covered → false`" accepts it.
#[test]
fn c04_n1_a_covered_graph_is_rejected() {
    let g = grid();
    let p = pair(&g, "traces/self");
    let fam = fam_of(p);
    let imp = &oracle_impl(p)[0];
    assert!(
        fam.is_covered(imp),
        "conformance: N1's precondition: covered"
    );
    let r = certify(
        fam,
        &Claim {
            graph: imp,
            tag: ReportTag::CompleteCoverage,
            cause: Cause::NoCover,
            serialized: true,
        },
    );
    assert!(r.is_err(), "conformance: N1 accepted");
    assert!(
        r.unwrap_err().contains("covered by Spec member"),
        "conformance: N1 rejected for the wrong reason"
    );
}

/// `{b1 sent}` on `ex:naive` encoding 2 (`k = 2`): a kept Impl graph
/// restricted to the `porf` view of `b1`'s send (round 04 m1).
fn n2_graph(p: &Pair) -> ExecutionGraph {
    let imp = &oracle_impl(p)[0];
    restrict_to_porf(imp, send_of(imp, "b1", 0))
}

/// **N2** (criterion 4): `{b1 sent}` tagged `GrowingExhaustion` is rejected —
/// `cone` holds against every Spec graph (D3). Killed mutant: "`cone →
/// false`".
#[test]
fn c04_n2_a_matched_prefix_is_rejected() {
    let g = grid();
    let p = pair(&g, "ex:naive/k2/enc2");
    let fam = fam_of(p);
    let n2 = n2_graph(p);
    assert!(
        fam.some_cone(&n2),
        "conformance: N2's precondition: cone holds"
    );
    let r = certify(
        fam,
        &Claim {
            graph: &n2,
            tag: ReportTag::GrowingExhaustion,
            cause: Cause::NoCover,
            serialized: true,
        },
    );
    assert!(
        r.as_ref()
            .is_err_and(|e| e.contains("cone(report, M) holds")),
        "conformance: N2: {r:?}"
    );
}

/// R2's stateful completion report graph (`a` errored, `b` sent).
fn r2_completion(p: &Pair) -> &ExecutionGraph {
    let r = run_where(p, |c| {
        c.engine == GridEngine::Stateful && c.selector == Selector::Ltr && !c.stop_at_first_report
    });
    reports_of(r)
        .into_iter()
        .next()
        .expect("conformance: R2's stateful report")
        .graph
}

/// **N3a** (criterion 4, round 05 m1): R2's completion report with `b`'s
/// value 0 → 5, tagged `VisibleError` with the cause naming `a`'s
/// `Block{Assert}`: no Impl member extends it ⇒ rejected. Killed mutant:
/// "drop the extension" (VisibleError arm).
#[test]
fn c04_n3a_an_altered_errored_graph_is_rejected() {
    let g = grid();
    let p = pair(&g, "R2");
    let fam = fam_of(p);
    let base = r2_completion(p);
    let n3a = with_send_value(base, send_of(base, "b", 0), 5);
    let a_err =
        crate::event::Event::new(crate::conformance::grid_oracle::thread_named(&n3a, "a"), 1);
    let r = certify(
        fam,
        &Claim {
            graph: &n3a,
            tag: ReportTag::VisibleError,
            cause: Cause::VisibleError {
                thread: "a".to_owned(),
                pos: a_err.to_string(),
            },
            serialized: true,
        },
    );
    assert!(
        r.as_ref().is_err_and(|e| e.contains("extends the report")),
        "conformance: N3a: {r:?}"
    );
}

/// **N3b** (criterion 4): N2 with `b1`'s value 1 → 9, tagged
/// `GrowingExhaustion`: no Spec graph passes `cone` (asserted), no Impl
/// member extends it ⇒ rejected. Killed mutant: "drop 'at least one
/// extension exists'" (GrowingExhaustion arm).
#[test]
fn c04_n3b_an_altered_prefix_is_rejected() {
    let g = grid();
    let p = pair(&g, "ex:naive/k2/enc2");
    let fam = fam_of(p);
    let n2 = n2_graph(p);
    let n3b = with_send_value(&n2, send_of(&n2, "b1", 0), 9);
    assert!(
        !fam.some_cone(&n3b),
        "conformance: N3b's precondition: no Spec graph passes cone"
    );
    let r = certify(
        fam,
        &Claim {
            graph: &n3b,
            tag: ReportTag::GrowingExhaustion,
            cause: Cause::NoCover,
            serialized: true,
        },
    );
    assert!(
        r.as_ref().is_err_and(|e| e.contains("extends the report")),
        "conformance: N3b: {r:?}"
    );
}

/// **N3c** (criterion 4, round 05 m1): a kept `ex:naive` Impl graph with
/// `c`'s send 0 → 7, tagged `CompleteCoverage`; asserted first: equal to no
/// Impl member and covered by no Spec graph ⇒ rejected by membership. Killed
/// mutant: "drop membership" (CompleteCoverage arm).
#[test]
fn c04_n3c_a_graph_outside_the_family_is_rejected() {
    let g = grid();
    let p = pair(&g, "ex:naive/k2/enc2");
    let fam = fam_of(p);
    let base = &oracle_impl(p)[0];
    let n3c = with_send_value(base, send_of(base, "c", 0), 7);
    assert!(
        !fam.has_impl_key(&canon_key(&n3c, &p.fixture.visible)),
        "conformance: N3c's precondition: no Impl member"
    );
    assert!(
        !fam.is_covered(&n3c),
        "conformance: N3c's precondition: uncovered"
    );
    let r = certify(
        fam,
        &Claim {
            graph: &n3c,
            tag: ReportTag::CompleteCoverage,
            cause: Cause::NoCover,
            serialized: true,
        },
    );
    assert!(
        r.as_ref().is_err_and(|e| e.contains("not a member")),
        "conformance: N3c: {r:?}"
    );
}

/// R2's enumerator report (Ltr, unlimited, memo on).
fn r2_enum_report(p: &Pair) -> (&ExecutionGraph, Cause) {
    let e = run_where(p, |c| is_enum_unlimited_memo(c, Selector::Ltr));
    let rep = reports_of(e)
        .into_iter()
        .next()
        .expect("conformance: R2's enumerator report");
    (rep.graph, rep.cause)
}

/// **N4a** (criterion 4): R2's enumerator report checked against the
/// families of an oracle run of R2 under `Tvis = {b}` — the error is on an
/// undeclared thread ⇒ rejected. Killed mutant: "drop the visible-thread
/// check".
#[test]
fn c04_n4a_an_error_on_an_undeclared_thread_is_rejected() {
    let g = grid();
    let p = pair(&g, "R2");
    let (graph, cause) = r2_enum_report(p);
    let mut f = p.fixture.clone();
    f.visible = vec!["b".to_owned()];
    let o = run(&f, &oracle_config());
    let GridRaw::Stateful(o) = &o.raw else {
        unreachable!("conformance: stateful")
    };
    assert!(
        o.spec_errors.is_empty(),
        "conformance: R2's Spec is error-free"
    );
    let fam_b = Families::new(&o.kept_spec_graphs, &o.kept_impl_graphs, 0, &f.visible);
    let r = certify(
        &fam_b,
        &Claim {
            graph,
            tag: ReportTag::VisibleError,
            cause,
            serialized: true,
        },
    );
    assert!(
        r.as_ref()
            .is_err_and(|e| e.contains("not declared visible")),
        "conformance: N4a: {r:?}"
    );
}

/// **N4b** (criterion 4, round 04 n2): R2's report with a cause whose
/// position is `a`'s `Begin` ⇒ rejected. Killed mutant: "drop the
/// cause/graph check".
#[test]
fn c04_n4b_a_cause_naming_the_wrong_event_is_rejected() {
    let g = grid();
    let p = pair(&g, "R2");
    let (graph, _) = r2_enum_report(p);
    let r = certify(
        fam_of(p),
        &Claim {
            graph,
            tag: ReportTag::VisibleError,
            cause: Cause::VisibleError {
                thread: "a".to_owned(),
                pos: begin_of(graph, "a").to_string(),
            },
            serialized: true,
        },
    );
    assert!(
        r.as_ref().is_err_and(|e| e.contains("names no Block")),
        "conformance: N4b: {r:?}"
    );
}

/// **N5** (criterion 4): R1's report with the Impl family from R1's oracle
/// run and a **supplied** non-empty Spec-error record ⇒ rejected. Killed
/// mutant: "drop the Spec-error check".
#[test]
fn c04_n5_a_spec_error_record_is_rejected() {
    let g = grid();
    let p = pair(&g, "R1");
    let e = run_where(p, |c| is_enum_unlimited_memo(c, Selector::Ltr));
    let rep = reports_of(e)
        .into_iter()
        .next()
        .expect("conformance: R1's report");
    let fam5 = Families::new(oracle_spec(p), oracle_impl(p), 1, &p.fixture.visible);
    let claim = Claim {
        graph: rep.graph,
        tag: rep.tag,
        cause: rep.cause.clone(),
        serialized: rep.serialized,
    };
    let r = certify(&fam5, &claim);
    assert!(
        r.as_ref().is_err_and(|e| e.contains("Spec error")),
        "conformance: N5: {r:?}"
    );
    // Control: the same report against the real record is accepted.
    certify(fam_of(p), &claim).expect("conformance: N5's control");
}

/// **Criterion 4, the other direction** (round 03 n2): `ex:cone`'s correct
/// enumerator report — a growing report where `cone`'s clauses (1)–(2) hold
/// against the one Spec graph and clause (3) fails — is **accepted**; the
/// md5 mutation "`cone` without clause (iii)" makes the oracle reject it.
#[test]
fn c04_ex_cone_s_correct_report_is_accepted() {
    let g = grid();
    let p = pair(&g, "ex:cone");
    for s in SELECTORS {
        let e = run_where(p, |c| is_enum_unlimited_memo(c, s));
        let reps = reports_of(e);
        assert_eq!(reps.len(), 1, "conformance: ex:cone {s:?}");
        assert_eq!(
            reps[0].tag,
            ReportTag::GrowingExhaustion,
            "conformance: ex:cone"
        );
        certify(
            fam_of(p),
            &Claim {
                graph: reps[0].graph,
                tag: reps[0].tag,
                cause: reps[0].cause.clone(),
                serialized: reps[0].serialized,
            },
        )
        .unwrap_or_else(|e| panic!("conformance: ex:cone {s:?}: {e}"));
    }
}

// =========================================================================
// X3 — the enumerator's two arms agree on everything but the nine fields
// =========================================================================

/// The `ConfCounters` with the nine instrumented-only fields and the wall
/// time cleared (X3; round 03 m1).
fn comparable(c: &ConfCounters) -> ConfCounters {
    let mut c = c.clone();
    c.distinct_keys_run_wide = 0;
    c.f63_distinct_run_wide = 0;
    c.explored_complete_keys.clear();
    c.report_keys.clear();
    c.wall_time_ms = 0;
    c.per_cover = c
        .per_cover
        .iter()
        .map(|p| CoverCounters {
            distinct_keys: 0,
            per_attempt_distinct: [0, 0],
            f63_per_attempt_distinct: [0, 0],
            run_wide_distinct_so_far: 0,
            f63_run_wide_distinct_so_far: 0,
            ..p.clone()
        })
        .collect();
    c
}

/// **X3**: every enumerator configuration ran uninstrumented and
/// instrumented; `reports` (canonical form, kind, gate), `exhaustions`,
/// `end`, `skipped_gates`, `inert_gates` and every counter but the nine
/// instrumented-only fields agree; the instrumented arm fills the nine.
fn check_x3(g: &[Pair], twins_per_pair: usize) -> Vec<String> {
    let mut failures = Vec::new();
    let mut twins = 0usize;
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        for (r, t) in &p.runs {
            let Some(t) = t else { continue };
            let (GridRaw::Enumerator(a), GridRaw::Enumerator(b)) = (&r.raw, &t.raw) else {
                failures.push(format!(
                    "{}: a twin that is not an enumerator run",
                    p.fixture.name
                ));
                continue;
            };
            twins += 1;
            let label = format!("{} {}", p.fixture.name, r.config.label());
            let rk = |o: &crate::conformance::Outcome| -> Vec<String> {
                o.reports
                    .iter()
                    .map(|x| {
                        format!(
                            "{:?}|{:?}|{}",
                            x.gate,
                            x.kind,
                            canon_key(&x.graph, &p.fixture.visible)
                        )
                    })
                    .collect()
            };
            if rk(a) != rk(b) {
                failures.push(format!("{label}: reports differ"));
            }
            // Round 01 n5: the exhaustion records themselves, by content.
            let ex = |o: &crate::conformance::Outcome| -> Vec<String> {
                o.exhaustions.iter().map(|x| format!("{x:?}")).collect()
            };
            if (ex(a), a.end, a.skipped_gates, a.inert_gates)
                != (ex(b), b.end, b.skipped_gates, b.inert_gates)
            {
                failures.push(format!("{label}: exhaustions/end/skipped/inert differ"));
            }
            if comparable(&a.counters) != comparable(&b.counters) {
                failures.push(format!(
                    "{label}: counters differ:\n    {:?}\n    {:?}",
                    comparable(&a.counters),
                    comparable(&b.counters)
                ));
            }
            // Round 01 n5: all nine instrumented-only fields, both ways.
            let (na, nb) = (nine_filled(&a.counters), nine_filled(&b.counters));
            if na.iter().any(|(_, f)| *f) {
                failures.push(format!("{label}: the timing arm filled {na:?}"));
            }
            if a.counters.cover_calls > 0 {
                // Filled whenever a `Cover` call ran: the seven key counters
                // (every call meets at least its root); `explored_complete_keys`
                // iff an unpruned execution completed; `report_keys` iff a
                // report was made.
                let want_complete = a.counters.executions > a.reports.len();
                for (name, filled) in &nb {
                    let want = match *name {
                        "explored_complete_keys" => want_complete || *filled,
                        "report_keys" => !a.reports.is_empty(),
                        _ => true,
                    };
                    if *filled != want {
                        failures.push(format!("{label}: instrumented `{name}` filled={filled}"));
                    }
                }
            }
        }
    }
    let included = g.iter().filter(|p| p.excluded.is_none()).count();
    if twins != twins_per_pair * included {
        failures.push(format!(
            "{twins} twins for {included} pairs, not {twins_per_pair} each"
        ));
    }
    failures
}

/// Whether each of the nine instrumented-only fields (X3; round 03 m1) is
/// filled: the four `ConfCounters` fields and, summed over `per_cover`, the
/// five `CoverCounters` ones.
fn nine_filled(c: &ConfCounters) -> Vec<(&'static str, bool)> {
    let any = |f: &dyn Fn(&CoverCounters) -> usize| c.per_cover.iter().any(|p| f(p) > 0);
    vec![
        ("distinct_keys_run_wide", c.distinct_keys_run_wide > 0),
        ("f63_distinct_run_wide", c.f63_distinct_run_wide > 0),
        (
            "explored_complete_keys",
            !c.explored_complete_keys.is_empty(),
        ),
        ("report_keys", !c.report_keys.is_empty()),
        ("distinct_keys", any(&|p| p.distinct_keys)),
        (
            "per_attempt_distinct",
            any(&|p| p.per_attempt_distinct.iter().sum()),
        ),
        (
            "f63_per_attempt_distinct",
            any(&|p| p.f63_per_attempt_distinct.iter().sum()),
        ),
        (
            "run_wide_distinct_so_far",
            any(&|p| p.run_wide_distinct_so_far),
        ),
        (
            "f63_run_wide_distinct_so_far",
            any(&|p| p.f63_run_wide_distinct_so_far),
        ),
    ]
}

#[test]
fn x3_the_instrumented_twin_agrees_with_the_timing_arm() {
    // Three selectors × three enumerator configurations.
    fail_if(check_x3(&grid(), 9), "X3");
}

// =========================================================================
// Criterion 5 — the bins
// =========================================================================

/// **Criterion 5 (X5 a; D5)** on the default subset: per (benchmark, engine)
/// the runs are binned; the tester's maxima here are **0** for bins 1–3 (no
/// default-subset run is bounded or exhausts: the enumerator runs are all
/// `unlimited()`); bin 3 is empty; no run ends `Unknown`; the unlimited
/// memo-on enumerator runs are inconclusive-free (`P4-ENUMERATOR` 8); at
/// least one conclusive run per engine per benchmark.
fn check_c05(g: &[Pair]) -> Vec<String> {
    let mut failures = Vec::new();
    let mut table: BTreeMap<(String, String, Bin), usize> = BTreeMap::new();
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        let mut conclusive: BTreeMap<String, usize> = BTreeMap::new();
        for (r, _) in &p.runs {
            let s = status(r);
            let b = bin(&s);
            let e = format!("{:?}", r.config.engine);
            *table
                .entry((p.fixture.name.clone(), e.clone(), b))
                .or_default() += 1;
            if b == Bin::Conclusive {
                *conclusive.entry(e.clone()).or_default() += 1;
            } else {
                failures.push(format!(
                    "{} {}: bin {b:?} over the maximum 0 ({:?})",
                    p.fixture.name,
                    r.config.label(),
                    s
                ));
            }
        }
        for e in ["Enumerator", "Stateful", "CompleteFirst", "Gated"] {
            if conclusive.get(e).copied().unwrap_or(0) == 0 {
                failures.push(format!("{}: no conclusive {e} run", p.fixture.name));
            }
        }
    }
    if table.is_empty() {
        failures.push("no run was binned".to_owned());
    }
    failures
}

#[test]
fn c05_bins_on_the_default_subset() {
    let g = grid();
    let mut failures = check_c05(&g);
    // Round 01 m6.
    if !excluded_names(&g).is_empty() {
        failures.push(format!(
            "excluded pairs {:?}, pinned none",
            excluded_names(&g)
        ));
    }
    fail_if(failures, "criterion 5");
}

// =========================================================================
// Criterion 9 — memo arms at `unlimited()`, the precheck arm
// =========================================================================

/// **Criterion 9 (D7's condition, `lem:memo`; D8)**: on every pair and
/// selector, the unlimited memo-off and memo-on enumerator runs have equal
/// verdicts and equal report sets (canonical form, gate, kind), and memo on
/// never does more inner work (`spec_visit_calls`).
fn check_c09_memo(g: &[Pair]) -> Vec<String> {
    let mut failures = Vec::new();
    let mut less = 0usize;
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        for s in SELECTORS {
            let on = run_where(p, |c| is_enum_unlimited_memo(c, s));
            let off = run_where(p, |c| {
                c.engine == GridEngine::Enumerator
                    && c.selector == s
                    && !c.memo
                    && !c.stop_at_first_report
                    && c.budget == Budget::Unlimited
            });
            let (GridRaw::Enumerator(a), GridRaw::Enumerator(b)) = (&on.raw, &off.raw) else {
                unreachable!("conformance: enumerator runs")
            };
            let keys = |o: &crate::conformance::Outcome| -> BTreeSet<String> {
                o.reports
                    .iter()
                    .map(|x| {
                        format!(
                            "{:?}|{:?}|{}",
                            x.gate,
                            x.kind,
                            canon_key(&x.graph, &p.fixture.visible)
                        )
                    })
                    .collect()
            };
            let label = format!("{} {s:?}", p.fixture.name);
            if class(&status(on)) != class(&status(off)) {
                failures.push(format!("{label}: verdicts differ"));
            }
            if keys(a) != keys(b) {
                failures.push(format!("{label}: report sets differ"));
            }
            if a.counters.spec_visit_calls > b.counters.spec_visit_calls {
                failures.push(format!(
                    "{label}: memo on did more inner work ({} > {})",
                    a.counters.spec_visit_calls, b.counters.spec_visit_calls
                ));
            }
            if a.counters.spec_visit_calls < b.counters.spec_visit_calls {
                less += 1;
            }
        }
    }
    if less == 0 {
        failures.push("memo on never saved work — the arm is vacuous".to_owned());
    }
    failures
}

#[test]
fn c09_unlimited_memo_off_and_on_agree_on_every_pair() {
    fail_if(check_c09_memo(&grid()), "criterion 9 (memo)");
}

/// **Criterion 9, the precheck arm (D9)** on the small paper pairs:
/// complete-first and gated through `run` (precheck on) give the verdict
/// class of `run_with` (precheck skipped), with `precheck_ran = true` and a
/// recorded `precheck_wall_time_ms`. The precheck's Spec-graph count is not
/// in any record (finding T3); its stand-in is the oracle run's
/// `spec_graphs` (completeness of both enumerations).
#[test]
fn c09_the_precheck_arm_changes_no_verdict() {
    let g = grid();
    let mut failures = Vec::new();
    for p in g
        .iter()
        .filter(|p| p.excluded.is_none() && p.fixture.group != Group::Corpus)
    {
        for engine in [GridEngine::CompleteFirst, GridEngine::Gated] {
            let c = GridConfig::new(engine).precheck(true);
            let r = run(&p.fixture, &c);
            let GridRaw::Verdict(v) = &r.raw else {
                unreachable!("conformance: the precheck arm is a verdict")
            };
            let Ok(v) = v else {
                failures.push(format!("{} {engine:?}: {v:?}", p.fixture.name));
                continue;
            };
            let want = class(&status(run_where(p, |x| {
                x.engine == engine
                    && x.selector == Selector::Ltr
                    && kind(x) == Kind::Enumerating
                    && x.gate_policy == GatePolicy::Always
            })));
            let got = match v {
                ConfVerdict::Conforms(_) => Class::Conforms,
                ConfVerdict::Reported(_) => Class::Reported,
                ConfVerdict::Inconclusive(_) => Class::Inconclusive,
            };
            if got != want {
                failures.push(format!(
                    "{} {engine:?}: {got:?} vs {want:?}",
                    p.fixture.name
                ));
            }
            let o = v.outcome();
            let ran = o
                .cfirst_counters
                .as_ref()
                .map(|c| c.precheck_ran)
                .or_else(|| o.gated_counters.as_ref().map(|c| c.precheck_ran));
            if ran != Some(true) {
                failures.push(format!(
                    "{} {engine:?}: precheck_ran {ran:?}",
                    p.fixture.name
                ));
            }
        }
    }
    fail_if(failures, "criterion 9 (precheck)");
}

// =========================================================================
// Criterion 10 — labels, each asserted by an observed justification
// =========================================================================

/// Every send value of every complete graph of a family, rendered.
fn send_values(gs: &[ExecutionGraph]) -> Vec<String> {
    let mut out = Vec::new();
    for g in gs {
        for t in g.thread_ids() {
            for i in 0..g.thread_size(t) as u32 {
                if let crate::event_label::LabelEnum::SendMsg(s) =
                    g.label(crate::event::Event::new(t, i))
                {
                    out.push(format!("{:?}", s.val()));
                }
            }
        }
    }
    out
}

/// The set of thread keys of a graph (`Declared` name or origination
/// vector), from its canonical form.
fn thread_keys(g: &ExecutionGraph, v: &[String]) -> BTreeSet<String> {
    let k = canon_key(g, v);
    // The thread keys are the first component of each position; the form's
    // `Debug` lists them, so the set of `Begin` positions identifies them.
    let c = crate::conformance::canon::CanonicalGraph::of(g, v)
        .unwrap_or_else(|e| panic!("conformance: {e:?} on {k}"));
    c.events()
        .iter()
        .filter(|(_, l)| matches!(l, crate::conformance::canon::CanonLabel::Begin))
        .map(|((t, _), _)| format!("{t:?}"))
        .collect()
}

/// Criterion 10's label of a benchmark pair: whether a `ThreadId` reaches an
/// observed value (F41), whether a spawn is conditional (F44), whether a
/// program uses ids by order (F79), and the argument, written by reading
/// the programs. A9 (a non-reflexive value) is labelled on no pair.
struct Label {
    f41_thread_id_in_values: bool,
    argument: &'static str,
}

fn label_of(name: &str) -> Label {
    const TWO_PC: &str =
        "F41: `Prepare(ThreadId)` (coordinator pair) or `BeLeader(Vec<ThreadId>)`/\
        `BeFollower(ThreadId)` (leader and ring pairs) reach a visible participant; stable \
        because every spawn is `main`'s, unconditional and in program order before any \
        communication, and the thread whose id is observed is spawned at the same position on \
        both sides — the coordinator first (`bench.rs::two_pc`/`two_pc_spec`), the \
        participants first (`demo.rs::le_impl`/`ring_impl`/`le_spec`), so its `ThreadId` is \
        equal on both sides and in every execution. F44: none (no spawn under a branch). F79: \
        none — ids are sent, received and compared for equality only; the elections order \
        `usize` indices, never ids. Included in criterion 1's cross-run check.";
    if name.starts_with("2pc/") {
        Label {
            f41_thread_id_in_values: true,
            argument: TWO_PC,
        }
    } else if name.starts_with("ndk") {
        Label {
            f41_thread_id_in_values: false,
            argument: "`bench.rs::ndk`: `c` spawned first, then the senders, all by `main`, \
                unconditionally; payloads `u64`; the senders branch on `nondet()` only for \
                the value. No F41/F44/F79.",
        }
    } else if name.starts_with("corpus/") {
        Label {
            f41_thread_id_in_values: false,
            argument: "`generator.rs`: every shape spawns every named thread in a fixed \
                prologue before communicating (no conditional spawn) and every payload is an \
                `i32` (its module doc, \"Not reached by this generator\"); no id ordering. \
                No F41/F44/F79.",
        }
    } else {
        Label {
            f41_thread_id_in_values: false,
            argument: "Paper and closed-part fixtures (`grid.rs` copies): `main` spawns \
                every thread unconditionally; payloads are integers; no id ordering. \
                No F41/F44/F79.",
        }
    }
}

/// **Criterion 10 (round 01 M6; gate 4 round 01 M1)**: every pair labelled
/// against F41, F44 and F79 with its argument ([`label_of`]), each label
/// asserted by an observation on the oracle run's families: **F41** — a send
/// value renders a `ThreadId` exactly on the pairs labelled so (the 2PC
/// pairs), whose cross-run stability criterion 1 then checks; **F44** —
/// every complete graph of each program has the same thread set; **F79** —
/// by reading, its observation the unlimited memo-off/on agreement of
/// criterion 9; **A9** — every graph's canonical form equals itself. Returns
/// the failures and one label row per pair.
fn check_c10(g: &[Pair]) -> (Vec<String>, Vec<Row>) {
    let mut failures = Vec::new();
    let mut rows = Vec::new();
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        let v = &p.fixture.visible;
        let label = label_of(&p.fixture.name);
        let mut seen_id = false;
        let mut thread_sets = Vec::new();
        for (side, gs) in [("Impl", oracle_impl(p)), ("Spec", oracle_spec(p))] {
            seen_id |= send_values(gs).iter().any(|s| s.contains("ThreadId"));
            let sets: BTreeSet<BTreeSet<String>> = gs.iter().map(|x| thread_keys(x, v)).collect();
            thread_sets.push(sets.len());
            if sets.len() > 1 {
                failures.push(format!(
                    "{} {side}: {} distinct thread sets (F44)",
                    p.fixture.name,
                    sets.len()
                ));
            }
            for x in gs {
                let a = crate::conformance::canon::CanonicalGraph::of(x, v)
                    .unwrap_or_else(|e| panic!("conformance: {e:?}"));
                if a != a.clone() {
                    failures.push(format!("{} {side}: A9 (non-reflexive)", p.fixture.name));
                }
            }
        }
        if seen_id != label.f41_thread_id_in_values {
            failures.push(format!(
                "{}: F41 label {} but a ThreadId value observed: {seen_id}",
                p.fixture.name, label.f41_thread_id_in_values
            ));
        }
        rows.push(vec![
            ("fixture", p.fixture.name.clone()),
            (
                "F41 (ThreadId in a value)",
                format!("{} (observed {seen_id})", label.f41_thread_id_in_values),
            ),
            ("F44 (thread sets Impl/Spec)", format!("{thread_sets:?}")),
            ("A9", "reflexive (observed)".to_owned()),
            ("argument", label.argument.to_owned()),
        ]);
    }
    (failures, rows)
}

#[test]
fn c10_labels_by_observation_on_the_default_subset() {
    fail_if(check_c10(&grid()).0, "criterion 10");
}

// =========================================================================
// L2, L6, L8, L10 — the lead's findings
// =========================================================================

/// **L2.** The selector reaches the enumerator's raw route: on the default
/// subset some pair's unlimited memo-on enumerator run differs between `Ltr`
/// and `Reverse` in its gate or inner-work counters (measured); and on
/// `ex:naive` all three selectors give the same §8.8 row (D1, D-6: the
/// encodings fix the first-send order under every selector).
#[test]
fn l2_the_selector_reaches_the_enumerator_route() {
    let g = grid();
    let sig = |r: &GridResult| -> String {
        let GridRaw::Enumerator(o) = &r.raw else {
            unreachable!("conformance: enumerator")
        };
        let c = &o.counters;
        format!(
            "{} {} {} {} {:?}",
            c.gate_invocations,
            c.cover_calls,
            c.spec_visit_calls,
            c.executions,
            c.per_cover
                .iter()
                .map(|p| p.spec_visit_calls)
                .collect::<Vec<_>>()
        )
    };
    let mut differ = Vec::new();
    for p in g.iter().filter(|p| p.excluded.is_none()) {
        let a = sig(run_where(p, |c| is_enum_unlimited_memo(c, Selector::Ltr)));
        let b = sig(run_where(p, |c| {
            is_enum_unlimited_memo(c, Selector::Reverse)
        }));
        let f = sig(run_where(p, |c| {
            is_enum_unlimited_memo(c, Selector::FewestEvents)
        }));
        if a != b || a != f {
            differ.push(p.fixture.name.clone());
        }
        if p.fixture.name.starts_with("ex:naive/k") {
            assert!(
                a == b && a == f,
                "conformance: L2: ex:naive's enumerator row depends on the selector: {} | {a} | {b} | {f}",
                p.fixture.name
            );
        }
    }
    assert!(
        !differ.is_empty(),
        "conformance: L2: no pair's enumerator run depends on the selector"
    );
}

/// **L6**: the sweeping engines read `search_budget` for nothing — the same
/// configuration at `Exact(1)` and at `Unlimited` gives identical counters,
/// report sets and ends on `ex:naive` (`k = 3`, encoding 2) and the reset
/// pair.
#[test]
fn l6_the_sweeping_engines_ignore_the_search_budget() {
    let fixtures = [
        naive_fixture(3, 2),
        paper_fixtures()
            .into_iter()
            .find(|f| f.name == "reset-pair")
            .expect("conformance: reset pair"),
    ];
    for f in &fixtures {
        for base in [
            GridConfig::new(GridEngine::Stateful),
            GridConfig::new(GridEngine::CompleteFirst),
            GridConfig::new(GridEngine::Gated),
            GridConfig::new(GridEngine::Gated).gated(GatedMode::FirstFailure, GatePolicy::Always),
        ] {
            let one = run(f, &base.clone().budget(Budget::Exact(1)));
            let inf = run(f, &base.clone().budget(Budget::Unlimited));
            let strip = |r: &GridResult| -> String {
                let keys: Vec<String> = reports_of(r)
                    .iter()
                    .map(|x| canon_key(x.graph, &f.visible))
                    .collect();
                let counters = match &r.raw {
                    GridRaw::Stateful(o) => {
                        let mut c = o.counters.clone();
                        c.spec_wall_time_ms = 0;
                        c.impl_wall_time_ms = 0;
                        format!("{c:?} {:?}", o.impl_end)
                    }
                    GridRaw::CompleteFirst(o) => {
                        let mut c = o.counters.clone();
                        c.outer_wall_time_ms = 0;
                        c.sweep_wall_time_ms = 0;
                        c.precheck_wall_time_ms = 0;
                        format!("{c:?} {:?}", o.impl_end)
                    }
                    GridRaw::Gated(o) => {
                        let mut c = o.counters.clone();
                        c.outer_wall_time_ms = 0;
                        c.sweep_wall_time_ms = 0;
                        c.precheck_wall_time_ms = 0;
                        format!("{c:?} {:?}", o.impl_end)
                    }
                    _ => unreachable!("conformance: a sweeping engine"),
                };
                format!("{keys:?} {counters}")
            };
            assert_eq!(
                strip(&one),
                strip(&inf),
                "conformance: L6: {} {} reads the budget",
                f.name,
                base.label()
            );
        }
    }
}

/// **L8, L10**: `two_pc_fixtures(4)` yields 17 rows — coordinator
/// conforming 3, eager 3, leader conforming 2, leader split-brain 3, ring
/// conforming 3, ring split-brain 3 — six seeded (coordinator and ring
/// conforming, each seed in `Fixture.config`); every other row and every
/// corpus pair runs under seed 0; the corpus keeps its pair's model.
#[test]
fn l8_l10_the_registry_counts_and_seeds() {
    let rows = two_pc_fixtures(4);
    assert_eq!(rows.len(), 17, "conformance: L8");
    let count = |p: &str| rows.iter().filter(|f| f.name.starts_with(p)).count();
    assert_eq!(
        [
            count("2pc/coord/conf"),
            count("2pc/coord/eager"),
            count("2pc/leader/conf"),
            count("2pc/leader/split"),
            count("2pc/ring/conf"),
            count("2pc/ring/split")
        ],
        [3, 3, 2, 3, 3, 3],
        "conformance: L8"
    );
    let mut seeded = 0;
    for f in &rows {
        let t = f
            .table
            .as_ref()
            .expect("conformance: a 2PC row has its table");
        match t.recorded_seed {
            Some(s) => {
                seeded += 1;
                assert_eq!(f.config.seed, s, "conformance: L10: {}", f.name);
                assert_eq!(t.entry, TableEntry::EngineOnly);
            }
            None => assert_eq!(f.config.seed, 0, "conformance: L10: {}", f.name),
        }
        let want_budget = if f.name.starts_with("2pc/leader/split") {
            100_000
        } else {
            10_000
        };
        assert_eq!(
            t.budget, want_budget,
            "conformance: criterion 7: {}",
            f.name
        );
        let violating = f.name.contains("eager") || f.name.contains("split");
        assert_eq!(
            t.entry == TableEntry::VerifyStopTriage,
            violating,
            "conformance: criterion 7's entry point: {}",
            f.name
        );
    }
    assert_eq!(seeded, 6, "conformance: L10");
    let gen = generator::corpus(7, 3);
    let corpus = corpus_fixtures(7, 3);
    assert_eq!(corpus.len(), 21, "conformance: X6");
    for (f, p) in corpus.iter().zip(&gen) {
        assert_eq!(f.config.seed, 0, "conformance: L8: {}", f.name);
        assert_eq!(
            f.config.cons_type, p.config.cons_type,
            "conformance: L8: the model is kept"
        );
    }
}

// =========================================================================
// X1 — every copied fixture against its source test's pinned figures
// =========================================================================

/// The gated exhaustive `Always` run of `f` under `s`.
fn gated_row(f: &Fixture, s: Selector) -> crate::conformance::gated::GatedOutcome {
    let r = run(
        f,
        &GridConfig::new(GridEngine::Gated)
            .selector(s)
            .gated(GatedMode::Exhaustive, GatePolicy::Always),
    );
    match r.raw {
        GridRaw::Gated(o) => o,
        _ => unreachable!("conformance: gated"),
    }
}

/// **X1 (round 01 m7)**: each copy in `grid.rs` reproduces its source test's
/// pinned figures — `naive_d` and `naive_e2` by `P4-GATED` 5's rows; the
/// reset pair by `P4-GATED` 4; the forward-pop pair by `P4-GATED` 12;
/// `ex:rebuild` (`traces`) by `P4-ENUMERATOR` 10; `ex:restart` by
/// `P4-ENUMERATOR` 12; R1/R2 by `cfirst_tests`' `c06` regressions; `ex:cone`,
/// the relay and the Blocking pair by `apparatus_tests`' `cone`/`covered`
/// pins (one graph each; `cone` fails on `ex:cone` and the relay; the
/// Blocking pair passes `cone` and fails `covered`); `a27` by A27 (two
/// completion reports cut off).
#[test]
fn x1_the_copies_reproduce_their_sources_pins() {
    // P4-GATED 5, under ltr (exact): encoding 2 gates = k+1+Σ,
    // certified = Σ, replay 0, carried k−1, sizes [1,k!]; encoding 1
    // certified 2k+k!−1, replay Σ−k−(k!−1), sizes [k!].
    for (k, sigma, fact) in [(2usize, 4usize, 2usize), (3, 15, 6)] {
        let o = gated_row(&naive_fixture(k, 2), Selector::Ltr);
        let c = &o.counters;
        assert_eq!(
            (
                c.gates,
                c.gates_skipped_certified,
                c.gates_skipped_replay,
                c.carried_hits,
                c.gate_sweep_sizes.clone(),
                c.reports_certified,
                c.certificates_set
            ),
            (k + 1 + sigma, sigma, 0, k - 1, vec![1, fact], fact, 1),
            "conformance: X1: naive_d enc 2, k={k}"
        );
        let o = gated_row(&naive_fixture(k, 1), Selector::Ltr);
        let c = &o.counters;
        assert_eq!(
            (
                c.gates,
                c.gates_skipped_certified,
                c.gates_skipped_replay,
                c.gate_sweep_sizes.clone()
            ),
            (
                2 * k + fact,
                2 * k + fact - 1,
                sigma - k - (fact - 1),
                vec![fact]
            ),
            "conformance: X1: naive_d enc 1, k={k}"
        );
        // E2 under reverse: failing sweeps = 1 + states_pushed, one
        // certificate per revisit, k! reports; k=2 states_pushed 1, k=3 3.
        let o = gated_row(&naive_e2_fixture(k), Selector::Reverse);
        let c = &o.counters;
        let pushed = if k == 2 { 1 } else { 3 };
        assert_eq!(
            (
                c.states_pushed,
                c.gate_sweeps_failing,
                c.certified_states_revisited,
                o.reports.len()
            ),
            (pushed, 1 + pushed, pushed, fact),
            "conformance: X1: naive_e2 k={k}"
        );
    }
    let paper = paper_fixtures();
    let get = |n: &str| {
        paper
            .iter()
            .find(|f| f.name == n)
            .unwrap_or_else(|| panic!("conformance: no fixture {n}"))
            .clone()
    };
    // P4-GATED 4: gates 4, sizes [1,1], certificates 1, reports_certified 1,
    // resets 0, states_pushed 1, certified_states_revisited 1.
    let o = gated_row(&get("reset-pair"), Selector::Ltr);
    let c = &o.counters;
    assert_eq!(
        (
            c.gates,
            c.gate_sweep_sizes.clone(),
            c.certificates_set,
            c.reports_certified,
            c.certificate_resets,
            c.states_pushed,
            c.certified_states_revisited
        ),
        (4, vec![1, 1], 1, 1, 0, 1, 1),
        "conformance: X1: reset pair"
    );
    // P4-GATED 12: certificate_resets 1, states_pushed 0, one report.
    let o = gated_row(&get("forward-pop"), Selector::Ltr);
    assert_eq!(
        (
            o.counters.certificate_resets,
            o.counters.states_pushed,
            o.reports.len(),
            o.counters.gate_sweep_sizes.clone()
        ),
        (1, 0, 1, vec![1, 2, 2]),
        "conformance: X1: forward-pop pair"
    );
    // P4-ENUMERATOR 10: one report, GrowingExhaustion at RevisitApply.
    let f = get("ex:rebuild");
    let r = run(
        &f,
        &GridConfig::new(GridEngine::Enumerator).budget(Budget::Unlimited),
    );
    let reps = reports_of(&r);
    assert_eq!(reps.len(), 1, "conformance: X1: ex:rebuild");
    assert_eq!(
        (reps[0].tag, reps[0].site.as_str()),
        (ReportTag::GrowingExhaustion, "RevisitApply"),
        "conformance: X1: ex:rebuild"
    );
    // P4-ENUMERATOR 12: ex:restart conforms with one rebuild under Ltr.
    let r = run(
        &get("ex:restart"),
        &GridConfig::new(GridEngine::Enumerator).budget(Budget::Unlimited),
    );
    let GridRaw::Enumerator(o) = &r.raw else {
        unreachable!("conformance: enumerator")
    };
    assert_eq!(
        (o.reports.len(), o.counters.rebuilds_taken),
        (0, 1),
        "conformance: X1: ex:restart"
    );
    // cfirst_tests c06: R1/R2 cut off — one CompleteCoverage report, one
    // Impl graph, the errored status.
    for n in ["R1", "R2"] {
        let r = run(&get(n), &GridConfig::new(GridEngine::CompleteFirst));
        let GridRaw::CompleteFirst(o) = &r.raw else {
            unreachable!("conformance: cfirst")
        };
        assert_eq!(
            (
                o.reports.len(),
                o.counters.impl_graphs,
                o.counters.sweeps_failing
            ),
            (1, 1, 1),
            "conformance: X1: {n}"
        );
    }
    // A27, cut off: two completion reports.
    let r = run(&get("a27"), &GridConfig::new(GridEngine::CompleteFirst));
    assert_eq!(reports_of(&r).len(), 2, "conformance: X1: a27");
    // apparatus_tests: one graph per program; cone fails on ex:cone and the
    // relay; the Blocking pair passes cone and fails covered.
    for (n, cone_holds) in [
        ("ex:cone", false),
        ("relay/apparatus", false),
        ("blocking/apparatus", true),
    ] {
        let f = get(n);
        let o = run(&f, &oracle_config());
        let GridRaw::Stateful(o) = &o.raw else {
            unreachable!("conformance: stateful")
        };
        assert_eq!(
            (o.kept_impl_graphs.len(), o.kept_spec_graphs.len()),
            (1, 1),
            "conformance: X1: {n}"
        );
        let fam = Families::new(&o.kept_spec_graphs, &o.kept_impl_graphs, 0, &f.visible);
        assert_eq!(
            fam.some_cone(&o.kept_impl_graphs[0]),
            cone_holds,
            "conformance: X1: {n}'s cone"
        );
        assert!(
            !fam.is_covered(&o.kept_impl_graphs[0]),
            "conformance: X1: {n} is uncovered"
        );
    }
}

// =========================================================================
// Criterion 6 — §8.8's rows on `ex:naive`
// =========================================================================

/// One §8.8 row set at `k` under encoding `enc` and selector `s` (D1, D2).
/// Returns the measured rows for the table.
fn naive_rows(k: usize, enc: u8, s: Selector) -> Vec<Row> {
    let f = naive_fixture(k, enc);
    let fact = (1..=k).product::<usize>();
    let r_k: usize = (0..=k).map(|j| fact / (1..=k - j).product::<usize>()).sum();
    let mut rows = Vec::new();
    let tag = format!("k={k} enc{enc} {s:?}");
    // Enumerator, unlimited, first report, memo off/on, instrumented.
    for memo in [false, true] {
        let c = GridConfig::new(GridEngine::Enumerator)
            .selector(s)
            .budget(Budget::Unlimited)
            .memo(memo)
            .stop(true)
            .instrumented(true);
        let r = run(&f, &c);
        rows.push(row_of(&r));
        let GridRaw::Enumerator(o) = &r.raw else {
            unreachable!("conformance: enumerator")
        };
        let c = &o.counters;
        assert_eq!(
            o.reports.len(),
            1,
            "conformance: c06 {tag} memo={memo}: one report"
        );
        assert_eq!(
            o.end,
            SearchEnd::StoppedAtFirstReport,
            "conformance: c06 {tag}"
        );
        let rep = &reports_of(&r)[0];
        assert_eq!(
            (rep.tag, rep.site.as_str()),
            (ReportTag::GrowingExhaustion, "FreshSend"),
            "conformance: c06 {tag}"
        );
        if enc == 1 {
            assert_eq!(
                (
                    c.spec_visit_calls,
                    c.rebuilds_taken,
                    c.rebuilds_skipped_initial_seed,
                    c.memo_hits,
                    c.paper_events_at_first_report,
                    c.max_paper_events_per_execution
                ),
                (1, 0, 1, 0, Some(1), 1),
                "conformance: c06 {tag} memo={memo}: encoding 1's row (D1)"
            );
        } else {
            let (total, hits, gate) = if memo {
                (
                    2 * k + 2 + k * (1 << (k - 1)),
                    k * (1 << (k - 1)) + 2 - (1 << k),
                    2 + k * (1 << (k - 1)),
                )
            } else {
                (2 * k + 1 + r_k, 0, 1 + r_k)
            };
            let last = c.per_cover.last().expect("conformance: C's gate");
            assert_eq!(
                (
                    c.spec_visit_calls,
                    c.memo_hits,
                    last.spec_visit_calls,
                    last.distinct_keys,
                    c.rebuilds_taken,
                    c.paper_events_at_first_report,
                    c.cover_calls
                ),
                (total, hits, gate, 1 << k, 1, Some(k + 1), k + 1),
                "conformance: c06 {tag} memo={memo}: encoding 2's row (D1)"
            );
        }
    }
    // Gated first-failure, Always.
    let r = run(
        &f,
        &GridConfig::new(GridEngine::Gated)
            .selector(s)
            .gated(GatedMode::FirstFailure, GatePolicy::Always),
    );
    rows.push(row_of(&r));
    let GridRaw::Gated(o) = &r.raw else {
        unreachable!("conformance: gated")
    };
    let c = &o.counters;
    let (sizes, ok_sweeps, carried, events) = if enc == 1 {
        (vec![fact], 0, 0, 1)
    } else {
        (vec![1, fact], 1, k - 1, k + 1)
    };
    assert_eq!(
        (
            c.gate_sweep_sizes.clone(),
            c.gate_sweeps_successful,
            c.carried_hits,
            c.paper_events_at_first_report,
            c.impl_graphs,
            o.executions,
            o.reports.len(),
            o.impl_end
        ),
        (
            sizes,
            ok_sweeps,
            carried,
            Some(events),
            0,
            1,
            1,
            SearchEnd::StoppedAtFirstReport
        ),
        "conformance: c06 {tag}: gated first-failure (D2)"
    );
    // Complete-first, stop.
    let r = run(
        &f,
        &GridConfig::new(GridEngine::CompleteFirst)
            .selector(s)
            .stop(true),
    );
    rows.push(row_of(&r));
    let GridRaw::CompleteFirst(o) = &r.raw else {
        unreachable!("conformance: cfirst")
    };
    assert_eq!(
        (
            o.counters.impl_graphs,
            o.max_paper_events,
            o.counters.sweep_sizes.clone(),
            o.counters.cache_hits,
            o.counters.witnesses,
            o.reports.len(),
            grid_paper_events(&o.reports[0].0)
        ),
        (1, 2 * k + 1, vec![fact], 0, 0, 1, 2 * k + 1),
        "conformance: c06 {tag}: complete-first (D2)"
    );
    // Stateful, stop.
    let r = run(
        &f,
        &GridConfig::new(GridEngine::Stateful).selector(s).stop(true),
    );
    rows.push(row_of(&r));
    let GridRaw::Stateful(o) = &r.raw else {
        unreachable!("conformance: stateful")
    };
    assert_eq!(
        (
            o.counters.spec_graphs,
            o.counters.impl_graphs,
            o.counters.lookups,
            o.reports.len()
        ),
        (fact, 1, 1, 1),
        "conformance: c06 {tag}: stateful (D2)"
    );
    rows
}

fn grid_paper_events(g: &ExecutionGraph) -> usize {
    crate::conformance::grid::paper_events_total(g)
}

/// **Criterion 6 (D1, D2)** at `k = 2, 3`: every engine's §8.8 row on both
/// encodings under all three selectors (`FewestEvents` measured: it equals
/// `Ltr`'s, as D1 derives).
#[test]
fn c06_the_section_8_8_rows_at_k_2_and_3() {
    for k in 2..=3 {
        for enc in [1, 2] {
            for s in SELECTORS {
                naive_rows(k, enc, s);
            }
        }
    }
}

/// **Criterion 6 at `k = 4`** on every engine (run totals 74 / 42, hits 18).
/// Measured runtime 0.3 s (2026-10-07, one process); ignored to keep the default
/// subset to criterion 12's list.
#[test]
#[ignore]
fn c06_the_section_8_8_rows_at_k_4() {
    let mut rows = Vec::new();
    for enc in [1, 2] {
        for s in SELECTORS {
            rows.extend(naive_rows(4, enc, s));
        }
    }
    Tables::open().table("criterion 6: §8.8 rows at k = 4", &rows);
}

/// **Criterion 6 at `k = 5..7`**, the first-report rows (every row of
/// [`naive_rows`] is a first-report run). Measured runtime 26.3 s (one process).
#[test]
#[ignore]
fn c06_the_section_8_8_rows_at_k_5_to_7() {
    let mut rows = Vec::new();
    for k in 5..=7 {
        for enc in [1, 2] {
            for s in SELECTORS {
                rows.extend(naive_rows(k, enc, s));
            }
        }
    }
    Tables::open().table("criterion 6: §8.8 rows at k = 5..7", &rows);
}

// =========================================================================
// Criterion 7 — baselines under their original settings (heavy, ignored)
// =========================================================================

fn ndk(name: &str) -> Fixture {
    crate::conformance::grid::ndk_fixtures()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("conformance: no ndk fixture {name}"))
}

/// F63's settings (criterion 7): the enumerator, memo off, instrumented,
/// `Recorded`, `Ltr`, budget 10 000; the fixture carries FIFO, seed 0,
/// `Tvis = {c}`.
fn f63_config() -> GridConfig {
    GridConfig::new(GridEngine::Enumerator)
        .budget(Budget::Exact(10_000))
        .instrumented(true)
}

/// The F63 figures of one instrumented enumerator outcome, as `P4-ENUMERATOR`
/// gate 3's T4 table defines them: Σ calls, Σ per-attempt `Display` distinct,
/// Σ per-attempt canonical distinct, run-wide canonical and `Display`
/// distinct, Σ per-`Cover` canonical distinct, and the largest attempt
/// (calls, `Display` distinct, canonical distinct).
#[derive(Debug, PartialEq, Eq)]
struct F63 {
    covers: usize,
    nodes: usize,
    sum_f63_attempt: usize,
    sum_canon_attempt: usize,
    run_wide_canon: usize,
    run_wide_f63: usize,
    per_cover_sum: usize,
    largest: (usize, usize, usize),
}

fn f63_of(c: &ConfCounters) -> F63 {
    let mut largest = (0, 0, 0);
    for p in &c.per_cover {
        for (i, n) in [p.spec_visit_calls_extend, p.spec_visit_calls_rebuild]
            .into_iter()
            .enumerate()
        {
            if n > largest.0 {
                largest = (n, p.f63_per_attempt_distinct[i], p.per_attempt_distinct[i]);
            }
        }
    }
    F63 {
        covers: c.cover_calls,
        nodes: c.spec_visit_calls,
        sum_f63_attempt: c
            .per_cover
            .iter()
            .map(|p| p.f63_per_attempt_distinct.iter().sum::<usize>())
            .sum(),
        sum_canon_attempt: c
            .per_cover
            .iter()
            .map(|p| p.per_attempt_distinct.iter().sum::<usize>())
            .sum(),
        run_wide_canon: c.distinct_keys_run_wide,
        run_wide_f63: c.f63_distinct_run_wide,
        per_cover_sum: c.per_cover.iter().map(|p| p.distinct_keys).sum(),
        largest,
    }
}

fn ratio(a: usize, b: usize) -> f64 {
    a as f64 / b as f64
}

fn enum_outcome(r: &GridResult) -> &crate::conformance::Outcome {
    match &r.raw {
        GridRaw::Enumerator(o) => o,
        _ => unreachable!("conformance: an enumerator run"),
    }
}

/// **Criterion 7, F63 on `ndk3 bad_A` and `ndk2` conforming, under F63's own
/// settings** (D6), before any reinterpretation: `bad_A` 15 reports / 11
/// exhaustions, 175 968 nodes over 126 `Cover` calls; `Display` within
/// 15.77×, largest attempt 18.66× (10 000 / 536), across 17.20× (11 160 /
/// 649); canonical per-attempt within 30.18× (/ 5 830), across 18.11× (/
/// 322); per-`Cover` 30.4× (/ 5 785). `ndk2` conforming 1.05× (177 / 169).
/// The uninstrumented twin agrees (X3). Measured runtime 31.3 s (one process).
#[test]
#[ignore]
fn c07_f63_reproduced_under_its_original_settings() {
    let mut rows = Vec::new();
    // ndk2 conforming.
    let f = ndk("ndk2/conf");
    let r = run(&f, &f63_config());
    rows.push(row_of(&r));
    let o = enum_outcome(&r);
    let m = f63_of(&o.counters);
    assert_eq!(
        (o.reports.len(), o.exhaustions.len()),
        (0, 0),
        "conformance: c07 ndk2"
    );
    assert_eq!(
        (
            m.covers,
            m.nodes,
            m.sum_f63_attempt,
            m.sum_canon_attempt,
            m.run_wide_canon
        ),
        (26, 177, 169, 155, 31),
        "conformance: c07 ndk2: {m:?}"
    );
    assert_eq!(
        format!("{:.2}", ratio(m.nodes, m.sum_f63_attempt)),
        "1.05",
        "conformance: c07 ndk2 within"
    );
    // bad_A.
    let f = ndk("ndk3/bad_A");
    let r = run(&f, &f63_config());
    let t = run(&f, &f63_config().instrumented(false));
    rows.push(row_of(&r));
    rows.push(row_of(&t));
    let o = enum_outcome(&r);
    let ot = enum_outcome(&t);
    assert_eq!(
        (o.reports.len(), o.exhaustions.len()),
        (15, 11),
        "conformance: c07 bad_A"
    );
    assert_eq!(
        comparable(&o.counters),
        comparable(&ot.counters),
        "conformance: c07 bad_A: X3 twins"
    );
    let m = f63_of(&o.counters);
    assert_eq!(
        m,
        F63 {
            covers: 126,
            nodes: 175_968,
            sum_f63_attempt: 11_160,
            sum_canon_attempt: 5_830,
            run_wide_canon: 322,
            run_wide_f63: 649,
            per_cover_sum: 5_785,
            largest: (10_000, 536, 267),
        },
        "conformance: c07 bad_A"
    );
    let figures = [
        ratio(m.nodes, m.sum_f63_attempt),
        ratio(m.largest.0, m.largest.1),
        ratio(m.sum_f63_attempt, m.run_wide_f63),
        ratio(m.nodes, m.sum_canon_attempt),
        ratio(m.sum_canon_attempt, m.run_wide_canon),
    ]
    .map(|x| format!("{x:.2}"));
    assert_eq!(
        figures,
        ["15.77", "18.66", "17.20", "30.18", "18.11"].map(String::from),
        "conformance: c07 bad_A ratios"
    );
    assert_eq!(
        format!("{:.1}", ratio(m.nodes, m.per_cover_sum)),
        "30.4",
        "conformance: c07 bad_A per-Cover"
    );
    Tables::open().table("criterion 7: F63 under its original settings", &rows);
}

/// **Criterion 7, D-B*: the unlimited arm's target.** The minimum budget at
/// which a pair never exhausts equals `max_i max(extend_i, rebuild_i)` of
/// its unlimited memo-off seed-0 run: **33** (`ndk2` conforming), **981**
/// (`ndk3` conforming), **12 082** (`bad_A`); the unlimited runs exhaust
/// nowhere; `bad_A` at 12 081 exhausts (the minimum is exact, not only
/// sufficient — `bench.rs` pins 12 082 as sufficient only). Measured
/// runtime 28.6 s (one process).
#[test]
#[ignore]
fn c07_the_unlimited_arm_reaches_the_minimum_budgets() {
    let mut rows = Vec::new();
    for (name, want) in [
        ("ndk2/conf", 33usize),
        ("ndk3/conf", 981),
        ("ndk3/bad_A", 12_082),
    ] {
        let f = ndk(name);
        let r = run(
            &f,
            &GridConfig::new(GridEngine::Enumerator).budget(Budget::Unlimited),
        );
        rows.push(row_of(&r));
        let o = enum_outcome(&r);
        assert!(
            o.exhaustions.is_empty(),
            "conformance: c07 {name} unlimited"
        );
        let got = o
            .counters
            .per_cover
            .iter()
            .map(|p| p.spec_visit_calls_extend.max(p.spec_visit_calls_rebuild))
            .max()
            .unwrap_or(0);
        assert_eq!(got, want, "conformance: c07 D-B* {name}");
        if name == "ndk3/bad_A" {
            let below = run(
                &f,
                &GridConfig::new(GridEngine::Enumerator).budget(Budget::Exact(want - 1)),
            );
            rows.push(row_of(&below));
            assert!(
                !enum_outcome(&below).exhaustions.is_empty(),
                "conformance: c07 bad_A exhausts at {}",
                want - 1
            );
        }
    }
    Tables::open().table("criterion 7: the unlimited arm (D-B*)", &rows);
}

/// The recorded outer-graph counts of the six seeded DEMO-2PC rows
/// (DEMO-2PC.md, DEMO-2PC-RING.md, measured at `ae3ab15`).
fn recorded_outer_graphs(name: &str) -> Option<usize> {
    match name {
        "2pc/coord/conf/n2" => Some(8),
        "2pc/coord/conf/n3" => Some(48),
        "2pc/coord/conf/n4" => Some(384),
        "2pc/ring/conf/n2" => Some(4),
        "2pc/ring/conf/n3" => Some(24),
        "2pc/ring/conf/n4" => Some(192),
        _ => None,
    }
}

/// **Criterion 7, the 17 DEMO-2PC rows under each table's own settings**
/// (round 04 M1, round 05 m3): conforming rows engine-only
/// (`verify_conformance` at budget 10 000, memo off, `Ltr`, FIFO) under the
/// recorded seed where the table prints one, else seed 0; violating rows
/// through `verify` with `stop_at_first_report(true)`, `triage(true)`, the
/// table's budget (100 000 for the leader split-brain rows) and the
/// precheck **on** (the table's `ConfBuilder` does not skip it). Compared:
/// the verdict (a difference fails); on the six seeded rows the outer-graph
/// count `stats.execs + stats.block` against the recorded figure (a
/// mismatch is **recorded**, never failed — the returned list goes into the
/// table). Measured runtime 6.3 s (one process).
#[test]
#[ignore]
fn c07_the_two_pc_rows_reproduce_their_verdicts() {
    let mut rows = Vec::new();
    let mut mismatches = Vec::new();
    for f in two_pc_fixtures(4) {
        let t = f.table.clone().expect("conformance: a 2PC row");
        let violating = t.entry == TableEntry::VerifyStopTriage;
        let c = if violating {
            GridConfig::new(GridEngine::Verify)
                .stop(true)
                .budget(Budget::Exact(t.budget))
                .precheck(true)
        } else {
            GridConfig::new(GridEngine::Enumerator).budget(Budget::Exact(t.budget))
        };
        let r = run(&f, &c);
        let mut row = row_of(&r);
        let s = status(&r);
        assert!(
            s.failure.is_none(),
            "conformance: c07 {}: {:?}",
            f.name,
            s.failure
        );
        let want = if violating {
            Class::Reported
        } else {
            Class::Conforms
        };
        assert_eq!(class(&s), want, "conformance: c07 {} verdict", f.name);
        if let (Some(rec), GridRaw::Enumerator(o)) = (recorded_outer_graphs(&f.name), &r.raw) {
            let got = o.stats.as_ref().map(|x| x.execs + x.block);
            row.push(("recorded_outer_graphs", rec.to_string()));
            if got != Some(rec) {
                mismatches.push(format!("{}: recorded {rec}, measured {got:?}", f.name));
            }
        }
        rows.push(row);
    }
    let mut tables = Tables::open();
    tables.table("criterion 7: the DEMO-2PC rows", &rows);
    tables.note(&format!(
        "Outer-graph mismatches on the seeded rows (recorded, not failed): {mismatches:?}"
    ));
}

/// **Criterion 7, the F63 shift's candidates by knob** (round 01 m11):
/// `ndk3` conforming's run-wide `Display` distinct was 488 (16 353 nodes)
/// at `66d395e` and is 283 (7 992 nodes) today. Each candidate a flag or
/// knob on the working tree can reverse is run under F63's settings and
/// otherwise unchanged: the seed (0..=15 and the two DEMO seeds), the
/// selector, the inner order, memo, an unlimited budget. Stopping rule: the
/// first candidate restoring 488 is named; the test records every figure in
/// the table and asserts only that today's seed-0 figure is 283 / 7 992 over
/// 160 `Cover` calls. The candidates needing a checkout are listed for the
/// owner in the report. Measured runtime 19.0 s (one process).
#[test]
#[ignore]
fn c07_the_f63_shift_candidates_by_knob() {
    let base = ndk("ndk3/conf");
    let mut rows = Vec::new();
    let mut restored = Vec::new();
    let mut probe = |label: String, f: &Fixture, c: GridConfig, rows: &mut Vec<Row>| {
        let r = run(f, &c);
        let o = enum_outcome(&r);
        let m = f63_of(&o.counters);
        let mut row = row_of(&r);
        row.insert(0, ("candidate", label.clone()));
        rows.push(row);
        if m.run_wide_f63 == 488 || m.nodes == 16_353 {
            restored.push(format!("{label}: {m:?}"));
        }
        m
    };
    let today = probe("today (seed 0)".into(), &base, f63_config(), &mut rows);
    assert_eq!(
        (today.covers, today.nodes, today.run_wide_f63),
        (160, 7_992, 283),
        "conformance: c07 the shift's baseline"
    );
    let mut seeds: Vec<u64> = (1..=15).collect();
    seeds.extend([11_267_641_651_409_304_418, 1_784_307_368_278_839_636]);
    for seed in seeds {
        let mut f = base.clone();
        f.config.seed = seed;
        probe(format!("seed {seed}"), &f, f63_config(), &mut rows);
    }
    for s in [Selector::FewestEvents, Selector::Reverse] {
        probe(
            format!("selector {s:?}"),
            &base,
            f63_config().selector(s),
            &mut rows,
        );
    }
    probe("memo on".into(), &base, f63_config().memo(true), &mut rows);
    probe(
        "unlimited".into(),
        &base,
        f63_config().budget(Budget::Unlimited),
        &mut rows,
    );
    let mut tables = Tables::open();
    tables.table(
        "criterion 7: the F63 shift, candidates by knob (ndk3 conforming)",
        &rows,
    );
    tables.note(&format!("Candidates restoring 488 / 16 353: {restored:?}"));
}

/// **Criterion 7, the inner-order candidate** (a knob of `SearchOpts` the
/// grid does not expose, so run through `verify_conformance_with_opts`
/// directly): `ndk3` conforming under F63's settings with `InnerOrder::
/// Reverse` and `SendsFirst`. Recorded only. Measured runtime 1.7 s.
#[test]
#[ignore]
fn c07_the_f63_shift_inner_order_candidate() {
    use crate::conformance::search::SearchOpts;
    use crate::conformance::selector::InnerOrder;
    let f = ndk("ndk3/conf");
    let mut notes = Vec::new();
    for order in [InnerOrder::Reverse, InnerOrder::SendsFirst] {
        let imp = f.implementation.clone();
        let spec = f.specification.clone();
        let config = f.config.clone();
        let visible = f.visible.clone();
        let o = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                crate::conformance::verify_conformance_with_opts(
                    config,
                    imp,
                    spec,
                    visible,
                    10_000,
                    false,
                    SearchOpts {
                        inner_order: order,
                        memo: false,
                        instrument: true,
                    },
                )
            })
            .expect("conformance: spawn")
            .join()
            .expect("conformance: the inner-order run panicked");
        notes.push(format!("{:?}", f63_of(&o.counters)));
    }
    Tables::open().note(&format!(
        "criterion 7, the F63 shift, inner order Reverse / SendsFirst (ndk3 conforming): {notes:?}"
    ));
}

// =========================================================================
// Criteria 5, 8, 9, 11 — the full grid and its tables (heavy, ignored)
// =========================================================================

/// The enumerator's performance arms (X3, D7): memo off/on at the default
/// budget and at `unlimited()`, each under one selector.
fn perf_enum_configs(s: Selector) -> Vec<GridConfig> {
    let mut v = Vec::new();
    for budget in [Budget::Default, Budget::Unlimited] {
        for memo in [false, true] {
            v.push(
                GridConfig::new(GridEngine::Enumerator)
                    .selector(s)
                    .budget(budget)
                    .memo(memo),
            );
        }
    }
    v.push(
        GridConfig::new(GridEngine::Enumerator)
            .selector(s)
            .budget(Budget::Unlimited)
            .memo(true)
            .stop(true),
    );
    v
}

fn full_configs() -> Vec<GridConfig> {
    let mut v = Vec::new();
    for s in SELECTORS {
        v.extend(perf_enum_configs(s));
        v.extend(sweep_configs(s));
    }
    v
}

/// One engine's inner work, in its own unit (E3): the enumerator's
/// `SpecVisit` calls (partial states); the stateful engine's Spec graphs;
/// complete-first's swept graphs; the gated engine's gate- plus
/// completion-swept graphs.
fn inner_work(r: &GridResult) -> Option<usize> {
    match &r.raw {
        GridRaw::Enumerator(o) => Some(o.counters.spec_visit_calls),
        GridRaw::Stateful(o) => Some(o.counters.spec_graphs),
        GridRaw::CompleteFirst(o) => Some(o.counters.sweep_graphs),
        GridRaw::Gated(o) => Some(
            o.counters.gate_sweep_sizes.iter().sum::<usize>()
                + o.counters.completion_sweep_sizes.iter().sum::<usize>(),
        ),
        GridRaw::Verdict(_) => None,
    }
}

/// The full grid's fixtures (X6): the default subset widened to
/// `corpus(7, 10)` and `ex:naive` `k = 4`, plus `ndk2`/`ndk3` conforming
/// and the 2PC rows at `N ≤ 3`, **every one at seed 0** (X3; gate 4 round 01
/// n3 — the recorded seeds belong to criterion 7's reproduction only).
fn full_fixtures() -> Vec<Fixture> {
    let mut v = Vec::new();
    for k in 2..=4 {
        v.push(naive_fixture(k, 1));
        v.push(naive_fixture(k, 2));
        v.push(naive_e2_fixture(k));
    }
    v.extend(paper_fixtures());
    v.extend(
        crate::conformance::grid::ndk_fixtures()
            .into_iter()
            .filter(|f| f.name != "ndk3/bad_A"),
    );
    v.extend(two_pc_fixtures(3).into_iter().map(|mut f| {
        f.config.seed = 0;
        f
    }));
    v.extend(corpus_fixtures(7, 10));
    v
}

/// F81's occurrences on the full grid (X5 e: counted, not failed), measured
/// at gate 4 round 01 and pinned.
const F81_FULL_GRID: [&str; 3] = [
    "ex:rebuild Ltr reports=1 end=StateSpaceExhausted",
    "ex:rebuild FewestEvents reports=1 end=StateSpaceExhausted",
    "ex:rebuild Reverse reports=1 end=StateSpaceExhausted",
];

/// **Criteria 1–5, 8–11 and X3 on the full grid** (gate 4 round 01 M1),
/// single-threaded (so the wall times feed E3 — X1), uncapped: every pair of
/// [`full_fixtures`] through every configuration of [`full_configs`] (54 per
/// pair, each enumerator configuration with its instrumented twin), the
/// oracle run per pair (X4), and **the default tests' own checks**:
/// criterion 1's cross-run plan-key check (the 2PC pairs included —
/// criterion 10), criterion 2 with X5 e's first-report rules and the F81
/// count (pinned), the excluded set (pinned empty), criterion 3,
/// certification of every report including the twins' (criterion 4), X3's
/// twin comparison, criterion 5's bins (maximum 0 for bins 1–3 on every
/// arm, the default-budget arms included — measured) and its
/// at-least-one-conclusive-run-per-engine rule, criterion 9's unlimited memo
/// agreement, criterion 10's labels with their arguments; then the tables
/// (one row per run), the labels, E1–E3 and the default-budget verdict
/// changes (D7), written to `P4_DIFF_TABLES`. Measured runtime 696 s (one
/// process, single-threaded, 2026-10-07).
#[test]
#[ignore]
fn c08_the_full_grid_and_its_tables() {
    let pairs = compute(full_fixtures(), &full_configs(), 1);
    let mut tables = Tables::open();
    let mut failures = Vec::new();
    let tagged = |c: &str, v: Vec<String>| -> Vec<String> {
        v.into_iter().map(|f| format!("{c}: {f}")).collect()
    };
    if !excluded_names(&pairs).is_empty() {
        failures.push(format!(
            "excluded pairs {:?}, pinned none",
            excluded_names(&pairs)
        ));
    }
    failures.extend(tagged("criterion 1", check_c01(&pairs)));
    let (f2, f81) = check_c02(&pairs, &corpus_expectations(10), 54);
    failures.extend(tagged("criterion 2", f2));
    if f81 != F81_FULL_GRID.to_vec() {
        failures.push(format!("F81 occurrences {f81:?}, pinned {F81_FULL_GRID:?}"));
    }
    failures.extend(tagged("criterion 3", check_c03(&pairs, 18)));
    failures.extend(tagged("criterion 4", check_c04(&pairs, true)));
    // Three selectors × five enumerator configurations.
    failures.extend(tagged("X3", check_x3(&pairs, 15)));
    failures.extend(tagged("criterion 5", check_c05(&pairs)));
    failures.extend(tagged("criterion 9", check_c09_memo(&pairs)));
    let (f10, labels) = check_c10(&pairs);
    failures.extend(tagged("criterion 10", f10));

    let mut verdict_changes = Vec::new();
    let mut e1 = Vec::new();
    let mut e2 = Vec::new();
    let mut e3 = Vec::new();
    let mut per_selector: BTreeMap<String, Vec<Row>> = BTreeMap::new();
    for p in pairs.iter().filter(|p| p.excluded.is_none()) {
        let name = &p.fixture.name;
        let violation = fam_of(p).some_impl_uncovered();
        let mut best_work: Option<(usize, String)> = None;
        let mut best_wall: Option<(u128, String)> = None;
        for (r, _) in &p.runs {
            let label = r.config.label();
            per_selector
                .entry(format!("{:?}", r.config.selector))
                .or_default()
                .push(row_of(r));
            if r.config.selector == Selector::Ltr
                && !r.config.stop_at_first_report
                && r.config.gated_mode == GatedMode::Exhaustive
            {
                if let Some(w) = inner_work(r) {
                    let e = format!(
                        "{:?}/memo={}/{:?}/{:?}",
                        r.config.engine, r.config.memo, r.config.budget, r.config.gate_policy
                    );
                    if best_work.as_ref().is_none_or(|(x, _)| w < *x) {
                        best_work = Some((w, e.clone()));
                    }
                    if best_wall
                        .as_ref()
                        .is_none_or(|(x, _)| r.wall.as_millis() < *x)
                    {
                        best_wall = Some((r.wall.as_millis(), e));
                    }
                }
            }
            if !violation && matches!(r.raw, GridRaw::CompleteFirst(_) | GridRaw::Gated(_)) {
                let row = row_of(r);
                let keep = |k: &str| {
                    row.iter()
                        .find(|(c, _)| *c == k)
                        .map(|(_, v)| v.clone())
                        .unwrap_or_default()
                };
                e1.push(vec![
                    ("fixture", name.clone()),
                    ("config", label.clone()),
                    ("cache_hits", keep("cache_hits")),
                    ("completion_cache_hits", keep("completion_cache_hits")),
                    ("carried_hits", keep("carried_hits")),
                    ("gate_cache_hits", keep("gate_cache_hits")),
                    ("sweeps", keep("sweeps")),
                    ("gate_sweeps", keep("gate_sweeps")),
                    ("completion_sweeps", keep("completion_sweeps")),
                ]);
            }
            if let GridRaw::Gated(o) = &r.raw {
                if o.counters.states_pushed > 0 {
                    e2.push(vec![
                        ("fixture", name.clone()),
                        ("config", label.clone()),
                        ("states_pushed", o.counters.states_pushed.to_string()),
                        (
                            "certified_states_revisited",
                            o.counters.certified_states_revisited.to_string(),
                        ),
                        (
                            "gate_sweeps_failing",
                            o.counters.gate_sweeps_failing.to_string(),
                        ),
                        ("gate_sweeps", o.counters.gate_sweeps.to_string()),
                    ]);
                }
            }
        }
        for sel in SELECTORS {
            let pick = |memo: bool| {
                p.runs.iter().map(|(r, _)| r).find(|r| {
                    r.config.engine == GridEngine::Enumerator
                        && r.config.selector == sel
                        && r.config.budget == Budget::Default
                        && r.config.memo == memo
                })
            };
            if let (Some(a), Some(b)) = (pick(false), pick(true)) {
                if class(&status(a)) != class(&status(b)) {
                    verdict_changes.push(format!(
                        "{name} {sel:?}: memo off {:?}, memo on {:?}",
                        class(&status(a)),
                        class(&status(b))
                    ));
                }
            }
        }
        e3.push(vec![
            ("fixture", name.clone()),
            (
                "least inner work (unit per engine)",
                format!("{best_work:?}"),
            ),
            ("least wall time (ms)", format!("{best_wall:?}")),
        ]);
    }
    for (s, rows) in &per_selector {
        tables.table(&format!("criterion 8/11: every run under {s}"), rows);
    }
    tables.table("criterion 10: labels, each with its argument", &labels);
    tables.table(
        "E1: witness reuse on conforming complete-first and gated runs",
        &e1,
    );
    tables.table(
        "E2: gated runs with backward revisits (no attribution claimed corpus-wide)",
        &e2,
    );
    tables.table("E3: crossover, Ltr exhaustive runs, single-threaded", &e3);
    tables.note(&format!("Excluded pairs: {:?}", excluded_names(&pairs)));
    tables.note(&format!("F81 occurrences (counted): {f81:?}"));
    tables.note(&format!(
        "Default-budget verdict changes memo off → on (D7): {verdict_changes:?}"
    ));
    fail_if(failures, "the full grid");
}

/// **Criterion 9's precheck arm, tabulated (D9; gate 4 round 01 M2):** for
/// `ndk3` conforming, the 2PC rows at `N ≤ 3` (seed 0) and the paper pairs,
/// complete-first and gated (`Always`, exhaustive) with the precheck on
/// (`run`) against skipped (`run_with`): `precheck_ran`,
/// `precheck_wall_time_ms`, the oracle run's `spec_graphs` (the precheck's
/// Spec-graph count by completeness — T3) against the sweeps' (complete-first
/// `sweep_graphs`; gated gate- plus completion-swept graphs), and the outer
/// and sweep wall times of both arms. Asserted: the precheck arm's verdict
/// class equals `run_with`'s and `precheck_ran`. Measured runtime 21 s.
#[test]
#[ignore]
fn c09_the_precheck_arm_tabulated() {
    let mut fixtures: Vec<Fixture> = crate::conformance::grid::ndk_fixtures()
        .into_iter()
        .filter(|f| f.name == "ndk3/conf")
        .collect();
    fixtures.extend(two_pc_fixtures(3).into_iter().map(|mut f| {
        f.config.seed = 0;
        f
    }));
    fixtures.extend(paper_fixtures());
    let mut rows = Vec::new();
    let mut failures = Vec::new();
    for f in &fixtures {
        let o = run(f, &oracle_config());
        let GridRaw::Stateful(os) = &o.raw else {
            unreachable!("conformance: stateful")
        };
        let spec_graphs = os.counters.spec_graphs;
        for engine in [GridEngine::CompleteFirst, GridEngine::Gated] {
            let skipped = run(f, &GridConfig::new(engine));
            let on = run(f, &GridConfig::new(engine).precheck(true));
            let GridRaw::Verdict(Ok(v)) = &on.raw else {
                failures.push(format!("{} {engine:?}: {:?}", f.name, on.raw));
                continue;
            };
            let got = match v {
                ConfVerdict::Conforms(_) => Class::Conforms,
                ConfVerdict::Reported(_) => Class::Reported,
                ConfVerdict::Inconclusive(_) => Class::Inconclusive,
            };
            if got != class(&status(&skipped)) {
                failures.push(format!("{} {engine:?}: precheck arm {got:?}", f.name));
            }
            let out = v.outcome();
            let (ran, pre_ms, on_sweep, on_outer, on_sweep_ms) =
                match (&out.cfirst_counters, &out.gated_counters) {
                    (Some(c), _) => (
                        c.precheck_ran,
                        c.precheck_wall_time_ms,
                        c.sweep_graphs,
                        c.outer_wall_time_ms,
                        c.sweep_wall_time_ms,
                    ),
                    (_, Some(c)) => (
                        c.precheck_ran,
                        c.precheck_wall_time_ms,
                        c.gate_sweep_sizes.iter().sum::<usize>()
                            + c.completion_sweep_sizes.iter().sum::<usize>(),
                        c.outer_wall_time_ms,
                        c.sweep_wall_time_ms,
                    ),
                    _ => {
                        failures.push(format!("{} {engine:?}: no engine counters", f.name));
                        continue;
                    }
                };
            if !ran {
                failures.push(format!("{} {engine:?}: precheck_ran false", f.name));
            }
            let (skip_outer, skip_sweep_ms) = match &skipped.raw {
                GridRaw::CompleteFirst(o) => {
                    (o.counters.outer_wall_time_ms, o.counters.sweep_wall_time_ms)
                }
                GridRaw::Gated(o) => (o.counters.outer_wall_time_ms, o.counters.sweep_wall_time_ms),
                _ => unreachable!("conformance: a sweeping engine"),
            };
            rows.push(vec![
                ("fixture", f.name.clone()),
                ("engine", format!("{engine:?}")),
                ("verdict", format!("{got:?}")),
                ("precheck_ran", ran.to_string()),
                ("precheck_wall_time_ms", pre_ms.to_string()),
                (
                    "oracle spec_graphs (precheck count, T3)",
                    spec_graphs.to_string(),
                ),
                ("swept graphs (precheck on)", on_sweep.to_string()),
                (
                    "swept graphs (skipped)",
                    inner_work(&skipped).unwrap_or(0).to_string(),
                ),
                (
                    "outer_wall_time_ms (on / skipped)",
                    format!("{on_outer} / {skip_outer}"),
                ),
                (
                    "sweep_wall_time_ms (on / skipped)",
                    format!("{on_sweep_ms} / {skip_sweep_ms}"),
                ),
                (
                    "wall_ms (on / skipped)",
                    format!("{} / {}", on.wall.as_millis(), skipped.wall.as_millis()),
                ),
            ]);
        }
    }
    Tables::open().table("criterion 9: the precheck arm (D9)", &rows);
    fail_if(failures, "criterion 9 (precheck arm)");
}

/// The configurations of X6's extent runs: the enumerator's five
/// performance arms, minus memo off at the default budget when
/// `skip_default_memo_off` (it is out of reach at `ex:naive` `k = 7`); the
/// stateful engine with and without the stop; complete-first and gated
/// first-report runs; and, when `exhaustive_sweeps`, the exhaustive
/// complete-first and gated runs — under each selector.
fn extent_configs(skip_default_memo_off: bool, exhaustive_sweeps: bool) -> Vec<GridConfig> {
    let mut v = Vec::new();
    for s in SELECTORS {
        for c in perf_enum_configs(s) {
            if skip_default_memo_off && c.budget == Budget::Default && !c.memo {
                continue;
            }
            v.push(c);
        }
        for c in sweep_configs(s) {
            if exhaustive_sweeps
                || c.engine == GridEngine::Stateful
                || kind(&c) == Kind::FirstReport
            {
                v.push(c);
            }
        }
    }
    v
}

/// Runs `fixtures` × `configs`, then the default tests' checks (criteria
/// 1–5, X3, 9's memo agreement, 10) with the per-pair counts of `configs`.
fn extent_checks(fixtures: Vec<Fixture>, configs: &[GridConfig], what: &str) -> Vec<Row> {
    let pairs = compute(fixtures, configs, 1);
    let per = |pred: &dyn Fn(&GridConfig) -> bool| configs.iter().filter(|c| pred(c)).count();
    let mut failures = Vec::new();
    if !excluded_names(&pairs).is_empty() {
        failures.push(format!("excluded {:?}", excluded_names(&pairs)));
    }
    failures.extend(check_c01(&pairs));
    let (f2, f81) = check_c02(&pairs, &BTreeMap::new(), configs.len());
    failures.extend(f2);
    if !f81.is_empty() {
        failures.push(format!("F81 occurrences (pinned none): {f81:?}"));
    }
    failures.extend(check_c03(&pairs, per(&|c| kind(c) == Kind::Enumerating)));
    failures.extend(check_c04(&pairs, false));
    failures.extend(check_x3(
        &pairs,
        per(&|c| c.engine == GridEngine::Enumerator),
    ));
    failures.extend(check_c05(&pairs));
    failures.extend(check_c09_memo(&pairs));
    failures.extend(check_c10(&pairs).0);
    fail_if(failures, what);
    pairs
        .iter()
        .flat_map(|p| p.runs.iter().map(|(r, _)| row_of(r)))
        .collect()
}

/// **X6's extent, `ex:naive` `k = 5`** (gate 4 round 01 m5): both encodings
/// on every configuration — the enumerator's five arms, stateful,
/// complete-first and gated exhaustive under every policy and their
/// first-report runs, each selector — with the default tests' checks.
/// Measured runtime 75 s (one process).
#[test]
#[ignore]
fn x6_ex_naive_k_5_every_engine() {
    let fixtures = vec![naive_fixture(5, 1), naive_fixture(5, 2)];
    let rows = extent_checks(fixtures, &extent_configs(false, true), "X6 at k = 5");
    Tables::open().table("X6: ex:naive k = 5, every configuration", &rows);
}

/// **X6's extent, `ex:naive` `k = 6, 7`, report-and-continue on the
/// enumerator and the stateful engine** (and the sweeping engines'
/// first-report runs): the exhaustive sweeping runs stop at `k = 5` (X6,
/// D-k). At `k = 7` the default-budget memo-off enumerator arm is left out
/// here and run capped, one per process
/// ([`cap_ex_naive_k7_default_budget_memo_off`]). Measured runtime 4 936 s
/// (one process): every run takes ≤ 2.5 s; the time is the checks (the
/// `k = 7` families hold 5 040 graphs each, certified per report).
#[test]
#[ignore]
fn x6_ex_naive_k_6_and_7_report_and_continue() {
    let mut rows = extent_checks(
        vec![naive_fixture(6, 1), naive_fixture(6, 2)],
        &extent_configs(false, false),
        "X6 at k = 6",
    );
    rows.extend(extent_checks(
        vec![naive_fixture(7, 1), naive_fixture(7, 2)],
        &extent_configs(true, false),
        "X6 at k = 7",
    ));
    Tables::open().table("X6: ex:naive k = 6, 7, report-and-continue", &rows);
}

/// **X6's extent, 2PC at `N = 4`** (seed 0) outside the exhaustive sweeping
/// runs: the coordinator and ring rows (conforming and violating) on the
/// enumerator's five arms, the stateful engine and the sweeping engines'
/// first-report runs, with the default tests' checks. The leader pair at
/// `N = 4` has no oracle run within reach (1 839 744 Impl executions) and
/// is run capped instead ([`cap_leader_conforming_n4_is_out_of_reach`],
/// [`cap_leader_split_n4_report_and_continue`]). Measured runtime 819 s
/// (one process).
#[test]
#[ignore]
fn x6_two_pc_n4_outside_the_exhaustive_sweeps() {
    let fixtures: Vec<Fixture> = two_pc_fixtures(4)
        .into_iter()
        .filter(|f| f.name.ends_with("/n4") && !f.name.contains("leader"))
        .map(|mut f| {
            f.config.seed = 0;
            f
        })
        .collect();
    assert_eq!(fixtures.len(), 4, "conformance: X6 2PC N = 4 rows");
    let rows = extent_checks(fixtures, &extent_configs(false, false), "X6 2PC N = 4");
    Tables::open().table(
        "X6: 2PC N = 4 (coordinator, ring), outside exhaustive sweeps",
        &rows,
    );
}

/// **Out of reach (X5 a), one per process:** `ex:naive` `k = 7`, encoding 2,
/// the enumerator at the default budget, memo off — `R_7 = 13 700 > 10 000`,
/// so every gate after `c`'s send exhausts (D5). Capped at 120 s; measured:
/// `Capped` (121 s with cargo).
///
/// **Why `Ltr` stands for the other two selectors** (round 02 m2): on
/// encoding 2 every selector installs `c`'s send last (D1, D-6), and the
/// measured enumerator rows at `k = 2..7` are selector-identical counter for
/// counter (`c06`, the `x6_*` tables, `l2_…`'s `ex:naive` assertion); the
/// rebuild at `c`'s gate is the same `R_7 = 13 700`-node tree, so
/// `FewestEvents` and `Reverse` exhaust at the same gates. Encoding 1 at
/// `k = 7` is not out of reach — it is measured by
/// [`x6_ex_naive_k7_encoding_1_default_budget_memo_off`].
#[test]
#[ignore]
fn cap_ex_naive_k7_default_budget_memo_off() {
    let end = run_grid(
        &naive_fixture(7, 2),
        &GridConfig::new(GridEngine::Enumerator),
        Some(Duration::from_secs(120)),
    );
    Tables::open().table("X5 a: out of differential reach", &[row_of_end(&end)]);
    assert!(
        matches!(end, GridEnd::Capped { .. }),
        "conformance: ex:naive k = 7 default-budget memo off finished: {end:?}"
    );
}

/// **Out of reach (X5 a), one per process:** the leader split-brain pair at
/// `N = 4` (seed 0) on the enumerator at its table's budget, report-and-
/// continue. Capped at 300 s (measured: `Capped`, 300 s); a run that finishes is recorded with its
/// verdict instead (asserted: `Reported`).
#[test]
#[ignore]
fn cap_leader_split_n4_report_and_continue() {
    let mut f = two_pc_fixtures(4)
        .into_iter()
        .find(|f| f.name == "2pc/leader/split/n4")
        .expect("conformance: the leader row");
    f.config.seed = 0;
    let end = run_grid(
        &f,
        &GridConfig::new(GridEngine::Enumerator).budget(Budget::Exact(100_000)),
        Some(Duration::from_secs(300)),
    );
    Tables::open().table(
        "X5 a: the leader split-brain pair at N = 4",
        &[row_of_end(&end)],
    );
    // Round 02 m1: an engine panic is a failure, never "out of reach" (X1).
    assert!(
        !matches!(end, GridEnd::Panicked { .. }),
        "conformance: the leader split pair at N = 4 panicked: {end:?}"
    );
    match &end {
        GridEnd::Ok(r) => assert_eq!(
            class(&status(r)),
            Class::Reported,
            "conformance: leader split N = 4"
        ),
        GridEnd::Capped { .. } => assert!(
            crate::conformance::grid::tainted(),
            "conformance: a capped run did not taint the process"
        ),
        GridEnd::Panicked { .. } => unreachable!("conformance: asserted above"),
    }
}

/// **Criterion 5 and 9 on `ndk3 bad_A`** (D5, D7): the default-budget
/// enumerator runs under each selector, memo off and on, binned. Measured
/// first and pinned: memo off `Ltr` is bin 1 with 15 reports / 11
/// exhaustions (F63); every report certified against the exhaustive
/// families; the unlimited memo-off and memo-on runs agree (criterion 9).
/// Measured runtime 129 s (one process).
#[test]
#[ignore]
fn c05_c09_bad_a_bins_and_memo_arms() {
    let f = ndk("ndk3/bad_A");
    let o = run(&f, &oracle_config());
    let GridRaw::Stateful(os) = &o.raw else {
        unreachable!("conformance: stateful")
    };
    assert!(os.spec_errors.is_empty());
    let fam = Families::new(&os.kept_spec_graphs, &os.kept_impl_graphs, 0, &f.visible);
    let mut rows = Vec::new();
    let mut seen = Vec::new();
    for s in SELECTORS {
        for memo in [false, true] {
            for budget in [Budget::Default, Budget::Unlimited] {
                let c = GridConfig::new(GridEngine::Enumerator)
                    .selector(s)
                    .memo(memo)
                    .budget(budget);
                let r = run(&f, &c);
                rows.push(row_of(&r));
                let st = status(&r);
                for rep in reports_of(&r) {
                    certify(
                        &fam,
                        &Claim {
                            graph: rep.graph,
                            tag: rep.tag,
                            cause: rep.cause.clone(),
                            serialized: rep.serialized,
                        },
                    )
                    .unwrap_or_else(|e| panic!("conformance: bad_A {}: {e}", c.label()));
                }
                seen.push((
                    format!("{s:?}/memo={memo}/{budget:?}"),
                    bin(&st),
                    st.reports,
                    st.exhaustions,
                ));
            }
        }
    }
    Tables::open().table("criteria 5/9: ndk3 bad_A, enumerator arms", &rows);
    // Measured first (gate 3), then pinned: (bin, reports, exhaustions) per
    // arm. Memo off at the default budget is bin 1 under every selector;
    // memo on never exhausts here, even at the default budget.
    let pinned: Vec<(&str, Bin, usize, usize)> = vec![
        ("Ltr/memo=false/Default", Bin::InconclusiveReported, 15, 11),
        ("Ltr/memo=false/Unlimited", Bin::Conclusive, 21, 0),
        ("Ltr/memo=true/Default", Bin::Conclusive, 21, 0),
        ("Ltr/memo=true/Unlimited", Bin::Conclusive, 21, 0),
        (
            "FewestEvents/memo=false/Default",
            Bin::InconclusiveReported,
            18,
            11,
        ),
        ("FewestEvents/memo=false/Unlimited", Bin::Conclusive, 24, 0),
        ("FewestEvents/memo=true/Default", Bin::Conclusive, 24, 0),
        ("FewestEvents/memo=true/Unlimited", Bin::Conclusive, 24, 0),
        (
            "Reverse/memo=false/Default",
            Bin::InconclusiveReported,
            15,
            11,
        ),
        ("Reverse/memo=false/Unlimited", Bin::Conclusive, 21, 0),
        ("Reverse/memo=true/Default", Bin::Conclusive, 21, 0),
        ("Reverse/memo=true/Unlimited", Bin::Conclusive, 21, 0),
    ];
    let got: Vec<(String, Bin, usize, usize)> =
        seen.iter().map(|x| (x.0.clone(), x.1, x.2, x.3)).collect();
    let want: Vec<(String, Bin, usize, usize)> = pinned
        .iter()
        .map(|x| (x.0.to_owned(), x.1, x.2, x.3))
        .collect();
    assert_eq!(got, want, "conformance: criterion 5's bins on bad_A");
    // Criterion 9 (D7's condition): per selector, the unlimited memo-off and
    // memo-on runs report the same set (canonical form, gate, kind).
    let mut failures = Vec::new();
    for s in SELECTORS {
        let keys = |memo: bool| -> BTreeSet<String> {
            let r = run(
                &f,
                &GridConfig::new(GridEngine::Enumerator)
                    .selector(s)
                    .memo(memo)
                    .budget(Budget::Unlimited),
            );
            enum_outcome(&r)
                .reports
                .iter()
                .map(|x| {
                    format!(
                        "{:?}|{:?}|{}",
                        x.gate,
                        x.kind,
                        canon_key(&x.graph, &f.visible)
                    )
                })
                .collect()
        };
        if keys(false) != keys(true) {
            failures.push(format!(
                "{s:?}: unlimited memo off and on report different sets"
            ));
        }
    }
    fail_if(failures, "criterion 9 on bad_A");
}

// =========================================================================
// Memory and caps — one configuration per process (X7, L9)
// =========================================================================

/// One configuration's `VmHWM` (kB) before and after, a process figure that
/// includes the sweep threads' stacks (X7). Each `mem_*` test measured 0.1–0.8 s.
/// Run alone:
/// `cargo test -j 2 -p traceforge --lib <name> -- --ignored --test-threads=1`.
fn memory_row(name: &str, c: GridConfig) {
    let f = ndk(name);
    let r = run(&f, &c);
    assert!(!r.tainted_at_start, "conformance: X7: a tainted process");
    let mut row = row_of(&r);
    row.insert(0, ("memory run", c.label()));
    Tables::open().table(&format!("X7: memory, {name}"), &[row]);
}

#[test]
#[ignore]
fn mem_ndk3_conf_enumerator() {
    memory_row(
        "ndk3/conf",
        GridConfig::new(GridEngine::Enumerator).budget(Budget::Unlimited),
    );
}

#[test]
#[ignore]
fn mem_ndk3_conf_stateful() {
    memory_row("ndk3/conf", GridConfig::new(GridEngine::Stateful));
}

#[test]
#[ignore]
fn mem_ndk3_conf_complete_first() {
    memory_row("ndk3/conf", GridConfig::new(GridEngine::CompleteFirst));
}

#[test]
#[ignore]
fn mem_ndk3_conf_gated() {
    memory_row("ndk3/conf", GridConfig::new(GridEngine::Gated));
}

/// **A capped configuration (L9, X5 a)**: the leader-election pair at
/// `N = 4` (1 839 744 Impl executions under plain checking) on the
/// enumerator at the default budget, capped at 120 s, is out of
/// differential reach: the run is abandoned, `GRID_TAINTED` is set, and the
/// result is `Capped`. One per process. Measured runtime 120.1 s (the cap).
#[test]
#[ignore]
fn cap_leader_conforming_n4_is_out_of_reach() {
    let f = crate::conformance::grid::two_pc_fixtures(4)
        .into_iter()
        .find(|f| f.name == "2pc/leader/split/n4")
        .map(|mut f| {
            f.name = "2pc/leader/conf/n4".to_owned();
            f.implementation =
                crate::conformance::grid::prog(crate::conformance::demo::le_impl(4, false));
            f.table = None;
            f
        })
        .expect("conformance: the leader row");
    let end = run_grid(
        &f,
        &GridConfig::new(GridEngine::Enumerator),
        Some(Duration::from_secs(120)),
    );
    let row = row_of_end(&end);
    Tables::open().table("X5 a: out of differential reach", &[row]);
    assert!(
        matches!(end, GridEnd::Capped { .. }),
        "conformance: L9: the leader pair at N = 4 finished: {end:?}"
    );
    assert!(
        crate::conformance::grid::tainted(),
        "conformance: L9: not tainted"
    );
}

// =========================================================================
// X1 — an engine panic is a failure, never a cap (gate 4 round 01 m1)
// =========================================================================

/// **X1, the panic path:** a configuration that panics on its run thread —
/// the stateful engine on a `Mailbox` configuration, which conformance
/// refuses at load (`ConfBuilder::build`'s scope check, reached through
/// `conf_config`'s `expect`) — comes back as `GridEnd::Panicked` with the
/// panic's payload under both `cap = None` and `cap = Some(_)`, never as
/// `Capped`, and leaves the process untainted.
#[test]
fn x1_an_engine_panic_is_panicked_with_its_payload_under_either_cap() {
    let mut f = paper_fixtures()
        .into_iter()
        .find(|f| f.name == "R1")
        .expect("conformance: R1");
    f.name = "R1/mailbox".to_owned();
    f.config = crate::Config::builder()
        .with_cons_type(crate::ConsType::Mailbox)
        .with_seed(0)
        .build();
    let c = GridConfig::new(GridEngine::Stateful);
    for cap in [None, Some(Duration::from_secs(60))] {
        match run_grid(&f, &c, cap) {
            GridEnd::Panicked {
                fixture, payload, ..
            } => {
                assert_eq!(fixture, "R1/mailbox");
                assert!(
                    payload.contains("conformance: a grid configuration is in scope"),
                    "conformance: X1: the payload is the panic's own text: {payload}"
                );
            }
            other => panic!("conformance: X1: cap {cap:?}: not Panicked: {other:?}"),
        }
    }
    assert!(
        !crate::conformance::grid::tainted(),
        "conformance: X1: a panic tainted the process"
    );
}

/// **X6 at `k = 7`, encoding 1, the enumerator's default-budget memo-off arm
/// under every selector** (round 02 m2): `c`'s send is the first event under
/// all three selectors (D1), its gate costs 1 `SpecVisit` call with the
/// rebuild skipped, so the arm is far inside the budget. Asserted per
/// selector: one report, conclusive (no exhaustion), the §8.8 row (1 call,
/// 0 hits, 1 paper event), and the report certified against the exhaustive
/// families (5 040 graphs a side). Measured runtime: see the round-02
/// follow-up in the report.
#[test]
#[ignore]
fn x6_ex_naive_k7_encoding_1_default_budget_memo_off() {
    let f = naive_fixture(7, 1);
    let o = run(&f, &oracle_config());
    let GridRaw::Stateful(os) = &o.raw else {
        unreachable!("conformance: stateful")
    };
    let fam = Families::new(&os.kept_spec_graphs, &os.kept_impl_graphs, 0, &f.visible);
    let mut rows = Vec::new();
    for s in SELECTORS {
        let r = run(&f, &GridConfig::new(GridEngine::Enumerator).selector(s));
        rows.push(row_of(&r));
        let st = status(&r);
        assert_eq!(
            (bin(&st), st.reports),
            (Bin::Conclusive, 1),
            "conformance: k = 7 enc 1 {s:?}"
        );
        let c = &enum_outcome(&r).counters;
        assert_eq!(
            (
                c.spec_visit_calls,
                c.memo_hits,
                c.paper_events_at_first_report
            ),
            (1, 0, Some(1)),
            "conformance: k = 7 enc 1 {s:?}: the §8.8 row"
        );
        for rep in reports_of(&r) {
            certify(
                &fam,
                &Claim {
                    graph: rep.graph,
                    tag: rep.tag,
                    cause: rep.cause.clone(),
                    serialized: rep.serialized,
                },
            )
            .unwrap_or_else(|e| panic!("conformance: k = 7 enc 1 {s:?}: {e}"));
        }
    }
    Tables::open().table(
        "X6: ex:naive k = 7, encoding 1, default budget, memo off",
        &rows,
    );
}

/// **X1's exclusion mechanism for the leader pair at `N = 4`** (round 02
/// m2): its **oracle run** (stateful, report-and-continue, `Ltr`, seed 0)
/// capped at 300 s, one per process. Asserted: not `Panicked` (X1); when
/// `Capped`, the process is tainted and the pair is excluded and listed
/// (both leader rows at N = 4 then stay out of every non-capped run).
#[test]
#[ignore]
fn cap_leader_conforming_n4_oracle_run() {
    let mut f = two_pc_fixtures(4)
        .into_iter()
        .find(|f| f.name == "2pc/leader/split/n4")
        .expect("conformance: the leader row");
    f.name = "2pc/leader/conf/n4".to_owned();
    f.implementation = crate::conformance::grid::prog(crate::conformance::demo::le_impl(4, false));
    f.table = None;
    f.config.seed = 0;
    let end = run_grid(&f, &oracle_config(), Some(Duration::from_secs(300)));
    Tables::open().table(
        "X1: the leader pair's oracle run at N = 4 (capped)",
        &[row_of_end(&end)],
    );
    assert!(
        !matches!(end, GridEnd::Panicked { .. }),
        "conformance: the oracle run panicked: {end:?}"
    );
    if matches!(end, GridEnd::Capped { .. }) {
        assert!(
            crate::conformance::grid::tainted(),
            "conformance: a capped run did not taint the process"
        );
    }
}
