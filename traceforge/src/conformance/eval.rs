//! `P5-HARNESS`: the evaluation runner (lead; **test-only**, like `grid.rs`).
//!
//! One OS process per row (H2): the driver test `eval_driver` expands an
//! experiment spec to row keys, skips the keys its store already holds (H1),
//! and for every other key re-executes this test binary with `--exact
//! conformance::eval::eval_row`, the row in `EVAL_ROW`; the child resolves the
//! fixture by name, runs the engine as `run_grid` does — but with
//! `keep_graphs = false` on timed and baseline rows (H2, M2) — and prints one
//! sentinel line. The driver enforces the tier's wall and memory limits by
//! sampling the child's `VmHWM` (H5, H6), classifies the outcome (H3), and
//! appends one RFC 4180 record to the row store under a fixed, declared header
//! (H7). `experiments` and `mixed` are computed at read time, never stored.
//!
//! Run one experiment (H9):
//!
//! ```text
//! EVAL_SPEC=X0 EVAL_OUT=<dir> cargo test --release -j 2 -p traceforge --lib \
//!     conformance::eval::eval_driver -- --ignored --exact --nocapture --test-threads=1
//! ```
//!
//! `EVAL_ONLY=<glob>` restricts the keys — an **anchored** glob on the whole row
//! key, `*` the only wildcard (e.g. `EVAL_ONLY='*|Stateful/*'`); a filter that
//! selects no key of the spec is refused. `EVAL_ALLOW_MIXED=1` lets a
//! dirty tree, a different host or a different commit through (never a
//! different header or schema).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use crate::channel::cons_to_model;
use crate::conformance::cfirst;
use crate::conformance::config::{CompletionCover, GatePolicy, GatedMode};
use crate::conformance::gated;
use crate::conformance::grid::APPS_CORNERS;
use crate::conformance::grid::{
    apps_fixtures, apps_grid, apps_series_fixtures, mixed_fixtures, registry, row_of_end,
    stack_mib_for, synth_fixtures, synth_grid, vm_hwm_kb, Budget, Fixture, GridConfig, GridEnd,
    GridEngine, GridRaw, GridResult, Group, Row, SynthPoint, FLAT_SUBSET,
};
use crate::conformance::search::SearchOpts;
use crate::conformance::selector::{InnerOrder, Selector};
use crate::conformance::stateful;
use crate::conformance::{verify, verify_conformance_with_opts};

// =========================================================================
// Schema (H7)
// =========================================================================

/// Bumped whenever a column is added or `GridConfig::label()`'s format
/// changes (round 03 m1: the tester's pinning test ties `LABEL_PIN` and
/// `header()` to this constant).
pub(super) const SCHEMA_VERSION: u32 = 2;

/// `GridConfig::new(GridEngine::Enumerator).label()` at this schema version.
pub(super) const LABEL_PIN: &str =
    "Enumerator/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep";

/// The runner's own columns, in order, before `row_of`'s (H7).
pub(super) const RUNNER_COLUMNS: &[&str] = &[
    "key",
    "run_kind",
    "profile",
    "commit",
    "rep",
    "tier",
    "end_class",
    "censor_via",
    "censored",
    "proc_wall_ms",
    "pid",
    "rss_sampled_hwm_kb",
    "rss_child_hwm_kb",
    "run_dir",
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

/// Every column `settings_columns`, `row_of`, `flat_columns` and `row_of_end`
/// can emit, in first-seen order over their arms — every `push`/`push_d` name
/// in `grid.rs`'s row builders (gate 3 T1: the first list had missed 31 of
/// them); `ended` is mapped to `end_class` by [`eval_row_of`], so it is not
/// listed; `payload` is a runner column too and listed once.
pub(super) const ROW_OF_COLUMNS: &[&str] = &[
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
    "cover",
    "flat_calls",
    "flat_visits",
    "flat_nd_branches",
    "wall_ms",
    "vm_hwm_kb_before",
    "vm_hwm_kb_after",
    "tainted_at_start",
    "stack_mib",
    "reports",
    "exhaustions",
    "diagnostics",
    "end",
    "skipped_gates",
    "inert_gates",
    "seed",
    "spec_error",
    "outer_graphs(execs+block)",
    "gate_invocations",
    "gate_skipped_inert",
    "gate_skipped_replay",
    "gate_skipped_pruned",
    "gate_skipped_disabled",
    "gate_skipped_aborted",
    "cover_calls",
    "cover_exhaustions",
    "rebuilds_taken",
    "rebuilds_skipped_initial_seed",
    "rebuilds_skipped_exhausted_seed",
    "spec_visit_calls",
    "spec_visit_calls_extend",
    "spec_visit_calls_rebuild",
    "memo_hits",
    "per_cover",
    "distinct_keys_run_wide",
    "f63_distinct_run_wide",
    "explored_complete_keys",
    "report_keys",
    "max_paper_events_per_execution",
    "paper_events_at_first_report",
    "executions",
    "engine_wall_time_ms",
    "per_cover_detail",
    "impl_end",
    "spec_end",
    "spec_errors",
    "impl_notes",
    "max_paper_events",
    "kept_impl_graphs",
    "kept_spec_graphs",
    "spec_graphs",
    "impl_graphs",
    "sig_key_buckets",
    "signatures",
    "orders_held",
    "lookups",
    "lookups_signature_miss",
    "lookups_containment_tested",
    "lookups_succeeded",
    "lookups_failed_after_tests",
    "containment_tests",
    "counter_reports",
    "spec_wall_time_ms",
    "impl_wall_time_ms",
    "cut_reports_list",
    "aborted",
    "witness_cache_len",
    "sweep_ends",
    "paper_events_at_first_report(grid)",
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
    "cut_reports",
    "precheck_ran",
    "precheck_wall_time_ms",
    "outer_wall_time_ms",
    "sweep_wall_time_ms",
    "reports_at_gates",
    "reports_at_completion",
    "abort_gate_at",
    "first_failure_mode",
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
    "completion_probes",
    "completion_cache_hits",
    "completion_cache_tests",
    "completion_sweeps",
    "completion_sweeps_successful",
    "completion_sweeps_failing",
    "completion_sweeps_aborted",
    "completion_sweep_sizes",
    "verdict",
    "notes",
    "rendered_engine",
    "spec_errfree",
    "communication_flat",
    "thread_flat",
    "spec_graphs_scanned",
    "first_invisible",
    "refused_at",
    "payload",
    "cap_ms",
    "flat_source_branches",
    "flat_source_recursions",
    "flat_send_kills",
    "flat_slot_kills",
    "flat_source_kills",
    "flat_done_kills",
    "flat_witnesses",
    "flat_max_depth",
    "flat_wall_time_ms",
];

/// The declared header: the runner's columns, then every `row_of` column.
pub(super) fn header() -> Vec<&'static str> {
    let mut h: Vec<&'static str> = RUNNER_COLUMNS.to_vec();
    for c in ROW_OF_COLUMNS {
        if !h.contains(c) {
            h.push(c);
        }
    }
    h
}

// =========================================================================
// Rows, keys, specs (H1)
// =========================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum RunKind {
    Timed,
    Profiling,
    Baseline,
    Contract,
}

impl RunKind {
    pub(super) fn name(self) -> &'static str {
        match self {
            RunKind::Timed => "timed",
            RunKind::Profiling => "profiling",
            RunKind::Baseline => "baseline",
            RunKind::Contract => "contract",
        }
    }

    pub(super) fn parse(s: &str) -> Option<RunKind> {
        Some(match s {
            "timed" => RunKind::Timed,
            "profiling" => RunKind::Profiling,
            "baseline" => RunKind::Baseline,
            "contract" => RunKind::Contract,
            _ => return None,
        })
    }

    /// H2: timed and baseline rows retain no graphs; profiling and contract
    /// rows keep them (the `kept_*` columns).
    pub(super) fn keep_graphs(self) -> bool {
        matches!(self, RunKind::Profiling | RunKind::Contract)
    }
}

/// A tier (H5): a wall limit and a memory limit, named.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Tier {
    pub(super) name: String,
    pub(super) wall: Duration,
    pub(super) mem_kb: u64,
}

impl Tier {
    /// 600 s (D2) and 4 GiB.
    pub(super) fn default_tier() -> Tier {
        Tier {
            name: "default".to_owned(),
            wall: Duration::from_secs(600),
            mem_kb: 4 * 1024 * 1024,
        }
    }

    /// 3600 s and 4 GiB.
    pub(super) fn extension() -> Tier {
        Tier {
            name: "extension".to_owned(),
            wall: Duration::from_secs(3600),
            mem_kb: 4 * 1024 * 1024,
        }
    }
}

/// A series membership (H5 rule (2)): the scope is the configuration minus
/// its size, plus engine, selector, tier and run kind; `size` is the value of
/// the knob the spec names as its size axis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Series {
    pub(super) scope: String,
    pub(super) size: i64,
}

impl Series {
    /// The scope as H5 defines it — the configuration **minus its size**
    /// (`family` and the knob values with the size axis blanked), plus the
    /// engine, selector and every other knob (the `GridConfig` label), the
    /// tier and the run kind. The code-built parts (label, tier, run kind)
    /// cannot be coarser than the rule; `family` and `knobs_without_size` are
    /// the caller's — prefer [`Series::of_row`], which derives them from the
    /// row (round 01 m1, round 02 m2).
    pub(super) fn of(
        family: &str,
        knobs_without_size: &str,
        config: &GridConfig,
        tier: &Tier,
        run_kind: RunKind,
        size: i64,
    ) -> Series {
        Series {
            scope: format!(
                "{family}|{knobs_without_size}|{}|{}|{}",
                config.label(),
                tier.name,
                run_kind.name()
            ),
            size,
        }
    }

    /// The scope derived from the row itself (round 02 m2): `family`, the
    /// `variant` (a mutant's series is never the conforming fixture's), the
    /// knob values `k1..k4` with the size axis blanked, then the label, tier
    /// and run kind; the author supplies only the size axis.
    pub(super) fn of_row(row: &RowSpec, size_axis: usize) -> Series {
        let knobs: Vec<String> = row
            .k
            .iter()
            .enumerate()
            .map(|(i, v)| {
                if i == size_axis {
                    "_".to_owned()
                } else {
                    v.map(|x| x.to_string()).unwrap_or_default()
                }
            })
            .collect();
        let size = row.k[size_axis].unwrap_or(0);
        Series::of(
            &format!("{}|{}", row.family, row.variant),
            &knobs.join(","),
            &row.config,
            &row.tier,
            row.run_kind,
            size,
        )
    }
}

/// One row to run.
#[derive(Clone, Debug)]
pub(super) struct RowSpec {
    pub(super) fixture: String,
    pub(super) config: GridConfig,
    pub(super) rep: u32,
    pub(super) tier: Tier,
    pub(super) run_kind: RunKind,
    pub(super) family: String,
    /// A label of the knob values (`k=2,enc=1`).
    pub(super) knobs: String,
    pub(super) k: [Option<i64>; 4],
    /// `conforming`, `violating`, `mutant:<id>`, `control:<id>`.
    pub(super) variant: String,
    /// The matched conforming twin's row key (RQ2), or empty.
    pub(super) twin_key: String,
    pub(super) series: Option<Series>,
}

impl RowSpec {
    pub(super) fn key(&self, profile: &str) -> String {
        key_of(
            &self.fixture,
            &self.config.label(),
            self.rep,
            &self.tier.name,
            self.run_kind,
            profile,
        )
    }

    /// The identity of a repetition set (H5 rule (1)): everything but `rep`
    /// and `profile`.
    pub(super) fn rep_set(&self) -> String {
        format!(
            "{}|{}|{}|{}",
            self.fixture,
            self.config.label(),
            self.tier.name,
            self.run_kind.name()
        )
    }
}

/// `fixture|label|rep|tier|run_kind|profile` (H1).
pub(super) fn key_of(
    fixture: &str,
    label: &str,
    rep: u32,
    tier: &str,
    run_kind: RunKind,
    profile: &str,
) -> String {
    format!(
        "{fixture}|{label}|{rep}|{tier}|{}|{profile}",
        run_kind.name()
    )
}

/// A key's parts, if it parses under the current label format
/// (`Refusal::KeyFormat` otherwise).
pub(super) fn parse_key(key: &str) -> Option<(String, GridConfig, u32, String, RunKind, String)> {
    let parts: Vec<&str> = key.split('|').collect();
    if parts.len() != 6 {
        return None;
    }
    let config = parse_label(parts[1])?;
    let rep = parts[2].parse().ok()?;
    let run_kind = RunKind::parse(parts[4])?;
    Some((
        parts[0].to_owned(),
        config,
        rep,
        parts[3].to_owned(),
        run_kind,
        parts[5].to_owned(),
    ))
}

/// The inverse of `GridConfig::label()` (every field prints as `Debug`).
pub(super) fn parse_label(label: &str) -> Option<GridConfig> {
    let p: Vec<&str> = label.split('/').collect();
    if p.len() != 11 {
        return None;
    }
    fn flag(s: &str, name: &str) -> Option<bool> {
        s.strip_prefix(name)?.strip_prefix('=')?.parse().ok()
    }
    Some(GridConfig {
        engine: parse_engine(p[0])?,
        selector: parse_selector(p[1])?,
        stop_at_first_report: flag(p[2], "stop")?,
        gated_mode: parse_gated_mode(p[3])?,
        gate_policy: parse_policy(p[4])?,
        memo: flag(p[5], "memo")?,
        budget: parse_budget(p[6])?,
        precheck: flag(p[7], "precheck")?,
        instrumented: flag(p[8], "instr")?,
        early_error_cut: flag(p[9], "cut")?,
        completion_cover: parse_cover(p[10].strip_prefix("cover=")?)?,
    })
}

pub(super) fn parse_engine(s: &str) -> Option<GridEngine> {
    Some(match s {
        "Enumerator" => GridEngine::Enumerator,
        "Stateful" => GridEngine::Stateful,
        "CompleteFirst" => GridEngine::CompleteFirst,
        "Gated" => GridEngine::Gated,
        "Verify" => GridEngine::Verify,
        _ => return None,
    })
}

pub(super) fn parse_selector(s: &str) -> Option<Selector> {
    Some(match s {
        "Ltr" => Selector::Ltr,
        "FewestEvents" => Selector::FewestEvents,
        "Reverse" => Selector::Reverse,
        _ => return None,
    })
}

pub(super) fn parse_gated_mode(s: &str) -> Option<GatedMode> {
    Some(match s {
        "Exhaustive" => GatedMode::Exhaustive,
        "FirstFailure" => GatedMode::FirstFailure,
        _ => return None,
    })
}

pub(super) fn parse_policy(s: &str) -> Option<GatePolicy> {
    Some(match s {
        "Never" => GatePolicy::Never,
        "Always" => GatePolicy::Always,
        other => GatePolicy::Budget(
            other
                .strip_prefix("Budget(")?
                .strip_suffix(')')?
                .parse()
                .ok()?,
        ),
    })
}

pub(super) fn parse_budget(s: &str) -> Option<Budget> {
    Some(match s {
        "Default" => Budget::Default,
        "Unlimited" => Budget::Unlimited,
        other => Budget::Exact(
            other
                .strip_prefix("Exact(")?
                .strip_suffix(')')?
                .parse()
                .ok()?,
        ),
    })
}

pub(super) fn parse_cover(s: &str) -> Option<CompletionCover> {
    Some(match s {
        "Sweep" => CompletionCover::Sweep,
        "Flat" => CompletionCover::Flat,
        _ => return None,
    })
}

/// An experiment: a name and its rows (H1; the X-names of plan §3).
#[derive(Clone, Debug)]
pub(super) struct Spec {
    pub(super) name: String,
    pub(super) rows: Vec<RowSpec>,
}

/// `X0` (criterion 1): `ex:naive/k2/enc1` × the four engines × three
/// selectors, Part 6's own configurations, timed, one repetition.
pub(super) fn x0_spec() -> Spec {
    let mut rows = Vec::new();
    for engine in [
        GridEngine::Enumerator,
        GridEngine::Stateful,
        GridEngine::CompleteFirst,
        GridEngine::Gated,
    ] {
        for selector in [Selector::Ltr, Selector::FewestEvents, Selector::Reverse] {
            rows.push(RowSpec {
                fixture: "ex:naive/k2/enc1".to_owned(),
                config: GridConfig::new(engine).selector(selector),
                rep: 0,
                tier: Tier::default_tier(),
                run_kind: RunKind::Timed,
                family: "ex:naive".to_owned(),
                knobs: "k=2,enc=1".to_owned(),
                k: [Some(2), Some(1), None, None],
                variant: "violating".to_owned(),
                twin_key: String::new(),
                series: None,
            });
        }
    }
    Spec {
        name: "X0".to_owned(),
        rows,
    }
}

/// The specs `eval_driver` knows by name (`EVAL_SPEC`); the campaign's specs
/// are added here by `P5-CAMPAIGN`.
pub(super) fn builtin_specs() -> Vec<Spec> {
    let mut out = vec![x0_spec()];
    out.extend(campaign_specs());
    out
}

/// The experiments whose expansion contains `key` (H1: computed at read
/// time, never stored).
pub(super) fn experiments_of(key: &str, specs: &[Spec], profile: &str) -> Vec<String> {
    specs
        .iter()
        .filter(|s| s.rows.iter().any(|r| r.key(profile) == key))
        .map(|s| s.name.clone())
        .collect()
}

// =========================================================================
// Fixtures by name (H2)
// =========================================================================

/// Every fixture the child may be asked for: Part 6's registry at its full
/// size, Part 7's mixed fixtures, later parts' families, and the tester's
/// test-only fixtures.
pub(super) fn all_fixtures() -> Vec<Fixture> {
    let mut out = registry(2..=7, 4, 10);
    out.extend(mixed_fixtures());
    out.extend(apps_fixtures());
    out.extend(synth_fixtures());
    out.extend(apps_series_fixtures());
    out.extend(super::eval_tests::test_fixtures());
    out
}

/// H2: resolution by name over the whole domain, which must be free of
/// duplicate names (`Refusal::DuplicateName`).
pub(super) fn fixture_by_name(name: &str) -> Result<Fixture, Refusal> {
    let all = all_fixtures();
    let mut seen = BTreeSet::new();
    for f in &all {
        if !seen.insert(f.name.clone()) {
            return Err(Refusal::DuplicateName(f.name.clone()));
        }
    }
    all.into_iter()
        .find(|f| f.name == name)
        .ok_or_else(|| Refusal::UnknownFixture(name.to_owned()))
}

// =========================================================================
// The run path (H2): `run_grid` without a cap, `keep_graphs` by run kind
// =========================================================================

/// The engine call, as `grid.rs::call` but with `keep_graphs` a parameter
/// (round 02 M2: the grid's `true` retains every graph).
fn call_with(fixture: &Fixture, config: &GridConfig, keep_graphs: bool) -> GridRaw {
    let imp = fixture.implementation.clone();
    let spec = fixture.specification.clone();
    match config.engine {
        GridEngine::Enumerator => {
            let mut engine_config = fixture.config.clone();
            engine_config.selector = config.selector;
            GridRaw::Enumerator(verify_conformance_with_opts(
                engine_config,
                imp,
                spec,
                fixture.visible.clone(),
                config.budget.value(),
                config.stop_at_first_report,
                SearchOpts {
                    inner_order: InnerOrder::Recorded,
                    memo: config.memo,
                    instrument: config.instrumented,
                },
            ))
        }
        GridEngine::Stateful => {
            let cc = config.conf_config(fixture);
            GridRaw::Stateful(stateful::run_with(&cc, &imp, &spec, keep_graphs))
        }
        GridEngine::CompleteFirst => {
            let cc = config.conf_config(fixture);
            if config.precheck {
                GridRaw::Verdict(cfirst::run(cc, imp, spec))
            } else {
                GridRaw::CompleteFirst(cfirst::run_with(&cc, &imp, &spec, keep_graphs))
            }
        }
        GridEngine::Gated => {
            let cc = config.conf_config(fixture);
            if config.precheck {
                GridRaw::Verdict(gated::run(cc, imp, spec))
            } else {
                GridRaw::Gated(gated::run_with(&cc, &imp, &spec, keep_graphs))
            }
        }
        GridEngine::Verify => {
            let cc = config.conf_config(fixture);
            GridRaw::Verdict(verify(cc, move || imp(), move || spec()))
        }
    }
}

fn panic_text(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_owned()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_owned()
    }
}

/// `run_grid(fixture, config, None)` with `keep_graphs` chosen by the run
/// kind: the `Flat` refusal, the run thread with the grid's stack, the
/// `VmHWM` read **before** any rendering (round 03 m3), the panic payload.
pub(super) fn run_row_in_process(
    fixture: &Fixture,
    config: &GridConfig,
    keep_graphs: bool,
) -> GridEnd {
    if config.completion_cover == CompletionCover::Flat {
        let bad_engine = !matches!(config.engine, GridEngine::CompleteFirst | GridEngine::Gated);
        if bad_engine || !config.precheck {
            return GridEnd::Panicked {
                fixture: fixture.name.clone(),
                config: config.clone(),
                payload: format!(
                    "refused: completion_cover(Flat) needs precheck = true and engine in \
                     {{CompleteFirst, Gated}} (got precheck = {}, engine = {:?})",
                    config.precheck, config.engine
                ),
            };
        }
    }
    let tainted_at_start = crate::conformance::grid::tainted();
    let stack_mib = stack_mib_for(fixture, config);
    let (tx, rx) = mpsc::channel();
    let f = fixture.clone();
    let c = config.clone();
    let handle = std::thread::Builder::new()
        .name(format!("eval:{}", fixture.name))
        .stack_size(stack_mib * 1024 * 1024)
        .spawn(move || {
            let before = vm_hwm_kb();
            let started = Instant::now();
            let outcome = catch_unwind(AssertUnwindSafe(|| call_with(&f, &c, keep_graphs)));
            let wall = started.elapsed();
            let after = vm_hwm_kb();
            let _ = tx.send((outcome, wall, before, after));
        })
        .expect("conformance: could not spawn the eval run thread");
    let received = rx.recv();
    let _ = handle.join();
    match received {
        Err(_) => GridEnd::Panicked {
            fixture: fixture.name.clone(),
            config: config.clone(),
            payload: "run thread vanished without sending its outcome".to_owned(),
        },
        Ok((Ok(raw), wall, before, after)) => GridEnd::Ok(GridResult {
            fixture: fixture.name.clone(),
            config: config.clone(),
            raw,
            wall,
            vm_hwm_kb: (before, after),
            tainted_at_start,
            stack_mib,
        }),
        Ok((Err(payload), _, _, _)) => GridEnd::Panicked {
            fixture: fixture.name.clone(),
            config: config.clone(),
            payload: panic_text(payload),
        },
    }
}

// =========================================================================
// Rows (H7)
// =========================================================================

/// What the runner knows about a row besides the engine's outcome.
#[derive(Clone, Debug, Default)]
pub(super) struct RowMeta {
    pub(super) key: String,
    pub(super) run_kind: String,
    pub(super) profile: String,
    pub(super) commit: String,
    pub(super) rep: String,
    pub(super) tier: String,
    pub(super) end_class: String,
    pub(super) censor_via: String,
    pub(super) censored: bool,
    pub(super) proc_wall_ms: String,
    pub(super) pid: String,
    pub(super) rss_sampled_hwm_kb: String,
    /// The child's run directory (stdout, stderr), relative to the store.
    pub(super) run_dir: String,
    pub(super) diag_bytes_est: String,
    pub(super) family: String,
    pub(super) knobs: String,
    pub(super) k: [Option<i64>; 4],
    pub(super) variant: String,
    pub(super) twin_key: String,
    pub(super) comm_model: String,
}

impl RowMeta {
    pub(super) fn of(spec: &RowSpec, profile: &str, commit: &str, comm_model: &str) -> RowMeta {
        RowMeta {
            key: spec.key(profile),
            run_kind: spec.run_kind.name().to_owned(),
            profile: profile.to_owned(),
            commit: commit.to_owned(),
            rep: spec.rep.to_string(),
            tier: spec.tier.name.clone(),
            family: spec.family.clone(),
            knobs: spec.knobs.clone(),
            k: spec.k,
            variant: spec.variant.clone(),
            twin_key: spec.twin_key.clone(),
            comm_model: comm_model.to_owned(),
            ..RowMeta::default()
        }
    }
}

/// The runner's row: [`RowMeta`]'s columns, then `row_of_end`'s with `ended`
/// mapped to `end_class` (n2) and the knob columns that do not apply as
/// `n/a` (n4). `rss_child_hwm_kb` is the run thread's post-call `VmHWM`
/// (`vm_hwm_kb_after`, read before rendering — round 03 m3); `diag_keys` is
/// read back from the instrumentation columns.
pub(super) fn eval_row_of(end: &GridEnd, meta: &RowMeta) -> Row {
    let inner = verdict_counter_fill(end, row_of_end(end));
    let (config, after) = match end {
        GridEnd::Ok(r) => (&r.config, r.vm_hwm_kb.1),
        GridEnd::Panicked { config, .. } | GridEnd::Capped { config, .. } => (config, None),
    };
    let ended = inner
        .iter()
        .find(|(k, _)| *k == "ended")
        .map(|(_, v)| v.clone());
    let end_class = if !meta.end_class.is_empty() {
        meta.end_class.clone()
    } else {
        match ended.as_deref() {
            Some("panicked") => "panicked".to_owned(),
            Some("capped") => "capped_wall".to_owned(),
            _ => "ok".to_owned(),
        }
    };
    let col = |name: &str| -> String {
        inner
            .iter()
            .find(|(k, _)| *k == name)
            .map(|(_, v)| v.clone())
            .unwrap_or_default()
    };
    let diag_keys = {
        let a: u64 = col("distinct_keys_run_wide").parse().unwrap_or(0);
        let b: u64 = col("f63_distinct_run_wide").parse().unwrap_or(0);
        if config.instrumented {
            (a + b).to_string()
        } else {
            String::new()
        }
    };
    let sweeping = matches!(config.engine, GridEngine::CompleteFirst | GridEngine::Gated);
    let mut row: Row = Vec::new();
    let mut p = |k: &'static str, v: String| row.push((k, v));
    p("key", meta.key.clone());
    p("run_kind", meta.run_kind.clone());
    p("profile", meta.profile.clone());
    p("commit", meta.commit.clone());
    p("rep", meta.rep.clone());
    p("tier", meta.tier.clone());
    p("end_class", end_class);
    p("censor_via", meta.censor_via.clone());
    p("censored", meta.censored.to_string());
    p("proc_wall_ms", meta.proc_wall_ms.clone());
    p("pid", meta.pid.clone());
    p("rss_sampled_hwm_kb", meta.rss_sampled_hwm_kb.clone());
    p(
        "rss_child_hwm_kb",
        after.map(|v| v.to_string()).unwrap_or_default(),
    );
    p("run_dir", meta.run_dir.clone());
    p("diag_keys", diag_keys);
    p("diag_bytes_est", meta.diag_bytes_est.clone());
    p("family", meta.family.clone());
    p("knobs", meta.knobs.clone());
    for (i, name) in ["k1", "k2", "k3", "k4"].iter().enumerate() {
        p(name, meta.k[i].map(|v| v.to_string()).unwrap_or_default());
    }
    p("variant", meta.variant.clone());
    p("twin_key", meta.twin_key.clone());
    p("cut", config.early_error_cut.to_string());
    p("inner_order", "Recorded".to_owned());
    p("comm_model", meta.comm_model.clone());
    p("cache", if sweeping { "on" } else { "n/a" }.to_owned());
    p(
        "carry",
        if config.engine == GridEngine::Gated {
            "on"
        } else {
            "n/a"
        }
        .to_owned(),
    );
    p("direction", "none".to_owned());
    for (k, v) in inner {
        if k == "ended" {
            continue;
        }
        row.push((k, v));
    }
    row
}

/// A `skipped_*` row (round 01 n3): built as a capped row but with no cap
/// time — the row never ran.
fn skipped_row(end: &GridEnd, meta: &RowMeta) -> Row {
    let mut row = eval_row_of(end, meta);
    if let Some(cell) = row.iter_mut().find(|(k, _)| *k == "cap_ms") {
        cell.1.clear();
    }
    row
}

/// A row's cells in header order (blank where absent).
pub(super) fn record_of(row: &Row) -> Vec<String> {
    header()
        .iter()
        .map(|c| {
            row.iter()
                .find(|(k, _)| k == c)
                .map(|(_, v)| v.clone())
                .unwrap_or_default()
        })
        .collect()
}

// =========================================================================
// CSV (H7): RFC 4180, every value quoted, control characters escaped (n3)
// =========================================================================

/// `\` first, then newline and carriage return — reversible.
pub(super) fn escape_value(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

pub(super) fn unescape_value(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('\\') => out.push('\\'),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

pub(super) fn csv_line(cells: &[String]) -> String {
    let quoted: Vec<String> = cells
        .iter()
        .map(|c| format!("\"{}\"", escape_value(c).replace('"', "\"\"")))
        .collect();
    quoted.join(",")
}

/// One RFC 4180 record (no embedded newlines: they are escaped on write);
/// `None` if the line is malformed (an unterminated quote).
pub(super) fn parse_csv_line(line: &str) -> Option<Vec<String>> {
    let mut cells = Vec::new();
    let mut cur = String::new();
    let mut chars = line.chars().peekable();
    // Gate 3 T5/L5: the writer quotes every cell, so an unquoted cell — a
    // record cut after its last comma included — is malformed.
    let mut after_comma = false;
    loop {
        match chars.peek() {
            None => {
                if after_comma || cells.is_empty() {
                    return None;
                }
                return Some(cells);
            }
            Some('"') => {
                chars.next();
                loop {
                    match chars.next() {
                        None => return None,
                        Some('"') => {
                            if chars.peek() == Some(&'"') {
                                chars.next();
                                cur.push('"');
                            } else {
                                break;
                            }
                        }
                        Some(c) => cur.push(c),
                    }
                }
                match chars.next() {
                    None => {
                        cells.push(unescape_value(&cur));
                        return Some(cells);
                    }
                    Some(',') => {
                        cells.push(unescape_value(&cur));
                        cur.clear();
                        after_comma = true;
                    }
                    Some(_) => return None,
                }
            }
            Some(_) => return None,
        }
    }
}

// =========================================================================
// Refusals (H7, m5) and probes
// =========================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Refusal {
    Header,
    Schema(String),
    KeyFormat(String),
    Host(String),
    Commit(String),
    Dirty(String),
    DuplicateName(String),
    UnknownFixture(String),
    Spec(String),
    Io(String),
}

impl Refusal {
    /// The reason, as a sentence (not a `Display` impl: the closed `s5_tests`
    /// emission scan allows those in `report.rs` only).
    pub(super) fn text(&self) -> String {
        match self {
            Refusal::Header => "refused: the store's header is not the declared header".to_owned(),
            Refusal::Schema(s) => format!("refused: schema version {s} is not {SCHEMA_VERSION}"),
            Refusal::KeyFormat(k) => format!("refused: stored key does not parse: {k}"),
            Refusal::Host(h) => format!("refused: the store was written on another host: {h}"),
            Refusal::Commit(c) => format!("refused: the store holds rows from commit {c}"),
            Refusal::Dirty(c) => format!("refused: the tree is dirty ({c})"),
            Refusal::DuplicateName(n) => format!("refused: duplicate fixture name {n}"),
            Refusal::UnknownFixture(n) => format!("refused: no fixture named {n}"),
            Refusal::Spec(s) => format!("refused: {s}"),
            Refusal::Io(e) => format!("refused: io: {e}"),
        }
    }
}

/// The git and host probes, injectable by tests (m5).
pub(super) struct Probes {
    /// `(commit, dirty)`.
    pub(super) git: Box<dyn Fn() -> (String, bool)>,
    pub(super) host: Box<dyn Fn() -> String>,
}

impl Probes {
    pub(super) fn real() -> Probes {
        Probes {
            git: Box::new(git_probe),
            host: Box::new(host_probe),
        }
    }
}

fn git_probe() -> (String, bool) {
    let dir = env!("CARGO_MANIFEST_DIR");
    let out = |args: &[&str]| -> String {
        Command::new("git")
            .args(args)
            .current_dir(dir)
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
            .unwrap_or_else(|| "unknown".to_owned())
    };
    let commit = out(&["rev-parse", "HEAD"]);
    let dirty = !out(&["status", "--porcelain"]).is_empty();
    (commit, dirty)
}

fn host_probe() -> String {
    let cpu = fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("model name"))
                .and_then(|l| l.split(':').nth(1))
                .map(|v| v.trim().to_owned())
        })
        .unwrap_or_else(|| "unknown cpu".to_owned());
    let ram = fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("MemTotal"))
                .map(|l| l.split_whitespace().skip(1).collect::<Vec<_>>().join(" "))
        })
        .unwrap_or_else(|| "unknown ram".to_owned());
    let kernel = fs::read_to_string("/proc/sys/kernel/osrelease")
        .map(|s| s.trim().to_owned())
        .unwrap_or_else(|_| "unknown kernel".to_owned());
    let rustc = Command::new("rustc")
        .arg("--version")
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
        .unwrap_or_else(|| "unknown rustc".to_owned());
    format!("{cpu}, {ram}, {kernel}, {rustc}")
}

pub(super) fn profile_name() -> &'static str {
    if cfg!(debug_assertions) {
        "test"
    } else {
        "release"
    }
}

// =========================================================================
// The store (H7)
// =========================================================================

pub(super) struct Store {
    path: PathBuf,
    keys: BTreeSet<String>,
    rows: Vec<Vec<String>>,
}

impl Store {
    /// Open or create; refuse on a different header or schema (no override),
    /// on a different host or commit unless `allow_mixed`, on a stored key
    /// that does not parse; drop a malformed last line (H7).
    pub(super) fn open(
        path: &Path,
        host: &str,
        commit: &str,
        allow_mixed: bool,
    ) -> Result<Store, Refusal> {
        let declared = header();
        let host_line = format!("#host: {host}; schema={SCHEMA_VERSION}");
        // Gate 3 T4: an empty or header-only file (a driver killed while
        // creating the store) holds no row and is created afresh; so is a
        // header-and-host file whose host line has no newline (gate 4 T8:
        // it holds no row either, and an append would fuse with the host
        // line).
        let fresh = !path.exists()
            || fs::read_to_string(path)
                .map(|t| {
                    let n = t.lines().filter(|l| !l.trim().is_empty()).count();
                    n < 2 || (n == 2 && !t.ends_with('\n'))
                })
                .unwrap_or(true);
        if fresh {
            if let Some(dir) = path.parent() {
                fs::create_dir_all(dir).map_err(|e| Refusal::Io(e.to_string()))?;
            }
            let mut f = fs::File::create(path).map_err(|e| Refusal::Io(e.to_string()))?;
            let hdr: Vec<String> = declared.iter().map(|s| (*s).to_owned()).collect();
            // One `write_all` for the header and the host line (T8).
            let head = format!("{}\n{host_line}\n", csv_line(&hdr));
            f.write_all(head.as_bytes())
                .map_err(|e| Refusal::Io(e.to_string()))?;
            return Ok(Store {
                path: path.to_owned(),
                keys: BTreeSet::new(),
                rows: Vec::new(),
            });
        }
        let text = fs::read_to_string(path).map_err(|e| Refusal::Io(e.to_string()))?;
        let mut lines: Vec<&str> = text.lines().collect();
        let stored_header = lines
            .first()
            .and_then(|l| parse_csv_line(l))
            .ok_or(Refusal::Header)?;
        if stored_header != declared {
            return Err(Refusal::Header);
        }
        let stored_host = lines.get(1).copied().unwrap_or_default();
        let (stored_host_part, stored_schema) = match stored_host
            .strip_prefix("#host: ")
            .and_then(|r| r.rsplit_once("; schema="))
        {
            Some((h, s)) => (h.to_owned(), s.to_owned()),
            None => return Err(Refusal::Schema("missing".to_owned())),
        };
        if stored_schema != SCHEMA_VERSION.to_string() {
            return Err(Refusal::Schema(stored_schema));
        }
        if stored_host_part != host && !allow_mixed {
            return Err(Refusal::Host(stored_host_part));
        }
        // A malformed last line (a driver killed mid-append) is dropped; so is
        // a last line without its newline, even when it parses (round 02 m1:
        // the writer never finished it, and the next append would fuse two
        // records into one line).
        let mut truncated = false;
        if lines.len() > 2 {
            let last = lines[lines.len() - 1];
            let ok = parse_csv_line(last).is_some_and(|c| c.len() == declared.len())
                && text.ends_with('\n');
            if !ok {
                lines.pop();
                truncated = true;
            }
        }
        let key_idx = declared
            .iter()
            .position(|c| *c == "key")
            .expect("conformance: the declared header has a key column");
        let commit_idx = declared
            .iter()
            .position(|c| *c == "commit")
            .expect("conformance: the declared header has a commit column");
        let mut keys = BTreeSet::new();
        let mut rows = Vec::new();
        for l in lines.iter().skip(2) {
            let cells = parse_csv_line(l).ok_or(Refusal::Header)?;
            if cells.len() != declared.len() {
                return Err(Refusal::Header);
            }
            let key = &cells[key_idx];
            if parse_key(key).is_none() {
                return Err(Refusal::KeyFormat(key.clone()));
            }
            if cells[commit_idx] != commit && !allow_mixed {
                return Err(Refusal::Commit(cells[commit_idx].clone()));
            }
            keys.insert(key.clone());
            rows.push(cells);
        }
        if truncated {
            // In place (round 01 m2): the store is cut at the end of its
            // last good line; nothing is rewritten, so a crash here loses
            // at most the already-malformed tail.
            let keep: usize = lines.iter().map(|l| l.len() + 1).sum();
            let f = fs::OpenOptions::new()
                .write(true)
                .open(path)
                .map_err(|e| Refusal::Io(e.to_string()))?;
            f.set_len(keep as u64)
                .map_err(|e| Refusal::Io(e.to_string()))?;
        }
        Ok(Store {
            path: path.to_owned(),
            keys,
            rows,
        })
    }

    /// The stored row's `end_class`, if the key is held.
    pub(super) fn end_class_of(&self, key: &str) -> Option<String> {
        let hdr = header();
        let key_idx = hdr.iter().position(|c| *c == "key")?;
        let ec_idx = hdr.iter().position(|c| *c == "end_class")?;
        self.rows
            .iter()
            .find(|r| r[key_idx] == key)
            .map(|r| r[ec_idx].clone())
    }

    pub(super) fn has(&self, key: &str) -> bool {
        self.keys.contains(key)
    }

    pub(super) fn rows(&self) -> &[Vec<String>] {
        &self.rows
    }

    pub(super) fn append(&mut self, row: &Row) -> Result<(), Refusal> {
        let cells = record_of(row);
        let mut f = fs::OpenOptions::new()
            .append(true)
            .open(&self.path)
            .map_err(|e| Refusal::Io(e.to_string()))?;
        // One `write_all` for the record and its newline (round 02 m1): a
        // driver killed mid-write leaves a fragment without a newline, which
        // `open` drops; never a complete record without its newline.
        let line = format!("{}\n", csv_line(&cells));
        f.write_all(line.as_bytes())
            .map_err(|e| Refusal::Io(e.to_string()))?;
        let key_idx = header()
            .iter()
            .position(|c| *c == "key")
            .expect("conformance: the declared header has a key column");
        self.keys.insert(cells[key_idx].clone());
        self.rows.push(cells);
        Ok(())
    }
}

/// Read a store's rows as maps (for the plotting script's tests and the
/// read-time columns `experiments` and `mixed`).
pub(super) fn read_rows(path: &Path) -> Result<Vec<BTreeMap<String, String>>, Refusal> {
    let text = fs::read_to_string(path).map_err(|e| Refusal::Io(e.to_string()))?;
    let hdr = header();
    let mut out = Vec::new();
    for l in text.lines().skip(2) {
        if let Some(cells) = parse_csv_line(l) {
            if cells.len() == hdr.len() {
                out.push(hdr.iter().map(|c| (*c).to_owned()).zip(cells).collect());
            }
        }
    }
    Ok(out)
}

/// H5 rule (1), at read time: a repetition set is `mixed` when some rep is
/// censored and some completed.
pub(super) fn mixed_of(rows: &[BTreeMap<String, String>], rep_set: &str) -> bool {
    let of_set: Vec<&BTreeMap<String, String>> = rows
        .iter()
        .filter(|r| {
            r.get("key")
                .and_then(|k| parse_key(k))
                .map(|(fx, cfg, _, tier, rk, _)| {
                    format!("{fx}|{}|{tier}|{}", cfg.label(), rk.name()) == rep_set
                })
                .unwrap_or(false)
        })
        .collect();
    let censored = of_set
        .iter()
        .any(|r| r.get("censored").map(String::as_str) == Some("true"));
    let completed = of_set
        .iter()
        .any(|r| r.get("end_class").map(String::as_str) == Some("ok"));
    censored && completed
}

// =========================================================================
// The child (H2)
// =========================================================================

/// The row, as JSON for `EVAL_ROW` (a hand-built `serde_json::Value`).
pub(super) fn row_json(spec: &RowSpec) -> String {
    let c = &spec.config;
    serde_json::json!({
        "fixture": spec.fixture,
        "label": c.label(),
        "rep": spec.rep,
        "tier": { "name": spec.tier.name, "wall_ms": spec.tier.wall.as_millis() as u64, "mem_kb": spec.tier.mem_kb },
        "run_kind": spec.run_kind.name(),
        "family": spec.family,
        "knobs": spec.knobs,
        "k": spec.k,
        "variant": spec.variant,
        "twin_key": spec.twin_key,
    })
    .to_string()
}

pub(super) fn row_from_json(s: &str) -> Option<RowSpec> {
    let v: serde_json::Value = serde_json::from_str(s).ok()?;
    let config = parse_label(v["label"].as_str()?)?;
    let k: Vec<Option<i64>> = v["k"].as_array()?.iter().map(|x| x.as_i64()).collect();
    Some(RowSpec {
        fixture: v["fixture"].as_str()?.to_owned(),
        config,
        rep: v["rep"].as_u64()? as u32,
        tier: Tier {
            name: v["tier"]["name"].as_str()?.to_owned(),
            wall: Duration::from_millis(v["tier"]["wall_ms"].as_u64()?),
            mem_kb: v["tier"]["mem_kb"].as_u64()?,
        },
        run_kind: RunKind::parse(v["run_kind"].as_str()?)?,
        family: v["family"].as_str()?.to_owned(),
        knobs: v["knobs"].as_str()?.to_owned(),
        k: [
            k.first().copied().flatten(),
            k.get(1).copied().flatten(),
            k.get(2).copied().flatten(),
            k.get(3).copied().flatten(),
        ],
        variant: v["variant"].as_str()?.to_owned(),
        twin_key: v["twin_key"].as_str()?.to_owned(),
        series: None,
    })
}

pub(super) const SENTINEL: &str = "EVALROW\t";

/// The child's work: resolve, run, print the sentinel record. Returns the
/// row for in-process callers (tests).
pub(super) fn child_row(spec: &RowSpec, commit: &str) -> Result<Row, Refusal> {
    let fixture = fixture_by_name(&spec.fixture)?;
    let comm_model = format!("{:?}", cons_to_model(fixture.config.cons_type));
    let meta = RowMeta::of(spec, profile_name(), commit, &comm_model);
    let export = std::env::var("EVAL_EXPORT").unwrap_or_default();
    // X2P's child keeps no graphs: the first report carries its own graph
    // (`P5-CAMPAIGN` C4; `P5-HARNESS` erratum H4).
    let keep = spec.run_kind.keep_graphs() && export != "first_report";
    let end = run_row_in_process(&fixture, &spec.config, keep);
    if let Ok(dir) = std::env::var("EVAL_RUN_DIR") {
        match export.as_str() {
            "first_report" => export_first_report(&end, &fixture.visible, Path::new(&dir))?,
            "spec_words" => export_spec_words(&end, &fixture.visible, Path::new(&dir))?,
            _ => {}
        }
    }
    Ok(eval_row_of(&end, &meta))
}

/// The child entry point (H2): `--ignored --exact conformance::eval::eval_row
/// --nocapture --test-threads=1` with `EVAL_ROW`; a no-op without it.
#[test]
#[ignore]
fn eval_row() {
    let Some(json) = std::env::var_os("EVAL_ROW") else {
        return;
    };
    let spec =
        row_from_json(&json.to_string_lossy()).expect("conformance: EVAL_ROW does not parse");
    let commit = std::env::var("EVAL_COMMIT").unwrap_or_default();
    let row = child_row(&spec, &commit).unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let line = format!("{SENTINEL}{}\n", csv_line(&record_of(&row)));
    let mut out = std::io::stdout().lock();
    out.write_all(line.as_bytes())
        .expect("conformance: writing the sentinel record");
    out.flush()
        .expect("conformance: flushing the sentinel record");
}

// =========================================================================
// The driver (H1–H6)
// =========================================================================

pub(super) struct Driver {
    pub(super) spec: Spec,
    /// Every spec, for `experiments_of` (read time).
    pub(super) specs: Vec<Spec>,
    pub(super) out_dir: PathBuf,
    pub(super) sample_period: Duration,
    pub(super) probes: Probes,
    pub(super) allow_mixed: bool,
    /// An anchored glob on row keys (`EVAL_ONLY`; `*` matches any run of
    /// characters, nothing is implied at either end).
    pub(super) only: Option<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Summary {
    pub(super) ran: usize,
    pub(super) skipped_present: usize,
    pub(super) skipped_rep: usize,
    pub(super) skipped_after_censor: usize,
    pub(super) censored: usize,
    pub(super) store: PathBuf,
}

/// What the driver observed of a child.
struct ChildOutcome {
    status: Option<std::process::ExitStatus>,
    killed: Option<&'static str>,
    elapsed: Duration,
    sampled_hwm_kb: Option<u64>,
    sentinel: Option<Vec<String>>,
    pid: u32,
}

impl Driver {
    pub(super) fn from_env() -> Result<Driver, Refusal> {
        let name =
            std::env::var("EVAL_SPEC").map_err(|_| Refusal::Spec("EVAL_SPEC unset".into()))?;
        let specs = builtin_specs();
        let spec = specs
            .iter()
            .find(|s| s.name == name)
            .cloned()
            .ok_or_else(|| Refusal::Spec(format!("no experiment named {name}")))?;
        // No default: a store inside the repository would dirty the tree
        // and refuse the next run (gate 3's note).
        let out_dir = std::env::var_os("EVAL_OUT")
            .map(PathBuf::from)
            .ok_or_else(|| Refusal::Spec("EVAL_OUT unset".into()))?;
        Ok(Driver {
            spec,
            specs,
            out_dir,
            sample_period: Duration::from_millis(100),
            probes: Probes::real(),
            allow_mixed: std::env::var("EVAL_ALLOW_MIXED")
                .map(|v| v == "1")
                .unwrap_or(false),
            only: std::env::var("EVAL_ONLY").ok(),
        })
    }

    pub(super) fn store_path(&self) -> PathBuf {
        let name = if profile_name() == "release" {
            "rows.csv"
        } else {
            "rows-test.csv"
        };
        self.out_dir.join(name)
    }

    /// Rows in series order: ascending size within a scope (H5 rule (2)),
    /// then by fixture, label, rep.
    fn ordered_rows(&self) -> Vec<RowSpec> {
        let mut rows = self.spec.rows.clone();
        rows.sort_by(|a, b| {
            let sa = a.series.as_ref().map(|s| (s.scope.clone(), s.size));
            let sb = b.series.as_ref().map(|s| (s.scope.clone(), s.size));
            sa.cmp(&sb)
                .then_with(|| a.fixture.cmp(&b.fixture))
                .then_with(|| a.config.label().cmp(&b.config.label()))
                .then_with(|| a.rep.cmp(&b.rep))
        });
        rows
    }

    pub(super) fn run(&self) -> Result<Summary, Refusal> {
        // `P5-CAMPAIGN` C1/C6: the contract's keys are never run by the driver,
        // and a spec built on an unfrozen list is refused.
        if self
            .spec
            .rows
            .iter()
            .any(|r| r.run_kind == RunKind::Contract)
        {
            return Err(Refusal::Spec(format!(
                "{} holds contract rows, which the driver never runs",
                self.spec.name
            )));
        }
        if let Some(what) = unfrozen_list_of(&self.spec.name, self.only.is_some()) {
            return Err(Refusal::Spec(format!(
                "{} is not runnable: the {what} list is not frozen",
                self.spec.name
            )));
        }
        // Under one extension step only the corner pass may run: every key the
        // filter selects must be a corner's (round 03 m1) — a rule of the seven
        // campaign specs, never of X0 or a test spec (gate 3 T10).
        if CAMPAIGN_SPECS.contains(&self.spec.name.as_str()) && frozen().extension.len() < 2 {
            let corners: BTreeSet<&str> = APPS_CORNERS.iter().map(|(f, _)| *f).collect();
            if let Some(only) = &self.only {
                let outside = self
                    .spec
                    .rows
                    .iter()
                    .filter(|r| glob_match(only, &r.key(profile_name())))
                    .find(|r| !corners.contains(r.fixture.as_str()));
                if let Some(r) = outside {
                    return Err(Refusal::Spec(format!(
                        "{} is not runnable beyond the corners with one extension step: {}",
                        self.spec.name, r.fixture
                    )));
                }
            }
        }
        // The lists rows ran under may only grow (round 02 M1, round 03 M1): the
        // record is checked and then written **before the first row runs**, so an
        // interrupted run leaves no unrecorded row; only the lists this spec
        // consumes enter it.
        let used_path = FrozenLists::used_path(&self.out_dir);
        let prev = if used_path.exists() {
            let text = fs::read_to_string(&used_path).map_err(|e| Refusal::Io(e.to_string()))?;
            FrozenLists::parse(&text)?
        } else {
            FrozenLists::default()
        };
        let now = frozen().consumed_by(&self.spec.name);
        if let Err(why) = frozen().extends(&prev) {
            return Err(Refusal::Spec(format!(
                "the frozen lists changed under rows already run: {why} (see {})",
                used_path.display()
            )));
        }
        let merged = FrozenLists::merged(&prev, &now);
        if merged != FrozenLists::default() && merged != prev {
            // Atomic: a temporary file renamed into place (round 04 n1).
            fs::create_dir_all(&self.out_dir).map_err(|e| Refusal::Io(e.to_string()))?;
            let tmp = used_path.with_extension("json.tmp");
            fs::write(&tmp, merged.to_json().to_string())
                .map_err(|e| Refusal::Io(e.to_string()))?;
            fs::rename(&tmp, &used_path).map_err(|e| Refusal::Io(e.to_string()))?;
        }
        let (commit, dirty) = (self.probes.git)();
        let commit = if dirty {
            format!("{commit}+dirty")
        } else {
            commit
        };
        if dirty && !self.allow_mixed {
            return Err(Refusal::Dirty(commit));
        }
        let host = (self.probes.host)();
        let profile = profile_name();
        let path = self.store_path();
        let mut store = Store::open(&path, &host, &commit, self.allow_mixed)?;
        fs::create_dir_all(self.out_dir.join("runs")).map_err(|e| Refusal::Io(e.to_string()))?;
        let mut summary = Summary {
            store: path.clone(),
            ..Summary::default()
        };
        // H4 (gate 3 T6): a timed row never runs instrumented.
        if let Some(bad) = self
            .spec
            .rows
            .iter()
            .find(|r| r.run_kind == RunKind::Timed && r.config.instrumented)
        {
            return Err(Refusal::Spec(format!(
                "timed row instrumented: {}",
                bad.key(profile)
            )));
        }
        // H5 rules (1)–(2): censored repetition sets and censored series scopes,
        // **rebuilt from the store on resumption** (gate 3 T3).
        let mut censored_reps: BTreeSet<String> = BTreeSet::new();
        let mut censored_scopes: BTreeMap<String, i64> = BTreeMap::new();
        for spec in &self.spec.rows {
            let key = spec.key(profile);
            if store
                .end_class_of(&key)
                .is_some_and(|c| c.starts_with("capped_"))
            {
                censored_reps.insert(spec.rep_set());
                if let Some(series) = &spec.series {
                    let e = censored_scopes
                        .entry(series.scope.clone())
                        .or_insert(series.size);
                    if series.size < *e {
                        *e = series.size;
                    }
                }
            }
        }
        if let Some(only) = &self.only {
            if !self
                .spec
                .rows
                .iter()
                .any(|r| glob_match(only, &r.key(profile)))
            {
                return Err(Refusal::Spec(format!(
                    "EVAL_ONLY={only} selects no key of {}",
                    self.spec.name
                )));
            }
        }
        for spec in self.ordered_rows() {
            let key = spec.key(profile);
            if let Some(only) = &self.only {
                if !glob_match(only, &key) {
                    continue;
                }
            }
            if store.has(&key) {
                summary.skipped_present += 1;
                continue;
            }
            let fixture = fixture_by_name(&spec.fixture)?;
            let comm_model = format!("{:?}", cons_to_model(fixture.config.cons_type));
            let mut meta = RowMeta::of(&spec, profile, &commit, &comm_model);
            if censored_reps.contains(&spec.rep_set()) {
                meta.end_class = "skipped_rep".to_owned();
                let end = GridEnd::Capped {
                    fixture: spec.fixture.clone(),
                    config: spec.config.clone(),
                    after: Duration::ZERO,
                };
                store.append(&skipped_row(&end, &meta))?;
                summary.skipped_rep += 1;
                continue;
            }
            if let Some(series) = &spec.series {
                if censored_scopes
                    .get(&series.scope)
                    .is_some_and(|n| series.size > *n)
                {
                    meta.end_class = "skipped_after_censor".to_owned();
                    let end = GridEnd::Capped {
                        fixture: spec.fixture.clone(),
                        config: spec.config.clone(),
                        after: Duration::ZERO,
                    };
                    store.append(&skipped_row(&end, &meta))?;
                    summary.skipped_after_censor += 1;
                    continue;
                }
            }
            let out = self.spawn_child(&spec, &key, &commit)?;
            let row = self.classify(&spec, &mut meta, &out);
            if meta.censored {
                summary.censored += 1;
                censored_reps.insert(spec.rep_set());
                if let Some(series) = &spec.series {
                    let e = censored_scopes
                        .entry(series.scope.clone())
                        .or_insert(series.size);
                    if series.size < *e {
                        *e = series.size;
                    }
                }
            }
            store.append(&row)?;
            summary.ran += 1;
        }
        Ok(summary)
    }

    fn spawn_child(
        &self,
        spec: &RowSpec,
        key: &str,
        commit: &str,
    ) -> Result<ChildOutcome, Refusal> {
        let exe = std::env::current_exe().map_err(|e| Refusal::Io(e.to_string()))?;
        let run_dir = self.out_dir.join("runs").join(key_hash(key));
        fs::create_dir_all(&run_dir).map_err(|e| Refusal::Io(e.to_string()))?;
        let stdout =
            fs::File::create(run_dir.join("stdout")).map_err(|e| Refusal::Io(e.to_string()))?;
        let stderr =
            fs::File::create(run_dir.join("stderr")).map_err(|e| Refusal::Io(e.to_string()))?;
        let started = Instant::now();
        let mut child = Command::new(exe)
            .args([
                "--ignored",
                "--exact",
                "conformance::eval::eval_row",
                "--nocapture",
                "--test-threads=1",
            ])
            .env("EVAL_ROW", row_json(spec))
            .env("EVAL_REP", spec.rep.to_string())
            .env("EVAL_COMMIT", commit)
            .env("EVAL_RUN_DIR", &run_dir)
            .env("EVAL_EXPORT", exports_of(&self.spec.name).unwrap_or(""))
            .stdin(Stdio::null())
            .stdout(Stdio::from(stdout))
            .stderr(Stdio::from(stderr))
            .spawn()
            .map_err(|e| Refusal::Io(e.to_string()))?;
        let pid = child.id();
        let mut sampled: Option<u64> = None;
        let mut killed: Option<&'static str> = None;
        // The exit is polled finely (so `proc_wall_ms` is not quantised to
        // the sampling period); `VmHWM` is sampled once per period. A zero
        // reading (the process before its exec) is not a sample.
        let poll = Duration::from_millis(1).min(self.sample_period);
        let mut last_sample: Option<Instant> = None;
        let status = loop {
            if let Some(st) = child.try_wait().map_err(|e| Refusal::Io(e.to_string()))? {
                break Some(st);
            }
            let due = last_sample.is_none_or(|t| t.elapsed() >= self.sample_period);
            if due {
                last_sample = Some(Instant::now());
                if let Some(hwm) = vm_hwm_of(pid).filter(|h| *h > 0) {
                    sampled = Some(sampled.map_or(hwm, |s| s.max(hwm)));
                    if hwm > spec.tier.mem_kb {
                        killed = Some("memory");
                    }
                }
            }
            if started.elapsed() >= spec.tier.wall {
                killed = Some("wall");
            }
            if killed.is_some() {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            std::thread::sleep(poll);
        };
        let elapsed = started.elapsed();
        let text = fs::read_to_string(run_dir.join("stdout")).unwrap_or_default();
        // Gate 3 T2: libtest prints `test … ... ` with no newline before the
        // child's own output, so the sentinel is found anywhere, not at a
        // line start; the record runs to the end of its line.
        let sentinel = text
            .find(SENTINEL)
            .map(|i| text[i + SENTINEL.len()..].lines().next().unwrap_or(""))
            .and_then(parse_csv_line)
            .filter(|c| c.len() == header().len());
        Ok(ChildOutcome {
            status,
            killed,
            elapsed,
            sampled_hwm_kb: sampled,
            sentinel,
            pid,
        })
    }

    /// H3: the row from the child's record (`ok`/`panicked`), or a capped or
    /// crashed row built here; the post-hoc memory rule.
    fn classify(&self, spec: &RowSpec, meta: &mut RowMeta, out: &ChildOutcome) -> Row {
        meta.pid = out.pid.to_string();
        meta.run_dir = format!("runs/{}", key_hash(&spec.key(profile_name())));
        meta.rss_sampled_hwm_kb = out
            .sampled_hwm_kb
            .map(|v| v.to_string())
            .unwrap_or_default();
        let hdr = header();
        let idx = |name: &str| {
            hdr.iter()
                .position(|c| *c == name)
                .expect("conformance: a declared column")
        };
        match (out.killed, &out.sentinel) {
            (Some(reason), _) => {
                meta.censored = true;
                meta.censor_via = "kill".to_owned();
                meta.end_class = if reason == "wall" {
                    meta.proc_wall_ms = spec.tier.wall.as_millis().to_string();
                    "capped_wall".to_owned()
                } else {
                    meta.proc_wall_ms = out.elapsed.as_millis().to_string();
                    "capped_memory".to_owned()
                };
                let end = GridEnd::Capped {
                    fixture: spec.fixture.clone(),
                    config: spec.config.clone(),
                    after: out.elapsed,
                };
                eval_row_of(&end, meta)
            }
            (None, Some(cells)) => {
                // The child's record, with the driver's columns filled in.
                let mut row: Row = hdr.iter().copied().zip(cells.iter().cloned()).collect();
                let set = |row: &mut Row, k: &str, v: String| {
                    if let Some(cell) = row.iter_mut().find(|(c, _)| *c == k) {
                        cell.1 = v;
                    }
                };
                meta.proc_wall_ms = out.elapsed.as_millis().to_string();
                let child_hwm: Option<u64> = cells[idx("rss_child_hwm_kb")].parse().ok();
                if cells[idx("end_class")] == "ok"
                    && child_hwm.is_some_and(|h| h > spec.tier.mem_kb)
                {
                    meta.censored = true;
                    meta.censor_via = "post_hoc".to_owned();
                    set(&mut row, "end_class", "capped_memory".to_owned());
                }
                set(&mut row, "proc_wall_ms", meta.proc_wall_ms.clone());
                set(&mut row, "pid", meta.pid.clone());
                set(&mut row, "run_dir", meta.run_dir.clone());
                set(
                    &mut row,
                    "rss_sampled_hwm_kb",
                    meta.rss_sampled_hwm_kb.clone(),
                );
                set(&mut row, "censor_via", meta.censor_via.clone());
                set(&mut row, "censored", meta.censored.to_string());
                row
            }
            (None, None) => {
                let status = out
                    .status
                    .map(|s| {
                        use std::os::unix::process::ExitStatusExt;
                        match (s.code(), s.signal()) {
                            (Some(c), _) => format!("status {c}"),
                            (None, Some(sig)) => format!("signal {sig}"),
                            _ => "unknown".to_owned(),
                        }
                    })
                    .unwrap_or_else(|| "unknown".to_owned());
                meta.end_class = format!("crashed({status})");
                meta.proc_wall_ms = out.elapsed.as_millis().to_string();
                let end = GridEnd::Panicked {
                    fixture: spec.fixture.clone(),
                    config: spec.config.clone(),
                    payload: format!("crashed: {status}"),
                };
                eval_row_of(&end, meta)
            }
        }
    }
}

/// H2's `EVAL_ONLY` glob (gate 3 T7): `*` matches any run of characters,
/// everything else literally.
pub(super) fn glob_match(pattern: &str, s: &str) -> bool {
    fn go(p: &[char], t: &[char]) -> bool {
        match p.split_first() {
            None => t.is_empty(),
            Some(('*', rest)) => (0..=t.len()).any(|i| go(rest, &t[i..])),
            Some((c, rest)) => t.first() == Some(c) && go(rest, &t[1..]),
        }
    }
    let p: Vec<char> = pattern.chars().collect();
    let t: Vec<char> = s.chars().collect();
    go(&p, &t)
}

/// `VmHWM` of another process, from `/proc/<pid>/status`.
fn vm_hwm_of(pid: u32) -> Option<u64> {
    let status = fs::read_to_string(format!("/proc/{pid}/status")).ok()?;
    let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    line.split_whitespace().nth(1)?.parse().ok()
}

/// A filesystem-safe name for a row's run directory.
fn key_hash(key: &str) -> String {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    key.hash(&mut h);
    format!("{:016x}", h.finish())
}

/// The driver entry point (H9).
#[test]
#[ignore]
fn eval_driver() {
    let driver = Driver::from_env().unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let summary = driver
        .run()
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let mut out = std::io::stdout().lock();
    writeln!(
        out,
        "eval_driver: spec {}: ran {}, present {}, skipped_rep {}, skipped_after_censor {}, \
         censored {}, store {}",
        driver.spec.name,
        summary.ran,
        summary.skipped_present,
        summary.skipped_rep,
        summary.skipped_after_censor,
        summary.censored,
        summary.store.display()
    )
    .expect("conformance: writing the driver summary");
}

// =========================================================================
// P5-CAMPAIGN — the experiments as data (lead; criteria rev 4.4 C1–C9)
// =========================================================================
//
// X1 (conforming, exhaustive, four engines × three selectors, 3 reps), X1V
// (violating exhaustive on the two sweeping engines), X2 (first-report, four
// engines, 3 reps, twin keys under X1's configuration), X2P (X2's rep-0 keys
// as profiling rows whose child exports the first report), X2S (one stateful
// `Ltr` profiling row per X2 fixture whose child exports the Spec family's
// words), X1P (the enumerator instrumented at the frozen point list), X3A
// (memo off; the budget sweep at the frozen ceilings). `contract_specs()`
// holds V for `experiments_of` only (the driver refuses contract rows). The
// four dated lists (`extension`, `x1p`, `budget_ceilings`, `x5`) are frozen
// after the pilots; a spec that needs an unfrozen list is refused by the driver.

/// One dated freeze of a list (C1; round 02 M1): the date, the pilot report
/// it was read from, and the items.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct FrozenStep {
    pub(super) date: String,
    pub(super) source: String,
    pub(super) items: Vec<String>,
}

/// The campaign's frozen lists, **data beside the store** (`EVAL_FROZEN`, else
/// `EVAL_OUT/frozen.json`; absent = every list unfrozen), never code: freezing
/// mid-campaign edits no tracked file, so the committed clean tree and the
/// store's commit check hold (round 02 M1). The task file records the file's
/// sha256 at each freeze. The extension list freezes in **two steps** (C2 as
/// amended at round 01 m2): D5's A1 points before the corner pass, the
/// synthetic promotions after the calibration pilot; a full run of a spec
/// that depends on it needs both steps, an `EVAL_ONLY`-restricted run (the
/// corner pass) one. X1P's list is frozen after X1, the budget ceilings after
/// X1 and X1V; each item is `(fixture, i)` for `B ∈ {2^0..2^i}`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct FrozenLists {
    pub(super) extension: Vec<FrozenStep>,
    pub(super) x1p: Option<FrozenStep>,
    pub(super) budget_ceilings: Option<FrozenStep>,
    /// `P5-X5` F2: the Flat arm's synthetic points, frozen after the
    /// calibration pilot and X1/X1V (every admissible point whose `A_sweep`
    /// row completed three reps at its tier).
    pub(super) x5: Option<FrozenStep>,
}

impl FrozenLists {
    /// The file's path: `EVAL_FROZEN`, else `EVAL_OUT/frozen.json`.
    pub(super) fn path() -> Option<PathBuf> {
        if let Some(p) = std::env::var_os("EVAL_FROZEN") {
            return Some(PathBuf::from(p));
        }
        std::env::var_os("EVAL_OUT").map(|d| PathBuf::from(d).join("frozen.json"))
    }

    /// Parse the file's JSON — `{"extension": [step, …], "x1p": step | null,
    /// "budget_ceilings": step | null, "x5": step | null}` (the four lists),
    /// `step = {"date", "source", "items"}` — and
    /// **refuse** anything else (round 03 m2): an unknown key, a step without a
    /// non-empty `date` and `source`, a non-string item, a ceiling item not of
    /// the form `fixture|i` with `i ≤ 20`, or more than two extension steps;
    /// every named fixture must be an admissible grid point (`validate`).
    pub(super) fn parse(text: &str) -> Result<FrozenLists, Refusal> {
        let bad = |what: String| Refusal::Spec(format!("the frozen lists are malformed: {what}"));
        let v: serde_json::Value = serde_json::from_str(text)
            .map_err(|e| Refusal::Spec(format!("the frozen lists do not parse: {e}")))?;
        let obj = v
            .as_object()
            .ok_or_else(|| bad("not an object".to_owned()))?;
        for k in obj.keys() {
            if !matches!(k.as_str(), "extension" | "x1p" | "budget_ceilings" | "x5") {
                return Err(bad(format!("unknown key `{k}`")));
            }
        }
        let step = |what: &str, x: &serde_json::Value| -> Result<Option<FrozenStep>, Refusal> {
            if x.is_null() {
                return Ok(None);
            }
            let o = x
                .as_object()
                .ok_or_else(|| bad(format!("{what}: a step is not an object")))?;
            for k in o.keys() {
                if !matches!(k.as_str(), "date" | "source" | "items") {
                    return Err(bad(format!("{what}: unknown step key `{k}`")));
                }
            }
            let text_field = |f: &str| -> Result<String, Refusal> {
                let t = o.get(f).and_then(|v| v.as_str()).unwrap_or_default();
                if t.is_empty() {
                    return Err(bad(format!("{what}: a step without a non-empty `{f}`")));
                }
                Ok(t.to_owned())
            };
            let date = text_field("date")?;
            let source = text_field("source")?;
            let arr = o
                .get("items")
                .and_then(|v| v.as_array())
                .ok_or_else(|| bad(format!("{what}: `items` is not an array")))?;
            let mut items = Vec::with_capacity(arr.len());
            for it in arr {
                let it = it
                    .as_str()
                    .ok_or_else(|| bad(format!("{what}: a non-string item")))?;
                items.push(it.to_owned());
            }
            Ok(Some(FrozenStep {
                date,
                source,
                items,
            }))
        };
        let mut extension = Vec::new();
        if let Some(ext) = obj.get("extension") {
            let arr = ext
                .as_array()
                .ok_or_else(|| bad("`extension` is not an array".to_owned()))?;
            if arr.len() > 2 {
                return Err(bad("more than two extension steps".to_owned()));
            }
            for (i, x) in arr.iter().enumerate() {
                match step(&format!("extension step {}", i + 1), x)? {
                    Some(st) => extension.push(st),
                    None => return Err(bad(format!("extension step {} is null", i + 1))),
                }
            }
        }
        let lists = FrozenLists {
            extension,
            x1p: step("X1P", obj.get("x1p").unwrap_or(&serde_json::Value::Null))?,
            budget_ceilings: step(
                "budget-ceilings",
                obj.get("budget_ceilings")
                    .unwrap_or(&serde_json::Value::Null),
            )?,
            x5: step("X5", obj.get("x5").unwrap_or(&serde_json::Value::Null))?,
        };
        if let Some(st) = &lists.budget_ceilings {
            for it in &st.items {
                let ok = it
                    .rsplit_once('|')
                    .and_then(|(_, i)| i.parse::<u32>().ok())
                    .is_some_and(|i| i <= 20);
                if !ok {
                    return Err(bad(format!(
                        "budget-ceilings: `{it}` is not `fixture|i` with i ≤ 20"
                    )));
                }
            }
        }
        lists.validate();
        Ok(lists)
    }

    /// The lists in force: the file if present, else every list unfrozen.
    pub(super) fn load() -> FrozenLists {
        match Self::path() {
            Some(p) if p.exists() => {
                let text = fs::read_to_string(&p)
                    .unwrap_or_else(|e| panic!("conformance: reading {}: {e}", p.display()));
                Self::parse(&text).unwrap_or_else(|e| panic!("conformance: {}", e.text()))
            }
            _ => FrozenLists::default(),
        }
    }

    /// Every frozen name resolves to an `in_grid` point of its list's admissible
    /// set (never dropped silently; round 03 m2): the extension list to any
    /// grid point; X1P's to C7's families (S2, S3, S5 `reset-twin`, A1 `correct`
    /// at `r = 1`); the ceilings to C8(ii)'s point set (S5 family and control,
    /// S2 `share-ctl`, A1 `correct` at `(2,1)`, `(3,1)`, `(4,1)`, `(2,2)`, `(2,3)` and
    /// the catalogue at `(2,1)`, `(3,1)`, `(2,2)`).
    fn validate(&self) {
        let grid: BTreeSet<String> = synth_grid()
            .into_iter()
            .chain(apps_grid())
            .filter(|p| p.in_grid)
            .map(|p| p.fixture)
            .collect();
        let check = |what: &str, name: &str, admissible: bool| {
            assert!(
                grid.contains(name),
                "conformance: the frozen {what} list names no grid point: {name}"
            );
            assert!(
                admissible,
                "conformance: the frozen {what} list names a point outside its admissible set: {name}"
            );
        };
        // The extension's first step is D5's three A1 points, its second the
        // synthetic promotions (C2); a corner fixture in step 2 would re-tier
        // the corner pass's rows (round 04 m1).
        const D5_A1: [&str; 3] = [
            "apps/a1/correct/spec/n5r1",
            "apps/a1/correct/spec/n6r1",
            "apps/a1/correct/spec/n2r4",
        ];
        for (i, st) in self.extension.iter().enumerate() {
            for n in &st.items {
                let ok = if i == 0 {
                    D5_A1.contains(&n.as_str())
                } else {
                    n.starts_with("synth/")
                };
                check("extension", n, ok); // the message names the list, the name the step
            }
        }
        // No list names a fixture twice (round 04 n5).
        let lists: Vec<(&str, Vec<String>)> = [
            ("extension", self.extension_items()),
            (
                "X1P",
                self.x1p.iter().flat_map(|st| st.items.clone()).collect(),
            ),
            (
                "budget-ceilings",
                self.ceilings().into_iter().map(|(f, _)| f).collect(),
            ),
            (
                "X5",
                self.x5.iter().flat_map(|st| st.items.clone()).collect(),
            ),
        ]
        .into_iter()
        .collect();
        for (what, items) in lists {
            let mut seen = BTreeSet::new();
            for n in items {
                assert!(
                    seen.insert(n.clone()),
                    "conformance: the frozen {what} list names a fixture twice: {n}"
                );
            }
        }
        if let Some(st) = &self.x1p {
            for n in &st.items {
                let ok = n.starts_with("synth/share/")
                    || n.starts_with("synth/commit/")
                    || n.starts_with("synth/reset-twin/")
                    || (n.starts_with("apps/a1/correct/spec/n") && n.ends_with("r1"));
                check("X1P", n, ok);
            }
        }
        if let Some(st) = &self.x5 {
            // `P5-X5` F2: S1's conforming twin at every k, its violating twin
            // at k ≤ 5 (X1V's rule), S2 `share` (not the control), S3, S4, S6.
            for n in &st.items {
                let naive_k = n
                    .strip_prefix("ex:naive/k")
                    .and_then(|r| r.split('/').next()?.parse::<u32>().ok());
                let ok = n.starts_with("synth/naive-self/")
                    || naive_k.is_some_and(|k| k <= 5)
                    || n.starts_with("synth/share/")
                    || n.starts_with("synth/commit/")
                    || n.starts_with("synth/chain/")
                    || n.starts_with("synth/width/");
                check("X5", n, ok);
            }
        }
        for (n, _) in self.ceilings() {
            let a1 = ["n2r1", "n3r1", "n4r1", "n2r2", "n2r3"]
                .iter()
                .any(|z| n == format!("apps/a1/correct/spec/{z}"));
            let cat = ["eager", "early-abort", "silent"].iter().any(|v| {
                ["n2r1", "n3r1", "n2r2"]
                    .iter()
                    .any(|z| n == format!("apps/a1/{v}/spec/{z}"))
            });
            let ok = n.starts_with("synth/reset/")
                || n.starts_with("synth/reset-ctl/")
                || n.starts_with("synth/share-ctl/")
                || a1
                || cat;
            check("budget-ceilings", &n, ok);
        }
    }

    /// The union of the extension steps' items.
    pub(super) fn extension_items(&self) -> Vec<String> {
        self.extension
            .iter()
            .flat_map(|s| s.items.iter().cloned())
            .collect()
    }

    /// The ceilings as `(fixture, i)`.
    pub(super) fn ceilings(&self) -> Vec<(String, u32)> {
        self.budget_ceilings
            .as_ref()
            .map(|st| {
                st.items
                    .iter()
                    .filter_map(|it| {
                        let (f, i) = it.rsplit_once('|')?;
                        Some((f.to_owned(), i.parse().ok()?))
                    })
                    .collect()
            })
            .unwrap_or_default()
    }
}

impl FrozenLists {
    /// The lists as JSON (the file's own format), for the used-record.
    pub(super) fn to_json(&self) -> serde_json::Value {
        let step = |st: &FrozenStep| serde_json::json!({ "date": st.date, "source": st.source, "items": st.items });
        serde_json::json!({
            "extension": self.extension.iter().map(step).collect::<Vec<_>>(),
            "x1p": self.x1p.as_ref().map(step),
            "budget_ceilings": self.budget_ceilings.as_ref().map(step),
            "x5": self.x5.as_ref().map(step),
        })
    }

    /// Whether `self` only **appends** to `prev` (round 02 M1(a)'s second clause,
    /// round 03 M1): every step `prev` had is present and identical; once `prev`
    /// holds **both** extension steps the extension list must be identical (a
    /// third step would re-tier keys that ran); a list `prev` had frozen is
    /// unchanged; newly frozen lists are allowed. `Err` names the first
    /// difference.
    pub(super) fn extends(&self, prev: &FrozenLists) -> Result<(), String> {
        if self.extension.len() < prev.extension.len() {
            return Err("an extension step was removed".to_owned());
        }
        if prev.extension.len() >= 2 && self.extension != prev.extension {
            return Err("the extension list changed after both steps were recorded".to_owned());
        }
        for (i, (a, b)) in prev.extension.iter().zip(&self.extension).enumerate() {
            if a != b {
                return Err(format!("extension step {} changed", i + 1));
            }
        }
        for (what, a, b) in [
            ("X1P", &prev.x1p, &self.x1p),
            (
                "budget-ceilings",
                &prev.budget_ceilings,
                &self.budget_ceilings,
            ),
            ("X5", &prev.x5, &self.x5),
        ] {
            if let Some(a) = a {
                if b.as_ref() != Some(a) {
                    return Err(format!("the {what} list changed or was removed"));
                }
            }
        }
        Ok(())
    }

    /// The lists `spec` consumes (round 03 m1): the extension list always; `x1p`
    /// for X1P; the ceilings for X3A; the X5 list for X5 and X5G. Only these
    /// enter the used-record.
    pub(super) fn consumed_by(&self, spec: &str) -> FrozenLists {
        if !CAMPAIGN_SPECS.contains(&spec) {
            return FrozenLists::default(); // X0 and test specs use no list (round 04 n1)
        }
        FrozenLists {
            extension: self.extension.clone(),
            x1p: if spec == "X1P" {
                self.x1p.clone()
            } else {
                None
            },
            budget_ceilings: if spec == "X3A" {
                self.budget_ceilings.clone()
            } else {
                None
            },
            x5: if spec == "X5" || spec == "X5G" {
                self.x5.clone()
            } else {
                None
            },
        }
    }

    /// `prev` with `now`'s consumed lists merged in (monotone).
    pub(super) fn merged(prev: &FrozenLists, now: &FrozenLists) -> FrozenLists {
        FrozenLists {
            extension: if now.extension.len() >= prev.extension.len() {
                now.extension.clone()
            } else {
                prev.extension.clone()
            },
            x1p: now.x1p.clone().or_else(|| prev.x1p.clone()),
            budget_ceilings: now
                .budget_ceilings
                .clone()
                .or_else(|| prev.budget_ceilings.clone()),
            x5: now.x5.clone().or_else(|| prev.x5.clone()),
        }
    }

    /// The driver's record of the lists its rows were run under:
    /// `EVAL_OUT/frozen.used.json`, written **before a run's first row** with
    /// the lists the spec consumes; a later run whose lists do not extend it is
    /// refused.
    pub(super) fn used_path(out_dir: &Path) -> PathBuf {
        out_dir.join("frozen.used.json")
    }
}

/// The lists in force for this process (read once).
pub(super) fn frozen() -> &'static FrozenLists {
    static LISTS: std::sync::OnceLock<FrozenLists> = std::sync::OnceLock::new();
    LISTS.get_or_init(FrozenLists::load)
}

/// Which spec needs which list; `Some(what)` when that list is unfrozen.
/// The seven campaign specs (C1) and `P5-X5`'s two; the frozen-list rules
/// apply to them alone.
const CAMPAIGN_SPECS: [&str; 9] = ["X1", "X1V", "X2", "X2P", "X2S", "X1P", "X3A", "X5", "X5G"];

fn unfrozen_list_of(spec: &str, restricted: bool) -> Option<&'static str> {
    let f = frozen();
    let steps = f.extension.len();
    // a full run needs both extension steps; an `EVAL_ONLY` run (the corner
    // pass) the first (round 02 M1).
    let ext_short = if restricted { steps < 1 } else { steps < 2 };
    match spec {
        "X1" | "X1V" | "X2" | "X2P" | "X2S" | "X1P" | "X3A" | "X5" | "X5G" if ext_short => {
            Some("extension")
        }
        "X1P" if f.x1p.is_none() => Some("X1P"),
        "X3A" if f.budget_ceilings.is_none() => Some("budget ceilings"),
        "X5" | "X5G" if f.x5.is_none() => Some("X5"),
        _ => None,
    }
}

/// What the child exports for a spec (C4): `first_report` for X2P,
/// `spec_words` for X2S.
pub(super) fn exports_of(spec: &str) -> Option<&'static str> {
    match spec {
        "X2P" => Some("first_report"),
        "X2S" => Some("spec_words"),
        _ => None,
    }
}

/// H5's extension tier: 3600 s and 4 GiB.
pub(super) fn extension_tier() -> Tier {
    Tier {
        name: "extension".to_owned(),
        wall: Duration::from_secs(3600),
        mem_kb: 4 * 1024 * 1024,
    }
}

fn tier_for(fixture: &str) -> Tier {
    if frozen().extension_items().iter().any(|f| f == fixture) {
        extension_tier()
    } else {
        Tier::default_tier()
    }
}

/// X1's configuration (C2): the enumerator memo on + unlimited (D11).
pub(super) fn x1_config(engine: GridEngine, selector: Selector) -> GridConfig {
    let c = GridConfig::new(engine).selector(selector);
    if engine == GridEngine::Enumerator {
        c.memo(true).budget(Budget::Unlimited)
    } else {
        c
    }
}

/// X2's configuration (C4): `stop = true`, gated first-failure.
pub(super) fn x2_config(engine: GridEngine, selector: Selector) -> GridConfig {
    let c = x1_config(engine, selector).stop(true);
    if engine == GridEngine::Gated {
        c.gated(GatedMode::FirstFailure, GatePolicy::Always)
    } else {
        c
    }
}

const CAMPAIGN_ENGINES: [GridEngine; 4] = [
    GridEngine::Enumerator,
    GridEngine::Stateful,
    GridEngine::CompleteFirst,
    GridEngine::Gated,
];
const SWEEPING_ENGINES: [GridEngine; 2] = [GridEngine::CompleteFirst, GridEngine::Gated];
const CAMPAIGN_SELECTORS: [Selector; 3] =
    [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];

/// The conforming §6 fixtures (C5), from `P4-DIFF.tables.md`'s exhaustive
/// verdicts; the tester pins this table (criterion 5). Every other §6 fixture
/// is violating (twinless X2).
const SECTION6_CONFORMING: &[&str] = &[
    "ex:restart",
    "ex:sched",
    "ex:nogate",
    "relay/paper",
    "relay/paper/rev",
    "traces/self",
    "ndk2/conf",
    "ndk3/conf",
    "2pc/coord/conf/n2",
    "2pc/coord/conf/n3",
    "2pc/leader/conf/n2",
    "2pc/leader/conf/n3",
    "2pc/ring/conf/n2",
    "2pc/ring/conf/n3",
];

/// The corpus' side by generator mode, as Part 6 recorded it (gate 3 T2):
/// `Identity`, `InvisibleRefactor`, `DecoupleSpec` and `UnionCovered` (an
/// `Identity` pair by construction, A15) conform; `VisibleMutation`,
/// `SpecBlocks` and `DecoupleImpl` report.
fn corpus_conforms(name: &str) -> bool {
    !(name.contains("/VisibleMutation/")
        || name.contains("/SpecBlocks/")
        || name.contains("/DecoupleImpl/"))
}

/// The §6 points (C5): the paper fixtures, the measured pairs and the corpus,
/// each a one-point line; `ex:naive/k*` are S1's points and `mixed/*` is a
/// non-goal.
fn section6_points() -> Vec<SynthPoint> {
    let mut out = Vec::new();
    for f in all_fixtures() {
        let name = f.name.clone();
        let sec6 = matches!(
            f.group,
            Group::Paper | Group::Regression | Group::Ndk | Group::TwoPc | Group::Corpus
        );
        // `ex:naive/k*` are S1's points; `mixed/*` a non-goal; `eval/*` the
        // harness's test-only fixtures (gate 3 T8).
        if !sec6
            || name.starts_with("ex:naive/k")
            || name.starts_with("mixed/")
            || name.starts_with("eval/")
        {
            continue;
        }
        let conforming = SECTION6_CONFORMING.contains(&name.as_str())
            || (name.starts_with("2pc/") && name.contains("/conf/"))
            || (name.starts_with("corpus/") && corpus_conforms(&name));
        let line: &'static str = Box::leak(format!("sec6/{name}").into_boxed_str());
        out.push(SynthPoint {
            fixture: name,
            family: "sec6",
            knobs: String::new(),
            k: [None; 4],
            variant: if conforming {
                "conforming"
            } else {
                "violating"
            },
            twin: None,
            line,
            size: 1,
            in_grid: true,
        });
    }
    out
}

/// A point's side: `conforming`, or a still-conforming control — every
/// control but S5's `reset-ctl`, which violates by construction (`P5-SYNTH`;
/// gate 3 T1).
fn is_conforming(p: &SynthPoint) -> bool {
    p.variant == "conforming"
        || (p.variant.starts_with("control:") && p.variant != "control:reset-ctl")
}

/// The twin fixture of an X2 point (C4's table): the point's own `twin`, or
/// `reset-twin` for `reset-ctl` (whose grid point carries none — gate 3 T1).
fn twin_of(p: &SynthPoint) -> Option<String> {
    match &p.twin {
        Some(t) => Some(t.clone()),
        None => p
            .fixture
            .strip_prefix("synth/reset-ctl/")
            .map(|rest| format!("synth/reset-twin/{rest}")),
    }
}

fn conforming_points() -> Vec<SynthPoint> {
    synth_grid()
        .into_iter()
        .filter(|p| p.in_grid && is_conforming(p))
        .chain(apps_grid().into_iter().filter(is_conforming))
        .chain(section6_points().into_iter().filter(is_conforming))
        .collect()
}

fn x2_points() -> Vec<SynthPoint> {
    synth_grid()
        .into_iter()
        .filter(|p| p.in_grid && !is_conforming(p))
        .chain(apps_grid().into_iter().filter(|p| !is_conforming(p)))
        .chain(section6_points().into_iter().filter(|p| !is_conforming(p)))
        .collect()
}

/// X1V's points (C8): S5 family and control, `ex:naive/k{k}` for `k ≤ 5`,
/// A1's catalogue.
fn x1v_points() -> Vec<SynthPoint> {
    synth_grid()
        .into_iter()
        .filter(|p| {
            p.in_grid
                && !is_conforming(p)
                && (p.family == "reset" || (p.family == "naive" && p.size <= 5))
        })
        .chain(
            apps_grid()
                .into_iter()
                .filter(|p| p.family == "a1" && p.variant.starts_with("mutant:")),
        )
        .collect()
}

/// An X2 row's twin key under X1's configuration (C4): the same engine,
/// selector, run kind and rep, `stop = false`, gated exhaustive/`Always`, the
/// tier X1 assigns to the twin point.
fn x1_twin_key(p: &SynthPoint, engine: GridEngine, selector: Selector, rep: u32) -> String {
    match twin_of(p) {
        Some(t) => key_of(
            &t,
            &x1_config(engine, selector).label(),
            rep,
            &tier_for(&t).name,
            RunKind::Timed,
            profile_name(),
        ),
        None => String::new(),
    }
}

fn timed_rows(
    points: &[SynthPoint],
    engines: &[GridEngine],
    config: fn(GridEngine, Selector) -> GridConfig,
) -> Vec<RowSpec> {
    let mut rows = Vec::new();
    for p in points {
        let tier = tier_for(&p.fixture);
        for &e in engines {
            for s in CAMPAIGN_SELECTORS {
                for rep in 0..3 {
                    let mut r = p.row_spec(&config(e, s), &tier, RunKind::Timed, rep);
                    r.twin_key.clear(); // twins are X2's (C4); nothing else pairs
                    rows.push(r);
                }
            }
        }
    }
    rows
}

pub(super) fn x1_spec() -> Spec {
    Spec {
        name: "X1".to_owned(),
        rows: timed_rows(&conforming_points(), &CAMPAIGN_ENGINES, x1_config),
    }
}

pub(super) fn x1v_spec() -> Spec {
    Spec {
        name: "X1V".to_owned(),
        rows: timed_rows(&x1v_points(), &SWEEPING_ENGINES, x1_config),
    }
}

pub(super) fn x2_spec() -> Spec {
    let points = x2_points();
    let mut rows = Vec::new();
    for p in &points {
        let tier = tier_for(&p.fixture);
        for e in CAMPAIGN_ENGINES {
            for s in CAMPAIGN_SELECTORS {
                for rep in 0..3 {
                    let mut r = p.row_spec(&x2_config(e, s), &tier, RunKind::Timed, rep);
                    r.twin_key = x1_twin_key(p, e, s, rep);
                    rows.push(r);
                }
            }
        }
    }
    Spec {
        name: "X2".to_owned(),
        rows,
    }
}

/// X2P (C4): X2's rep-0 keys as profiling rows, the same label; the child
/// exports the first report.
pub(super) fn x2p_spec() -> Spec {
    let rows = x2_spec()
        .rows
        .into_iter()
        .filter(|r| r.rep == 0)
        .map(|mut r| {
            r.run_kind = RunKind::Profiling;
            r
        })
        .collect();
    Spec {
        name: "X2P".to_owned(),
        rows,
    }
}

/// X2S (C4): one stateful `Ltr` profiling row per X2 fixture (the mutant's
/// own Spec); the child exports the Spec family's words.
/// Fixtures with **no completed stateful record** in Part 6's tables (round
/// 02 m2: `2pc/leader/split/n4`'s cap was the enumerator's and its stateful run
/// is unrecorded; `ndk3/bad_*` has no stateful record): no X2S row until the
/// task file measures them; their growing reports stay "unclassified" (C4).
/// `2pc/coord/eager/n4` (84 ms) and `2pc/ring/split/n4` (61 ms) are recorded
/// and stay in.
fn x2s_excluded(fixture: &str) -> bool {
    fixture == "2pc/leader/split/n4" || fixture.starts_with("ndk3/bad_")
}

/// X2S (C4): one stateful `Ltr` profiling row per X2 fixture (the mutant's
/// own Spec) inside reach; the child exports the Spec family's words. The row
/// explores and keeps the mutant's whole Impl family too (the stateful route
/// keeps both sides under `keep_graphs`): the task file estimates that cost
/// per point from the pilots (round 01 m1).
pub(super) fn x2s_spec() -> Spec {
    let rows = x2_points()
        .iter()
        .filter(|p| !x2s_excluded(&p.fixture))
        .map(|p| {
            let mut r = p.row_spec(
                &x1_config(GridEngine::Stateful, Selector::Ltr),
                &tier_for(&p.fixture),
                RunKind::Profiling,
                0,
            );
            r.twin_key.clear();
            r
        })
        .collect();
    Spec {
        name: "X2S".to_owned(),
        rows,
    }
}

/// The grid point of a frozen name; a name no grid holds is a defect of the
/// frozen list, never dropped silently (round 01 m3).
fn grid_point(name: &str) -> SynthPoint {
    synth_grid()
        .into_iter()
        .chain(apps_grid())
        .filter(|p| p.in_grid)
        .find(|p| p.fixture == name)
        .unwrap_or_else(|| panic!("conformance: a frozen list names no grid point: {name}"))
}

/// X1P (C7): the enumerator instrumented, memo on + unlimited, `Ltr`, one
/// rep, at the frozen points (empty until frozen; the driver refuses).
pub(super) fn x1p_spec() -> Spec {
    let rows = frozen()
        .x1p
        .iter()
        .flat_map(|st| st.items.iter())
        .map(|name| grid_point(name))
        .map(|p| {
            let mut r = p.row_spec(
                &x1_config(GridEngine::Enumerator, Selector::Ltr).instrumented(true),
                &tier_for(&p.fixture),
                RunKind::Profiling,
                0,
            );
            r.twin_key.clear();
            r
        })
        .collect();
    Spec {
        name: "X1P".to_owned(),
        rows,
    }
}

/// X3A (C8): (i) the enumerator memo off on X1's points (`Ltr`; every
/// selector on S1 and A1); (ii) the gated budget sweep at the frozen
/// ceilings plus `Never`, exhaustive, `Ltr`. The memo-on and `Always` arms are
/// X1's/X1V's rows by key.
pub(super) fn x3a_spec() -> Spec {
    let mut rows = Vec::new();
    for p in &conforming_points() {
        let tier = tier_for(&p.fixture);
        let sels: &[Selector] = if p.family == "naive" || p.family == "a1" {
            &CAMPAIGN_SELECTORS
        } else {
            &CAMPAIGN_SELECTORS[..1]
        };
        for &s in sels {
            for rep in 0..3 {
                // the memo-on arm is X1's row (the same key, run once — C1);
                let mut on = p.row_spec(
                    &x1_config(GridEngine::Enumerator, s),
                    &tier,
                    RunKind::Timed,
                    rep,
                );
                on.twin_key.clear();
                rows.push(on);
                let c = x1_config(GridEngine::Enumerator, s).memo(false);
                let mut off = p.row_spec(&c, &tier, RunKind::Timed, rep);
                off.twin_key.clear();
                rows.push(off);
            }
        }
    }
    for (name, i) in frozen().ceilings() {
        let p = grid_point(&name);
        let tier = tier_for(&name);
        let mut policies: Vec<GatePolicy> =
            (0..=i).map(|e| GatePolicy::Budget(1usize << e)).collect();
        policies.push(GatePolicy::Never);
        // the `Always` arm is X1's/X1V's row (the same key — C8(ii)).
        policies.push(GatePolicy::Always);
        for pol in policies {
            for rep in 0..3 {
                let c =
                    x1_config(GridEngine::Gated, Selector::Ltr).gated(GatedMode::Exhaustive, pol);
                let mut r = p.row_spec(&c, &tier, RunKind::Timed, rep);
                r.twin_key.clear();
                rows.push(r);
            }
        }
    }
    Spec {
        name: "X3A".to_owned(),
        rows,
    }
}

/// The campaign's specs (C1), in the run order of C9.
pub(super) fn campaign_specs() -> Vec<Spec> {
    vec![
        x1_spec(),
        x1v_spec(),
        x2_spec(),
        x2p_spec(),
        x2s_spec(),
        x1p_spec(),
        x3a_spec(),
        x5_spec(),
        x5g_spec(),
    ]
}

/// The tractable validation suite's fixtures (C6): Part 6's registry
/// (`registry(2..=4, 3, 10)`, `P4-FLAT`'s and `P4-DIFF`'s domain), `P5-APPS`
/// criterion 4's pilot sizes and `P5-SYNTH` criterion 4's smallest sizes.
pub(super) fn contract_fixtures() -> Vec<String> {
    let mut names: Vec<String> = registry(2..=4, 3, 10)
        .iter()
        .map(|f| f.name.clone())
        .collect();
    // P5-APPS criterion 4 (the lists of "Pilot sizes").
    let a1 = ["n2r1", "n3r1", "n4r1", "n2r2", "n2r3"];
    for v in [
        "correct",
        "control-reverse",
        "eager",
        "early-abort",
        "silent",
    ] {
        names.extend(a1.iter().map(|s| format!("apps/a1/{v}/spec/{s}")));
    }
    let five = ["k1q1", "k2q1", "k3q1", "k1q2", "k1q3"];
    for v in [
        "pb",
        "pb-br",
        "silent-put",
        "control-early-ack-primary",
        "control-early-ack-fwd",
    ] {
        names.extend(five.iter().map(|s| format!("apps/a2/{v}/spec/{s}")));
    }
    for v in ["early-ack", "stale-get"] {
        names.extend(
            ["k2q1", "k3q1", "k2q2", "k2q3", "k1q2"]
                .iter()
                .map(|s| format!("apps/a2/{v}/spec/{s}")),
        );
    }
    names.extend(five.iter().map(|s| format!("apps/a2/sh/spec/{s}s1")));
    names.extend(
        ["k1q1s2", "k2q1s2", "k3q1s2", "k1q3s2"]
            .iter()
            .map(|s| format!("apps/a2/sh/spec/{s}")),
    );
    names.extend(
        ["k1q2s2", "k2q2s2", "k3q2s2", "k1q3s2"]
            .iter()
            .map(|s| format!("apps/a2/misroute/spec/{s}")),
    );
    for v in [
        "fifo",
        "double-grant",
        "never-grant",
        "wrong-round",
        "control-lifo",
    ] {
        names.extend(
            ["k2q1", "k3q1", "k2q2"]
                .iter()
                .map(|s| format!("apps/a3/{v}/spec/{s}")),
        );
    }
    let seven = [
        "k1q1m1", "k2q1m1", "k3q1m1", "k1q2m1", "k1q1m2", "k1q1m3", "k2q1m2",
    ];
    for (imp, spec) in [("hash", "a4a"), ("hash", "a4b"), ("rr", "a4b")] {
        names.extend(seven.iter().map(|s| format!("apps/a4/{imp}/{spec}/{s}")));
    }
    names.extend(
        ["k1q2m2", "k2q2m2", "k3q2m2", "k1q2m3"]
            .iter()
            .map(|s| format!("apps/a4/rr/a4a/{s}")),
    );
    names.extend(seven.iter().map(|s| format!("apps/a4/drop/a4b/{s}")));
    for (imp, spec) in [
        ("pair-swap-hash", "a4a"),
        ("pair-swap-hash", "a4b"),
        ("pair-swap-rr", "a4b"),
    ] {
        names.extend(
            ["k2q1m1", "k2q2m1", "k2q1m2", "k2q1m3"]
                .iter()
                .map(|s| format!("apps/a4/{imp}/{spec}/{s}")),
        );
    }
    // P5-SYNTH criterion 4 (the smallest sizes).
    for enc in [1, 2] {
        for k in [2, 3, 4] {
            names.push(format!("synth/naive-self/k{k}enc{enc}"));
        }
    }
    for m in [2usize, 4] {
        for c in [0, m / 2, m] {
            names.push(format!("synth/share/m{m}c{c}"));
            names.push(format!("synth/share-ctl/m{m}c{c}"));
        }
    }
    for n in [2usize, 4] {
        for j in [0, n / 2, n] {
            names.push(format!("synth/commit/n{n}j{j}"));
        }
    }
    for d in [2, 8, 32] {
        names.push(format!("synth/chain/d{d}"));
    }
    for (k, s) in [(1, 1), (2, 1), (3, 1), (1, 2), (2, 3)] {
        for v in ["reset", "reset-ctl", "reset-twin"] {
            names.push(format!("synth/{v}/k{k}s{s}"));
        }
    }
    for w in [2, 8, 32] {
        names.push(format!("synth/width/w{w}"));
    }
    names.sort();
    names.dedup();
    names
}

/// V (C6): the contract's **declared domain** — Part 6's benchmark set and the
/// two pilots' lists, every engine, every selector — for `experiments_of` only;
/// never run. It is not the reach set (reach is per (fixture, engine), decided
/// from the records at read time).
pub(super) fn contract_specs() -> Vec<Spec> {
    let mut rows = Vec::new();
    for name in contract_fixtures() {
        for e in CAMPAIGN_ENGINES {
            for s in CAMPAIGN_SELECTORS {
                rows.push(RowSpec {
                    fixture: name.clone(),
                    config: x1_config(e, s),
                    rep: 0,
                    tier: Tier::default_tier(),
                    run_kind: RunKind::Contract,
                    family: "contract".to_owned(),
                    knobs: String::new(),
                    k: [None; 4],
                    variant: String::new(),
                    twin_key: String::new(),
                    series: None,
                });
            }
        }
    }
    vec![Spec {
        name: "V".to_owned(),
        rows,
    }]
}

// ---- the child's exports (C4) --------------------------------------------

/// `complete`: a complete-graph report (statuses defined); else a growing one,
/// whose status vector is undefined and written `null` (round 01 M1). The
/// canonical key is the value-erased `CanonKey` (round 01 M2), the form the
/// instrumented enumerator's `report_keys` carry.
fn graph_words_json(
    g: &crate::exec_graph::ExecutionGraph,
    visible: &[String],
    complete: bool,
    with_cause: bool,
) -> serde_json::Value {
    use crate::conformance::morphism::{statuses, CompleteExecution};
    use crate::conformance::obs::wobs;
    use crate::conformance::report::obs_text;
    let w = match wobs(g, visible) {
        Ok(w) => w,
        Err(e) => {
            return serde_json::json!({
                "error": format!("{e:?}"),
                "growth": if complete { "complete" } else { "growing" },
                "cause": "unknown",
            })
        }
    };
    let words: serde_json::Map<String, serde_json::Value> = visible
        .iter()
        .map(|n| {
            let ws: Vec<String> = w.of(n).iter().map(|(_, o)| obs_text(o)).collect();
            (n.clone(), serde_json::json!(ws))
        })
        .collect();
    // `growth` decides (round 01 M1): a growing report's status vector is
    // undefined and written `null`; a complete report's must compute.
    let st = if !complete {
        serde_json::Value::Null
    } else {
        // A complete report's graph has every spawned thread stopped; anything
        // else is a contract violation of the engine's report, never `null`.
        let ce = CompleteExecution::try_finished(g)
            .expect("conformance: a complete report's graph has a running spawned thread");
        let m = statuses(ce, &w, visible)
            .unwrap_or_else(|e| panic!("conformance: no statuses for a complete report: {e:?}"));
        serde_json::Value::Object(
            m.iter()
                .map(|(k, v)| (k.clone(), serde_json::json!(format!("{v:?}"))))
                .collect(),
        )
    };
    // §6 case (3): a visible thread that failed an assertion makes the report
    // a visible-error report, genuine by construction (round 02 m1) — the
    // scan `morphism::status_of` performs, over the visible threads.
    let cause = if visible_assertion_failed(g, visible) {
        "visible-error"
    } else {
        "no-cover"
    };
    let key = super::canon::CanonicalGraph::of(g, visible)
        .map(|c| format!("{:?}", c.key()))
        .unwrap_or_default();
    serde_json::json!({
        "words": words,
        "statuses": st,
        "canonical_key": key,
        "growth": if complete { "complete" } else { "growing" },
        "cause": if with_cause { serde_json::json!(cause) } else { serde_json::Value::Null },
    })
}

/// Whether some visible thread carries an `Assert` block (§4.4's visible
/// error), scanning every index as `morphism::status_of` does.
fn visible_assertion_failed(g: &crate::exec_graph::ExecutionGraph, visible: &[String]) -> bool {
    use crate::event::Event;
    use crate::event_label::{BlockType, LabelEnum};
    visible.iter().any(|name| {
        let Ok(Some(tid)) = crate::conformance::obs::resolve_visible(g, name) else {
            return false;
        };
        let size = g.thread_size(tid) as u32;
        (0..size).any(|index| {
            matches!(
                g.label(Event::new(tid, index)),
                LabelEnum::Block(b) if matches!(b.btype(), BlockType::Assert)
            )
        })
    })
}

/// X2P: the first report's visible words, its value-erased canonical key, its
/// `growth` (complete / growing), its `cause` (no-cover / visible-error) and,
/// for a complete report, the Impl side's status vector, to
/// `first_report.json`; the enumerator's report graph (`ctx::Report.graph`)
/// is exported like the others', with its `report_keys` entries when
/// instrumented.
fn export_first_report(end: &GridEnd, visible: &[String], dir: &Path) -> Result<(), Refusal> {
    let GridEnd::Ok(r) = end else { return Ok(()) };
    let v = match &r.raw {
        GridRaw::Stateful(o) => o.reports.first().map(|(g, _)| {
            let mut j = graph_words_json(g, visible, true, true);
            j["engine"] = serde_json::json!("stateful");
            j["kind"] = serde_json::json!("complete");
            j
        }),
        GridRaw::CompleteFirst(o) => o.reports.first().map(|(g, _)| {
            let mut j = graph_words_json(g, visible, true, true);
            j["engine"] = serde_json::json!("complete-first");
            j["kind"] = serde_json::json!("complete");
            j
        }),
        GridRaw::Gated(o) => o.reports.first().map(|(g, _, site)| {
            let complete = matches!(site, super::gated::ReportSite::Completion);
            let mut j = graph_words_json(g, visible, complete, true);
            j["engine"] = serde_json::json!("gated");
            j["kind"] = serde_json::json!(format!("{site:?}"));
            j
        }),
        GridRaw::Enumerator(o) => o.reports.first().map(|rep| {
            let complete = matches!(rep.gate, Some(super::ctx::Gate::Completion));
            let mut j = graph_words_json(&rep.graph, visible, complete, true);
            j["engine"] = serde_json::json!("enumerator");
            j["kind"] = serde_json::json!(format!("{:?} at {:?}", rep.kind, rep.gate));
            j["report_keys"] = serde_json::json!(o
                .counters
                .report_keys
                .iter()
                .map(|(g, k)| format!("{g:?}: {k}"))
                .collect::<Vec<_>>());
            j
        }),
        GridRaw::Verdict(_) => None,
    };
    if let Some(v) = v {
        fs::create_dir_all(dir).map_err(|e| Refusal::Io(e.to_string()))?;
        fs::write(dir.join("first_report.json"), v.to_string())
            .map_err(|e| Refusal::Io(e.to_string()))?;
    }
    Ok(())
}

/// X2S: every kept Spec graph's visible word and status vector to
/// `spec_words.json` (the stateful route, `keep_graphs = true`).
fn export_spec_words(end: &GridEnd, visible: &[String], dir: &Path) -> Result<(), Refusal> {
    let GridEnd::Ok(r) = end else { return Ok(()) };
    let GridRaw::Stateful(o) = &r.raw else {
        return Ok(());
    };
    let graphs: Vec<serde_json::Value> = o
        .kept_spec_graphs
        .iter()
        .map(|g| graph_words_json(g, visible, true, false))
        .collect();
    fs::create_dir_all(dir).map_err(|e| Refusal::Io(e.to_string()))?;
    fs::write(
        dir.join("spec_words.json"),
        serde_json::json!({ "spec_graphs": graphs }).to_string(),
    )
    .map_err(|e| Refusal::Io(e.to_string()))?;
    Ok(())
}

// =========================================================================
// P5-X5 — FlatCover against the sweep inside the complete-first host (lead;
// criteria rev 3.1 F1–F7; gate 3 T1–T6; gate 4 round 01 B1, M1, n1, m2)
// =========================================================================
//
// (1) `verdict_counter_fill`: a `Verdict` row (the precheck route,
//     `cfirst::run`/`gated::run`) gets the sweep counters the `run_with` routes
//     push, from the outcome's counter records, and `max_paper_events` from
//     `ConfOutcome::counters()` (`cfirst::run`/`gated::run` copy the outcome's
//     `max_paper_events` into `max_paper_events_per_execution`) — header and
//     schema unchanged, `row_of` untouched.
// (2) `x5_spec`: the Flat arm (`precheck=true`, `cover=Flat`, complete-first)
//     at the frozen X5 points × three selectors × 3 reps; the violating
//     `ex:naive/k*` points at every `k` also under `stop = true` (unfrozen);
//     `FLAT_SUBSET` under `Ltr` (unfrozen). Every `A_flat` row's sweep partner
//     is `x5_partner`'s (not `twin_key`), and X5 **lists** every partner row,
//     built by the holding spec's configuration function (X1/X1V: `x1_config`;
//     X2: `x2_config`, with X2's RQ2 `twin_key`; own: X5's sweep arm), each key
//     once; `twin_key` is empty on every other X5 row.
// (3) `x5g_spec` (the predeclared optional extension X5G): the exhaustive
//     points of (2) — not the `stop = true` pairs — in the gated host
//     (`Exhaustive`/`Never`, `P4-FLAT` criterion 6(b)), both arms
//     `precheck = true`, every row X5G's own.

/// `P5-X5` F1: a `Verdict` row (the precheck route) gets `max_paper_events`
/// and the complete-first and gated counters; columns already present are
/// left alone.
fn verdict_counter_fill(end: &GridEnd, mut inner: Row) -> Row {
    let GridEnd::Ok(r) = end else { return inner };
    let GridRaw::Verdict(Ok(v)) = &r.raw else {
        return inner;
    };
    fn push(row: &mut Row, name: &'static str, val: String) {
        if !row.iter().any(|(k, _)| *k == name) {
            row.push((name, val));
        }
    }
    let o = v.outcome();
    if o.cfirst_counters().is_some() || o.gated_counters().is_some() {
        // the paper's `L` (`row_of` renders it with `Display` on the `run_with` routes)
        push(
            &mut inner,
            "max_paper_events",
            o.counters().max_paper_events_per_execution.to_string(),
        );
    }
    if let Some(c) = o.cfirst_counters() {
        push(&mut inner, "impl_graphs", c.impl_graphs.to_string());
        push(&mut inner, "cache_probes", c.cache_probes.to_string());
        push(&mut inner, "cache_hits", c.cache_hits.to_string());
        push(&mut inner, "cache_tests", c.cache_tests.to_string());
        push(&mut inner, "sweeps", c.sweeps.to_string());
        push(
            &mut inner,
            "sweeps_successful",
            c.sweeps_successful.to_string(),
        );
        push(&mut inner, "sweeps_failing", c.sweeps_failing.to_string());
        push(&mut inner, "sweeps_aborted", c.sweeps_aborted.to_string());
        push(&mut inner, "sweep_sizes", format!("{:?}", c.sweep_sizes));
        push(&mut inner, "sweep_graphs", c.sweep_graphs.to_string());
        push(
            &mut inner,
            "sweep_graphs_max",
            c.sweep_graphs_max.to_string(),
        );
        push(&mut inner, "witnesses", c.witnesses.to_string());
        push(
            &mut inner,
            "witness_duplicates",
            c.witness_duplicates.to_string(),
        );
        push(&mut inner, "counter_reports", c.reports.to_string());
        push(&mut inner, "cut_reports", c.cut_reports.to_string());
        push(
            &mut inner,
            "outer_wall_time_ms",
            c.outer_wall_time_ms.to_string(),
        );
        push(
            &mut inner,
            "sweep_wall_time_ms",
            c.sweep_wall_time_ms.to_string(),
        );
    }
    if let Some(g) = o.gated_counters() {
        push(
            &mut inner,
            "first_failure_mode",
            g.first_failure_mode.to_string(),
        );
        push(&mut inner, "counter_reports", g.reports.to_string());
        push(&mut inner, "gates", g.gates.to_string());
        push(&mut inner, "gates_inert", g.gates_inert.to_string());
        push(
            &mut inner,
            "gates_skipped_replay",
            g.gates_skipped_replay.to_string(),
        );
        push(
            &mut inner,
            "gates_skipped_certified",
            g.gates_skipped_certified.to_string(),
        );
        push(&mut inner, "gates_declined", g.gates_declined.to_string());
        push(
            &mut inner,
            "c1_tests_carried",
            g.c1_tests_carried.to_string(),
        );
        push(&mut inner, "carried_hits", g.carried_hits.to_string());
        push(&mut inner, "c1_tests_cache", g.c1_tests_cache.to_string());
        push(&mut inner, "gate_cache_hits", g.gate_cache_hits.to_string());
        push(&mut inner, "c1_tests_sweep", g.c1_tests_sweep.to_string());
        push(&mut inner, "gate_sweeps", g.gate_sweeps.to_string());
        push(
            &mut inner,
            "gate_sweeps_successful",
            g.gate_sweeps_successful.to_string(),
        );
        push(
            &mut inner,
            "gate_sweeps_failing",
            g.gate_sweeps_failing.to_string(),
        );
        push(
            &mut inner,
            "gate_sweeps_budgeted",
            g.gate_sweeps_budgeted.to_string(),
        );
        push(
            &mut inner,
            "gate_sweeps_aborted",
            g.gate_sweeps_aborted.to_string(),
        );
        push(
            &mut inner,
            "gate_sweep_sizes",
            format!("{:?}", g.gate_sweep_sizes),
        );
        push(
            &mut inner,
            "certificates_set",
            g.certificates_set.to_string(),
        );
        push(
            &mut inner,
            "certificate_resets",
            g.certificate_resets.to_string(),
        );
        push(&mut inner, "states_pushed", g.states_pushed.to_string());
        push(
            &mut inner,
            "certified_states_revisited",
            g.certified_states_revisited.to_string(),
        );
        push(
            &mut inner,
            "reports_certified",
            g.reports_certified.to_string(),
        );
        push(
            &mut inner,
            "reports_by_completion_test",
            g.reports_by_completion_test.to_string(),
        );
        push(
            &mut inner,
            "paper_events_at_first_report",
            format!("{:?}", g.paper_events_at_first_report), // as `row_of` renders it
        );
        push(&mut inner, "impl_graphs", g.impl_graphs.to_string());
        push(
            &mut inner,
            "completion_probes",
            g.completion_probes.to_string(),
        );
        push(
            &mut inner,
            "completion_cache_hits",
            g.completion_cache_hits.to_string(),
        );
        push(
            &mut inner,
            "completion_cache_tests",
            g.completion_cache_tests.to_string(),
        );
        push(
            &mut inner,
            "completion_sweeps",
            g.completion_sweeps.to_string(),
        );
        push(
            &mut inner,
            "completion_sweeps_successful",
            g.completion_sweeps_successful.to_string(),
        );
        push(
            &mut inner,
            "completion_sweeps_failing",
            g.completion_sweeps_failing.to_string(),
        );
        push(
            &mut inner,
            "completion_sweeps_aborted",
            g.completion_sweeps_aborted.to_string(),
        );
        push(
            &mut inner,
            "completion_sweep_sizes",
            format!("{:?}", g.completion_sweep_sizes),
        );
        push(&mut inner, "witnesses", g.witnesses.to_string());
        push(
            &mut inner,
            "witness_duplicates",
            g.witness_duplicates.to_string(),
        );
        push(
            &mut inner,
            "outer_wall_time_ms",
            g.outer_wall_time_ms.to_string(),
        );
        push(
            &mut inner,
            "sweep_wall_time_ms",
            g.sweep_wall_time_ms.to_string(),
        );
    }
    inner
}

/// The spec class holding a Flat-arm row's sweep partner (`P5-X5` F1, m2):
/// X1 (conforming points), X1V (`ex:naive/k*` exhaustive, `k ≤ 5`), X2 (the
/// `stop = true` pairs), or X5's own `A_sweep` row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PartnerClass {
    X1,
    X1V,
    X2,
    Own,
}

/// A Flat-arm row's sweep partner: the same label with `cover=Sweep` under the
/// same engine, selector, tier, run kind and rep, and the spec class that holds
/// it. In the complete-first host (X5) the partner is X1's row, `precheck =
/// false`; in the gated host (X5G) both arms carry `precheck = true` and the
/// partner is X5G's own row. Total over the `A_flat` rows of both specs.
pub(super) fn x5_partner(row: &RowSpec) -> (String, PartnerClass) {
    let mut c = row.config.clone();
    c.completion_cover = CompletionCover::Sweep;
    if c.engine == GridEngine::Gated {
        let key = key_of(
            &row.fixture,
            &c.label(),
            row.rep,
            &row.tier.name,
            row.run_kind,
            profile_name(),
        );
        return (key, PartnerClass::Own);
    }
    c.precheck = false;
    let key = key_of(
        &row.fixture,
        &c.label(),
        row.rep,
        &row.tier.name,
        row.run_kind,
        profile_name(),
    );
    let class = if row.config.stop_at_first_report {
        PartnerClass::X2
    } else if row.variant == "conforming" || row.variant.starts_with("control:") {
        PartnerClass::X1
    } else if row.fixture.starts_with("ex:naive/k") {
        PartnerClass::X1V
    } else {
        PartnerClass::Own
    };
    (key, class)
}

/// The §6 points of `FLAT_SUBSET` (F2's breadth), one-point lines, plus the
/// six `ex:naive/k{2,3,4}/enc{1,2}` names, which are S1's grid points
/// (`section6_points` excludes them; gate 3 T1). They coincide by key with
/// S1's `Ltr` rows once the X5 list holds them (`x5_rows` keeps each key once).
fn flat_points() -> Vec<SynthPoint> {
    section6_points()
        .into_iter()
        .chain(synth_grid().into_iter().filter(|p| p.in_grid))
        .filter(|p| FLAT_SUBSET.contains(&p.fixture.as_str()))
        .collect()
}

/// The X5 point set with its selectors and stop modes (F2): the frozen
/// synthetic points (three selectors, `stop = false`), the violating
/// `ex:naive/k*` points at every `k` (three selectors, `stop = true`; unfrozen),
/// `FLAT_SUBSET`'s points (`Ltr`, `stop = false`; unfrozen).
fn x5_points() -> Vec<(SynthPoint, &'static [Selector], bool)> {
    let mut out: Vec<(SynthPoint, &'static [Selector], bool)> = Vec::new();
    for n in frozen().x5.iter().flat_map(|st| st.items.iter()) {
        out.push((grid_point(n), &CAMPAIGN_SELECTORS, false));
    }
    for p in synth_grid()
        .into_iter()
        .filter(|p| p.in_grid && p.fixture.starts_with("ex:naive/k"))
    {
        out.push((p, &CAMPAIGN_SELECTORS, true));
    }
    for p in flat_points() {
        out.push((p, &CAMPAIGN_SELECTORS[..1], false));
    }
    out
}

/// The `A_flat` and `A_sweep` rows of one host over `x5_points()`, each key
/// once (criterion 1; gate 3 T2): `flat` is the host's Flat arm, `sweep` its
/// sweep arm for the partner classes the host owns (`X5G`: every row), and the
/// partners another spec holds are listed too, built by **that** spec's
/// configuration function (`x1_config` for X1/X1V, `x2_config` for X2 — gate 3
/// T5) and deduplicated by key with it at run time; `stop_pairs` says whether
/// the `stop = true` pairs are in (X5) or out (X5G; gate 4 m2). `twin_key` is X2/X2P's RQ2
/// pairing (`P5-CAMPAIGN` H7; gate 3 T4): empty on every `A_flat` row and on
/// the sweep rows except those X2 holds, which carry X2's value (T6); the
/// partner is `x5_partner`'s.
fn x5_rows(
    name: &str,
    sweep: fn(Selector, bool) -> GridConfig,
    flat: fn(Selector, bool) -> GridConfig,
    stop_pairs: bool,
) -> Spec {
    let mut rows: Vec<RowSpec> = Vec::new();
    let mut keys: BTreeSet<String> = BTreeSet::new();
    let mut push = |r: RowSpec, rows: &mut Vec<RowSpec>| {
        if keys.insert(r.key(profile_name())) {
            rows.push(r);
        }
    };
    for (p, sels, stop) in x5_points() {
        if stop && !stop_pairs {
            continue;
        }
        let tier = tier_for(&p.fixture);
        for &s in sels {
            for rep in 0..3 {
                let mut r = p.row_spec(&flat(s, stop), &tier, RunKind::Timed, rep);
                r.twin_key.clear();
                let (_, class) = x5_partner(&r);
                push(r, &mut rows);
                let config = match class {
                    PartnerClass::Own => sweep(s, stop),
                    PartnerClass::X1 | PartnerClass::X1V => x1_config(GridEngine::CompleteFirst, s),
                    PartnerClass::X2 => x2_config(GridEngine::CompleteFirst, s),
                };
                let mut sw = p.row_spec(&config, &tier, RunKind::Timed, rep);
                // The row X5 lists for X2 is X2's row, RQ2 twin key included, so
                // the store holds the same row whichever spec runs it (gate 3 T6).
                sw.twin_key = match class {
                    PartnerClass::X2 => x1_twin_key(&p, GridEngine::CompleteFirst, s, rep),
                    _ => String::new(),
                };
                push(sw, &mut rows);
            }
        }
    }
    Spec {
        name: name.to_owned(),
        rows,
    }
}

/// X5 (`P5-X5` criterion 1): the complete-first host; the sweep arm is X1's
/// configuration (`x1_config`, no precheck) and the Flat arm the same with
/// `precheck = true`, `cover = Flat`; `stop = true` on the `ex:naive` pairs.
/// The synthetic points are empty until the X5 list is frozen (the driver
/// refuses X5 until then).
pub(super) fn x5_spec() -> Spec {
    // The sweep arm is the partner's configuration function (F1 m1): X2's for
    // the `stop = true` pairs, X1's otherwise (gate 4 n1).
    fn sweep(s: Selector, stop: bool) -> GridConfig {
        if stop {
            x2_config(GridEngine::CompleteFirst, s)
        } else {
            x1_config(GridEngine::CompleteFirst, s)
        }
    }
    fn flat(s: Selector, stop: bool) -> GridConfig {
        sweep(s, stop).precheck(true).cover(CompletionCover::Flat)
    }
    x5_rows("X5", sweep, flat, true)
}

/// X5G (the predeclared optional extension; `P4-FLAT` criterion 6(b), the
/// exhaustive self-conformance pair): the gated host, `Exhaustive`/`Never`,
/// both arms `precheck = true`, every row X5G's own; the exhaustive points
/// only — the `stop = true` pairs are a cell no criterion defines
/// (`P5-CAMPAIGN` C5(vii) lists gated `Exhaustive` + stop among the cells not
/// run; gate 4 m2) and are left out. Run after X5 if D14's cap has room.
pub(super) fn x5g_spec() -> Spec {
    fn sweep(s: Selector, _stop: bool) -> GridConfig {
        x1_config(GridEngine::Gated, s)
            .gated(GatedMode::Exhaustive, GatePolicy::Never)
            .precheck(true)
    }
    fn flat(s: Selector, stop: bool) -> GridConfig {
        sweep(s, stop).cover(CompletionCover::Flat)
    }
    x5_rows("X5G", sweep, flat, false)
}
