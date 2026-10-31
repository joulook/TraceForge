//! `H` (criteria `H.md` H-0.1): the code that builds one evaluation row's
//! record, in the library, so that any program built on
//! [`crate::program`] runs a row by its `row` subcommand.
//!
//! **A copy, not a move** (ruling Q7). Every item below is copied from the
//! test-only `grid.rs` and `eval.rs` at `a3a7e1b`, each block headed by its
//! source; the originals stay unchanged behind the `fixture-tests` flag. The
//! changes against the originals are these, and no other:
//! - a row runs a [`Subject`] (the row's opaque name, the `Config`, the visible
//!   threads and the two entry points) where the originals read a `Fixture`;
//!   nothing here resolves a name, and no catalogue is copied;
//! - `stack_mib_for` reads the configuration only: a subject has no big-stack
//!   flag (no row's fixture set it, derivation §2.1);
//! - `call_with`'s `Explore` arm returns its outcome without writing the split
//!   line; [`xbase_line`] builds that line and the caller writes it, before
//!   the record, as the original did (no printing under `conformance/`, S5
//!   criterion 1);
//! - `RowSpec` has no `series` field (the driver's, not a row's);
//! - [`run_row`] is the original `child_row` and `eval_row` body on a subject,
//!   without the `EVAL_EXPORT` exporters;
//! - `pub(super)` reads `pub(crate)`.
//!
//! The record is schema 8: the same 262 cells, header, labels and tiers.

use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::channel::cons_to_model;
use crate::conformance::cfirst::{self, CFirstOutcome, SweepEnd};
use crate::conformance::config::{
    BucketKind, Capacity, CompletionCover, ConfConfig, Engine, GatePolicy, GatedMode, IndexKind,
};
use crate::conformance::gated::{self, GatedOutcome, ReportSite};
use crate::conformance::search::SearchOpts;
use crate::conformance::selector::{paper_events, InnerOrder, Selector};
use crate::conformance::stateful::{self, StatefulOutcome};
use crate::conformance::{
    verify, verify_conformance_with_opts, ConfBuilder, ConfError, ConfVerdict, Outcome,
    DEFAULT_SEARCH_BUDGET,
};
use crate::exec_graph::ExecutionGraph;
use crate::Config;

/// An entry point of a program, as [`crate::program::Entry`].
pub(crate) type Prog = Arc<dyn Fn() + Send + Sync>;

/// What one row runs: the row's opaque name (copied into the record and its
/// key, never resolved), the program's `Config` (model, seed, thread
/// threshold), its visible threads and its two entry points, built from the
/// program's arguments.
#[derive(Clone)]
pub(crate) struct Subject {
    pub(crate) name: String,
    pub(crate) config: Config,
    pub(crate) visible: Vec<String>,
    pub(crate) implementation: Prog,
    pub(crate) specification: Prog,
}

/// What [`run_row`] returns: the `Explore` split line, if the row ran
/// `Explore`, and the sentinel line with the record; both end in a newline;
/// then `B`'s measurement block (K1).
pub(crate) struct RowLines {
    pub(crate) xbase: Option<String>,
    pub(crate) record: String,
    pub(crate) measurements: crate::conformance::measure::Measurements,
}

/// The row of `EVAL_ROW`'s JSON `json` on the subject built from it: the
/// original child's path — the legacy-key refusal, the per-phase peaks for
/// `SverifyP` and `ExploreP`, the run on its own thread, the record, then the
/// process's CPU time read after the engine returned. `subject` receives the
/// row's name. An `Err` is a refusal: no record.
pub(crate) fn run_row(
    json: &str,
    commit: &str,
    subject: impl FnOnce(&str) -> Subject,
) -> Result<RowLines, String> {
    let mut spec = row_from_json(json).ok_or_else(|| "EVAL_ROW does not parse".to_owned())?;
    // `MIN-ENGINES` E1-2: before any engine, the clearer child diagnostic.
    if let Some(s) = spec.config.legacy_selector {
        return Err(format!(
            "EVAL_ROW names a legacy key (selector `{s:?}` on {:?}); the stateful and stateless \
             engines schedule by plain Must (MIN-ENGINES E1) — rerun under the `Plain` key",
            spec.config.engine
        ));
    }
    // `SVERIFY-P` I4-3 R1: the per-phase resets run in the row's process.
    if matches!(
        spec.config.engine,
        GridEngine::SverifyP | GridEngine::ExploreP
    ) {
        spec.config.phase_peaks = true;
    }
    let subject = subject(&spec.fixture);
    let comm_model = format!("{:?}", cons_to_model(subject.config.cons_type));
    let meta = RowMeta::of(&spec, profile_name(), commit, &comm_model);
    let end = run_row_in_process(&subject, &spec.config, spec.run_kind.keep_graphs());
    let mut row = eval_row_of(&end, &meta);
    // `SVERIFY-P` V-C (VC-0): the process's own CPU time, read after the
    // engine returned (a panic is caught inside the run), before the record.
    let (user, sys) = cpu_cells(cpu_ms_of_pid(std::process::id()));
    for (k, v) in row.iter_mut() {
        if *k == "cpu_user_ms" {
            *v = user.clone();
        } else if *k == "cpu_sys_ms" {
            *v = sys.clone();
        }
    }
    let measurements =
        crate::conformance::measure::of_row(&row, &end, spec.config.engine, spec.config.threads);
    Ok(RowLines {
        xbase: xbase_line(&end),
        record: format!("{SENTINEL}{}\n", csv_line(&record_of(&row))),
        measurements,
    })
}

/// `P5-XBASE` F2: the `Explore` row's split line, as `call_with`'s original
/// arm wrote it; `None` for any other row or a panicked run.
pub(crate) fn xbase_line(end: &GridEnd) -> Option<String> {
    match end {
        GridEnd::Ok(r) => match &r.raw {
            GridRaw::Explore(s) => Some(format!(
                "xbase: execs={} block={} max_graph_events={}\n",
                s.execs, s.block, s.max_graph_events
            )),
            _ => None,
        },
        _ => None,
    }
}

// --- copied from grid.rs: GridEngine .. panic_text ---
/// Which engine a configuration runs (`GridEngine` rather than
/// `config::Engine` so that the enumerator's two arms and the precheck arm are
/// explicit).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GridEngine {
    /// `verify_conformance_with_opts`, raw `Outcome` (X3).
    Enumerator,
    /// `stateful::run_with(cc, impl, spec, true)`.
    Stateful,
    /// `cfirst::run_with(.., true)`, or `cfirst::run` with `precheck`.
    CompleteFirst,
    /// `gated::run_with(.., true)`, or `gated::run` with `precheck`.
    Gated,
    /// `verify(cc, impl, spec)` as a DEMO-2PC violating table calls it
    /// (`stop_at_first_report(true)`, `triage(true)`; criterion 7).
    Verify,
    /// `P5-XBASE` F1: TraceForge's plain model checker on the implementation
    /// closure alone — `crate::verify(config, impl)`, no conformance mode, the
    /// specification never called. The ten knobs after the engine are inert.
    Explore,
    /// `SVERIFY-P` I4: SVerify-P, `sverify_p::run_with(&cc, impl, spec)`, the
    /// raw outcome; the label carries `threads=<t>` and an off-default
    /// `flush=<F>` after `index=set`.
    SverifyP,
    /// `SVERIFY-P` I4-4: the baseline — Must alone in the partitioned mode on
    /// the specification, then on the implementation, under SVerify-P's phase
    /// `Config` with the same `threads` (`explore_partitioned`); the label is
    /// the eleven-field form plus `threads=<t>`.
    ExploreP,
    /// `SVERIFY-P` P-S: CVerify-P, `cfirst_p::run_with(&cc, impl, spec)`, the
    /// raw outcome; the label is the complete-first row's `index=set` form
    /// plus `threads=<t>`.
    CFirstP,
}

/// The enumerator's search budget (X3: the default-budget arm and the
/// unlimited arm; a 2PC row's own budget).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Budget {
    Default,
    Unlimited,
    Exact(usize),
}

impl Budget {
    pub(crate) fn value(self) -> usize {
        match self {
            Budget::Default => DEFAULT_SEARCH_BUDGET,
            Budget::Unlimited => usize::MAX,
            Budget::Exact(n) => n,
        }
    }
}

/// One grid configuration (X3). Fields that an engine does not read are
/// carried unchanged into the row so a table can say what was set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GridConfig {
    pub(crate) engine: GridEngine,
    /// The selector the enumerator, precheck, triage, oracle and gated runs
    /// read; `MIN-ENGINES` E1: not read by the stateful and stateless engines,
    /// which schedule by plain Must — their key prints `Plain` in this field
    /// (`selector_field`), whatever this holds.
    pub(crate) selector: Selector,
    /// `MIN-ENGINES` E1-2: `Some(s)` only on a configuration parsed from a
    /// stored key whose second field names a selector on a plain-scheduled
    /// engine — a legacy key, kept as a stored identity (its label reprints
    /// `s`) and refused by every execution path; `None` on every
    /// configuration the driver builds.
    pub(crate) legacy_selector: Option<Selector>,
    /// `stop_at_first_report` on every engine (plan §6's "stopped at first
    /// report"; on the enumerator, the stop flag of
    /// `verify_conformance_with_opts`).
    pub(crate) stop_at_first_report: bool,
    pub(crate) gated_mode: GatedMode,
    pub(crate) gate_policy: GatePolicy,
    /// The enumerator's memo (`SearchOpts::memo`).
    pub(crate) memo: bool,
    /// The enumerator's budget; the sweeping engines take the same figure as
    /// `search_budget` (their sweeps are unbounded under Parts 4–5).
    pub(crate) budget: Budget,
    /// Complete-first and gated: `run` (precheck on) instead of `run_with`.
    pub(crate) precheck: bool,
    /// The enumerator's `SearchOpts::instrument`.
    pub(crate) instrumented: bool,
    /// Complete-first's early-error cut (plan §6 runs it off).
    pub(crate) early_error_cut: bool,
    /// `P4-FLAT`: the completion-question engine of the complete-first and
    /// gated checkers; `Flat` runs only with `precheck` and on those engines
    /// (refused by `run_grid` otherwise).
    pub(crate) completion_cover: CompletionCover,
    /// `P5-CFCFG` F1/F4: the complete-first witness cache's capacity
    /// (`w=0` | `w=<n>` | `w=inf` in the label); carried unchanged by the
    /// other engines.
    pub(crate) witness_cache: Capacity,
    /// `P5-CFCFG` F3/F4: the complete-first sweeps' quiet flag
    /// (`quiet=<bool>` in the label).
    pub(crate) quiet: bool,
    /// `MIN-ENGINES` E6: keep every report's graph, snapshot and dump (not in
    /// the label: off is the default and no campaign row turns it on).
    pub(crate) all_reports: bool,
    /// `MIN-ENGINES` E7a: the complete-first per-sweep record (not in the
    /// label: off is the default and no campaign row turns it on).
    pub(crate) sweep_record: bool,
    /// `COMPACT-INDEX` §5 (frozen §8): the index kind of the stateful and
    /// complete-first engines (`index=compact` in the label when `Compact`;
    /// the label is today's byte for byte under `Current`).
    pub(crate) index: IndexKind,
    /// `COMPACT-INDEX` §5.1 item 3 (`anti=<bool>`; printed under `Compact`).
    pub(crate) antichain: bool,
    /// `COMPACT-INDEX` §5.1 item 4(b) (`pmemo=<bool>`; printed under `Compact`).
    pub(crate) probe_memo: bool,
    /// `COMPACT-INDEX` phase 2 D6 (`distinct=on`; printed only when on and
    /// effective: the stateful engine, and the complete-first engine under
    /// `Compact` or `Set` (`MIN-ENGINES` E7b)).
    pub(crate) impl_distinct: bool,
    /// `COMPACT-INDEX` phase 2 item 7 (`bucket=inverted:<t>` or
    /// `bucket=trie`, printed under `Compact`; nothing for the scan).
    pub(crate) bucket: BucketKind,
    /// `SVERIFY-P` I4-1: the worker count of the two partitioned engines
    /// (`threads=<t>`, printed on the `SverifyP` and `ExploreP` labels only;
    /// `1` and unprinted elsewhere).
    pub(crate) threads: usize,
    /// `SVERIFY-P` I4-1: SVerify-P's flush size (`flush=<F>` on the
    /// `SverifyP` label when not 4096; `4096` and unprinted elsewhere).
    pub(crate) flush_entries: usize,
    /// `SVERIFY-P` I4-3: the per-phase `VmHWM` resets of the two partitioned
    /// engines — a measurement mode, not an identity (no label field): on in
    /// the driver's per-row children only (R1), off in every in-process run.
    pub(crate) phase_peaks: bool,
}

impl GridConfig {
    /// `engine` with every other knob at plan §6's defaults: `Ltr`,
    /// report-and-continue, `Exhaustive`/`Always`, memo off, the default
    /// budget, no precheck, uninstrumented, the cut off.
    pub(crate) fn new(engine: GridEngine) -> Self {
        Self {
            engine,
            selector: Selector::Ltr,
            legacy_selector: None,
            stop_at_first_report: false,
            gated_mode: GatedMode::Exhaustive,
            gate_policy: GatePolicy::Always,
            memo: false,
            budget: Budget::Default,
            precheck: false,
            instrumented: false,
            early_error_cut: false,
            completion_cover: CompletionCover::Sweep,
            witness_cache: Capacity::Unbounded,
            quiet: false,
            all_reports: false,
            sweep_record: false,
            // `MIN-ENGINES` E7b: `Set` for the two engines that read the index,
            // `Current` for the rest, whose keys print no index field.
            index: if matches!(
                engine,
                GridEngine::Stateful
                    | GridEngine::CompleteFirst
                    | GridEngine::SverifyP
                    | GridEngine::CFirstP
            ) {
                IndexKind::Set
            } else {
                IndexKind::Current
            },
            antichain: true,
            // `MIN-ENGINES` E7a: the probe memo off by default.
            probe_memo: false,
            impl_distinct: false,
            bucket: BucketKind::Scan,
            // `SVERIFY-P` I4-1: one worker, 4096 orders per flush, no reset.
            threads: 1,
            flush_entries: 4096,
            phase_peaks: false,
        }
    }

    /// `SVERIFY-P` I4-1: the worker count (`SverifyP` and `ExploreP`).
    pub(crate) fn threads(mut self, t: usize) -> Self {
        self.threads = t;
        self
    }

    /// `SVERIFY-P` I4-1: SVerify-P's flush size.
    pub(crate) fn flush_entries(mut self, f: usize) -> Self {
        self.flush_entries = f;
        self
    }

    /// `SVERIFY-P` I4-3: the per-phase resets (the driver's child only).
    pub(crate) fn phase_peaks(mut self, on: bool) -> Self {
        self.phase_peaks = on;
        self
    }

    /// `P5-CFCFG` F1: the complete-first witness cache's capacity.
    pub(crate) fn witness_cache(mut self, c: Capacity) -> Self {
        self.witness_cache = c;
        self
    }

    /// `COMPACT-INDEX` §5: the index kind.
    pub(crate) fn index(mut self, k: IndexKind) -> Self {
        self.index = k;
        self
    }

    /// `COMPACT-INDEX` §5.1 item 3: the antichain knob.
    pub(crate) fn antichain(mut self, b: bool) -> Self {
        self.antichain = b;
        self
    }

    /// `COMPACT-INDEX` §5.1 item 4(b): the probe memo knob.
    pub(crate) fn probe_memo(mut self, b: bool) -> Self {
        self.probe_memo = b;
        self
    }

    /// `COMPACT-INDEX` phase 2 D6: the step-0 counter's knob.
    pub(crate) fn impl_distinct(mut self, b: bool) -> Self {
        self.impl_distinct = b;
        self
    }

    /// `COMPACT-INDEX` phase 2 item 7: the slot structure.
    pub(crate) fn bucket(mut self, k: BucketKind) -> Self {
        self.bucket = k;
        self
    }

    /// `P5-CFCFG` F3: the complete-first sweeps' quiet flag.
    pub(crate) fn quiet(mut self, b: bool) -> Self {
        self.quiet = b;
        self
    }

    pub(crate) fn cover(mut self, c: CompletionCover) -> Self {
        self.completion_cover = c;
        // `MIN-ENGINES` E7b (the owner's ruling F1): a Flat row runs the
        // `Current` witness cache, set explicitly here.
        if c == CompletionCover::Flat {
            self.index = IndexKind::Current;
        }
        self
    }

    pub(crate) fn selector(mut self, s: Selector) -> Self {
        self.selector = s;
        self
    }

    pub(crate) fn stop(mut self, b: bool) -> Self {
        self.stop_at_first_report = b;
        self
    }

    pub(crate) fn gated(mut self, m: GatedMode, p: GatePolicy) -> Self {
        self.gated_mode = m;
        self.gate_policy = p;
        self
    }

    pub(crate) fn memo(mut self, b: bool) -> Self {
        self.memo = b;
        self
    }

    pub(crate) fn budget(mut self, b: Budget) -> Self {
        self.budget = b;
        self
    }

    pub(crate) fn precheck(mut self, b: bool) -> Self {
        self.precheck = b;
        self
    }

    pub(crate) fn instrumented(mut self, b: bool) -> Self {
        self.instrumented = b;
        self
    }

    /// The `ConfConfig` this configuration builds for `fixture` (every engine
    /// but the enumerator's raw route reads it; the precheck is skipped unless
    /// `precheck`, in which case `run` performs it).
    pub(crate) fn conf_config(&self, subject: &Subject) -> ConfConfig {
        let engine = match self.engine {
            GridEngine::Enumerator | GridEngine::Verify => Engine::Enumerator,
            GridEngine::Stateful => Engine::Stateful,
            GridEngine::CompleteFirst => Engine::CompleteFirst,
            GridEngine::Gated => Engine::Gated,
            GridEngine::SverifyP => Engine::SverifyP,
            GridEngine::CFirstP => Engine::CFirstP,
            // `P5-XBASE` F1: never reached — the `Explore` arms of `call` and
            // `call_with` do not build a conformance configuration.
            GridEngine::Explore => {
                panic!("conformance: `Explore` has no conformance configuration (P5-XBASE F1)")
            }
            // `SVERIFY-P` I4-4: likewise — the baseline runs Must alone.
            GridEngine::ExploreP => {
                panic!("conformance: `ExploreP` has no conformance configuration (SVERIFY-P I4-4)")
            }
        };
        // `MIN-ENGINES` E7b: the complete-first engine reads `Set`; Flat + `Set`
        // is refused here (this path does not pass `cfirst::run`'s refusal),
        // before any engine starts — the fix is `index(Current)` (F1).
        assert!(
            !(self.completion_cover == CompletionCover::Flat && self.index == IndexKind::Set),
            "conformance: index(Set) with completion_cover(Flat) is not a configuration; set \
             index(Current) (MIN-ENGINES E7b)"
        );
        let b = ConfBuilder::new()
            .config(subject.config.clone())
            .visible_threads(subject.visible.clone())
            .engine(engine)
            .selector(self.selector)
            .inner_order(InnerOrder::Recorded)
            .memo(self.memo)
            .search_budget(self.budget.value())
            .stop_at_first_report(self.stop_at_first_report)
            .gated_mode(self.gated_mode)
            .gate_policy(self.gate_policy)
            .early_error_cut(self.early_error_cut)
            .completion_cover(self.completion_cover)
            .witness_cache(self.witness_cache)
            .quiet_sweeps(self.quiet)
            .all_reports(self.all_reports)
            .sweep_record(self.sweep_record)
            .index(self.index)
            .antichain(self.antichain)
            .probe_memo(self.probe_memo)
            .impl_distinct(self.impl_distinct)
            .bucket(self.bucket)
            .threads(self.threads)
            .flush_entries(self.flush_entries)
            .phase_peaks(self.phase_peaks)
            .skip_spec_errfree_check(!self.precheck)
            .triage(self.engine == GridEngine::Verify);
        b.build()
            .expect("conformance: a grid configuration is in scope")
    }

    /// One line naming every knob, for a table row.
    /// `MIN-ENGINES` E1-2: the key's second field — `Plain` when no run of
    /// this configuration reads the selector: the stateful engine always, the
    /// stateless engine when its precheck is off (its outer run and sweeps
    /// schedule by plain Must whatever `selector` holds; a `precheck = true`
    /// row's `Precheck` run still reads it, so that row keeps the selector's
    /// name — one key for one scheduling, and no key hides a knob a run
    /// read); the selector's name for the engines that read it; a legacy
    /// key's own spelling when this configuration was parsed from one (a
    /// stored identity, never run).
    fn selector_field(&self) -> String {
        match (self.legacy_selector, self.engine) {
            (Some(s), _) => format!("{s:?}"),
            (None, GridEngine::Stateful) => "Plain".to_owned(),
            // `SVERIFY-P` I4-1: the twin mode is plain-scheduled (I3-2).
            (None, GridEngine::SverifyP) => "Plain".to_owned(),
            // `SVERIFY-P` P-S: likewise (the precheck is `run`'s, not the grid's).
            (None, GridEngine::CFirstP) => "Plain".to_owned(),
            (None, GridEngine::CompleteFirst) if !self.precheck => "Plain".to_owned(),
            (None, _) => format!("{:?}", self.selector),
        }
    }

    /// `MIN-ENGINES` E1-2: whether this configuration's key prints `Plain`
    /// (`selector_field`), i.e. no run of it reads the selector.
    pub(crate) fn plain_key(&self) -> bool {
        self.legacy_selector.is_none()
            && match self.engine {
                GridEngine::Stateful => true,
                GridEngine::SverifyP => true,
                GridEngine::CFirstP => true,
                GridEngine::CompleteFirst => !self.precheck,
                _ => false,
            }
    }

    pub(crate) fn label(&self) -> String {
        let eleven = format!(
            "{:?}/{}/stop={}/{:?}/{:?}/memo={}/{:?}/precheck={}/instr={}/cut={}/cover={:?}",
            self.engine,
            self.selector_field(),
            self.stop_at_first_report,
            self.gated_mode,
            self.gate_policy,
            self.memo,
            self.budget,
            self.precheck,
            self.instrumented,
            self.early_error_cut,
            self.completion_cover
        );
        // `P5-CFCFG` F4 (landing erratum E-CF-1): the eleven-field form is
        // kept byte for byte while both new knobs are at their defaults, so
        // every key of the campaign and APPTAB stores and schedules stays the
        // key the driver derives; a non-default knob prints the two fields.
        // `COMPACT-INDEX` frozen §8: under `Compact` the thirteen-field form
        // followed by the three knobs; under `Current` nothing changes.
        // Phase 2 D6: `/distinct=on` appended only when the knob is on, so
        // every key with it off is the slice's key; P7: and only where it has
        // effect (the stateful engine, every index; complete-first under
        // `Compact` or `Set`, `MIN-ENGINES` E7b).
        let base = if self.index == IndexKind::Compact {
            format!(
                "{eleven}/{}/quiet={}/index=compact/anti={}/pmemo={}",
                capacity_field(self.witness_cache),
                self.quiet,
                self.antichain,
                self.probe_memo
            )
        } else if self.index == IndexKind::Set {
            // `SVERIFY-P` I2b-7: fourteen fields; `antichain`, `probe_memo`
            // and `bucket` are neither read nor printed under `Set`, as
            // under `Current`.
            format!(
                "{eleven}/{}/quiet={}/index=set",
                capacity_field(self.witness_cache),
                self.quiet
            )
        } else if self.witness_cache == Capacity::Unbounded && !self.quiet {
            eleven
        } else {
            format!("{eleven}/{}/quiet={}", capacity_field(self.witness_cache), self.quiet)
        };
        // Phase 2 item 7 (P2-frozen §6): the slot structure after the
        // compact fields, under `Compact` only; nothing for the scan, so every
        // scan key is the slice's.
        let base = match (self.index, self.bucket) {
            (IndexKind::Compact, BucketKind::Inverted(t)) => format!("{base}/bucket=inverted:{t}"),
            (IndexKind::Compact, BucketKind::Trie) => format!("{base}/bucket=trie"),
            _ => base,
        };
        // Phase 2 D6, `MIN-ENGINES` E7b: the knob acts in the stateful engine
        // under every index, and in the complete-first engine under `Compact`
        // and `Set` (its step-0 set, `cfirst.rs`); only there is it printed.
        // `SVERIFY-P` I4-1: the two partitioned engines' fields, appended —
        // `threads=<t>` always (the rows of V-S's curve must not share a key),
        // `flush=<F>` only off its default; no `explore=` (ruling D3, one
        // value adds no identity). Every other engine's label is untouched.
        let base = match self.engine {
            GridEngine::SverifyP if self.flush_entries != 4096 => {
                format!("{base}/threads={}/flush={}", self.threads, self.flush_entries)
            }
            GridEngine::SverifyP | GridEngine::ExploreP | GridEngine::CFirstP => {
                format!("{base}/threads={}", self.threads)
            }
            _ => base,
        };
        // `SVERIFY-P` I4: the knob acts in SVerify-P as in the stateful engine.
        let distinct_effective = self.engine == GridEngine::Stateful
            || self.engine == GridEngine::SverifyP
            || self.engine == GridEngine::CFirstP
            || (self.engine == GridEngine::CompleteFirst
                && matches!(self.index, IndexKind::Compact | IndexKind::Set));
        if self.impl_distinct && distinct_effective {
            format!("{base}/distinct=on")
        } else {
            base
        }
    }
}

/// `COMPACT-INDEX` frozen §7: the `index_kind` column, from the
/// configuration's kind (`SVERIFY-P` I2b-7: `set` as well).
fn index_kind_field(index: IndexKind) -> &'static str {
    match index {
        IndexKind::Current => "current",
        IndexKind::Compact => "compact",
        IndexKind::Set => "set",
    }
}

/// `P5-CFCFG` F4: the label's capacity field (`w=0` | `w=<n>` | `w=inf`).
pub(crate) fn capacity_field(c: Capacity) -> String {
    match c {
        Capacity::Zero => "w=0".to_owned(),
        Capacity::Bounded(n) => format!("w={n}"),
        Capacity::Unbounded => "w=inf".to_owned(),
    }
}

/// The inverse of [`capacity_field`]; `w=0` is `Zero`, never `Bounded(0)`.
pub(crate) fn parse_capacity(s: &str) -> Option<Capacity> {
    let v = s.strip_prefix("w=")?;
    if v == "inf" {
        return Some(Capacity::Unbounded);
    }
    let n: usize = v.parse().ok()?;
    Some(if n == 0 { Capacity::Zero } else { Capacity::Bounded(n) })
}

/// The raw engine outcome, whole (X3: the tester reads `spec_error` /
/// `spec_errors` first).
#[allow(clippy::large_enum_variant)]
pub(crate) enum GridRaw {
    Enumerator(Outcome),
    Stateful(StatefulOutcome),
    CompleteFirst(CFirstOutcome),
    Gated(GatedOutcome),
    /// `cfirst::run` / `gated::run` (the precheck arm) and the `Verify`
    /// engine: the rendered route's verdict.
    Verdict(Result<ConfVerdict, ConfError>),
    /// `P5-XBASE` F2: plain `verify`'s `Stats` (`execs` finished normally,
    /// `block` blocked; the maximal graphs are their sum).
    Explore(crate::Stats),
    /// `SVERIFY-P` I4: SVerify-P's raw outcome, with `VmPeak` at its end and
    /// the run's `Config` parameters.
    SverifyP(Box<SverifyPRun>),
    /// `SVERIFY-P` I4-4: the baseline's two partitioned explorations.
    ExploreP(Box<ExplorePRun>),
    /// `SVERIFY-P` P-S: CVerify-P's raw outcome with `VmPeak` at its end.
    CFirstP(Box<CFirstPRun>),
}

/// `SVERIFY-P` P-S: one CVerify-P run as the row sees it.
pub(crate) struct CFirstPRun {
    pub(crate) outcome: crate::conformance::cfirst_p::CFirstPOutcome,
    pub(crate) vm_peak_kb: Option<u64>,
}

/// `SVERIFY-P` I4: one SVerify-P run as the row sees it.
pub(crate) struct SverifyPRun {
    pub(crate) outcome: crate::conformance::sverify_p::SverifyPOutcome,
    /// `VmPeak` (the address space's high-water mark) at the row's end,
    /// I2b-8 (c)'s figure.
    pub(crate) vm_peak_kb: Option<u64>,
    pub(crate) warmup: usize,
    pub(crate) state_batch_size: usize,
}

/// `SVERIFY-P` I4-4: the baseline's raw outcome — Must alone in the
/// partitioned mode on each side, under SVerify-P's phase `Config`, with the
/// per-phase readings of I4-3 when the knob is on.
pub(crate) struct ExplorePRun {
    pub(crate) spec: crate::parallel_verify::PartitionedRun,
    pub(crate) imp: crate::parallel_verify::PartitionedRun,
    pub(crate) spec_wall_ms: u128,
    pub(crate) impl_wall_ms: u128,
    pub(crate) spec_vmhwm_kb: Option<u64>,
    pub(crate) impl_vmhwm_kb: Option<u64>,
    pub(crate) vmhwm_kb_max: Option<u64>,
    pub(crate) phase_peaks: bool,
    pub(crate) vm_peak_kb: Option<u64>,
    pub(crate) threads: usize,
    pub(crate) warmup: usize,
    pub(crate) iterations_until_split: usize,
    pub(crate) state_batch_size: usize,
}

impl std::fmt::Debug for GridRaw {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GridRaw::Enumerator(o) => f
                .debug_struct("Enumerator")
                .field("reports", &o.reports.len())
                .field("exhaustions", &o.exhaustions.len())
                .field("end", &o.end)
                .field("spec_error", &o.spec_error.is_some())
                .finish(),
            GridRaw::Stateful(o) => f
                .debug_struct("Stateful")
                .field("reports", &o.counters.reports)
                .field("impl_end", &o.impl_end)
                .field("spec_end", &o.spec_end)
                .field("spec_errors", &o.spec_errors.len())
                .finish(),
            GridRaw::CompleteFirst(o) => f
                .debug_struct("CompleteFirst")
                .field("reports", &o.counters.reports)
                .field("cut_reports", &o.cut_reports.len())
                .field("impl_end", &o.impl_end)
                .field("aborted", &o.aborted)
                .field("spec_errors", &o.spec_errors.len())
                .finish(),
            GridRaw::Gated(o) => f
                .debug_struct("Gated")
                .field("reports", &o.reports.len())
                .field("impl_end", &o.impl_end)
                .field("aborted", &o.aborted)
                .field("spec_errors", &o.spec_errors.len())
                .finish(),
            GridRaw::Verdict(v) => f.debug_tuple("Verdict").field(v).finish(),
            GridRaw::Explore(s) => f
                .debug_struct("Explore")
                .field("execs", &s.execs)
                .field("block", &s.block)
                .finish(),
            GridRaw::SverifyP(r) => f
                .debug_struct("SverifyP")
                .field("reports", &r.outcome.counters.reports)
                .field("impl_end", &r.outcome.impl_end)
                .field("spec_end", &r.outcome.spec_end)
                .field("spec_errors", &r.outcome.spec_errors.len())
                .finish(),
            GridRaw::CFirstP(r) => f
                .debug_struct("CFirstP")
                .field("reports", &r.outcome.counters.base.reports)
                .field("impl_end", &r.outcome.impl_end)
                .field("aborted", &r.outcome.aborted)
                .field("spec_errors", &r.outcome.spec_errors.len())
                .finish(),
            GridRaw::ExploreP(r) => f
                .debug_struct("ExploreP")
                .field("spec_execs", &r.spec.stats.execs)
                .field("spec_block", &r.spec.stats.block)
                .field("impl_execs", &r.imp.stats.execs)
                .field("impl_block", &r.imp.stats.block)
                .finish(),
        }
    }
}

/// One completed run.
#[derive(Debug)]
pub(crate) struct GridResult {
    pub(crate) fixture: String,
    pub(crate) config: GridConfig,
    pub(crate) raw: GridRaw,
    /// Wall time of the engine call alone, on the run thread.
    pub(crate) wall: Duration,
    /// The process's `VmHWM` (kB) before and after the run, when
    /// `/proc/self/status` is readable — a process figure that includes every
    /// thread's stack (X7).
    pub(crate) vm_hwm_kb: (Option<u64>, Option<u64>),
    /// [`GRID_TAINTED`] was already set when this run started: the tester
    /// drops its timing and memory rows (X1).
    pub(crate) tainted_at_start: bool,
    /// The stack the run thread was given, in MiB.
    pub(crate) stack_mib: usize,
}

/// How a run ended.
#[allow(clippy::large_enum_variant)]
#[derive(Debug)]
pub(crate) enum GridEnd {
    Ok(GridResult),
    /// The engine panicked; the payload rendered (X1: a failure, never "out of
    /// reach").
    Panicked {
        fixture: String,
        config: GridConfig,
        payload: String,
    },
    /// `recv_timeout` elapsed: the run thread was abandoned and the process
    /// marked tainted.
    Capped {
        fixture: String,
        config: GridConfig,
        after: Duration,
    },
}

/// Set once a run has been abandoned (X1); every later timing or memory row
/// of this process is suspect and the tester drops it.
pub(crate) static GRID_TAINTED: AtomicBool = AtomicBool::new(false);

pub(crate) fn tainted() -> bool {
    GRID_TAINTED.load(Ordering::SeqCst)
}

/// `VmHWM` from `/proc/self/status`, in kB (Linux only; `None` elsewhere).
pub(crate) fn vm_hwm_kb() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    line.split_whitespace().nth(1)?.parse().ok()
}

/// `SVERIFY-P` I4-4: `VmPeak` from `/proc/self/status`, in kB — the address
/// space's high-water mark, what `ulimit -v` bounds (I2b-8 (c)).
pub(crate) fn vm_peak_kb() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|l| l.starts_with("VmPeak:"))?;
    line.split_whitespace().nth(1)?.parse().ok()
}

/// `SVERIFY-P` I4-3 R4: the run thread's `after` reading on a reset run is
/// the maximum of what it read and the engine's `vmhwm_kb_max`, so
/// `vm_hwm_kb_after`, `rss_child_hwm_kb` and the post-hoc censor keep the
/// process's peak; every other engine's reading is returned as is.
pub(crate) fn after_reading(raw: &GridRaw, after: Option<u64>) -> Option<u64> {
    let engine_max = match raw {
        GridRaw::SverifyP(r) => r.outcome.counters.vmhwm_kb_max,
        GridRaw::ExploreP(r) => r.vmhwm_kb_max,
        _ => None,
    };
    [after, engine_max].into_iter().flatten().max()
}

/// `SVERIFY-P` I4-4: the baseline — `verify_partitioned_rayon_with` with
/// default hooks (a token nobody cancels) on the specification, then on the
/// implementation, each under SVerify-P's phase `Config` exactly (the
/// fixture's with `keep_going_after_error`, the partitioned mode at
/// `threads`, the fixture's `warmup`, `iterations_until_split` and
/// `state_batch_size`); with the knob on, `VmHWM` reset before each side and
/// read after it, every reading kept (R2, R5), as the engine does.
pub(crate) fn explore_partitioned(subject: &Subject, config: &GridConfig) -> ExplorePRun {
    use crate::conformance::sverify_p::reset_vm_hwm;
    use crate::parallel_verify::{verify_partitioned_rayon_with, PartitionHooks};
    let mut cfg = subject.config.clone();
    cfg.keep_going_after_error = true;
    cfg.partitioned_parallelization = true;
    cfg.partitioned_num_threads = Some(config.threads);
    let peaks = config.phase_peaks;
    let read = || if peaks { vm_hwm_kb() } else { None };
    let before = read();
    let mut ok = !peaks || reset_vm_hwm();
    let spec = subject.specification.clone();
    let t0 = Instant::now();
    let spec_run =
        verify_partitioned_rayon_with(cfg.clone(), move || spec(), PartitionHooks::default());
    let spec_wall_ms = t0.elapsed().as_millis();
    let spec_hwm = read();
    ok = ok && (!peaks || reset_vm_hwm());
    let imp = subject.implementation.clone();
    let t1 = Instant::now();
    let impl_run =
        verify_partitioned_rayon_with(cfg.clone(), move || imp(), PartitionHooks::default());
    let impl_wall_ms = t1.elapsed().as_millis();
    let impl_hwm = read();
    let phase_peaks = peaks && ok;
    let vmhwm_kb_max = [before, spec_hwm, impl_hwm, vm_hwm_kb()]
        .into_iter()
        .flatten()
        .max();
    ExplorePRun {
        spec: spec_run,
        imp: impl_run,
        spec_wall_ms,
        impl_wall_ms,
        spec_vmhwm_kb: if phase_peaks { spec_hwm } else { None },
        impl_vmhwm_kb: if phase_peaks { impl_hwm } else { None },
        vmhwm_kb_max,
        phase_peaks,
        vm_peak_kb: vm_peak_kb(),
        threads: config.threads,
        warmup: cfg.warmup,
        iterations_until_split: cfg.iterations_until_split,
        state_batch_size: cfg.state_batch_size,
    }
}

/// The sum over threads of `selector::paper_events` (X7: complete-first's
/// `paper_events_at_first_report` is computed in the grid from its first
/// report graph; the gated engine sums the same way).
pub(crate) fn paper_events_total(g: &ExecutionGraph) -> usize {
    g.thread_ids().into_iter().map(|t| paper_events(g, t)).sum()
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

// --- copied from grid.rs: stack_mib_for ---
/// The run thread's stack: 32 MiB, or 64 MiB for an unlimited enumerator run
/// (X1). `H`: a subject has no big-stack flag.
pub(crate) fn stack_mib_for(config: &GridConfig) -> usize {
    if config.engine == GridEngine::Enumerator && config.budget == Budget::Unlimited {
        64
    } else {
        32
    }
}

// --- copied from grid.rs: Row ---
/// One row: column name and rendered value, in column order.
pub(crate) type Row = Vec<(&'static str, String)>;

// --- copied from grid.rs: push .. row_of_end ---
fn push<T: std::fmt::Debug>(row: &mut Row, k: &'static str, v: T) {
    row.push((k, format!("{v:?}")));
}

fn push_d<T: std::fmt::Display>(row: &mut Row, k: &'static str, v: T) {
    row.push((k, v.to_string()));
}

/// `P5-CFCFG` F5: an optional counter prints its value or nothing (never
/// `Some(…)`/`None`), so a cell is a number or blank.
fn push_opt<T: std::fmt::Display>(row: &mut Row, k: &'static str, v: Option<T>) {
    row.push((k, v.map(|x| x.to_string()).unwrap_or_default()));
}

/// The settings columns every row starts with.
fn settings_columns(fixture: &str, config: &GridConfig, row: &mut Row) {
    push_d(row, "fixture", fixture);
    push(row, "engine", config.engine);
    // `MIN-ENGINES` E1-2 (gate 3 F2): the key's field — `Plain` where no run
    // read the selector, so the column names no knob the run did not use.
    push_d(row, "selector", config.selector_field());
    push_d(row, "stop", config.stop_at_first_report);
    push(row, "gated_mode", config.gated_mode);
    push(row, "policy", config.gate_policy);
    push_d(row, "memo", config.memo);
    push(row, "budget", config.budget);
    push_d(row, "precheck", config.precheck);
    push_d(row, "instrumented", config.instrumented);
    push(row, "cover", config.completion_cover);
}

/// `P4-FLAT` criterion 9: `FlatCounters`' columns, absent under `Sweep`.
fn flat_columns(row: &mut Row, fc: Option<&crate::conformance::FlatCounters>) {
    let Some(fc) = fc else {
        return;
    };
    push_d(row, "flat_calls", fc.calls);
    push_d(row, "flat_visits", fc.visits);
    push_d(row, "flat_nd_branches", fc.nd_branches);
    push_d(row, "flat_source_branches", fc.source_branches);
    push_d(row, "flat_source_recursions", fc.source_recursions);
    push_d(row, "flat_send_kills", fc.send_kills);
    push_d(row, "flat_slot_kills", fc.slot_kills);
    push_d(row, "flat_source_kills", fc.source_kills);
    push_d(row, "flat_done_kills", fc.done_kills);
    push_d(row, "flat_witnesses", fc.witnesses);
    push_d(row, "flat_max_depth", fc.max_depth);
    push_d(row, "flat_wall_time_ms", fc.wall_time_ms);
}

/// `COMPACT-INDEX` §5.1 item 5 (frozen §7): the bucket index's columns,
/// absent under `IndexKind::Current`; `containment_tests` and
/// `impl_distinct_summaries` are pushed by the engine arms themselves.
fn compact_columns(row: &mut Row, cs: Option<&crate::conformance::compact::CompactStats>) {
    let Some(cs) = cs else {
        return;
    };
    push_d(row, "antichain_effective", cs.antichain_effective);
    push_d(row, "entries", cs.entries);
    push_d(row, "buckets", cs.buckets);
    push_d(row, "bucket_max", cs.bucket_max);
    push_d(row, "admitted", cs.admitted);
    push_d(row, "duplicates", cs.duplicates);
    push_d(row, "antichain_dropped_new", cs.antichain_dropped_new);
    push_d(row, "antichain_dropped_old", cs.antichain_dropped_old);
    push_d(row, "insert_tests", cs.insert_tests);
    push_d(row, "summary_bytes", cs.summary_bytes);
    // Phase 2 D1 (P2-frozen §1): `sig_bytes` replaced by the estimate and
    // the slot counts; D4's coordinate count. (`signatures` is pushed by the
    // engine arms: the stateful engine's counter carries it.)
    push_d(row, "sig_bytes_est", cs.sig_bytes_est);
    push_d(row, "signatures_seen", cs.signatures_seen);
    push_d(row, "sig_tests", cs.sig_tests);
    push_d(row, "sig_aliases", cs.sig_aliases);
    push_d(row, "coordinates_compared", cs.coordinates_compared);
    // Items 4, 5: blank unless the row's slot structure is that one.
    push_opt(row, "inverted_used", cs.inverted_used);
    push_opt(row, "inverted_words", cs.inverted_words);
    push_opt(row, "trie_nodes_visited", cs.trie_nodes_visited);
    push_d(row, "memo_on", cs.memo_on);
    push_d(row, "memo_hits", cs.memo_hits);
    push_d(row, "memo_entries", cs.memo_entries);
    push_d(row, "memo_clears", cs.memo_clears);
}

/// `MIN-ENGINES` E7a: the complete-first row's `sweep_ends` text from the scalar
/// counters — the same text `sweep_split` gives for the recorded vector (the
/// completion sweeps run without a limit, so none is budgeted), whatever the
/// `sweep_record` knob.
fn sweep_split_counts(c: &crate::conformance::report::CFirstCounters) -> String {
    format!(
        "witness={} exhausted={} aborted={} budgeted=0",
        c.sweeps_successful, c.sweeps_failing, c.sweeps_aborted
    )
}

fn sweep_split(ends: &[SweepEnd]) -> String {
    let n = |e: SweepEnd| ends.iter().filter(|x| **x == e).count();
    format!(
        "witness={} exhausted={} aborted={} budgeted={}",
        n(SweepEnd::Witness),
        n(SweepEnd::Exhausted),
        n(SweepEnd::Aborted),
        n(SweepEnd::Budgeted)
    )
}

/// Every field of the engine's own record, flattened into one row (X7: "the
/// engine's own record is kept whole"), with the run's wall time and memory
/// figures. No derived ratio is computed here.
pub(crate) fn row_of(r: &GridResult) -> Row {
    let mut row = Row::new();
    settings_columns(&r.fixture, &r.config, &mut row);
    push_d(&mut row, "wall_ms", r.wall.as_millis());
    push(&mut row, "vm_hwm_kb_before", r.vm_hwm_kb.0);
    push(&mut row, "vm_hwm_kb_after", r.vm_hwm_kb.1);
    push_d(&mut row, "tainted_at_start", r.tainted_at_start);
    push_d(&mut row, "stack_mib", r.stack_mib);
    match &r.raw {
        GridRaw::Enumerator(o) => {
            push_d(&mut row, "reports", o.reports.len());
            push_d(&mut row, "exhaustions", o.exhaustions.len());
            push_d(&mut row, "diagnostics", o.diagnostics.len());
            push(&mut row, "end", o.end);
            push_d(&mut row, "skipped_gates", o.skipped_gates);
            push_d(&mut row, "inert_gates", o.inert_gates);
            push_d(&mut row, "seed", o.seed);
            push_d(&mut row, "spec_error", o.spec_error.is_some());
            push(
                &mut row,
                "outer_graphs(execs+block)",
                o.stats.as_ref().map(|s| s.execs + s.block),
            );
            let c = &o.counters;
            push_d(&mut row, "gate_invocations", c.gate_invocations);
            push_d(&mut row, "gate_skipped_inert", c.gate_skipped_inert);
            push_d(&mut row, "gate_skipped_replay", c.gate_skipped_replay);
            push_d(&mut row, "gate_skipped_pruned", c.gate_skipped_pruned);
            push_d(&mut row, "gate_skipped_disabled", c.gate_skipped_disabled);
            push_d(&mut row, "gate_skipped_aborted", c.gate_skipped_aborted);
            push_d(&mut row, "cover_calls", c.cover_calls);
            push_d(&mut row, "cover_exhaustions", c.cover_exhaustions);
            push_d(&mut row, "rebuilds_taken", c.rebuilds_taken);
            push_d(
                &mut row,
                "rebuilds_skipped_initial_seed",
                c.rebuilds_skipped_initial_seed,
            );
            push_d(
                &mut row,
                "rebuilds_skipped_exhausted_seed",
                c.rebuilds_skipped_exhausted_seed,
            );
            push_d(&mut row, "spec_visit_calls", c.spec_visit_calls);
            push_d(
                &mut row,
                "spec_visit_calls_extend",
                c.spec_visit_calls_extend,
            );
            push_d(
                &mut row,
                "spec_visit_calls_rebuild",
                c.spec_visit_calls_rebuild,
            );
            push_d(&mut row, "memo_hits", c.memo_hits);
            push_d(&mut row, "per_cover", c.per_cover.len());
            push_d(&mut row, "distinct_keys_run_wide", c.distinct_keys_run_wide);
            push_d(&mut row, "f63_distinct_run_wide", c.f63_distinct_run_wide);
            push_d(
                &mut row,
                "explored_complete_keys",
                c.explored_complete_keys.len(),
            );
            push_d(&mut row, "report_keys", c.report_keys.len());
            push_d(
                &mut row,
                "max_paper_events_per_execution",
                c.max_paper_events_per_execution,
            );
            push(
                &mut row,
                "paper_events_at_first_report",
                c.paper_events_at_first_report,
            );
            push_d(&mut row, "executions", c.executions);
            push_d(&mut row, "engine_wall_time_ms", c.wall_time_ms);
            let per: Vec<String> = c
                .per_cover
                .iter()
                .map(|p| {
                    format!(
                        "calls={}/{}/{} hits={} rebuild={}/{}/{} distinct={} per_attempt={:?} f63={:?} so_far={} f63_so_far={}",
                        p.spec_visit_calls,
                        p.spec_visit_calls_extend,
                        p.spec_visit_calls_rebuild,
                        p.memo_hits,
                        p.rebuild_taken,
                        p.rebuild_skipped_initial_seed,
                        p.rebuild_skipped_exhausted_seed,
                        p.distinct_keys,
                        p.per_attempt_distinct,
                        p.f63_per_attempt_distinct,
                        p.run_wide_distinct_so_far,
                        p.f63_run_wide_distinct_so_far
                    )
                })
                .collect();
            push_d(&mut row, "per_cover_detail", per.join("; "));
        }
        GridRaw::Stateful(o) => {
            // `MIN-ENGINES` E6: the count, kept or not.
            push_d(&mut row, "reports", o.counters.reports);
            push(&mut row, "impl_end", o.impl_end);
            push(&mut row, "spec_end", o.spec_end);
            push_d(&mut row, "spec_errors", o.spec_errors.len());
            push_d(&mut row, "impl_notes", o.impl_notes.len());
            push_d(&mut row, "executions", o.executions);
            // `MIN-ENGINES` E3: blank unless the knob counted `L`.
            push_opt(&mut row, "max_paper_events", o.max_paper_events);
            push_d(&mut row, "kept_impl_graphs", o.kept_impl_graphs.len());
            push_d(&mut row, "kept_spec_graphs", o.kept_spec_graphs.len());
            let c = &o.counters;
            push_d(&mut row, "spec_graphs", c.spec_graphs);
            push_d(&mut row, "impl_graphs", c.impl_graphs);
            push_d(&mut row, "sig_key_buckets", c.sig_key_buckets);
            push_d(&mut row, "signatures", c.signatures);
            push_d(&mut row, "orders_held", c.orders_held);
            push_d(&mut row, "lookups", c.lookups);
            push_d(&mut row, "lookups_signature_miss", c.lookups_signature_miss);
            push_d(
                &mut row,
                "lookups_containment_tested",
                c.lookups_containment_tested,
            );
            push_d(&mut row, "lookups_succeeded", c.lookups_succeeded);
            push_d(
                &mut row,
                "lookups_failed_after_tests",
                c.lookups_failed_after_tests,
            );
            push_d(&mut row, "containment_tests", c.containment_tests);
            push_d(&mut row, "counter_reports", c.reports);
            push_d(&mut row, "spec_wall_time_ms", c.spec_wall_time_ms);
            push_d(&mut row, "impl_wall_time_ms", c.impl_wall_time_ms);
            // `MIN-ENGINES` E9: the two first-report columns, as the
            // complete-first row's (blank for `None`).
            push_opt(&mut row, "wall_ms_at_first_report", c.wall_ms_at_first_report);
            push_opt(&mut row, "vmhwm_kb_at_first_report", c.vmhwm_kb_at_first_report);
            // `COMPACT-INDEX` §5.1 items 1 and 5.
            push_opt(&mut row, "impl_distinct_summaries", c.impl_distinct_summaries);
            // `SVERIFY-P` I2b-7: the kind from the configuration (stateful row).
            push_d(&mut row, "index_kind", index_kind_field(r.config.index));
            compact_columns(&mut row, c.compact.as_ref());
            // `SVERIFY-P` I4-2: the exact-hit probe's count, comparable with
            // the sverify-p row's (I2-4: invariant under the insertion order).
            push_opt(&mut row, "exact_hits", o.set_index.as_ref().map(|s| s.stats().exact_hits));
        }
        GridRaw::CompleteFirst(o) => {
            // `MIN-ENGINES` E6: the completion count, kept or not.
            push_d(&mut row, "reports", o.counters.reports);
            push_d(&mut row, "cut_reports_list", o.cut_reports.len());
            push(&mut row, "impl_end", o.impl_end);
            push_d(&mut row, "spec_errors", o.spec_errors.len());
            push_d(&mut row, "aborted", o.aborted);
            push_d(&mut row, "impl_notes", o.impl_notes.len());
            push_d(&mut row, "executions", o.executions);
            // `MIN-ENGINES` E3: blank unless the knob counted `L`.
            push_opt(&mut row, "max_paper_events", o.max_paper_events);
            push_d(&mut row, "kept_impl_graphs", o.kept_impl_graphs.len());
            push_d(
                &mut row,
                "kept_spec_graphs",
                o.kept_spec_graphs.iter().map(Vec::len).sum::<usize>(),
            );
            push_d(&mut row, "witness_cache_len", o.witnesses.len());
            // `MIN-ENGINES` E7a: from the scalars, so the text is the same
            // whatever the `sweep_record` knob.
            push_d(&mut row, "sweep_ends", sweep_split_counts(&o.counters));
            push(
                &mut row,
                "paper_events_at_first_report(grid)",
                o.reports.first().map(|(g, _)| paper_events_total(g)),
            );
            let c = &o.counters;
            push_d(&mut row, "impl_graphs", c.impl_graphs);
            push_d(&mut row, "cache_probes", c.cache_probes);
            push_d(&mut row, "cache_hits", c.cache_hits);
            push_d(&mut row, "cache_tests", c.cache_tests);
            push_d(&mut row, "sweeps", c.sweeps);
            push_d(&mut row, "sweeps_successful", c.sweeps_successful);
            push_d(&mut row, "sweeps_failing", c.sweeps_failing);
            push_d(&mut row, "sweeps_aborted", c.sweeps_aborted);
            // `MIN-ENGINES` E7a: blank unless the per-sweep record is on.
            if r.config.sweep_record {
                push(&mut row, "sweep_sizes", &c.sweep_sizes);
            } else {
                push_d(&mut row, "sweep_sizes", "");
            }
            push_d(&mut row, "sweep_graphs", c.sweep_graphs);
            push_d(&mut row, "sweep_graphs_max", c.sweep_graphs_max);
            push_d(&mut row, "witnesses", c.witnesses);
            // `P5-CFCFG` F5: the five columns after `witnesses`.
            push_d(&mut row, "admissions", c.admissions);
            push_d(&mut row, "evictions", c.evictions);
            push_d(&mut row, "readmissions", c.readmissions);
            push_opt(&mut row, "wall_ms_at_first_report", c.wall_ms_at_first_report);
            push_opt(&mut row, "vmhwm_kb_at_first_report", c.vmhwm_kb_at_first_report);
            push_d(&mut row, "witness_duplicates", c.witness_duplicates);
            push_d(&mut row, "counter_reports", c.reports);
            push_d(&mut row, "cut_reports", c.cut_reports);
            push_d(&mut row, "precheck_ran", c.precheck_ran);
            push_d(&mut row, "precheck_wall_time_ms", c.precheck_wall_time_ms);
            push_d(&mut row, "outer_wall_time_ms", c.outer_wall_time_ms);
            push_d(&mut row, "sweep_wall_time_ms", c.sweep_wall_time_ms);
            flat_columns(&mut row, c.flat.as_ref());
            // `COMPACT-INDEX` §5.1 item 5: the Impl phase is the outer run
            // minus the sweeps; the index columns under `Compact`.
            push_d(
                &mut row,
                "impl_phase_wall_ms",
                c.outer_wall_time_ms.saturating_sub(c.sweep_wall_time_ms),
            );
            // `SVERIFY-P` I2b-7: the kind from the configuration (complete-first row).
            push_d(&mut row, "index_kind", index_kind_field(r.config.index));
            if let Some(cs) = c.compact.as_ref() {
                push_d(&mut row, "containment_tests", cs.containment_tests);
                push_opt(&mut row, "impl_distinct_summaries", cs.impl_distinct_summaries);
                push_d(&mut row, "signatures", cs.signatures);
            }
            compact_columns(&mut row, c.compact.as_ref());
        }
        GridRaw::Gated(o) => {
            push_d(&mut row, "reports", o.reports.len());
            let gate_reports = o
                .reports
                .iter()
                .filter(|(_, _, s)| matches!(s, ReportSite::Gate(_)))
                .count();
            push_d(&mut row, "reports_at_gates", gate_reports);
            push_d(
                &mut row,
                "reports_at_completion",
                o.reports.len() - gate_reports,
            );
            push(&mut row, "impl_end", o.impl_end);
            push_d(&mut row, "spec_errors", o.spec_errors.len());
            push_d(&mut row, "aborted", o.aborted);
            push(&mut row, "abort_gate_at", o.abort_gate_at.is_some());
            push_d(&mut row, "impl_notes", o.impl_notes.len());
            push_d(&mut row, "executions", o.executions);
            push_d(&mut row, "max_paper_events", o.max_paper_events);
            push_d(&mut row, "kept_impl_graphs", o.kept_impl_graphs.len());
            push_d(
                &mut row,
                "kept_spec_graphs",
                o.kept_spec_graphs.iter().map(Vec::len).sum::<usize>(),
            );
            push_d(&mut row, "witness_cache_len", o.witnesses.len());
            push_d(&mut row, "sweep_ends", sweep_split(&o.sweep_ends));
            let c = &o.counters;
            push_d(&mut row, "first_failure_mode", c.first_failure_mode);
            push_d(&mut row, "gates", c.gates);
            push_d(&mut row, "gates_inert", c.gates_inert);
            push_d(&mut row, "gates_skipped_replay", c.gates_skipped_replay);
            push_d(
                &mut row,
                "gates_skipped_certified",
                c.gates_skipped_certified,
            );
            push_d(&mut row, "gates_declined", c.gates_declined);
            push_d(&mut row, "c1_tests_carried", c.c1_tests_carried);
            push_d(&mut row, "carried_hits", c.carried_hits);
            push_d(&mut row, "c1_tests_cache", c.c1_tests_cache);
            push_d(&mut row, "gate_cache_hits", c.gate_cache_hits);
            push_d(&mut row, "c1_tests_sweep", c.c1_tests_sweep);
            push_d(&mut row, "gate_sweeps", c.gate_sweeps);
            push_d(&mut row, "gate_sweeps_successful", c.gate_sweeps_successful);
            push_d(&mut row, "gate_sweeps_failing", c.gate_sweeps_failing);
            push_d(&mut row, "gate_sweeps_budgeted", c.gate_sweeps_budgeted);
            push_d(&mut row, "gate_sweeps_aborted", c.gate_sweeps_aborted);
            push(&mut row, "gate_sweep_sizes", &c.gate_sweep_sizes);
            push_d(&mut row, "certificates_set", c.certificates_set);
            push_d(&mut row, "certificate_resets", c.certificate_resets);
            push_d(&mut row, "states_pushed", c.states_pushed);
            push_d(
                &mut row,
                "certified_states_revisited",
                c.certified_states_revisited,
            );
            push_d(&mut row, "reports_certified", c.reports_certified);
            push_d(
                &mut row,
                "reports_by_completion_test",
                c.reports_by_completion_test,
            );
            push(
                &mut row,
                "paper_events_at_first_report",
                c.paper_events_at_first_report,
            );
            push_d(&mut row, "impl_graphs", c.impl_graphs);
            push_d(&mut row, "completion_probes", c.completion_probes);
            push_d(&mut row, "completion_cache_hits", c.completion_cache_hits);
            push_d(&mut row, "completion_cache_tests", c.completion_cache_tests);
            push_d(&mut row, "completion_sweeps", c.completion_sweeps);
            push_d(
                &mut row,
                "completion_sweeps_successful",
                c.completion_sweeps_successful,
            );
            push_d(
                &mut row,
                "completion_sweeps_failing",
                c.completion_sweeps_failing,
            );
            push_d(
                &mut row,
                "completion_sweeps_aborted",
                c.completion_sweeps_aborted,
            );
            push(
                &mut row,
                "completion_sweep_sizes",
                &c.completion_sweep_sizes,
            );
            push_d(&mut row, "witnesses", c.witnesses);
            push_d(&mut row, "witness_duplicates", c.witness_duplicates);
            push_d(&mut row, "counter_reports", c.reports);
            push_d(&mut row, "precheck_ran", c.precheck_ran);
            push_d(&mut row, "precheck_wall_time_ms", c.precheck_wall_time_ms);
            push_d(&mut row, "outer_wall_time_ms", c.outer_wall_time_ms);
            push_d(&mut row, "sweep_wall_time_ms", c.sweep_wall_time_ms);
            flat_columns(&mut row, c.flat.as_ref());
        }
        GridRaw::Verdict(v) => {
            let class = match v {
                Ok(ConfVerdict::Conforms(_)) => "Conforms",
                Ok(ConfVerdict::Reported(_)) => "Reported",
                Ok(ConfVerdict::Inconclusive(_)) => "Inconclusive",
                Err(_) => "Err",
            };
            push_d(&mut row, "verdict", class);
            if let Ok(verdict) = v {
                let o = verdict.outcome();
                push_d(&mut row, "reports", o.report_count());
                push_d(&mut row, "exhaustions", o.exhaustions.len());
                push_d(&mut row, "notes", o.notes.len());
                push(&mut row, "end", o.end);
                push_d(&mut row, "seed", o.seed);
                push(&mut row, "rendered_engine", o.engine);
                push(&mut row, "spec_errfree", o.spec_errfree);
                push_d(&mut row, "executions", o.counters.executions);
                push_d(&mut row, "engine_wall_time_ms", o.counters.wall_time_ms);
                let precheck_ms = o
                    .cfirst_counters
                    .as_ref()
                    .map(|c| c.precheck_wall_time_ms)
                    .or_else(|| o.gated_counters.as_ref().map(|c| c.precheck_wall_time_ms));
                push(&mut row, "precheck_wall_time_ms", precheck_ms);
                push(
                    &mut row,
                    "precheck_ran",
                    o.cfirst_counters
                        .as_ref()
                        .map(|c| c.precheck_ran)
                        .or_else(|| o.gated_counters.as_ref().map(|c| c.precheck_ran)),
                );
                if let Some(e) = o.flat_eligibility() {
                    push_d(&mut row, "communication_flat", e.communication_flat);
                    push_d(&mut row, "thread_flat", e.thread_flat);
                    push_d(&mut row, "spec_graphs_scanned", e.spec_graphs_scanned);
                    push(&mut row, "first_invisible", &e.first_invisible);
                }
                flat_columns(&mut row, o.flat_counters());
            } else if let Err(crate::conformance::ConfError::SpecNotCommunicationFlat { thread, pos }) = v {
                push_d(&mut row, "communication_flat", false);
                push_d(&mut row, "refused_at", format!("{thread} @ {pos}"));
            }
        }
        GridRaw::Explore(s) => {
            // `P5-XBASE` F2 (gate 1 round 01 B1): the conformance `executions`
            // is the completion-gate count — every ending, blocked ones
            // included — so the baseline's is `execs + block`; the second
            // column is the enumerator's spelling of the same sum.
            push_d(&mut row, "executions", s.execs + s.block);
            push(&mut row, "outer_graphs(execs+block)", Some(s.execs + s.block));
        }
        GridRaw::SverifyP(r) => sverify_p_columns(&mut row, r),
        GridRaw::ExploreP(r) => explore_p_columns(&mut row, r),
        GridRaw::CFirstP(r) => cfirst_p_columns(&mut row, r, &r.outcome.counters.base),
    }
    row
}

/// `SVERIFY-P` P-S: the CVerify-P row — the verdict by `run`'s rule on the raw
/// outcome, the complete-first row's columns from the base record under their
/// sequential meanings, then the partitioned run's own columns.
fn cfirst_p_columns(row: &mut Row, r: &CFirstPRun, c: &crate::conformance::report::CFirstCounters) {
    let o = &r.outcome;
    let p = &o.counters;
    let class = if !o.spec_errors.is_empty() {
        "Err"
    } else if c.reports > 0 {
        "Reported"
    } else {
        "Conforms"
    };
    push_d(row, "verdict", class);
    push_d(row, "reports", c.reports);
    push(row, "impl_end", o.impl_end);
    push_d(row, "spec_errors", o.spec_errors.len());
    push_d(row, "aborted", o.aborted);
    push_d(row, "impl_notes", o.impl_notes.len());
    push_d(row, "executions", o.executions);
    // `SVERIFY-P` V-C (VC-0, schema 8): the outer run's split.
    push_d(row, "impl_complete", o.impl_complete);
    push_d(row, "impl_blocked", o.impl_blocked);
    push_opt(row, "max_paper_events", o.max_paper_events);
    push_d(row, "witness_cache_len", c.witnesses);
    push_d(row, "sweep_ends", sweep_split_counts(c));
    push_d(row, "impl_graphs", c.impl_graphs);
    push_d(row, "cache_probes", c.cache_probes);
    push_d(row, "cache_hits", c.cache_hits);
    push_d(row, "cache_tests", c.cache_tests);
    push_d(row, "sweeps", c.sweeps);
    push_d(row, "sweeps_successful", c.sweeps_successful);
    push_d(row, "sweeps_failing", c.sweeps_failing);
    push_d(row, "sweeps_aborted", c.sweeps_aborted);
    if r.outcome.counters.base.sweep_sizes.is_empty() {
        push_d(row, "sweep_sizes", "");
    } else {
        push(row, "sweep_sizes", &c.sweep_sizes);
    }
    push_d(row, "sweep_graphs", c.sweep_graphs);
    push_d(row, "sweep_graphs_max", c.sweep_graphs_max);
    push_d(row, "witnesses", c.witnesses);
    push_d(row, "admissions", c.admissions);
    push_d(row, "evictions", c.evictions);
    push_d(row, "readmissions", c.readmissions);
    push_opt(row, "wall_ms_at_first_report", c.wall_ms_at_first_report);
    push_opt(row, "vmhwm_kb_at_first_report", c.vmhwm_kb_at_first_report);
    push_d(row, "witness_duplicates", c.witness_duplicates);
    push_d(row, "counter_reports", c.reports);
    push_d(row, "cut_reports", c.cut_reports);
    push_d(row, "precheck_ran", c.precheck_ran);
    push_d(row, "precheck_wall_time_ms", c.precheck_wall_time_ms);
    push_d(row, "outer_wall_time_ms", c.outer_wall_time_ms);
    // `SVERIFY-P` V-C (Q14 a): `sweep_wall_time_ms` sums the sweeps' times
    // over the workers. At one thread they run in the exploring thread, so
    // outer minus sweep is the implementation phase's wall. Above one thread
    // the sweeps overlap the exploration and the sum is worker time, not a
    // wall: the run has no implementation phase to time, and the cell is
    // blank (the sweep share is `sweep_wall_time_ms` over the row's CPU time).
    push_d(row, "sweep_wall_time_ms", c.sweep_wall_time_ms);
    if p.threads > 1 {
        push_d(row, "impl_phase_wall_ms", "");
    } else {
        push_d(
            row,
            "impl_phase_wall_ms",
            c.outer_wall_time_ms.saturating_sub(c.sweep_wall_time_ms),
        );
    }
    push_d(row, "index_kind", "set");
    push_d(row, "containment_tests", c.cache_tests);
    push_opt(row, "impl_distinct_summaries", p.impl_distinct_summaries);
    push_d(row, "signatures", p.cache_signatures);
    push_d(row, "entries", c.witnesses);
    push_d(row, "summary_bytes", p.cache_summary_bytes);
    push_d(row, "sig_tests", p.sig_tests);
    push_d(row, "coordinates_compared", p.coordinates_compared);
    push_d(row, "exact_hits", p.exact_hits);
    push_d(row, "threads", p.threads);
    push_d(row, "impl_tasks", p.tasks);
    push_d(row, "impl_tasks_nonempty", p.tasks_nonempty);
    push_d(row, "impl_flushes", p.flushes);
    push_d(row, "redundant_sweeps", p.redundant_sweeps);
    push_d(row, "unadmitted_after_cancel", p.unadmitted_after_cancel);
    push_d(row, "unprobed_after_cancel", p.unprobed_after_cancel);
    push_d(row, "sweeps_in_warmup", p.sweeps_in_warmup);
    push_d(row, "sweeps_in_root_loop", p.sweeps_in_root_loop);
    push_d(row, "sweeps_in_tasks", p.sweeps_in_tasks);
    push_d(row, "sweeps_abandoned", p.sweeps_abandoned);
    push_d(row, "watch_probes", p.watch_probes);
    push_d(row, "signature_syncs", p.signature_syncs);
    push_d(row, "admission_lock_held_ms", p.admission_lock_held_ms);
    push_d(row, "admission_lock_wait_ms", p.admission_lock_wait_ms);
    push_d(row, "stopped_early", p.stopped_early);
    push_d(row, "spawned_at_stop", p.spawned_at_stop);
    push_d(row, "uncovered_distinct", p.uncovered_distinct);
    push_d(row, "uncovered_multiplicity", p.uncovered_multiplicity);
    push_opt(row, "vm_peak_kb", r.vm_peak_kb);
}

/// `SVERIFY-P` I4-2, I4-6: the sverify-p row — the verdict by `run`'s rule
/// on the raw outcome, the stateful row's columns under their meanings
/// (`duplicates` = worker + merge; `sig_tests` = the merge's resolutions +
/// the queries'; `containment_tests` and `coordinates_compared` the
/// queries'), then the engine's record flattened whole.
fn sverify_p_columns(row: &mut Row, r: &SverifyPRun) {
    let o = &r.outcome;
    let c = &o.counters;
    let class = if !o.spec_errors.is_empty() {
        "Err"
    } else if c.uncovered_multiplicity > 0 {
        "Reported"
    } else {
        "Conforms"
    };
    push_d(row, "verdict", class);
    push_d(row, "reports", c.reports);
    push(row, "impl_end", o.impl_end);
    push(row, "spec_end", o.spec_end);
    push_d(row, "spec_errors", o.spec_errors.len());
    push_d(row, "impl_notes", o.impl_notes.len());
    push_d(row, "executions", o.executions);
    push_opt(row, "max_paper_events", o.max_paper_events);
    push_d(row, "spec_graphs", c.spec_graphs);
    push_d(row, "impl_graphs", c.impl_graphs);
    push_d(row, "signatures", c.signatures);
    push_d(row, "orders_held", c.orders_held);
    push_d(row, "lookups", c.lookups);
    push_d(row, "lookups_signature_miss", c.lookups_signature_miss);
    push_d(row, "lookups_containment_tested", c.lookups_containment_tested);
    push_d(row, "lookups_succeeded", c.lookups_succeeded);
    push_d(row, "lookups_failed_after_tests", c.lookups_failed_after_tests);
    push_d(row, "containment_tests", c.containment_tests);
    push_d(row, "counter_reports", c.reports);
    push_d(row, "spec_wall_time_ms", c.spec_wall_time_ms);
    push_d(row, "impl_wall_time_ms", c.impl_wall_time_ms);
    push_opt(row, "wall_ms_at_first_report", c.wall_ms_at_first_report);
    push_opt(row, "vmhwm_kb_at_first_report", c.vmhwm_kb_at_first_report);
    push_opt(row, "impl_distinct_summaries", c.impl_distinct_summaries);
    push_d(row, "index_kind", "set");
    let mut cs = c.spec_set.as_compact_stats();
    cs.duplicates = c.spec_worker_duplicates + c.spec_merge_duplicates;
    cs.sig_tests = c.spec_set.sig_tests + c.sig_tests;
    cs.containment_tests = c.containment_tests;
    cs.coordinates_compared = c.coordinates_compared;
    cs.impl_distinct_summaries = c.impl_distinct_summaries;
    compact_columns(row, Some(&cs));
    push_d(row, "threads", c.threads);
    push_d(row, "flush_entries", c.flush_entries);
    push_d(row, "iterations_until_split", c.iterations_until_split);
    push_d(row, "warmup", r.warmup);
    push_d(row, "state_batch_size", r.state_batch_size);
    push_d(row, "freeze_wall_time_ms", c.freeze_wall_time_ms);
    push_opt(row, "spec_vmhwm_kb", c.spec_vmhwm_kb);
    push_opt(row, "freeze_vmhwm_kb", c.freeze_vmhwm_kb);
    push_opt(row, "impl_vmhwm_kb", c.impl_vmhwm_kb);
    push_opt(row, "vmhwm_kb_max", c.vmhwm_kb_max);
    push_d(row, "phase_peaks", if c.phase_peaks { "per-phase" } else { "process" });
    push_opt(row, "vm_peak_kb", r.vm_peak_kb);
    push_d(row, "spec_complete", c.spec_complete);
    push_d(row, "spec_blocked", c.spec_blocked);
    push_d(row, "impl_complete", c.impl_complete);
    push_d(row, "impl_blocked", c.impl_blocked);
    push_d(row, "spec_tasks", c.spec_tasks);
    push_d(row, "impl_tasks", c.impl_tasks);
    push_d(row, "spec_tasks_nonempty", c.spec_tasks_nonempty);
    push_d(row, "impl_tasks_nonempty", c.impl_tasks_nonempty);
    push_d(row, "spec_flushes", c.spec_flushes);
    push_d(row, "impl_flushes", c.impl_flushes);
    push_d(row, "spec_merge_lock_held_ms", c.spec_merge_lock_held_ms);
    push_d(row, "spec_merge_lock_wait_ms", c.spec_merge_lock_wait_ms);
    push_d(row, "impl_merge_lock_held_ms", c.impl_merge_lock_held_ms);
    push_d(row, "impl_merge_lock_wait_ms", c.impl_merge_lock_wait_ms);
    push_d(row, "spec_flush_entries", c.spec_flush_entries);
    push_d(row, "spec_worker_duplicates", c.spec_worker_duplicates);
    push_d(row, "spec_merge_duplicates", c.spec_merge_duplicates);
    push_d(row, "impl_seen_flush_entries", c.impl_seen_flush_entries);
    push_d(row, "impl_seen_worker_duplicates", c.impl_seen_worker_duplicates);
    push_d(row, "exact_hits", c.exact_hits);
    push_d(row, "uncovered_distinct", c.uncovered_distinct);
    push_d(row, "uncovered_multiplicity", c.uncovered_multiplicity);
    push_d(row, "uncovered_flush_entries", c.uncovered_flush_entries);
    push_d(row, "uncovered_worker_duplicates", c.uncovered_worker_duplicates);
    push_d(row, "uncovered_merge_duplicates", c.uncovered_merge_duplicates);
    push_d(row, "stopped_early", c.stopped_early);
    push_d(row, "uncovered_at_stop", c.uncovered_at_stop);
    push_d(row, "spawned_at_stop", c.spawned_at_stop);
}

/// `SVERIFY-P` I4-4: the baseline row — the per-side counts, walls, tasks and
/// peaks under the sverify-p row's names; `executions` the implementation's
/// `execs + block` (XBASE's convention).
fn explore_p_columns(row: &mut Row, r: &ExplorePRun) {
    let (sp, im) = (&r.spec.stats, &r.imp.stats);
    push_d(row, "executions", im.execs + im.block);
    push(row, "outer_graphs(execs+block)", Some(im.execs + im.block));
    push_d(row, "spec_graphs", sp.execs + sp.block);
    push_d(row, "impl_graphs", im.execs + im.block);
    push_d(row, "spec_complete", sp.execs);
    push_d(row, "spec_blocked", sp.block);
    push_d(row, "impl_complete", im.execs);
    push_d(row, "impl_blocked", im.block);
    push_d(row, "spec_wall_time_ms", r.spec_wall_ms);
    push_d(row, "impl_wall_time_ms", r.impl_wall_ms);
    push_d(row, "spec_tasks", r.spec.tasks_spawned + 1);
    push_d(row, "impl_tasks", r.imp.tasks_spawned + 1);
    push_d(row, "spec_tasks_nonempty", r.spec.workers_reported);
    push_d(row, "impl_tasks_nonempty", r.imp.workers_reported);
    push_d(row, "threads", r.threads);
    push_d(row, "iterations_until_split", r.iterations_until_split);
    push_d(row, "warmup", r.warmup);
    push_d(row, "state_batch_size", r.state_batch_size);
    push_opt(row, "spec_vmhwm_kb", r.spec_vmhwm_kb);
    push_opt(row, "impl_vmhwm_kb", r.impl_vmhwm_kb);
    push_opt(row, "vmhwm_kb_max", r.vmhwm_kb_max);
    push_d(row, "phase_peaks", if r.phase_peaks { "per-phase" } else { "process" });
    push_opt(row, "vm_peak_kb", r.vm_peak_kb);
}

/// A row for a run that did not complete (a panic or a cap), with the
/// settings columns and the reason.
pub(crate) fn row_of_end(end: &GridEnd) -> Row {
    let mut row = Row::new();
    match end {
        GridEnd::Ok(r) => return row_of(r),
        GridEnd::Panicked {
            fixture,
            config,
            payload,
        } => {
            settings_columns(fixture, config, &mut row);
            push_d(&mut row, "ended", "panicked");
            push_d(&mut row, "payload", payload);
        }
        GridEnd::Capped {
            fixture,
            config,
            after,
        } => {
            settings_columns(fixture, config, &mut row);
            push_d(&mut row, "ended", "capped");
            push_d(&mut row, "cap_ms", after.as_millis());
        }
    }
    row
}

// --- copied from eval.rs: schema 8 header ---
/// Bumped whenever a column is added or `GridConfig::label()`'s format
/// changes (round 03 m1: the tester's pinning test ties `LABEL_PIN` and
/// `header()` to this constant).
/// `P5-CFCFG` F5: schema 3 adds the five complete-first columns after
/// `witnesses` (`admissions`, `evictions`, `readmissions`,
/// `wall_ms_at_first_report`, `vmhwm_kb_at_first_report`); a schema-2 store is
/// refused as any other schema, without override.
/// `COMPACT-INDEX` §5.1 item 5 (tester F1): schema 4 adds the seventeen
/// columns after `flat_wall_time_ms` (`impl_distinct_summaries`, `index_kind`,
/// `impl_phase_wall_ms`, and the bucket index's fourteen); the label at the
/// defaults is unchanged (`LABEL_PIN`), so every key of a schema-3 store is
/// still the key the driver derives, but a schema-3 store is refused by the
/// driver as any other schema (the scripts read it; `compact-1` is schema 4).
/// `COMPACT-INDEX` phase 2 (D1, D4; P2-frozen §1–§2): schema 5 replaces
/// `sig_bytes` by `sig_bytes_est` and adds `signatures_seen`, `sig_tests`,
/// `sig_aliases` (P3), `coordinates_compared`, and the three columns of items 4–5
/// (`inverted_used`, `inverted_words`, `trie_nodes_visited`), which only a
/// row with `bucket` other than the scan fills; the label at the defaults is
/// unchanged.
/// `SVERIFY-P` I4-2: schema 6 appends the forty columns of the parallel
/// stateful engine's record after `memo_clears` (the three phase peaks and
/// `vmhwm_kb_max`, `phase_peaks`, `vm_peak_kb`, the per-side counts, tasks,
/// flushes and lock timers, the conservation terms, `exact_hits`, the
/// uncovered counts and the stop fields); the label at the defaults is
/// unchanged (`LABEL_PIN`); a schema-5 store is refused as any other.
/// `SVERIFY-P` P-S: schema 7 appends the parallel stateless engine's eleven
/// columns after `spawned_at_stop`; the label at the defaults is unchanged;
/// a schema-6 store is refused as any other.
/// `SVERIFY-P` V-C (VC-0): schema 8 appends `cpu_user_ms` and `cpu_sys_ms`
/// after `watch_probes` and fills `impl_complete`/`impl_blocked` on the
/// CFirstP row, whose `impl_phase_wall_ms` is blank above one thread (Q14 a);
/// the label at the defaults is unchanged; a schema-7 store is refused as any
/// other.
pub(crate) const SCHEMA_VERSION: u32 = 8;

/// `GridConfig::new(GridEngine::Enumerator).label()` at this schema version.
pub(crate) const LABEL_PIN: &str =
    "Enumerator/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep";

/// The runner's own columns, in order, before `row_of`'s (H7).
pub(crate) const RUNNER_COLUMNS: &[&str] = &[
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
pub(crate) const ROW_OF_COLUMNS: &[&str] = &[
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
    "admissions",
    "evictions",
    "readmissions",
    "wall_ms_at_first_report",
    "vmhwm_kb_at_first_report",
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
    // `COMPACT-INDEX` §5.1 item 5 (frozen §7).
    "impl_distinct_summaries",
    "index_kind",
    "impl_phase_wall_ms",
    "antichain_effective",
    "entries",
    "buckets",
    "bucket_max",
    "admitted",
    "duplicates",
    "antichain_dropped_new",
    "antichain_dropped_old",
    "insert_tests",
    "summary_bytes",
    "sig_bytes_est",
    "signatures_seen",
    "sig_tests",
    "sig_aliases",
    "coordinates_compared",
    "inverted_used",
    "inverted_words",
    "trie_nodes_visited",
    "memo_on",
    "memo_entries",
    "memo_clears",
    // `SVERIFY-P` I4-2 (schema 6): the parallel stateful engine's record.
    "threads",
    "flush_entries",
    "iterations_until_split",
    "warmup",
    "state_batch_size",
    "freeze_wall_time_ms",
    "spec_vmhwm_kb",
    "freeze_vmhwm_kb",
    "impl_vmhwm_kb",
    "vmhwm_kb_max",
    "phase_peaks",
    "vm_peak_kb",
    "spec_complete",
    "spec_blocked",
    "impl_complete",
    "impl_blocked",
    "spec_tasks",
    "impl_tasks",
    "spec_tasks_nonempty",
    "impl_tasks_nonempty",
    "spec_flushes",
    "impl_flushes",
    "spec_merge_lock_held_ms",
    "spec_merge_lock_wait_ms",
    "impl_merge_lock_held_ms",
    "impl_merge_lock_wait_ms",
    "spec_flush_entries",
    "spec_worker_duplicates",
    "spec_merge_duplicates",
    "impl_seen_flush_entries",
    "impl_seen_worker_duplicates",
    "exact_hits",
    "uncovered_distinct",
    "uncovered_multiplicity",
    "uncovered_flush_entries",
    "uncovered_worker_duplicates",
    "uncovered_merge_duplicates",
    "stopped_early",
    "uncovered_at_stop",
    "spawned_at_stop",
    // `SVERIFY-P` P-S (schema 7): the parallel stateless engine's own.
    "redundant_sweeps",
    "unadmitted_after_cancel",
    "unprobed_after_cancel",
    "signature_syncs",
    "admission_lock_held_ms",
    "admission_lock_wait_ms",
    "sweeps_in_warmup",
    "sweeps_in_root_loop",
    "sweeps_in_tasks",
    "sweeps_abandoned",
    "watch_probes",
    // `SVERIFY-P` V-C (schema 8): the child process's CPU time (VC-0).
    "cpu_user_ms",
    "cpu_sys_ms",
];

/// The declared header: the runner's columns, then every `row_of` column.
pub(crate) fn header() -> Vec<&'static str> {
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

// --- copied from eval.rs: RunKind, Tier ---
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RunKind {
    Timed,
    Profiling,
    Baseline,
    Contract,
}

impl RunKind {
    pub(crate) fn name(self) -> &'static str {
        match self {
            RunKind::Timed => "timed",
            RunKind::Profiling => "profiling",
            RunKind::Baseline => "baseline",
            RunKind::Contract => "contract",
        }
    }

    pub(crate) fn parse(s: &str) -> Option<RunKind> {
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
    pub(crate) fn keep_graphs(self) -> bool {
        matches!(self, RunKind::Profiling | RunKind::Contract)
    }
}

/// A tier (H5): a wall limit and a memory limit, named.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Tier {
    pub(crate) name: String,
    pub(crate) wall: Duration,
    pub(crate) mem_kb: u64,
}

impl Tier {
    /// 600 s (D2) and 4 GiB.
    pub(crate) fn default_tier() -> Tier {
        Tier {
            name: "default".to_owned(),
            wall: Duration::from_secs(600),
            mem_kb: 4 * 1024 * 1024,
        }
    }

    /// 3600 s and 4 GiB.
    pub(crate) fn extension() -> Tier {
        Tier {
            name: "extension".to_owned(),
            wall: Duration::from_secs(3600),
            mem_kb: 4 * 1024 * 1024,
        }
    }
}

// --- copied from eval.rs: RowSpec, key_of ---
/// One row to run.
#[derive(Clone, Debug)]
pub(crate) struct RowSpec {
    pub(crate) fixture: String,
    pub(crate) config: GridConfig,
    pub(crate) rep: u32,
    pub(crate) tier: Tier,
    pub(crate) run_kind: RunKind,
    pub(crate) family: String,
    /// A label of the knob values (`k=2,enc=1`).
    pub(crate) knobs: String,
    pub(crate) k: [Option<i64>; 4],
    /// `conforming`, `violating`, `mutant:<id>`, `control:<id>`.
    pub(crate) variant: String,
    /// The matched conforming twin's row key (RQ2), or empty.
    pub(crate) twin_key: String,
}

impl RowSpec {
    pub(crate) fn key(&self, profile: &str) -> String {
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
    pub(crate) fn rep_set(&self) -> String {
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
pub(crate) fn key_of(
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

// --- copied from eval.rs: parse_label and helpers ---
/// The inverse of `GridConfig::label()` (every field prints as `Debug`).
pub(crate) fn parse_label(label: &str) -> Option<GridConfig> {
    let mut p: Vec<&str> = label.split('/').collect();
    // `COMPACT-INDEX` phase 2 D6: a trailing `distinct=on` is the knob on;
    // it is stripped before the fields below are counted.
    let impl_distinct = p.last() == Some(&"distinct=on");
    if impl_distinct {
        p.pop();
    }
    // Phase 2 item 7: a trailing `bucket=…` (printed under `Compact` only;
    // the round trip below refuses it anywhere else).
    let bucket = match p.last().copied().and_then(|f| f.strip_prefix("bucket=")) {
        Some(b) => {
            let k = parse_bucket(b)?;
            p.pop();
            k
        }
        None => BucketKind::Scan,
    };
    // `SVERIFY-P` I4-1: the two partitioned engines' trailing fields, taken
    // off before the counts below — `flush=<F>` (`SverifyP`, off-default
    // only), then `threads=<t>`; `ExploreP` is the eleven-field form plus
    // `threads=`. The round trip at the end refuses a non-canonical spelling
    // (`threads=04`, `flush=4096`) as it refuses every other.
    let partitioned = matches!(
        p.first().copied(),
        Some("SverifyP") | Some("ExploreP") | Some("CFirstP")
    );
    let (threads, flush_entries) = if partitioned {
        let flush = match p.last().copied().and_then(|f| f.strip_prefix("flush=")) {
            Some(f) if p[0] == "SverifyP" => {
                let v: usize = f.parse().ok()?;
                // I4-1: `flush=0` is no configuration (the engine refuses it);
                // `flush=4096`, the default printed, fails the round trip.
                if v == 0 {
                    return None;
                }
                p.pop();
                v
            }
            Some(_) => return None,
            None => 4096,
        };
        let t: usize = p.last().copied()?.strip_prefix("threads=")?.parse().ok()?;
        // I4-1: `threads=0` is no configuration (gate 3, L1).
        if t == 0 {
            return None;
        }
        p.pop();
        (t, flush)
    } else {
        (1, 4096)
    };
    // `P5-CFCFG` F4: eleven fields (the campaign's form: the unbounded cache,
    // sweeps not quiet) or thirteen (`w=…`, `quiet=…`); `COMPACT-INDEX`
    // frozen §8: sixteen (`index=compact`, `anti=…`, `pmemo=…`); `SVERIFY-P`
    // I2b-7: fourteen (`index=set`); any other count fails.
    if p.len() != 11 && p.len() != 13 && p.len() != 14 && p.len() != 16 {
        return None;
    }
    fn flag(s: &str, name: &str) -> Option<bool> {
        s.strip_prefix(name)?.strip_prefix('=')?.parse().ok()
    }
    let (witness_cache, quiet) = if p.len() >= 13 {
        (parse_capacity(p[11])?, flag(p[12], "quiet")?)
    } else {
        (Capacity::Unbounded, false)
    };
    let (index, antichain, probe_memo) = if p.len() == 16 {
        if p[13] != "index=compact" {
            return None;
        }
        (
            IndexKind::Compact,
            flag(p[14], "anti")?,
            flag(p[15], "pmemo")?,
        )
    } else if p.len() == 14 {
        // `SVERIFY-P` I2b-7: `index=set`; the knobs it does not print are not
        // read under `Set` and take `GridConfig::new`'s values, as under
        // `Current` below (`MIN-ENGINES` E7a: the memo's default is off, so
        // `pmemo` reads `false` here — gate 3's F-1).
        if p[13] != "index=set" {
            return None;
        }
        (IndexKind::Set, true, false)
    } else {
        (IndexKind::Current, true, false)
    };
    let engine = parse_engine(p[0])?;
    let precheck = flag(p[7], "precheck")?;
    // `MIN-ENGINES` E1-2: `Plain` is the key of a configuration no run of which
    // reads the selector (the stateful engine; the stateless engine with its
    // precheck off); a selector name there is a legacy key — parsed as a
    // stored identity with its own spelling kept (`legacy_selector`), refused
    // by every execution path; `Plain` anywhere else is no key (a stateless
    // row with the precheck on reads the selector in that run and keeps its
    // name).
    let plain_engine = match engine {
        GridEngine::Stateful => true,
        // `SVERIFY-P` I4-1: the twin mode is plain-scheduled (I3-2).
        GridEngine::SverifyP => true,
        // `SVERIFY-P` P-S: likewise.
        GridEngine::CFirstP => true,
        GridEngine::CompleteFirst => !precheck,
        _ => false,
    };
    let (selector, legacy_selector) = match (p[1], plain_engine) {
        ("Plain", true) => (Selector::Ltr, None),
        ("Plain", false) => return None,
        (s, true) => {
            let sel = parse_selector(s)?;
            (sel, Some(sel))
        }
        (s, false) => (parse_selector(s)?, None),
    };
    let parsed = GridConfig {
        witness_cache,
        quiet,
        // `MIN-ENGINES` E6: not in the label (off is the default).
        all_reports: false,
        sweep_record: false,
        index,
        antichain,
        probe_memo,
        impl_distinct,
        bucket,
        engine,
        selector,
        legacy_selector,
        stop_at_first_report: flag(p[2], "stop")?,
        gated_mode: parse_gated_mode(p[3])?,
        gate_policy: parse_policy(p[4])?,
        memo: flag(p[5], "memo")?,
        budget: parse_budget(p[6])?,
        precheck,
        instrumented: flag(p[8], "instr")?,
        early_error_cut: flag(p[9], "cut")?,
        completion_cover: parse_cover(p[10].strip_prefix("cover=")?)?,
        threads,
        flush_entries,
        // `SVERIFY-P` I4-3: a measurement mode, never in a key.
        phase_peaks: false,
    };
    // `SVERIFY-P` I2b-7, `MIN-ENGINES` E7b: `index=set` is the key of the
    // engines that read the index (the others do not), never with Flat (F1).
    // `SVERIFY-P` I4-1: SVerify-P has no other index, so its key is the
    // `index=set` form and no other.
    if parsed.index == IndexKind::Set
        && (!matches!(
            parsed.engine,
            GridEngine::Stateful
                | GridEngine::CompleteFirst
                | GridEngine::SverifyP
                | GridEngine::CFirstP
        ) || parsed.completion_cover == CompletionCover::Flat)
    {
        return None;
    }
    if matches!(parsed.engine, GridEngine::SverifyP | GridEngine::CFirstP)
        && parsed.index != IndexKind::Set
    {
        return None;
    }
    // `P5-CFCFG` F4 (gate 4 n1): only `label()`'s own spelling parses — the
    // thirteen-field form at the defaults, `w=08`, `w=+8` and the like are
    // refused, so a stored key is always the key the driver derives.
    (parsed.label() == label).then_some(parsed)
}

/// Phase 2 item 7: `trie` or `inverted:<t>`.
fn parse_bucket(s: &str) -> Option<BucketKind> {
    if s == "trie" {
        return Some(BucketKind::Trie);
    }
    Some(BucketKind::Inverted(
        s.strip_prefix("inverted:")?.parse().ok()?,
    ))
}

pub(crate) fn parse_engine(s: &str) -> Option<GridEngine> {
    Some(match s {
        "Enumerator" => GridEngine::Enumerator,
        "Stateful" => GridEngine::Stateful,
        "CompleteFirst" => GridEngine::CompleteFirst,
        "Gated" => GridEngine::Gated,
        "Verify" => GridEngine::Verify,
        "Explore" => GridEngine::Explore,
        "SverifyP" => GridEngine::SverifyP,
        "ExploreP" => GridEngine::ExploreP,
        "CFirstP" => GridEngine::CFirstP,
        _ => return None,
    })
}

pub(crate) fn parse_selector(s: &str) -> Option<Selector> {
    Some(match s {
        "Ltr" => Selector::Ltr,
        "FewestEvents" => Selector::FewestEvents,
        "Reverse" => Selector::Reverse,
        _ => return None,
    })
}

pub(crate) fn parse_gated_mode(s: &str) -> Option<GatedMode> {
    Some(match s {
        "Exhaustive" => GatedMode::Exhaustive,
        "FirstFailure" => GatedMode::FirstFailure,
        _ => return None,
    })
}

pub(crate) fn parse_policy(s: &str) -> Option<GatePolicy> {
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

pub(crate) fn parse_budget(s: &str) -> Option<Budget> {
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

pub(crate) fn parse_cover(s: &str) -> Option<CompletionCover> {
    Some(match s {
        "Sweep" => CompletionCover::Sweep,
        "Flat" => CompletionCover::Flat,
        _ => return None,
    })
}

// --- copied from eval.rs: call_with ---
/// The engine call, as `grid.rs::call` but with `keep_graphs` a parameter
/// (round 02 M2: the grid's `true` retains every graph). `H`: the `Explore`
/// arm writes nothing; [`xbase_line`] builds its split line (`P5-XBASE` F2).
fn call_with(subject: &Subject, config: &GridConfig, keep_graphs: bool) -> GridRaw {
    let imp = subject.implementation.clone();
    let spec = subject.specification.clone();
    match config.engine {
        GridEngine::Enumerator => {
            let mut engine_config = subject.config.clone();
            engine_config.selector = config.selector;
            GridRaw::Enumerator(verify_conformance_with_opts(
                engine_config,
                imp,
                spec,
                subject.visible.clone(),
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
            let cc = config.conf_config(subject);
            GridRaw::Stateful(stateful::run_with(&cc, &imp, &spec, keep_graphs))
        }
        GridEngine::CompleteFirst => {
            let cc = config.conf_config(subject);
            if config.precheck {
                GridRaw::Verdict(cfirst::run(cc, imp, spec))
            } else {
                GridRaw::CompleteFirst(cfirst::run_with(&cc, &imp, &spec, keep_graphs))
            }
        }
        GridEngine::Gated => {
            let cc = config.conf_config(subject);
            if config.precheck {
                GridRaw::Verdict(gated::run(cc, imp, spec))
            } else {
                GridRaw::Gated(gated::run_with(&cc, &imp, &spec, keep_graphs))
            }
        }
        GridEngine::Verify => {
            let cc = config.conf_config(subject);
            GridRaw::Verdict(verify(cc, move || imp(), move || spec()))
        }
        GridEngine::Explore => {
            // `P5-XBASE` F1: the subject's own `Config` with the one field
            // conformance forces (`Must::enable_conformance`): no stop at an
            // error. The specification closure is never called.
            let mut cfg = subject.config.clone();
            cfg.keep_going_after_error = true;
            let s = crate::verify(cfg, move || imp());
            GridRaw::Explore(s)
        }
        // `SVERIFY-P` I4: as `call`'s arms.
        GridEngine::SverifyP => {
            let cc = config.conf_config(subject);
            let outcome = crate::conformance::sverify_p::run_with(&cc, &imp, &spec);
            GridRaw::SverifyP(Box::new(SverifyPRun {
                outcome,
                vm_peak_kb: vm_peak_kb(),
                warmup: subject.config.warmup,
                state_batch_size: subject.config.state_batch_size,
            }))
        }
        GridEngine::ExploreP => GridRaw::ExploreP(Box::new(
            explore_partitioned(subject, config),
        )),
        // `SVERIFY-P` P-S: as `call`'s arm.
        GridEngine::CFirstP => {
            let cc = config.conf_config(subject);
            let outcome = crate::conformance::cfirst_p::run_with(&cc, &imp, &spec);
            GridRaw::CFirstP(Box::new(CFirstPRun {
                outcome,
                vm_peak_kb: vm_peak_kb(),
            }))
        }
    }
}

// --- copied from eval.rs: run_row_in_process ---
/// `run_grid(fixture, config, None)` with `keep_graphs` chosen by the run
/// kind: the `Flat` refusal, the run thread with the grid's stack, the
/// `VmHWM` read **before** any rendering (round 03 m3), the panic payload.
pub(crate) fn run_row_in_process(
    subject: &Subject,
    config: &GridConfig,
    keep_graphs: bool,
) -> GridEnd {
    // `MIN-ENGINES` E1-2: a legacy key names a scheduling the stateful and
    // stateless engines no longer run; it is a stored identity, never a run.
    if let Some(s) = config.legacy_selector {
        return GridEnd::Panicked {
            fixture: subject.name.clone(),
            config: config.clone(),
            payload: format!(
                "refused: the key's selector field `{s:?}` is a legacy spelling for engine {:?}; \
                 the stateful and stateless engines schedule by plain Must (MIN-ENGINES E1) and \
                 their key prints `Plain` — rerun the row under its `Plain` key",
                config.engine
            ),
        };
    }
    if config.completion_cover == CompletionCover::Flat {
        let bad_engine = !matches!(config.engine, GridEngine::CompleteFirst | GridEngine::Gated);
        if bad_engine || !config.precheck {
            return GridEnd::Panicked {
                fixture: subject.name.clone(),
                config: config.clone(),
                payload: format!(
                    "refused: completion_cover(Flat) needs precheck = true and engine in \
                     {{CompleteFirst, Gated}} (got precheck = {}, engine = {:?})",
                    config.precheck, config.engine
                ),
            };
        }
    }
    let tainted_at_start = tainted();
    let stack_mib = stack_mib_for(config);
    let (tx, rx) = mpsc::channel();
    let f = subject.clone();
    let c = config.clone();
    let handle = std::thread::Builder::new()
        .name(format!("eval:{}", subject.name))
        .stack_size(stack_mib * 1024 * 1024)
        .spawn(move || {
            let before = vm_hwm_kb();
            let started = Instant::now();
            let outcome = catch_unwind(AssertUnwindSafe(|| call_with(&f, &c, keep_graphs)));
            let wall = started.elapsed();
            // `SVERIFY-P` I4-3 R4: the engine's peak folded in on a reset run.
            let after = match &outcome {
                Ok(raw) => after_reading(raw, vm_hwm_kb()),
                Err(_) => vm_hwm_kb(),
            };
            let _ = tx.send((outcome, wall, before, after));
        })
        .expect("conformance: could not spawn the eval run thread");
    let received = rx.recv();
    let _ = handle.join();
    match received {
        Err(_) => GridEnd::Panicked {
            fixture: subject.name.clone(),
            config: config.clone(),
            payload: "run thread vanished without sending its outcome".to_owned(),
        },
        Ok((Ok(raw), wall, before, after)) => GridEnd::Ok(GridResult {
            fixture: subject.name.clone(),
            config: config.clone(),
            raw,
            wall,
            vm_hwm_kb: (before, after),
            tainted_at_start,
            stack_mib,
        }),
        Ok((Err(payload), _, _, _)) => GridEnd::Panicked {
            fixture: subject.name.clone(),
            config: config.clone(),
            payload: panic_text(payload),
        },
    }
}

// =========================================================================
// Rows (H7)
// =========================================================================

// --- copied from eval.rs: RowMeta .. csv_line ---
/// What the runner knows about a row besides the engine's outcome.
#[derive(Clone, Debug, Default)]
pub(crate) struct RowMeta {
    pub(crate) key: String,
    pub(crate) run_kind: String,
    pub(crate) profile: String,
    pub(crate) commit: String,
    pub(crate) rep: String,
    pub(crate) tier: String,
    pub(crate) end_class: String,
    pub(crate) censor_via: String,
    pub(crate) censored: bool,
    pub(crate) proc_wall_ms: String,
    pub(crate) pid: String,
    pub(crate) rss_sampled_hwm_kb: String,
    /// The child's run directory (stdout, stderr), relative to the store.
    pub(crate) run_dir: String,
    pub(crate) diag_bytes_est: String,
    pub(crate) family: String,
    pub(crate) knobs: String,
    pub(crate) k: [Option<i64>; 4],
    pub(crate) variant: String,
    pub(crate) twin_key: String,
    pub(crate) comm_model: String,
    /// `SVERIFY-P` V-C (VC-0): the parent's CPU reading for a row the child
    /// did not record (the reading at the kill, or the last sample on a
    /// crash); blank otherwise. A child's record carries its own.
    pub(crate) cpu_user_ms: String,
    pub(crate) cpu_sys_ms: String,
}

impl RowMeta {
    pub(crate) fn of(spec: &RowSpec, profile: &str, commit: &str, comm_model: &str) -> RowMeta {
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
pub(crate) fn eval_row_of(end: &GridEnd, meta: &RowMeta) -> Row {
    let mut inner = verdict_counter_fill(end, row_of_end(end));
    // E21 (the calibration pilot): `row_of`'s enumerator arm renders one record
    // per `Cover` call in `per_cover_detail` (2 MB at `naive-self(7, ·)`); a
    // timed row carries lightweight counters only (plan §0), so the column is
    // blank there and kept on profiling and baseline rows.
    if meta.run_kind == "timed" {
        for (k, v) in inner.iter_mut() {
            if *k == "per_cover_detail" {
                v.clear();
            }
        }
    }
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
    // `P5-CFCFG` F1 (gate 4 M2; E-CF-8): the column follows the knob on
    // complete-first rows — `off` under `Zero`, `bounded(n)` under
    // `Bounded(n)`, `on` under `Unbounded`; the gated checker's cache is `on`.
    p(
        "cache",
        match (config.engine, config.witness_cache) {
            (GridEngine::CompleteFirst, Capacity::Zero) => "off".to_owned(),
            (GridEngine::CompleteFirst, Capacity::Bounded(n)) => format!("bounded({n})"),
            _ if sweeping => "on".to_owned(),
            _ => "n/a".to_owned(),
        },
    );
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
    p("cpu_user_ms", meta.cpu_user_ms.clone());
    p("cpu_sys_ms", meta.cpu_sys_ms.clone());
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
pub(crate) fn record_of(row: &Row) -> Vec<String> {
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
pub(crate) fn escape_value(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

pub(crate) fn unescape_value(s: &str) -> String {
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

pub(crate) fn csv_line(cells: &[String]) -> String {
    let quoted: Vec<String> = cells
        .iter()
        .map(|c| format!("\"{}\"", escape_value(c).replace('"', "\"\"")))
        .collect();
    quoted.join(",")
}

// --- copied from eval.rs: profile_name ---
pub(crate) fn profile_name() -> &'static str {
    if cfg!(debug_assertions) {
        "test"
    } else {
        "release"
    }
}

// --- copied from eval.rs: row_from_json, SENTINEL ---
pub(crate) fn row_from_json(s: &str) -> Option<RowSpec> {
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
    })
}

pub(crate) const SENTINEL: &str = "EVALROW\t";

// --- copied from eval.rs: cpu readings ---
/// `SVERIFY-P` V-C (VC-0): user and system CPU time in milliseconds from a
/// `/proc/<pid>/stat` line — fields 14 (`utime`) and 15 (`stime`), counted
/// after the last `)` so a `comm` holding spaces or `)` cannot shift them;
/// ticks at Linux's `USER_HZ` of 100 per second (10 ms each).
pub(crate) fn cpu_ms_of_stat(stat: &str) -> Option<(u64, u64)> {
    let rest = &stat[stat.rfind(')')? + 1..];
    let mut fields = rest.split_whitespace().skip(11);
    let utime: u64 = fields.next()?.parse().ok()?;
    let stime: u64 = fields.next()?.parse().ok()?;
    Some((utime * 10, stime * 10))
}

/// A process's CPU time (all its threads), or `None` if it cannot be read.
fn cpu_ms_of_pid(pid: u32) -> Option<(u64, u64)> {
    cpu_ms_of_stat(&fs::read_to_string(format!("/proc/{pid}/stat")).ok()?)
}

/// The two cells of a reading: numbers, or blank when there was none.
pub(crate) fn cpu_cells(reading: Option<(u64, u64)>) -> (String, String) {
    reading.map_or((String::new(), String::new()), |(u, s)| {
        (u.to_string(), s.to_string())
    })
}

// --- copied from eval.rs: verdict_counter_fill ---
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
    if o.gated_counters().is_some() {
        // the paper's `L` (`row_of` renders it with `Display` on the `run_with` routes)
        push(
            &mut inner,
            "max_paper_events",
            o.counters().max_paper_events_per_execution.to_string(),
        );
    } else if o.cfirst_counters().is_some() {
        // `MIN-ENGINES` E3: the complete-first engine counts `L` only with
        // `ConfConfig::paper_events` on, which no grid route sets, so the
        // column is blank here as `row_of` leaves it on the `run_with` route
        // (`push_opt` of `None`); the public counter would read 0.
        push(&mut inner, "max_paper_events", String::new());
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
        // `MIN-ENGINES` E7a: blank unless the row's configuration records the
        // sweeps, as `row_of` leaves it on the `run_with` route (gate 3's F-2).
        if r.config.sweep_record {
            push(&mut inner, "sweep_sizes", format!("{:?}", c.sweep_sizes));
        } else {
            push(&mut inner, "sweep_sizes", String::new());
        }
        push(&mut inner, "sweep_graphs", c.sweep_graphs.to_string());
        push(
            &mut inner,
            "sweep_graphs_max",
            c.sweep_graphs_max.to_string(),
        );
        push(&mut inner, "witnesses", c.witnesses.to_string());
        push(&mut inner, "admissions", c.admissions.to_string());
        push(&mut inner, "evictions", c.evictions.to_string());
        push(&mut inner, "readmissions", c.readmissions.to_string());
        push(
            &mut inner,
            "wall_ms_at_first_report",
            c.wall_ms_at_first_report
                .map(|v| v.to_string())
                .unwrap_or_default(),
        );
        push(
            &mut inner,
            "vmhwm_kb_at_first_report",
            c.vmhwm_kb_at_first_report
                .map(|v| v.to_string())
                .unwrap_or_default(),
        );
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
