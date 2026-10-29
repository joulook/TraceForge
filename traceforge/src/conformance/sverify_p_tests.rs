//! `SVERIFY-P` I3, gate 3: the tester's tests of SVerify-P on the minimal core, derived first in
//! `log/dev/SVERIFY-P.derived-i3.md` (d85a9d51) against criteria rev 2.3. The item numbers below
//! are that derivation's. Every engine run takes `SERIAL`: the engine's test hooks are
//! process-wide, and one engine run at a time keeps the machine quiet.
//!
//! Heavy tests are `#[ignore]`d and run one process each, selected by `P_CELL` (a fixture) and
//! `P_THREADS` (a comma list), under the resource rule.

use std::collections::{BTreeMap, BTreeSet};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::conformance::compact::{CompactSummary, Covers, OrdCounts, SetIndex, SigLookup};
use crate::conformance::compact_tests::{PILOT_NAMES, SIZE2_CELLS, SLICE_CELLS};
use crate::conformance::config::{ConfBuilder, ConfConfig, Engine, IndexKind, ScopeField};
use crate::conformance::ctx::{CompletionSink, ConfCtx, ConfMode, SinkVerdict};
use crate::conformance::eval::{fixture_by_name, x1_config};
use crate::conformance::grid::{Fixture, GridEngine, Prog};
use crate::conformance::report::{ConfError, ConfVerdict, SearchEnd};
use crate::conformance::selector::Selector;
use crate::conformance::sig::Sig;
use crate::conformance::stateful::{self, enumerate, EnumRun, StatefulOutcome};
use crate::conformance::sverify_p::{self, SverifyPOutcome};
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::parallel_verify::{verify_partitioned_rayon_with, CancelToken, PartitionHooks};
use crate::{thread, CommunicationModel, Config, ConsType};

// =========================================================================
// Harness
// =========================================================================

/// The measurement lines, to stderr as `compact_tests`' `note!`: S5's criterion 1
/// (`s5_tests::c1_no_user_facing_emission_outside_the_rendering_module`) allows no printing macro
/// under `conformance/` outside its test-only list.
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> std::sync::MutexGuard<'static, ()> {
    SERIAL.lock().unwrap_or_else(|e| e.into_inner())
}

fn fx(name: &str) -> Fixture {
    crate::conformance::grid::mixed_fixtures()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| {
            fixture_by_name(name).unwrap_or_else(|e| panic!("conformance: {name}: {}", e.text()))
        })
}

/// The sequential reference: SVerify-S on `Set`, `impl_distinct` on, every report kept.
fn seq_cc(f: &Fixture, stop: bool) -> ConfConfig {
    let mut cc = x1_config(GridEngine::Stateful, Selector::Ltr)
        .index(IndexKind::Set)
        .impl_distinct(true)
        .stop(stop)
        .conf_config(f);
    cc.all_reports = true;
    cc
}

fn seq(f: &Fixture, stop: bool) -> StatefulOutcome {
    stateful::run_with(&seq_cc(f, stop), &f.implementation, &f.specification, false)
}

/// One SVerify-P configuration.
#[derive(Clone, Copy, Debug)]
struct P {
    t: usize,
    f: usize,
    split: usize,
    warmup: usize,
    stop: bool,
    distinct: bool,
    paper: bool,
}

impl P {
    fn new(t: usize, f: usize, split: usize) -> Self {
        P {
            t,
            f,
            split,
            warmup: if split == 1 { 1 } else { 100 },
            stop: false,
            distinct: true,
            paper: false,
        }
    }
}

fn par_cc(fx: &Fixture, p: &P) -> ConfConfig {
    let mut cc = seq_cc(fx, p.stop);
    cc.engine = Engine::SverifyP;
    cc.threads = p.t;
    cc.flush_entries = p.f;
    cc.impl_distinct = p.distinct;
    cc.paper_events = p.paper;
    cc.config.iterations_until_split = p.split;
    cc.config.warmup = p.warmup;
    cc.config.state_batch_size = 1;
    cc
}

fn par(fx: &Fixture, p: &P) -> SverifyPOutcome {
    sverify_p::run_with(&par_cc(fx, p), &fx.implementation, &fx.specification)
}

type Key = (String, String);

fn key(sig: &Sig, ord: &OrdCounts) -> Key {
    (format!("{sig:?}"), format!("{ord:?}"))
}

/// SVerify-S's uncovered multiset: the summaries of its reports (every report is kept).
fn seq_uncovered(f: &Fixture, o: &StatefulOutcome) -> BTreeMap<Key, usize> {
    let mut m = BTreeMap::new();
    for (g, _) in &o.reports {
        let s = CompactSummary::at_completion(g, &f.visible, "implementation");
        *m.entry(key(&s.sig, &s.ord)).or_default() += 1;
    }
    m
}

fn par_uncovered(o: &SverifyPOutcome) -> BTreeMap<Key, usize> {
    let mut m = BTreeMap::new();
    for (sig, ord, n) in &o.uncovered {
        *m.entry(key(sig, ord)).or_default() += *n;
    }
    m
}

/// I3-10's assertions for one run against the reference; `stop` limits them to what the stop path
/// keeps comparable (I3-6s). Returns the mismatches.
fn compare(f: &Fixture, s: &StatefulOutcome, p: &SverifyPOutcome, stop: bool) -> Vec<String> {
    let mut bad = Vec::new();
    let c = &p.counters;
    let sc = &s.counters;
    macro_rules! eq {
        ($a:expr, $b:expr, $what:expr) => {
            if $a != $b {
                bad.push(format!("{}: {:?} vs {:?}", $what, $a, $b));
            }
        };
    }
    // The specification side (I3-4).
    let ss = s
        .set_index
        .as_ref()
        .expect("conformance: the reference ran on Set")
        .stats();
    let ps = c.spec_set;
    eq!(c.spec_graphs, sc.spec_graphs, "spec_graphs");
    eq!(c.spec_complete + c.spec_blocked, c.spec_graphs, "spec complete + blocked");
    eq!(ps.entries, ss.entries, "spec entries");
    eq!(ps.admitted, ss.admitted, "spec admitted");
    eq!(ps.signatures, ss.signatures, "spec signatures");
    eq!(ps.signatures_seen, ss.signatures_seen, "spec signatures_seen");
    eq!(ps.buckets, ss.buckets, "spec buckets");
    eq!(ps.slot_max, ss.slot_max, "spec slot_max");
    eq!(ps.summary_bytes, ss.summary_bytes, "spec summary_bytes");
    eq!(ps.sig_bytes_est, ss.sig_bytes_est, "spec sig_bytes_est");
    eq!(ps.sig_aliases, 0, "spec sig_aliases (render_hash is None)");
    eq!(c.orders_held, sc.orders_held, "orders_held");
    eq!(
        c.spec_worker_duplicates + c.spec_merge_duplicates,
        ss.duplicates,
        "spec duplicates (worker + merge)"
    );
    eq!(c.spec_flush_entries + c.spec_worker_duplicates, c.spec_graphs, "spec identity 1");
    eq!(ps.entries + c.spec_merge_duplicates, c.spec_flush_entries, "spec identity 2");
    eq!(p.spec_end, SearchEnd::StateSpaceExhausted, "spec_end");
    if c.spec_flushes < c.spec_tasks {
        bad.push(format!("spec flushes {} < tasks {}", c.spec_flushes, c.spec_tasks));
    }
    if stop {
        return bad;
    }
    // The implementation side (I3-6).
    eq!(c.impl_graphs, sc.impl_graphs, "impl_graphs");
    eq!(c.impl_complete + c.impl_blocked, c.impl_graphs, "impl complete + blocked");
    eq!(c.lookups, sc.lookups, "lookups");
    eq!(c.lookups, c.impl_graphs, "lookups = impl_graphs");
    eq!(c.lookups_succeeded, sc.lookups_succeeded, "lookups_succeeded");
    eq!(c.lookups_signature_miss, sc.lookups_signature_miss, "lookups_signature_miss");
    eq!(c.lookups_failed_after_tests, sc.lookups_failed_after_tests, "lookups_failed_after_tests");
    eq!(c.lookups_containment_tested, sc.lookups_containment_tested, "lookups_containment_tested");
    eq!(c.exact_hits, ss.exact_hits, "exact_hits");
    eq!(c.reports, sc.reports, "reports");
    eq!(c.uncovered_multiplicity, sc.reports, "uncovered multiplicity");
    eq!(c.uncovered_distinct, p.uncovered.len(), "uncovered distinct");
    eq!(par_uncovered(p), seq_uncovered(f, s), "the uncovered multiset");
    eq!(c.impl_distinct_summaries, sc.impl_distinct_summaries, "impl_distinct_summaries");
    eq!(c.uncovered_flush_entries + c.uncovered_worker_duplicates, c.reports, "uncovered identity 1");
    eq!(
        c.uncovered_distinct + c.uncovered_merge_duplicates,
        c.uncovered_flush_entries,
        "uncovered identity 2"
    );
    if let Some(st) = c.impl_set {
        eq!(c.impl_seen_flush_entries + c.impl_seen_worker_duplicates, c.impl_graphs, "seen identity 1");
        eq!(st.entries + st.duplicates, c.impl_seen_flush_entries, "seen identity 2");
    }
    eq!(
        c.wall_ms_at_first_report.is_some(),
        c.uncovered_multiplicity >= 1,
        "wall_ms_at_first_report Some iff a report"
    );
    eq!(
        c.vmhwm_kb_at_first_report.is_some(),
        c.uncovered_multiplicity >= 1,
        "vmhwm_kb_at_first_report Some iff a report"
    );
    if let Some(w) = c.wall_ms_at_first_report {
        if w > c.impl_wall_time_ms {
            bad.push(format!("first report at {w} ms > impl wall {} ms", c.impl_wall_time_ms));
        }
    }
    eq!(p.impl_end, SearchEnd::StateSpaceExhausted, "impl_end");
    eq!(c.stopped_early, false, "stopped_early");
    eq!(c.spawned_at_stop, 0, "spawned_at_stop");
    if c.impl_flushes < c.impl_tasks {
        bad.push(format!("impl flushes {} < tasks {}", c.impl_flushes, c.impl_tasks));
    }
    bad
}

fn env_list(var: &str, default: &[usize]) -> Vec<usize> {
    std::env::var(var)
        .map(|v| v.split(',').map(|x| x.trim().parse().expect("conformance: a number")).collect())
        .unwrap_or_else(|_| default.to_vec())
}

fn panic_text(e: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = e.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = e.downcast_ref::<&str>() {
        (*s).to_owned()
    } else {
        "<non-string payload>".to_owned()
    }
}

fn panic_of<R>(f: impl FnOnce() -> R) -> Option<String> {
    catch_unwind(AssertUnwindSafe(f)).err().map(|e| panic_text(&e))
}

/// Every completion's compact summary of one side, in the sequential exploration's order.
fn summaries(f: &Fixture, side: &'static str) -> Vec<CompactSummary> {
    let out = Arc::new(Mutex::new(Vec::new()));
    let sink: CompletionSink = {
        let (out, vis) = (Arc::clone(&out), f.visible.clone());
        Box::new(move |g: &ExecutionGraph, _| {
            out.lock().unwrap().push(CompactSummary::at_completion(g, &vis, side));
            SinkVerdict::Continue
        })
    };
    let cc = seq_cc(f, false);
    let mut config = cc.config.clone();
    config.max_iterations = None;
    let program = if side == "specification" {
        &f.specification
    } else {
        &f.implementation
    };
    enumerate(
        EnumRun {
            config,
            visible: f.visible.clone(),
            mode: ConfMode::Enumerate,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        program,
    );
    let v = std::mem::take(&mut *out.lock().unwrap());
    v
}

fn buf_addr(ord: &OrdCounts) -> usize {
    match ord {
        OrdCounts::U8(v) => v.as_ptr() as usize,
        OrdCounts::U16(v) => v.as_ptr() as usize,
    }
}

fn held_keys(s: &SetIndex) -> BTreeSet<Key> {
    s.entries().map(|(_, sig, _, ord)| key(sig, ord)).collect()
}

/// The invariant list of I2-4 that two insertion orders share.
fn invariants(s: &SetIndex) -> [usize; 7] {
    let st = s.stats();
    [
        st.entries,
        st.signatures,
        st.signatures_seen,
        st.buckets,
        st.slot_max,
        st.summary_bytes,
        st.sig_bytes_est,
    ]
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
}

fn prog<F: Fn() + Send + Sync + 'static>(f: F) -> Prog {
    Arc::new(f)
}

// =========================================================================
// I3-2: the twin mode and the second scope predicate
// =========================================================================

#[test]
fn i3_2_the_twin_mode_is_enumerate_under_its_own_label() {
    let m = ConfMode::EnumeratePartitioned;
    assert_eq!(m.engine_label(), "sverify-p");
    assert!(m.enumerates());
    assert!(m.plain_scheduling());
    // Every site that names `Enumerate` in a match also names the twin; none compares to it
    // alone (the derivation's I3-2 table, as a source check on the gate-2 tree).
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut bad = Vec::new();
    for rel in [
        "must.rs",
        "conformance/ctx.rs",
        "conformance/stateful.rs",
        "conformance/cfirst.rs",
        "conformance/gated.rs",
        "conformance/grid.rs",
        "conformance/mod.rs",
    ] {
        let src = std::fs::read_to_string(dir.join(rel)).expect("conformance: a source file");
        for (i, l) in src.lines().enumerate() {
            let t = l.trim_start();
            if t.starts_with("//") {
                continue;
            }
            if l.contains("== ConfMode::Enumerate") && !l.contains("EnumeratePartitioned") {
                bad.push(format!("{rel}:{}: {}", i + 1, l.trim()));
            }
        }
    }
    let ctx = std::fs::read_to_string(dir.join("conformance/ctx.rs")).unwrap();
    for f in ["fn enumerates", "fn plain_scheduling"] {
        let at = ctx.find(f).expect("conformance: the mode's function");
        let body = &ctx[at..at + ctx[at..].find("\n    }\n").unwrap()];
        if !body.contains("ConfMode::EnumeratePartitioned") {
            bad.push(format!("ctx.rs {f}: no twin"));
        }
    }
    assert!(bad.is_empty(), "conformance: I3-2 sites: {bad:#?}");
}

#[test]
fn i3_2_enable_conformance_partitioned_takes_the_twin_only() {
    let mut c = Config::builder().with_cons_type(ConsType::FIFO).build();
    c.partitioned_parallelization = true;
    let got = panic_of(|| {
        let mut m = Must::new(c.clone(), false);
        let ctx = ConfCtx::gate_disabled(c.clone(), vec![], ConfMode::Enumerate);
        m.enable_conformance_partitioned(ctx);
    });
    assert!(
        got.as_deref().is_some_and(|m| m.contains("partitioned checker's mode only")),
        "conformance: {got:?}"
    );
    // and it admits the twin on a partitioned configuration
    let mut m = Must::new(c.clone(), false);
    m.enable_conformance_partitioned(ConfCtx::gate_disabled(
        c.clone(),
        vec![],
        ConfMode::EnumeratePartitioned,
    ));
}

/// One `Config` field out of scope (s5's constructor, `s5_tests.rs`), in scope otherwise.
fn out_of_scope(field: ScopeField) -> Config {
    use std::collections::HashMap;
    let b = Config::builder().with_cons_type(ConsType::FIFO);
    match field {
        ScopeField::ConsType => b.with_cons_type(ConsType::Mailbox).build(),
        ScopeField::SchedulePolicy => b.with_policy(crate::SchedulePolicy::Arbitrary).build(),
        ScopeField::Mode => {
            let mut c = b.build();
            c.mode = crate::ExplorationMode::Estimation;
            c
        }
        ScopeField::LossyBudget => b.with_lossy(1).build(),
        ScopeField::Parallel => b.with_parallel(true).build(),
        ScopeField::PartitionedParallelization => b.with_partitioned_parallelization(true).build(),
        ScopeField::PredeterminedChoices => {
            let mut m = HashMap::new();
            m.insert("c".to_owned(), vec![vec![true]]);
            b.with_predetermined_choices(m).build()
        }
        ScopeField::PredeterminedGlobalChoices => {
            let mut m = HashMap::new();
            m.insert("c".to_owned(), true);
            b.with_predetermined_global_choices(m).build()
        }
        #[cfg(feature = "symbolic")]
        ScopeField::Symbolic => b.with_symbolic(true).build(),
        #[cfg(not(feature = "symbolic"))]
        ScopeField::Symbolic => b.build(),
    }
}

#[test]
fn i3_2_the_second_predicate_diffed_per_field() {
    let first = |c: &Config| panic_of(|| crate::conformance::assert_config_in_scope(c, "x"));
    let second =
        |c: &Config| panic_of(|| crate::conformance::assert_config_in_scope_partitioned(c, "x"));
    let mut bad = Vec::new();
    for field in ScopeField::checked() {
        let c = out_of_scope(field);
        if field == ScopeField::PartitionedParallelization {
            // The one difference: the first refuses it; the second requires it.
            if first(&c).is_none() {
                bad.push("the first predicate admits partitioned_parallelization".to_owned());
            }
            if let Some(m) = second(&c) {
                bad.push(format!("the second refuses partitioned_parallelization: {m}"));
            }
            let mut off = c.clone();
            off.partitioned_parallelization = false;
            if !second(&off).is_some_and(|m| m.contains("partitioned mode")) {
                bad.push("the second admits a run outside the partitioned mode".to_owned());
            }
            continue;
        }
        let mut p = c.clone();
        p.partitioned_parallelization = true;
        let (a, b) = (first(&c), second(&p));
        match (&a, &b) {
            (Some(x), Some(y)) => {
                let same = x == y;
                let renamed = matches!(field, ScopeField::LossyBudget | ScopeField::Parallel);
                if !same && !renamed {
                    bad.push(format!("{field:?}: messages differ: {x:?} vs {y:?}"));
                }
            }
            (None, None) if matches!(field, ScopeField::Symbolic) && !cfg!(feature = "symbolic") => {}
            _ => bad.push(format!("{field:?}: first {a:?}, second {b:?}")),
        }
    }
    // The second predicate, in scope otherwise, admits the partitioned configuration.
    let mut ok = Config::builder().with_cons_type(ConsType::FIFO).build();
    ok.partitioned_parallelization = true;
    if let Some(m) = second(&ok) {
        bad.push(format!("an in-scope partitioned configuration is refused: {m}"));
    }
    assert!(bad.is_empty(), "conformance: I3-2 predicate diff: {bad:#?}");
}

#[test]
fn i3_2_an_out_of_scope_program_names_sverify_p() {
    let _g = serial();
    let imp = prog(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new()
            .with_comm(CommunicationModel::TotalOrder)
            .build();
        let _w = named("w", move || tx.send_msg(1));
    });
    let spec = prog(|| {
        let _w = named("w", || {});
    });
    let cc = ConfBuilder::new()
        .config(Config::builder().with_cons_type(ConsType::FIFO).build())
        .visible_threads(vec!["w".to_owned()])
        .engine(Engine::SverifyP)
        .threads(2)
        .build()
        .expect("conformance: in scope");
    // A model thread's panic is re-raised by the runtime as "A panic was detected\noriginal
    // panic: <message>" (`runtime/execution.rs`); the original is read, as `stateful_tests` does.
    let want = "sverify-p: `a TotalOrder (mailbox) send` is outside conformance scope";
    for (side, i, s) in [("impl", &imp, &spec), ("spec", &spec, &imp)] {
        let got = panic_of(|| sverify_p::run_with(&cc, i, s)).unwrap_or_default();
        let original = got.split("original panic: ").nth(1).unwrap_or(got.as_str());
        assert!(original.starts_with(want), "conformance: the {side} side's scope panic: {got:?}");
    }
}

// =========================================================================
// I3-3: the hooked runner and the cancel token
// =========================================================================

/// The runner with a counting sink in every exploring `Must` (installed by `on_must`), on one
/// program; `cancel_at` cancels the token from the sink at that completion.
struct Hooked {
    musts: Arc<AtomicUsize>,
    max_iterations_unset: Arc<AtomicUsize>,
    task_ends: Arc<AtomicUsize>,
    completions: Arc<AtomicUsize>,
    at_cancel: Arc<AtomicUsize>,
    cancel_returned: Arc<AtomicU64>,
    token: Arc<CancelToken>,
}

fn hooked_run(
    f: &Fixture,
    program: &Prog,
    t: usize,
    split: usize,
    warmup: usize,
    cancel_at: Option<usize>,
) -> (Hooked, crate::parallel_verify::PartitionedRun) {
    let h = Hooked {
        musts: Arc::new(AtomicUsize::new(0)),
        max_iterations_unset: Arc::new(AtomicUsize::new(0)),
        task_ends: Arc::new(AtomicUsize::new(0)),
        completions: Arc::new(AtomicUsize::new(0)),
        at_cancel: Arc::new(AtomicUsize::new(usize::MAX)),
        cancel_returned: Arc::new(AtomicU64::new(u64::MAX)),
        token: Arc::new(CancelToken::new()),
    };
    let mut conf = f.config.clone();
    conf.partitioned_parallelization = true;
    conf.partitioned_num_threads = Some(t);
    conf.warmup = warmup;
    conf.iterations_until_split = split;
    conf.state_batch_size = 1;
    let visible = f.visible.clone();
    let on_must: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let (musts, unset, completions, at_cancel, ret, token) = (
            Arc::clone(&h.musts),
            Arc::clone(&h.max_iterations_unset),
            Arc::clone(&h.completions),
            Arc::clone(&h.at_cancel),
            Arc::clone(&h.cancel_returned),
            Arc::clone(&h.token),
        );
        Arc::new(move |must: &mut Must| {
            musts.fetch_add(1, Ordering::SeqCst);
            if must.config.max_iterations.is_none() {
                unset.fetch_add(1, Ordering::SeqCst);
            }
            let mut ctx = ConfCtx::gate_disabled(
                must.config.clone(),
                visible.clone(),
                ConfMode::EnumeratePartitioned,
            );
            let (completions, at_cancel, ret, token) = (
                Arc::clone(&completions),
                Arc::clone(&at_cancel),
                Arc::clone(&ret),
                Arc::clone(&token),
            );
            ctx.set_sink(Box::new(move |_, _| {
                let n = completions.fetch_add(1, Ordering::SeqCst) + 1;
                if Some(n) == cancel_at {
                    at_cancel.store(n, Ordering::SeqCst);
                    ret.store(token.cancel(), Ordering::SeqCst);
                }
                SinkVerdict::Continue
            }));
            must.enable_conformance_partitioned(ctx);
        })
    };
    let on_task_end: Arc<dyn Fn(&mut Must) + Send + Sync> = {
        let ends = Arc::clone(&h.task_ends);
        Arc::new(move |_: &mut Must| {
            ends.fetch_add(1, Ordering::SeqCst);
        })
    };
    let hooks = PartitionHooks {
        on_must,
        on_task_end,
        cancel: Arc::clone(&h.token),
    };
    let p = Arc::clone(program);
    let run = verify_partitioned_rayon_with(conf, move || p(), hooks);
    (h, run)
}

/// I3-3 (a), (b), 10-26 15.3: the hooks' counts on A1 correct n2r2's specification (256
/// completions), many small tasks.
#[test]
fn i3_3_the_hooks_count_once() {
    let _g = serial();
    let f = fx("apps/a1/correct/spec/n2r2");
    let mut bad = Vec::new();
    for t in [1, 2, 8] {
        let (h, run) = hooked_run(&f, &f.specification, t, 1, 1, None);
        let musts = h.musts.load(Ordering::SeqCst);
        let ends = h.task_ends.load(Ordering::SeqCst);
        let n = h.completions.load(Ordering::SeqCst);
        if musts > t + 1 || musts == 0 {
            bad.push(format!("t{t}: on_must {musts} (≤ t + 1)"));
        }
        if h.max_iterations_unset.load(Ordering::SeqCst) != musts {
            bad.push(format!("t{t}: max_iterations set at an on_must"));
        }
        if ends != run.tasks_spawned + 1 {
            bad.push(format!("t{t}: on_task_end {ends}, tasks spawned {} + 1", run.tasks_spawned));
        }
        if n != 256 || run.stats.execs + run.stats.block != 256 {
            bad.push(format!(
                "t{t}: sink {n}, execs + block {}",
                run.stats.execs + run.stats.block
            ));
        }
        if run.tasks_spawned < 2 {
            bad.push(format!("t{t}: only {} tasks (the split did not happen)", run.tasks_spawned));
        }
        note!(
            "P13\t{t}\tmusts {musts}\ttask_ends {ends}\ttasks_spawned {}\tworkers_reported {}",
            run.tasks_spawned, run.workers_reported
        );
    }
    assert!(bad.is_empty(), "conformance: I3-3: {bad:#?}");
}

/// I3-3 (e): the source check — the three token reads at the warmup and the two loop heads, the
/// one `total_spawned` increment inside `admit`, and no other way to a spawn.
#[test]
fn i3_3_e_every_spawn_is_admitted_through_the_token() {
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/parallel_verify.rs"),
    )
    .unwrap();
    let code: Vec<&str> = src
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect();
    let code = code.join("\n");
    let mut bad = Vec::new();
    let reads = code.matches("hooks.cancel.is_cancelled()").count();
    if reads != 3 {
        bad.push(format!("{reads} reads of the token, not 3"));
    }
    // 1: before the warmup's exploration
    let warm = code
        .find("must.borrow_mut().config.max_iterations = Some(warmup as u64);")
        .unwrap();
    let after_warm = &code[warm..];
    let r = after_warm.find("hooks.cancel.is_cancelled()").unwrap();
    let e = after_warm.find("explore_with_pool(&must, &f, &root_pool)").unwrap();
    if r > e {
        bad.push("the warmup's exploration is not guarded".to_owned());
    }
    // 2 and 3: the first statement of the root's and a task's loop
    for marker in ["let root_start = Instant::now();", "let explore_result = catch_unwind("] {
        let at = code.find(marker).unwrap();
        let rest = &code[at..];
        let l = rest.find("loop {").unwrap();
        let body = rest[l + "loop {".len()..].trim_start();
        if !body.starts_with("if hooks.cancel.is_cancelled() {") {
            bad.push(format!("the loop after `{marker}` does not read the token first"));
        }
    }
    // 4: the one increment, inside `admit`; one spawn site
    if code.matches("total_spawned.fetch_add").count() != 1 {
        bad.push("more than one total_spawned increment".to_owned());
    }
    if !code.contains(".admit(|| metrics.total_spawned.fetch_add(1, Ordering::Relaxed))") {
        bad.push("the increment is not the closure of admit".to_owned());
    }
    if code.matches("scope.spawn(").count() != 1 {
        bad.push("more than one scope.spawn".to_owned());
    }
    let admit = code.find(".admit(||").unwrap();
    let spawn = code.find("scope.spawn(").unwrap();
    if !(admit < spawn && code[admit..spawn].contains("return;")) {
        bad.push("the spawn does not follow the admission and its refusal".to_owned());
    }
    assert!(bad.is_empty(), "conformance: I3-3 (e): {bad:#?}");
}

/// I3-3 (f)–(h): the controlled race. A test sink cancels the token after 1 000 completions of A3
/// fifo k3q3's implementation at 16 threads, warmup 1, interval 1, batch 1; `cancel`'s return
/// value equals the spawns the runner counted at its return. Probabilistic alone against a plain
/// poll; (e) makes it exact.
#[test]
fn i3_3_f_no_spawn_is_admitted_after_the_cancel() {
    let _g = serial();
    let f = fx("apps/a3/fifo/spec/k3q3");
    let mut bad = Vec::new();
    for round in 0..5 {
        let (h, run) = hooked_run(&f, &f.implementation, 16, 1, 1, Some(1000));
        let ret = h.cancel_returned.load(Ordering::SeqCst);
        let at = h.at_cancel.load(Ordering::SeqCst);
        let n = h.completions.load(Ordering::SeqCst);
        let ends = h.task_ends.load(Ordering::SeqCst);
        if at != 1000 {
            bad.push(format!("round {round}: the sink never cancelled ({n} completions)"));
            continue;
        }
        if ret != run.tasks_spawned as u64 {
            bad.push(format!(
                "round {round}: cancel returned {ret}, the runner spawned {}",
                run.tasks_spawned
            ));
        }
        if n - at > 16 + 16 {
            bad.push(format!("round {round}: {} completions after the cancel", n - at));
        }
        if ends != run.tasks_spawned + 1 {
            bad.push(format!(
                "round {round}: on_task_end {ends}, tasks {} + 1",
                run.tasks_spawned
            ));
        }
        note!(
            "P1F\t{round}\tcancel_returned {ret}\ttasks_spawned {}\tcompletions {n}\tafter {}",
            run.tasks_spawned,
            n - at
        );
    }
    assert!(bad.is_empty(), "conformance: I3-3 (f): {bad:#?}");
}

/// I3-3 (i): the legacy entry, a token nobody cancels — P0's counts (`P_CELL`: `a3` the A3 fifo
/// k3q3 implementation, `le` the 2PC leader n4 implementation, `a4` the A4 hash k3q3m3
/// specification), at `P_THREADS` (default 1, 4, 8, 16).
#[test]
#[ignore]
fn i3_3_i_the_legacy_entry_keeps_p0s_counts() {
    let Ok(cell) = std::env::var("P_CELL") else {
        return;
    };
    let _g = serial();
    let (name, side, want) = match cell.as_str() {
        "a3" => ("apps/a3/fifo/spec/k3q3", "impl", (330_252, 0)),
        "le" => ("2pc/leader/conf/n4", "impl", (1_839_744, 0)),
        "a4" => ("apps/a4/hash/a4a/k3q3m3", "spec", (0, 45_360)),
        _ => panic!("conformance: P_CELL a3 | le | a4"),
    };
    let f = fx(name);
    let program = if side == "impl" { &f.implementation } else { &f.specification };
    let mut bad = Vec::new();
    for t in env_list("P_THREADS", &[1, 4, 8, 16]) {
        let mut conf = f.config.clone();
        conf.keep_going_after_error = true;
        conf.partitioned_parallelization = true;
        conf.partitioned_num_threads = Some(t);
        let p = Arc::clone(program);
        let started = std::time::Instant::now();
        let s = crate::parallel_verify::verify_partitioned_rayon(conf, move || p());
        note!(
            "P0L\t{cell}\t{t}\texecs {}\tblock {}\twall {} ms",
            s.execs,
            s.block,
            started.elapsed().as_millis()
        );
        if (s.execs, s.block) != want {
            bad.push(format!("t{t}: {:?}, P0 {want:?}", (s.execs, s.block)));
        }
    }
    assert!(bad.is_empty(), "conformance: I3-3 (i) {cell}: {bad:#?}");
}

// =========================================================================
// I3-4: the merge by move, the identities
// =========================================================================

/// I3-4 (c), (d), (e) and the counting set, on A1 correct n2r2's specification (256 completions,
/// each of its 64 summaries 4 times), split into two halves.
#[test]
fn i3_4_absorb_by_move_moves_and_equals_one_insertion_order() {
    let _g = serial();
    let f = fx("apps/a1/correct/spec/n2r2");
    let all = summaries(&f, "specification");
    assert_eq!(all.len(), 256);
    // Interleaved (even and odd completions), so both halves hold most summaries: the sequential
    // order's two halves are disjoint subtrees and would share none.
    let h1: Vec<&CompactSummary> = all.iter().step_by(2).collect();
    let h2: Vec<&CompactSummary> = all.iter().skip(1).step_by(2).collect();
    let mut reference = SetIndex::new();
    for s in &all {
        reference.insert(s);
    }
    for counting in [false, true] {
        let mk = || {
            if counting {
                SetIndex::with_multiplicities()
            } else {
                SetIndex::new()
            }
        };
        let (mut a, mut b) = (mk(), mk());
        for s in &h1 {
            a.insert(s);
        }
        for s in &h2 {
            b.insert(s);
        }
        let held_a = held_keys(&a);
        let new_addrs: BTreeSet<usize> = b
            .entries()
            .filter(|(_, sig, _, ord)| !held_a.contains(&key(sig, ord)))
            .map(|(_, _, _, ord)| buf_addr(ord))
            .collect();
        let (dup_a, dup_b) = (a.stats().duplicates, b.stats().duplicates);
        let b_slots = b.stats().signatures_seen;
        let tests_before = a.stats().sig_tests;
        a.absorb_by_move(b);
        let st = a.stats();
        // (e) the invariant list and the held identities equal one insertion order's
        assert_eq!(invariants(&a), invariants(&reference), "conformance: I3-4 (e) counting {counting}");
        assert_eq!(held_keys(&a), held_keys(&reference));
        // the duplicates: A's own + B's own + the merge's = the reference's
        let merge_dups = st.duplicates - dup_a;
        assert_eq!(dup_a + dup_b + merge_dups, reference.stats().duplicates);
        assert!(
            merge_dups > 0 && dup_a > 0,
            "conformance: non-vacuity: A's duplicates {dup_a}, the merge's {merge_dups}"
        );
        // (c) moved, not cloned: every order B brought new keeps its buffer
        let after: BTreeSet<usize> = a.entries().map(|(_, _, _, ord)| buf_addr(ord)).collect();
        assert!(!new_addrs.is_empty());
        assert!(
            new_addrs.is_subset(&after),
            "conformance: I3-4 (c): {} of {} moved orders have new buffers",
            new_addrs.difference(&after).count(),
            new_addrs.len()
        );
        // (d) one resolution per flushed slot
        let a_slots = st.signatures_seen;
        assert!(
            st.sig_tests - tests_before <= b_slots * a_slots,
            "conformance: I3-4 (d): {} Sig tests for {b_slots} slots",
            st.sig_tests - tests_before
        );
        // fresh seqs: 0 .. entries − 1
        let seqs: BTreeSet<u64> = a.entries().map(|(_, _, q, _)| q).collect();
        assert_eq!(seqs, (0..st.entries as u64).collect());
        // the counting set's multiplicities sum to the completions, each the reference's
        if counting {
            let mut want: BTreeMap<Key, u32> = BTreeMap::new();
            for s in &all {
                *want.entry(key(&s.sig, &s.ord)).or_default() += 1;
            }
            let got: BTreeMap<Key, u32> = a
                .entries_counted()
                .map(|(_, _, sig, _, ord, n)| (key(sig, ord), n))
                .collect();
            assert_eq!(got, want, "conformance: I3-6 multiplicities");
        } else {
            assert!(a.entries_counted().all(|(.., n)| n == 1));
        }
    }
}

/// I3-4 (f): the worker set after a flush — the engine re-creates it (decision 9), and a fresh set
/// holds no capacity; every flush site replaces it with `fresh_set` (source).
#[test]
fn i3_4_f_the_worker_set_is_replaced_fresh() {
    assert_eq!(SetIndex::new().orders_capacity_for_test(), 0);
    assert_eq!(SetIndex::with_multiplicities().orders_capacity_for_test(), 0);
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/sverify_p.rs"),
    )
    .unwrap();
    // every flush call takes the set out by `std::mem::replace(.., fresh_set(..))`
    let mut bad = Vec::new();
    let lines: Vec<&str> = src.lines().collect();
    for (i, l) in lines.iter().enumerate() {
        if l.contains("flush_into(") && !l.contains("fn flush_into") {
            let window = lines[i.saturating_sub(3)..i].join("\n");
            if !(window.contains("std::mem::replace(") && window.contains("fresh_set(")) {
                bad.push(format!("sverify_p.rs:{}: {}", i + 1, l.trim()));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: I3-4 (f): a flush without a fresh set: {bad:#?}");
}

/// I3-4's identities on the engine with both kinds of duplicate certain: A1 correct n2r2 at t = 2
/// and 8, warmup 1, interval 1, F = 7.
#[test]
fn i3_4_the_conservation_identities_hold_with_both_duplicates() {
    let _g = serial();
    let f = fx("apps/a1/correct/spec/n2r2");
    let s = seq(&f, false);
    let mut bad = Vec::new();
    for t in [2, 8] {
        let p = P::new(t, 7, 1);
        let o = par(&f, &p);
        let c = &o.counters;
        bad.extend(compare(&f, &s, &o, false).into_iter().map(|b| format!("t{t}: {b}")));
        if c.spec_worker_duplicates == 0 || c.spec_merge_duplicates == 0 {
            bad.push(format!(
                "t{t}: non-vacuity: worker {} merge {}",
                c.spec_worker_duplicates, c.spec_merge_duplicates
            ));
        }
        if (c.spec_graphs, c.spec_set.entries, c.impl_graphs) != (256, 64, 64) {
            bad.push(format!(
                "t{t}: {:?}, the record's (256, 64, 64)",
                (c.spec_graphs, c.spec_set.entries, c.impl_graphs)
            ));
        }
    }
    assert!(bad.is_empty(), "conformance: I3-4: {bad:#?}");
}

// =========================================================================
// I3-5: the freeze
// =========================================================================

/// I3-5 (a)–(c), (f) on one fixture: the store and the table answer every implementation query as
/// the set index does — the id, the `Covers` value with its seq, and the per-query counts — and the
/// freeze moves the orders. Returns the mismatches and the query count.
fn freeze_check(name: &str) -> (Vec<String>, usize) {
    let f = fx(name);
    let spec = summaries(&f, "specification");
    let imp = summaries(&f, "implementation");
    let mut set = SetIndex::new();
    for s in &spec {
        set.insert(s);
    }
    let reference = set.clone();
    let addrs: BTreeSet<usize> = set.entries().map(|(_, _, _, o)| buf_addr(o)).collect();
    let sigs = set.stats().signatures_seen;
    let (table, store) = set.freeze();
    let mut bad = Vec::new();
    let moved: BTreeSet<usize> = store.entries().map(|(_, _, o)| buf_addr(o)).collect();
    if moved != addrs {
        bad.push(format!("{name}: the freeze changed {} buffers", addrs.symmetric_difference(&moved).count()));
    }
    if table.signatures() != sigs {
        bad.push(format!("{name}: table {} signatures, set {sigs}", table.signatures()));
    }
    for (len, cap) in store.capacities_for_test() {
        if cap != len {
            bad.push(format!("{name}: a slot's map holds {len} with capacity {cap}"));
            break;
        }
    }
    for (i, q) in imp.iter().enumerate() {
        let before = reference.stats();
        let (id, want) = reference.covers(q);
        let after = reference.stats();
        let mut tests = 0;
        let (got_id, got) = match table.resolve(q.hash, &q.sig, &mut tests) {
            SigLookup::NoBucket => (None, Covers::NoBucket),
            SigLookup::NoSig => (None, Covers::NoSig),
            SigLookup::Found(id) => {
                let (c, counts) = store.covers(id, &q.ord);
                let d = (
                    after.exact_hits - before.exact_hits,
                    after.containment_tests - before.containment_tests,
                    after.coordinates_compared - before.coordinates_compared,
                );
                if (counts.exact_hits, counts.containment_tests, counts.coordinates_compared) != d {
                    bad.push(format!("{name} query {i}: counts {counts:?}, the set's {d:?}"));
                }
                (Some(id), c)
            }
        };
        if (got_id, got) != (id, want) {
            bad.push(format!("{name} query {i}: {:?}, the set's {:?}", (got_id, got), (id, want)));
        }
        if bad.len() > 20 {
            break;
        }
    }
    (bad, imp.len())
}

/// I3-5 on I2's pilot corpus and the size-2 cells (the s2 corpus).
#[test]
fn i3_5_the_frozen_store_answers_as_the_set_index_on_the_pilot() {
    let _g = serial();
    let mut bad = Vec::new();
    let mut queries = 0;
    for name in PILOT_NAMES.iter().chain(SIZE2_CELLS.iter()) {
        let (b, n) = freeze_check(name);
        bad.extend(b);
        queries += n;
    }
    note!("P5\tpilot+size2\tqueries {queries}");
    assert!(queries > 0);
    assert!(bad.is_empty(), "conformance: I3-5: {bad:#?}");
}

/// I3-5 on the ten s7 cells, one per process (`P_CELL`).
#[test]
#[ignore]
fn i3_5_the_frozen_store_answers_as_the_set_index_on_one_cell() {
    let Ok(name) = std::env::var("P_CELL") else {
        return;
    };
    assert!(SLICE_CELLS.contains(&name.as_str()), "conformance: P_CELL is one of the ten cells");
    let _g = serial();
    let (bad, n) = freeze_check(&name);
    note!("P5\t{name}\tqueries {n}\tmismatches {}", bad.len());
    assert!(bad.is_empty(), "conformance: I3-5 {name}: {bad:#?}");
}

// =========================================================================
// I3-10: the matrix
// =========================================================================

/// The size-2 cells, every combination of threads, F and the split interval.
#[test]
fn i3_10_the_size2_cells_over_the_whole_matrix() {
    let _g = serial();
    let mut bad = Vec::new();
    let mut runs = 0;
    for name in SIZE2_CELLS {
        let f = fx(name);
        let s = seq(&f, false);
        for t in [1, 2, 4, 8, 16] {
            for fe in [1, 7, 4096] {
                for split in [1, 100] {
                    let o = par(&f, &P::new(t, fe, split));
                    runs += 1;
                    for b in compare(&f, &s, &o, false) {
                        bad.push(format!("{name} t{t} F{fe} s{split}: {b}"));
                    }
                }
            }
        }
    }
    note!("P10\tsize2\truns {runs}\tmismatches {}", bad.len());
    assert!(bad.is_empty(), "conformance: I3-10 size 2: {bad:#?}");
}

/// The 132-fixture pilot at one thread count per process (`P_THREADS`, the first value), F = 7,
/// the split at every execution.
#[test]
#[ignore]
fn i3_10_the_pilot_at_one_thread_count() {
    let Ok(_) = std::env::var("P_THREADS") else {
        return;
    };
    let _g = serial();
    let t = env_list("P_THREADS", &[1])[0];
    let mut bad = Vec::new();
    let (mut reported, mut reports) = (0, 0);
    let started = std::time::Instant::now();
    for name in PILOT_NAMES {
        let f = fx(name);
        let s = seq(&f, false);
        let o = par(&f, &P::new(t, 7, 1));
        reported += usize::from(o.counters.uncovered_multiplicity > 0);
        reports += o.counters.uncovered_multiplicity;
        for b in compare(&f, &s, &o, false) {
            bad.push(format!("{name}: {b}"));
        }
    }
    note!(
        "P10\tpilot\tt {t}\tfixtures {}\treported {reported}\treports {reports}\tmismatches {}\twall {} s",
        PILOT_NAMES.len(),
        bad.len(),
        started.elapsed().as_secs()
    );
    assert!(bad.is_empty(), "conformance: I3-10 pilot t{t}: {bad:#?}");
}

/// The three larger programs (`P_CELL`), threads from `P_THREADS` (default 1, 2, 4, 8, 16), F 7
/// and 4096, the split interval 100.
#[test]
#[ignore]
fn i3_10_one_larger_program() {
    let Ok(name) = std::env::var("P_CELL") else {
        return;
    };
    let _g = serial();
    let f = fx(&name);
    let started = std::time::Instant::now();
    let s = seq(&f, false);
    note!(
        "P10\t{name}\treference\tspec {}\timpl {}\treports {}\twall {} ms",
        s.counters.spec_graphs,
        s.counters.impl_graphs,
        s.counters.reports,
        started.elapsed().as_millis()
    );
    let mut bad = Vec::new();
    for t in env_list("P_THREADS", &[1, 2, 4, 8, 16]) {
        for fe in [7, 4096] {
            let started = std::time::Instant::now();
            let o = par(&f, &P::new(t, fe, 100));
            let c = &o.counters;
            note!(
                "P10\t{name}\tt {t}\tF {fe}\tspec {} ({} ms)\timpl {} ({} ms)\ttasks {}/{}\tflushes {}/{}\t\
                 lock held {}/{} ms wait {}/{} ms\twall {} ms",
                c.spec_graphs,
                c.spec_wall_time_ms,
                c.impl_graphs,
                c.impl_wall_time_ms,
                c.spec_tasks,
                c.impl_tasks,
                c.spec_flushes,
                c.impl_flushes,
                c.spec_merge_lock_held_ms,
                c.impl_merge_lock_held_ms,
                c.spec_merge_lock_wait_ms,
                c.impl_merge_lock_wait_ms,
                started.elapsed().as_millis()
            );
            for b in compare(&f, &s, &o, false) {
                bad.push(format!("t{t} F{fe}: {b}"));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: I3-10 {name}: {bad:#?}");
}

// =========================================================================
// I3-6: the streaming queries, the first report, the knobs
// =========================================================================

/// I3-6 (e): one first-report read across 16 workers on a fixture whose every completion is
/// uncovered (a1 silent n2r3, 512 of 512), with the stop knob off and on.
#[test]
fn i3_6_e_the_first_report_is_read_once_across_workers() {
    let _g = serial();
    let f = fx("apps/a1/silent/spec/n2r3");
    for stop in [false, true] {
        sverify_p::reset_first_report_reads_for_test();
        let mut p = P::new(16, 7, 1);
        p.stop = stop;
        let o = par(&f, &p);
        assert_eq!(sverify_p::first_report_reads_for_test(), 1, "conformance: I3-6 (e) stop {stop}");
        assert!(o.counters.wall_ms_at_first_report.is_some());
    }
    // and none on a conforming fixture
    sverify_p::reset_first_report_reads_for_test();
    let o = par(&fx("apps/a1/correct/spec/n2r2"), &P::new(16, 7, 1));
    assert_eq!(sverify_p::first_report_reads_for_test(), 0);
    assert!(o.counters.wall_ms_at_first_report.is_none());
}

/// I3-6 (f): `impl_distinct` off — no count and no set; I3-2's paper-events site: the maximum equal
/// to SVerify-S's with the knob on, `None` with it off.
#[test]
fn i3_6_f_the_knobs_impl_distinct_and_paper_events() {
    let _g = serial();
    let f = fx("apps/a3/never-grant/spec/k2q2");
    let mut p = P::new(4, 7, 1);
    p.distinct = false;
    let o = par(&f, &p);
    assert_eq!(o.counters.impl_distinct_summaries, None);
    assert!(o.counters.impl_set.is_none());
    assert_eq!(o.max_paper_events, None);
    assert_eq!(o.counters.max_paper_events, None);
    let mut cc = seq_cc(&f, false);
    cc.paper_events = true;
    let s = stateful::run_with(&cc, &f.implementation, &f.specification, false);
    p.paper = true;
    let o = par(&f, &p);
    assert!(s.max_paper_events.is_some());
    assert_eq!(o.max_paper_events, s.max_paper_events);
    assert_eq!(o.counters.max_paper_events, s.max_paper_events);
}

// =========================================================================
// I3-6s: the stop path
// =========================================================================

#[test]
fn i3_6s_the_stop_at_first_report_path() {
    let _g = serial();
    let mut bad = Vec::new();
    for name in ["apps/a1/silent/spec/n2r3", "apps/a1/early-abort/spec/n2r3"] {
        let f = fx(name);
        let s_off = seq(&f, false);
        let s_on = seq(&f, true);
        let want = seq_uncovered(&f, &s_off);
        if s_on.counters.reports != 1 || s_on.impl_end != SearchEnd::StoppedAtFirstReport {
            bad.push(format!("{name}: the reference with the knob: {} reports", s_on.counters.reports));
        }
        for t in [1, 2, 16] {
            sverify_p::reset_first_report_reads_for_test();
            let mut p = P::new(t, 7, 1);
            p.stop = true;
            let o = par(&f, &p);
            let c = &o.counters;
            let tag = format!("{name} t{t}");
            bad.extend(compare(&f, &s_off, &o, true).into_iter().map(|b| format!("{tag}: {b}")));
            let got = par_uncovered(&o);
            if got.is_empty() || got.len() > t {
                bad.push(format!("{tag}: {} distinct uncovered (1 ..= {t})", got.len()));
            }
            if !got.keys().all(|k| want.contains_key(k)) {
                bad.push(format!("{tag}: a reported summary SVerify-S does not report"));
            }
            if o.impl_end != SearchEnd::StoppedAtFirstReport || !c.stopped_early {
                bad.push(format!("{tag}: impl_end {:?}, stopped_early {}", o.impl_end, c.stopped_early));
            }
            if c.spawned_at_stop != c.impl_tasks as u64 - 1 {
                bad.push(format!("{tag}: spawned_at_stop {}, impl_tasks {}", c.spawned_at_stop, c.impl_tasks));
            }
            if c.uncovered_at_stop != got.len() {
                bad.push(format!("{tag}: uncovered_at_stop {}", c.uncovered_at_stop));
            }
            if sverify_p::first_report_reads_for_test() != 1 {
                bad.push(format!("{tag}: {} cancels", sverify_p::first_report_reads_for_test()));
            }
            if c.impl_graphs > s_off.counters.impl_graphs || c.lookups > c.impl_graphs {
                bad.push(format!("{tag}: impl_graphs {} lookups {}", c.impl_graphs, c.lookups));
            }
            note!(
                "P6S\t{tag}\tuncovered {}\treports {}\timpl_graphs {}\tlookups {}\ttasks {}\tspawned_at_stop {}",
                got.len(),
                c.reports,
                c.impl_graphs,
                c.lookups,
                c.impl_tasks,
                c.spawned_at_stop
            );
        }
    }
    // a conforming fixture: nothing stops, the results equal the knob-off run's
    let f = fx("apps/a1/correct/spec/n2r2");
    let s = seq(&f, false);
    for t in [1, 2, 16] {
        let mut p = P::new(t, 7, 1);
        p.stop = true;
        let o = par(&f, &p);
        bad.extend(compare(&f, &s, &o, false).into_iter().map(|b| format!("conforming t{t}: {b}")));
    }
    // the specification-side source check: the sink reads the token before any summary
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/sverify_p.rs"),
    )
    .unwrap();
    let branch = &src[src.find("// The implementation side (I3-6, (B))").unwrap()..];
    let read = branch.find("is_cancelled()").unwrap();
    let summary = branch.find("CompactSummary::at_completion").unwrap();
    if read > summary {
        bad.push("the implementation sink computes a summary before reading the token".to_owned());
    }
    let code: String = src
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    if code.matches(".cancel()").count() != 1 {
        bad.push("cancel is called at more than one site".to_owned());
    }
    assert!(bad.is_empty(), "conformance: I3-6s: {bad:#?}");
}

// =========================================================================
// I3-7: the public verdict, the refusals, the panics, the specification's errors
// =========================================================================

#[test]
fn i3_7_the_verdict_through_the_public_entry() {
    let _g = serial();
    let f = fx("apps/a3/never-grant/spec/k2q2");
    let cc = par_cc(&f, &P::new(4, 7, 1));
    let (i, s) = (Arc::clone(&f.implementation), Arc::clone(&f.specification));
    let v = crate::conformance::verify(cc, move || i(), move || s()).expect("conformance: a verdict");
    let ConfVerdict::Reported(out) = &v else {
        panic!("conformance: I3-7: {v:?}");
    };
    assert_eq!(out.report_count(), 8, "conformance: I3-7: the record's 8 reports of 21");
    assert!(out.reports.is_empty());
    let u = out.uncovered_summaries();
    assert!(!u.is_empty());
    assert_eq!(u.iter().map(|x| x.multiplicity()).sum::<usize>(), 8);
    let c = out.sverify_p_counters().expect("conformance: the engine's record");
    assert_eq!(c.uncovered.len(), u.len());
    let shown = format!("{v}");
    assert!(u.iter().all(|x| shown.contains(x.signature())), "conformance: the Display lists them");
    let rendered = format!("{c}");
    for field in ["threads", "flush_entries", "spec_flushes", "impl_flushes", "spawned_at_stop",
                  "merge_lock_wait_ms", "uncovered_multiplicity", "lookups_signature_miss"] {
        assert!(rendered.contains(field), "conformance: SverifyPCounters' Display lacks {field}");
    }
    // conforming
    let f = fx("apps/a1/correct/spec/n2r2");
    let cc = par_cc(&f, &P::new(4, 7, 1));
    let (i, s) = (Arc::clone(&f.implementation), Arc::clone(&f.specification));
    let v = crate::conformance::verify(cc, move || i(), move || s()).unwrap();
    assert!(matches!(v, ConfVerdict::Conforms(_)), "conformance: {v:?}");
}

#[test]
fn i3_7_the_refusals_on_both_paths() {
    let _g = serial();
    let f = fx("apps/a1/correct/spec/n2r2");
    let calls = Arc::new(AtomicUsize::new(0));
    let counted = |p: &Prog| -> Prog {
        let (p, calls) = (Arc::clone(p), Arc::clone(&calls));
        Arc::new(move || {
            calls.fetch_add(1, Ordering::SeqCst);
            p()
        })
    };
    let (imp, spec) = (counted(&f.implementation), counted(&f.specification));
    let base = par_cc(&f, &P::new(2, 7, 100));
    let cases: Vec<(&str, ConfConfig)> = vec![
        ("threads(0)", {
            let mut c = base.clone();
            c.threads = 0;
            c
        }),
        ("flush_entries(0)", {
            let mut c = base.clone();
            c.flush_entries = 0;
            c
        }),
        ("max_iterations(Some(_))", {
            let mut c = base.clone();
            c.config.max_iterations = Some(5);
            c
        }),
        ("parallel(true)", {
            let mut c = base.clone();
            c.config.parallel = true;
            c
        }),
    ];
    let mut bad = Vec::new();
    for (knob, cc) in cases {
        let (i, s) = (Arc::clone(&imp), Arc::clone(&spec));
        match crate::conformance::verify(cc.clone(), move || i(), move || s()) {
            Err(ConfError::KnobConflict { knob: k, conflicts_with }) => {
                if k != knob || conflicts_with != "engine(SverifyP)" {
                    bad.push(format!("{knob}: {k} / {conflicts_with}"));
                }
            }
            other => bad.push(format!("{knob}: {other:?}")),
        }
        let got = panic_of(|| sverify_p::run_with(&cc, &imp, &spec));
        if !got.as_deref().is_some_and(|m| m.starts_with("conformance: ")) {
            bad.push(format!("{knob} through run_with: {got:?}"));
        }
    }
    assert_eq!(calls.load(Ordering::SeqCst), 0, "conformance: a refused run called a program");
    // stop_at_first_report is accepted
    let mut c = base.clone();
    c.stop_at_first_report = true;
    let (i, s) = (Arc::clone(&imp), Arc::clone(&spec));
    if let Err(e) = crate::conformance::verify(c, move || i(), move || s()) {
        bad.push(format!("stop_at_first_report refused: {e:?}"));
    }
    assert!(bad.is_empty(), "conformance: I3-7 refusals: {bad:#?}");
}

/// 10-26 15.7: the root's panic (in its warmup, and in its loop) and a task's panic propagate
/// through the hooked runner; an engine-level panic in the specification gives no outcome.
#[test]
fn i3_7_the_panics_propagate() {
    let _g = serial();
    // Which Must, by creation order (0 is the root), panics at which of its completions (`at` 0:
    // none); the root's completions are counted into `root_seen`.
    fn hooked_panic(
        f: &Fixture,
        program: &Prog,
        warmup: usize,
        who: usize,
        at: usize,
        root_seen: &Arc<AtomicUsize>,
    ) -> Option<String> {
        let mut conf = f.config.clone();
        conf.partitioned_parallelization = true;
        conf.partitioned_num_threads = Some(2);
        conf.warmup = warmup;
        conf.iterations_until_split = 1;
        let musts = Arc::new(AtomicUsize::new(0));
        let (vis, rs) = (f.visible.clone(), Arc::clone(root_seen));
        let on_must: Arc<dyn Fn(&mut Must) + Send + Sync> = Arc::new(move |must: &mut Must| {
            let me = musts.fetch_add(1, Ordering::SeqCst);
            let mut ctx = ConfCtx::gate_disabled(
                must.config.clone(),
                vis.clone(),
                ConfMode::EnumeratePartitioned,
            );
            let (n, rs) = (Arc::new(AtomicUsize::new(0)), Arc::clone(&rs));
            ctx.set_sink(Box::new(move |_, _| {
                let k = n.fetch_add(1, Ordering::SeqCst) + 1;
                if me == 0 {
                    rs.fetch_add(1, Ordering::SeqCst);
                }
                if at > 0 && ((who == 0 && me == 0) || (who == 1 && me >= 1)) && k == at {
                    panic!("conformance: planted {who}");
                }
                SinkVerdict::Continue
            }));
            must.enable_conformance_partitioned(ctx);
        });
        let hooks = PartitionHooks {
            on_must,
            on_task_end: Arc::new(|_| {}),
            cancel: Arc::new(CancelToken::new()),
        };
        let p = Arc::clone(program);
        catch_unwind(AssertUnwindSafe(|| verify_partitioned_rayon_with(conf, move || p(), hooks)))
            .err()
            .map(|e| panic_text(&e))
    }
    // The root runs its loop only if its current revisit queue is non-empty after the warmup. A
    // dry run per candidate counts the root's completions; the first candidate whose root runs
    // past its warmup carries the loop case, which panics at completion warmup + 1.
    let mut chosen = None;
    let mut tried = Vec::new();
    'scan: for (name, side) in [
        ("apps/a3/fifo/spec/k2q2", "impl"),
        ("apps/a1/correct/spec/n2r2", "spec"),
        ("apps/a1/correct/spec/n2r2", "impl"),
        ("apps/a3/fifo/spec/k3q3", "impl"),
    ] {
        let c = fx(name);
        let program =
            if side == "impl" { Arc::clone(&c.implementation) } else { Arc::clone(&c.specification) };
        for warmup in [1, 2, 3, 5] {
            let seen = Arc::new(AtomicUsize::new(0));
            let dry = hooked_panic(&c, &program, warmup, 0, 0, &seen);
            let n = seen.load(Ordering::SeqCst);
            tried.push(format!("{name} {side} warmup {warmup}: root {n}, {dry:?}"));
            if dry.is_none() && n > warmup {
                chosen = Some((c, program, warmup));
                break 'scan;
            }
        }
    }
    let Some((c, program, warmup)) = chosen else {
        panic!("conformance: non-vacuity: no candidate's root ran its loop: {tried:#?}")
    };
    note!("I3-7 the root's loop: {}", tried.last().unwrap());
    let mut bad = Vec::new();
    for (who, at, what) in [(0, 1, "the root's warmup"), (0, warmup + 1, "the root's loop"), (1, 1, "a task")] {
        match hooked_panic(&c, &program, warmup, who, at, &Arc::new(AtomicUsize::new(0))) {
            Some(m) if m.contains(&format!("planted {who}")) => {}
            other => bad.push(format!("{what}: {other:?}")),
        }
    }
    let f = fx("apps/a3/fifo/spec/k2q2");
    // the engine: a specification that panics in its first execution gives no outcome
    let spec = prog(|| panic!("conformance: planted spec"));
    let mut cc = par_cc(&f, &P::new(2, 7, 100));
    cc.visible = vec![];
    let got = panic_of(|| sverify_p::run_with(&cc, &f.implementation, &spec));
    if !got.as_deref().is_some_and(|m| m.contains("planted spec")) {
        bad.push(format!("the engine: {got:?}"));
    }
    assert!(bad.is_empty(), "conformance: the panics: {bad:#?}");
}

/// I3-4: a visible assertion failure on the specification side is recorded, never pruned, and the
/// public error is SVerify-S's, word for word.
#[test]
fn i3_7_the_specifications_errors_match_the_sequential_engine() {
    let _g = serial();
    let spec = prog(|| {
        let _x = named("x", || {});
        let _a = named("a", || crate::assert(false));
    });
    let imp = prog(|| {
        let _x = named("x", || {});
        let _a = named("a", || {});
    });
    let cfg = Config::builder().with_cons_type(ConsType::Bag).with_seed(0).build();
    let mk = |engine| {
        ConfBuilder::new()
            .config(cfg.clone())
            .visible_threads(vec!["a".to_owned(), "x".to_owned()])
            .engine(engine)
            .threads(2)
            .build()
            .expect("conformance: in scope")
    };
    let (i, s) = (Arc::clone(&imp), Arc::clone(&spec));
    let a = crate::conformance::verify(mk(Engine::Stateful), move || i(), move || s());
    let (i, s) = (Arc::clone(&imp), Arc::clone(&spec));
    let b = crate::conformance::verify(mk(Engine::SverifyP), move || i(), move || s());
    match (&a, &b) {
        (
            Err(ConfError::SpecNotErrorFree { detail: x }),
            Err(ConfError::SpecNotErrorFree { detail: y }),
        ) => assert_eq!(x, y, "conformance: the detail"),
        _ => panic!("conformance: stateful {a:?}, sverify-p {b:?}"),
    }
    // and the engine's spec graphs equal SVerify-S's (no completion pruned)
    let ss = stateful::run_with(&mk(Engine::Stateful), &imp, &spec, false);
    let pp = sverify_p::run_with(&mk(Engine::SverifyP), &imp, &spec);
    assert_eq!(pp.counters.spec_graphs, ss.counters.spec_graphs);
    assert_eq!(pp.spec_errors.len(), ss.spec_errors.len());
}

// =========================================================================
// I3-9: peak memory
// =========================================================================

fn vm_hwm_kb() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status")
        .ok()?
        .lines()
        .find(|l| l.starts_with("VmHWM:"))?
        .split_whitespace()
        .nth(1)?
        .parse()
        .ok()
}

/// I3-9 (a)–(b) on the engine: the largest worker set at a flush is ≤ F, and the merged index
/// never shrinks, on A1 correct n2r2 at F 1, 7 and 64.
#[test]
fn i3_9_the_worker_sets_stay_within_f() {
    let _g = serial();
    let f = fx("apps/a1/correct/spec/n2r2");
    for fe in [1, 7, 64] {
        sverify_p::reset_flush_record_for_test();
        let o = par(&f, &P::new(4, fe, 1));
        let (largest, decreased) = sverify_p::flush_record_for_test();
        assert!(largest >= 1 && largest <= fe, "conformance: I3-9 (a): largest {largest} at F {fe}");
        assert!(!decreased, "conformance: I3-9 (b) at F {fe}");
        assert_eq!(o.counters.spec_set.entries, 64);
    }
}

/// I3-9 (d), information: one size-3 run (`P_CELL`), 16 threads, the defaults; `VmHWM` before and
/// after, the merged specification index's size.
#[test]
#[ignore]
fn i3_9_d_one_size3_measurement() {
    let Ok(name) = std::env::var("P_CELL") else {
        return;
    };
    let _g = serial();
    let f = fx(&name);
    sverify_p::reset_flush_record_for_test();
    let before = vm_hwm_kb();
    let o = par(&f, &P::new(16, 4096, 100));
    let after = vm_hwm_kb();
    let c = &o.counters;
    let (largest, decreased) = sverify_p::flush_record_for_test();
    note!(
        "P9\t{name}\tVmHWM before {before:?} after {after:?} kB\tspec entries {}\tsummary_bytes {}\t\
         sig_bytes_est {}\tspec {} ({} ms)\timpl {} ({} ms)\tlargest flush {largest}\tdecreased {decreased}",
        c.spec_set.entries,
        c.spec_set.summary_bytes,
        c.spec_set.sig_bytes_est,
        c.spec_graphs,
        c.spec_wall_time_ms,
        c.impl_graphs,
        c.impl_wall_time_ms
    );
    assert!(largest <= 4096 && !decreased);
}

// =========================================================================
// After the lead's §5 (`SVERIFY-P.i3.md`): the engine-level address check, the stop after the
// split, and the derivation's cheap checks
// =========================================================================

/// I3-12 (i) and (iii) at the engine level, through `run_with` (the lead's `ADDRESS_RECORD`): every
/// order the frozen store holds keeps the heap buffer a flush moved, and the store holds exactly
/// `orders_held` orders. A flush that copies, or a freeze that clones, gives the store buffers no
/// flush recorded. Non-vacuous: flushes at F occur (flushes > tasks).
#[test]
fn i3_12_i_iii_the_flush_and_the_freeze_move_through_the_engine() {
    let _g = serial();
    for name in ["apps/a1/correct/spec/n2r2", "apps/a4/hash/a4a/k3q3m3"] {
        let f = fx(name);
        sverify_p::reset_address_record_for_test();
        let o = par(&f, &P::new(4, 7, 1));
        let (flushed, frozen) = sverify_p::address_record_for_test();
        let c = &o.counters;
        assert!(c.spec_flushes > c.spec_tasks, "conformance: non-vacuity: no flush at F on {name}");
        assert_eq!(frozen.len(), c.orders_held, "conformance: {name}: the store's orders");
        assert_eq!(frozen.len(), c.spec_set.entries, "conformance: {name}: the merged entries");
        let flushed: BTreeSet<usize> = flushed.into_iter().collect();
        let frozen_set: BTreeSet<usize> = frozen.iter().copied().collect();
        let strays = frozen_set.difference(&flushed).count();
        note!(
            "P12\t{name}\tflushes {}\ttasks {}\tflushed addresses {}\tfrozen {} ({} distinct)\tnot flushed {strays}",
            c.spec_flushes,
            c.spec_tasks,
            flushed.len(),
            frozen.len(),
            frozen_set.len()
        );
        assert_eq!(strays, 0, "conformance: I3-12 (i)/(iii): {name}: frozen buffers no flush moved");
        assert_eq!(frozen_set.len(), frozen.len(), "conformance: {name}: one buffer per held order");
    }
}

/// A late violation (the tester's, for I3-6s after the split): visible `r` receives `recvs` `i32`s
/// from `k` invisible senders (`s0` before `r`, the rest after); in the specification every sender
/// sends 1, in the implementation sender `bad` ≥ 1 sends 2. In the first execution `r` reads `s0`; the
/// violation needs a backward revisit to the 2, and the other senders' revisits (to a 1, covered)
/// may come first — whether they do, and so whether a state is spawned before the report, is what
/// the dry run measures.
fn late_violation(k: usize, bad: usize, recvs: usize) -> Fixture {
    let mk = move |implementation: bool| {
        prog(move || {
            let (tx, rx) = crate::channel::Builder::<i32>::new()
                .with_comm(CommunicationModel::NoOrder)
                .build();
            // `s0` is created before `r`, so under LTR `r` receives while only `s0`'s message
            // exists, and the later senders' messages reach it by backward revisits (which push
            // the states the runner spawns); created after them, `r` would see every message at
            // its receive and explore them as forward alternatives, with nothing to spawn.
            let t0 = tx.clone();
            let _s0 = named("s0", move || t0.send_msg(1));
            let _r = named("r", move || {
                for _ in 0..recvs {
                    let _v: i32 = rx.recv_msg_block();
                }
            });
            for i in 1..k {
                let t = tx.clone();
                let v = if implementation && i == bad { 2 } else { 1 };
                let _s = named(&format!("s{i}"), move || t.send_msg(v));
            }
        })
    };
    let mut f = fx("apps/a1/correct/spec/n2r2");
    f.name = format!("stop:late/k{k}b{bad}r{recvs}");
    f.specification = mk(false);
    f.implementation = mk(true);
    f.visible = vec!["r".to_owned()];
    f.config = crate::conformance::grid::cfg(ConsType::Bag);
    f
}

/// I3-6s (b), (f), (h) on a fixture whose first uncovered completion comes after the root's split:
/// chosen by a dry run at t = 1 (warmup 1, interval 1, batch 1) as the first violating candidate
/// whose stop finds a spawn admitted and comes before the last completion (the `late_violation`
/// programs, a3 never-grant k2q2, then the pilot in its order); then at t = 1, 2 and 16: `spawned_at_stop` ≥ 1 and =
/// `impl_tasks` − 1, the uncovered set non-empty, ≤ t and inside SVerify-S's, `impl_graphs` ≤ the
/// knob-off run's, the verdict `Reported` through the public entry.
#[test]
fn i3_6s_the_stop_after_the_split() {
    let _g = serial();
    let mut tried = Vec::new();
    let mut chosen = None;
    let mut late = Vec::new();
    for (k, recvs) in [(3, 1), (4, 1), (5, 1), (4, 2), (5, 2)] {
        for bad in 1..k {
            late.push(late_violation(k, bad, recvs));
        }
    }
    let corpus = std::iter::once("apps/a3/never-grant/spec/k2q2").chain(PILOT_NAMES.iter().copied());
    for f in late.into_iter().chain(corpus.map(fx)) {
        let name = f.name.clone();
        let name = name.as_str();
        let s_off = seq(&f, false);
        if s_off.counters.reports == 0 {
            continue;
        }
        let mut p = P::new(1, 7, 1);
        p.stop = true;
        let o = par(&f, &p);
        tried.push(format!(
            "{name}: spawned_at_stop {}, impl_graphs {} of {}, reports {}",
            o.counters.spawned_at_stop,
            o.counters.impl_graphs,
            s_off.counters.impl_graphs,
            s_off.counters.reports
        ));
        // a spawn admitted before the stop, and the stop before the last completion
        if o.counters.spawned_at_stop >= 1 && o.counters.impl_graphs < s_off.counters.impl_graphs {
            chosen = Some((f, s_off));
            break;
        }
    }
    let Some((f, s_off)) = chosen else {
        panic!("conformance: non-vacuity: no violating fixture stops after a spawn: {tried:#?}")
    };
    note!("P6T\tchosen {}\tafter {} candidates", f.name, tried.len());
    let want = seq_uncovered(&f, &s_off);
    let mut bad = Vec::new();
    for t in [1, 2, 16] {
        sverify_p::reset_first_report_reads_for_test();
        let mut p = P::new(t, 7, 1);
        p.stop = true;
        let o = par(&f, &p);
        let c = &o.counters;
        let tag = format!("{} t{t}", f.name);
        bad.extend(compare(&f, &s_off, &o, true).into_iter().map(|b| format!("{tag}: {b}")));
        let got = par_uncovered(&o);
        if c.spawned_at_stop < 1 || c.spawned_at_stop != c.impl_tasks as u64 - 1 {
            bad.push(format!("{tag}: spawned_at_stop {}, impl_tasks {}", c.spawned_at_stop, c.impl_tasks));
        }
        if got.is_empty() || got.len() > t || !got.keys().all(|k| want.contains_key(k)) {
            bad.push(format!("{tag}: {} uncovered, inside SVerify-S's: {}", got.len(), got.keys().all(|k| want.contains_key(k))));
        }
        if o.impl_end != SearchEnd::StoppedAtFirstReport || !c.stopped_early {
            bad.push(format!("{tag}: impl_end {:?}", o.impl_end));
        }
        if c.impl_graphs > s_off.counters.impl_graphs || c.lookups > c.impl_graphs {
            bad.push(format!("{tag}: impl_graphs {} lookups {}", c.impl_graphs, c.lookups));
        }
        if sverify_p::first_report_reads_for_test() != 1 {
            bad.push(format!("{tag}: {} first-report reads", sverify_p::first_report_reads_for_test()));
        }
        let mut cc = par_cc(&f, &p);
        cc.stop_at_first_report = true;
        let (i, s) = (Arc::clone(&f.implementation), Arc::clone(&f.specification));
        match crate::conformance::verify(cc, move || i(), move || s()) {
            Ok(ConfVerdict::Reported(_)) => {}
            other => bad.push(format!("{tag}: the public verdict {other:?}")),
        }
        note!(
            "P6T\t{tag}\tuncovered {}\treports {}\timpl_graphs {} of {}\tlookups {}\ttasks {}\tspawned_at_stop {}",
            got.len(),
            c.reports,
            c.impl_graphs,
            s_off.counters.impl_graphs,
            c.lookups,
            c.impl_tasks,
            c.spawned_at_stop
        );
    }
    assert!(bad.is_empty(), "conformance: I3-6s after the split: {bad:#?}");
}

/// The non-test, non-comment lines of a source file under `src/`.
fn code_lines(rel: &str) -> Vec<(usize, String)> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src").join(rel);
    let text = std::fs::read_to_string(&path).expect("conformance: a source file");
    let body = match text.find("#[cfg(test)]\nmod ") {
        Some(at) => &text[..at],
        None => text.as_str(),
    };
    body.lines()
        .enumerate()
        .filter(|(_, l)| !l.trim_start().starts_with("//"))
        .map(|(i, l)| (i + 1, l.to_owned()))
        .collect()
}

/// I3-1: `ConfConfig::threads` and `ConfConfig::flush_entries` are read by `sverify_p.rs` only
/// (outside `config.rs`, which defines and sets them). Source check over every non-test `.rs` file
/// under `src/`: a read is `<binding>.threads` / `<binding>.flush_entries` with a `ConfConfig`
/// binding name (`cc`, `conf_config`, `conf`); `self.` (the builder, the counters' `Display`) and the
/// graph's `threads` are other types.
#[test]
fn i3_1_the_two_knobs_are_read_by_the_engine_only() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    for dir in ["", "conformance"] {
        for e in std::fs::read_dir(root.join(dir)).expect("conformance: src") {
            let p = e.unwrap().path();
            let name = p.file_name().unwrap().to_str().unwrap().to_owned();
            if name.ends_with(".rs") && !name.ends_with("_tests.rs") {
                files.push(if dir.is_empty() { name } else { format!("{dir}/{name}") });
            }
        }
    }
    let mut readers: BTreeMap<String, usize> = BTreeMap::new();
    for rel in &files {
        for (_, l) in code_lines(rel) {
            for b in ["cc.", "conf_config.", "conf."] {
                for k in ["threads", "flush_entries"] {
                    let pat = format!("{b}{k}");
                    let mut from = 0;
                    while let Some(at) = l[from..].find(&pat) {
                        let end = from + at + pat.len();
                        let before = l[..from + at].chars().last();
                        let after = l[end..].chars().next();
                        let word_start = before.map_or(true, |c| !(c.is_alphanumeric() || c == '_'));
                        let word_end = after.map_or(true, |c| !(c.is_alphanumeric() || c == '_'));
                        if word_start && word_end {
                            *readers.entry(rel.clone()).or_default() += 1;
                        }
                        from = end;
                    }
                }
            }
        }
    }
    note!("P11\treaders {readers:?}");
    assert!(readers.get("conformance/sverify_p.rs").is_some_and(|n| *n >= 4), "conformance: non-vacuity");
    assert_eq!(readers.len(), 1, "conformance: I3-1: readers outside sverify_p.rs: {readers:?}");
}

/// I3-2's rows the engine meets by not calling: no `set_cut`, no `set_gate_sink`, no snapshot
/// (`ReplaySnapshot`, `replay_snapshot`, `snapshot`) in `sverify_p.rs`'s code; the engine's contexts
/// are built by `gate_disabled` in the twin mode only.
#[test]
fn i3_2_the_engine_never_cuts_gates_or_snapshots() {
    let code: Vec<String> = code_lines("conformance/sverify_p.rs").into_iter().map(|(_, l)| l).collect();
    let code = code.join("\n");
    for no in ["set_cut(", "set_gate_sink(", "ReplaySnapshot", "replay_snapshot", "snapshot"] {
        assert!(!code.contains(no), "conformance: I3-2: sverify_p.rs calls {no}");
    }
    let built = code.matches("ConfCtx::gate_disabled(").count();
    assert!(built >= 1, "conformance: non-vacuity: the engine builds its contexts");
    assert_eq!(code.matches("ConfMode::").count(), code.matches("ConfMode::EnumeratePartitioned").count());
}

/// I3-2's E1, E2 and M8 rows on a twin run (the hooked runner, the twin's gate-disabled context):
/// per pool thread, `MIN-ENGINES`' test counters — selector picks 0 (E1-1), gate takes = the
/// completions and no carry clone (E2-4) — and the context's M8 counter 0. Non-vacuous: on the
/// same programs under `Collect` (`compact_tests::e2_entry_counts`) the takes exceed the
/// completions, A3 fifo k2q2 clones the carry, and `mixed/branch`'s M8 is > 0.
#[test]
fn i3_2_the_twin_run_takes_no_selector_no_gate_and_no_m8() {
    use crate::must::{
        carry_clones_for_test, gate_takes_for_test, reset_gate_counts_for_test,
        reset_selector_picks_for_test, selector_picks_for_test,
    };
    let _g = serial();
    let mut bad = Vec::new();
    for (name, side) in [("apps/a3/fifo/spec/k2q2", "impl"), ("mixed/branch", "impl")] {
        let f = fx(name);
        let program = if side == "impl" { Arc::clone(&f.implementation) } else { Arc::clone(&f.specification) };
        for t in [1, 4] {
            let counts: Arc<[AtomicUsize; 5]> = Arc::new(Default::default());
            let mut conf = f.config.clone();
            conf.partitioned_parallelization = true;
            conf.partitioned_num_threads = Some(t);
            conf.warmup = 1;
            conf.iterations_until_split = 1;
            conf.state_batch_size = 1;
            let (vis, k) = (f.visible.clone(), Arc::clone(&counts));
            let on_must: Arc<dyn Fn(&mut Must) + Send + Sync> = Arc::new(move |must: &mut Must| {
                reset_selector_picks_for_test();
                reset_gate_counts_for_test();
                let mut ctx = ConfCtx::gate_disabled(
                    must.config.clone(),
                    vis.clone(),
                    ConfMode::EnumeratePartitioned,
                );
                let k = Arc::clone(&k);
                ctx.set_sink(Box::new(move |_, _| {
                    k[0].fetch_add(1, Ordering::SeqCst);
                    SinkVerdict::Continue
                }));
                must.enable_conformance_partitioned(ctx);
            });
            let k = Arc::clone(&counts);
            let on_task_end: Arc<dyn Fn(&mut Must) + Send + Sync> = Arc::new(move |must: &mut Must| {
                k[1].fetch_add(selector_picks_for_test(), Ordering::SeqCst);
                k[2].fetch_add(gate_takes_for_test(), Ordering::SeqCst);
                k[3].fetch_add(carry_clones_for_test(), Ordering::SeqCst);
                reset_selector_picks_for_test();
                reset_gate_counts_for_test();
                let m8 = must.conf_ctx().map_or(0, |c| c.counters().invisible_ops_of_visible_threads);
                k[4].fetch_max(m8, Ordering::SeqCst);
            });
            let hooks = PartitionHooks { on_must, on_task_end, cancel: Arc::new(CancelToken::new()) };
            let p = Arc::clone(&program);
            let run = verify_partitioned_rayon_with(conf, move || p(), hooks);
            let [n, picks, takes, clones, m8] = [0, 1, 2, 3, 4].map(|i| counts[i].load(Ordering::SeqCst));
            note!("P2T\t{name} {side} t{t}\tcompletions {n}\tpicks {picks}\ttakes {takes}\tclones {clones}\tm8 {m8}\ttasks {}", run.tasks_spawned);
            if n == 0 || picks != 0 || takes != n || clones != 0 || m8 != 0 {
                bad.push(format!("{name} t{t}: completions {n}, picks {picks}, takes {takes}, clones {clones}, m8 {m8}"));
            }
        }
        // the control: the same program in `Collect`, on the test thread
        let (cnt, _, _, execs, _, takes, clones) =
            crate::conformance::compact_tests::e2_entry_counts(&f, &program, ConfMode::Collect);
        note!("P2T\t{name} {side} Collect\texecutions {execs}\ttakes {takes}\tclones {clones}\tm8 {}", cnt.invisible_ops_of_visible_threads);
        if takes <= execs {
            bad.push(format!("{name}: the Collect control's takes {takes} ≤ executions {execs}"));
        }
        if name == "apps/a3/fifo/spec/k2q2" && clones == 0 {
            bad.push(format!("{name}: the Collect control clones no carry"));
        }
        if name == "mixed/branch" && cnt.invisible_ops_of_visible_threads == 0 {
            bad.push(format!("{name}: the Collect control's M8 is 0"));
        }
    }
    assert!(bad.is_empty(), "conformance: I3-2 twin counters: {bad:#?}");
}

/// I3-5 (d): `OrderStore: Sync` and `SigTable: Send + !Sync` (compile-time facts, read through
/// inherent-before-trait associated-constant resolution), and no `unsafe` in the code of the eight
/// files the lead's I3 touched (comment lines dropped; `must.rs`'s two occurrences are comments).
#[test]
fn i3_5_d_the_store_is_sync_the_table_is_not_and_no_unsafe() {
    use crate::conformance::compact::{OrderStore, SigTable};
    struct Probe<T>(std::marker::PhantomData<T>);
    trait Fallback {
        const SYNC: bool = false;
    }
    impl<T> Fallback for Probe<T> {}
    #[allow(dead_code)]
    impl<T: Sync> Probe<T> {
        const SYNC: bool = true;
    }
    fn assert_sync<T: Sync>() {}
    fn assert_send<T: Send>() {}
    assert_sync::<OrderStore>();
    assert_send::<SigTable>();
    assert!(Probe::<OrderStore>::SYNC, "conformance: the probe reads a Sync type as Sync");
    assert!(!Probe::<std::cell::Cell<u8>>::SYNC, "conformance: the probe reads a !Sync type as !Sync");
    assert!(!Probe::<SigTable>::SYNC, "conformance: I3-5 (d): SigTable is Sync");
    let mut bad = Vec::new();
    for rel in [
        "parallel_verify.rs",
        "must.rs",
        "conformance/ctx.rs",
        "conformance/mod.rs",
        "conformance/config.rs",
        "conformance/report.rs",
        "conformance/compact.rs",
        "conformance/sverify_p.rs",
    ] {
        for (n, l) in code_lines(rel) {
            if l.split(|c: char| !(c.is_alphanumeric() || c == '_')).any(|w| w == "unsafe") {
                bad.push(format!("{rel}:{n}: {}", l.trim()));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: I3-5 (d): unsafe in the lead's files: {bad:#?}");
}

// =========================================================================
// SVERIFY-P I4 (gate 3, the tester): the driver and the store row, and the baseline row,
// against criteria rev 1.2 and `log/dev/SVERIFY-P.derived-i4.md` (10d5f6e9). Every in-process
// test keeps `phase_peaks` off (R1); the reset runs only in `i4_3_a_…` (ignored, own process)
// and in the driver's children.
// =========================================================================

use crate::conformance::eval::{
    header, parse_key, parse_label, read_rows, Driver, Probes, RowSpec, RunKind, Spec, Tier,
    LABEL_PIN,
};
use crate::conformance::grid::{run_grid, row_of, GridConfig, GridEnd, GridRaw, GridResult};

/// One engine run through the grid's own path (`run_grid`, the run thread, the `VmHWM` reads).
fn i4_run(f: &Fixture, c: &GridConfig) -> GridResult {
    match run_grid(f, c, None) {
        GridEnd::Ok(r) => r,
        other => panic!("conformance: I4 run of {}: {other:?}", f.name),
    }
}

/// A row as name → text.
fn i4_cells(r: &GridResult) -> BTreeMap<String, String> {
    row_of(r).into_iter().map(|(k, v)| (k.to_owned(), v)).collect()
}

fn i4_num(m: &BTreeMap<String, String>, k: &str) -> u128 {
    let v = m.get(k).unwrap_or_else(|| panic!("conformance: no column {k}"));
    v.parse()
        .unwrap_or_else(|_| panic!("conformance: column {k} = {v:?} is not a number"))
}

/// A blank, `None`, a number or `Some(<number>)` (the `push` of an `Option`, as `vm_hwm_kb_after`).
fn i4_opt(m: &BTreeMap<String, String>, k: &str) -> Option<u128> {
    match m.get(k).map(String::as_str) {
        None | Some("") | Some("None") => None,
        Some(v) => {
            let n = v.strip_prefix("Some(").and_then(|x| x.strip_suffix(')')).unwrap_or(v);
            Some(n.parse().unwrap_or_else(|_| panic!("conformance: {k} = {v:?}")))
        }
    }
}

/// I4-6 (c)–(e) read off a sverify-p row's cells; `stop` relaxes the one equality a stopped run
/// cannot keep (`lookups` ≤ `impl_graphs`).
fn i4_identities(m: &BTreeMap<String, String>) -> Vec<String> {
    let n = |k: &str| i4_num(m, k);
    let mut bad = Vec::new();
    fn eq(bad: &mut Vec<String>, what: &str, a: u128, b: u128) {
        if a != b {
            bad.push(format!("{what}: {a} vs {b}"));
        }
    }
    eq(&mut bad, "spec complete + blocked", n("spec_complete") + n("spec_blocked"), n("spec_graphs"));
    eq(&mut bad, "impl complete + blocked", n("impl_complete") + n("impl_blocked"), n("impl_graphs"));
    eq(
        &mut bad,
        "flush entries + worker duplicates",
        n("spec_flush_entries") + n("spec_worker_duplicates"),
        n("spec_graphs"),
    );
    eq(&mut bad, "entries + merge duplicates", n("entries") + n("spec_merge_duplicates"), n("spec_flush_entries"));
    eq(&mut bad, "duplicates", n("duplicates"), n("spec_graphs") - n("entries"));
    eq(&mut bad, "entries = orders_held", n("entries"), n("orders_held"));
    eq(
        &mut bad,
        "lookup classes",
        n("lookups_signature_miss") + n("lookups_succeeded") + n("lookups_failed_after_tests"),
        n("lookups"),
    );
    eq(
        &mut bad,
        "containment tested",
        n("lookups_containment_tested"),
        n("lookups_succeeded") + n("lookups_failed_after_tests"),
    );
    eq(
        &mut bad,
        "uncovered flush + worker duplicates",
        n("uncovered_flush_entries") + n("uncovered_worker_duplicates"),
        n("reports"),
    );
    eq(
        &mut bad,
        "uncovered distinct + merge duplicates",
        n("uncovered_distinct") + n("uncovered_merge_duplicates"),
        n("uncovered_flush_entries"),
    );
    eq(&mut bad, "reports = uncovered_multiplicity", n("reports"), n("uncovered_multiplicity"));
    eq(&mut bad, "counter_reports", n("counter_reports"), n("reports"));
    let stopped = m["stopped_early"] == "true";
    if stopped {
        if n("lookups") > n("impl_graphs") {
            bad.push(format!("stopped: lookups {} > impl_graphs {}", n("lookups"), n("impl_graphs")));
        }
        if m["impl_end"] != "StoppedAtFirstReport" {
            bad.push(format!("stopped_early with impl_end {}", m["impl_end"]));
        }
        eq(&mut bad, "spawned_at_stop", n("spawned_at_stop"), n("impl_tasks") - 1);
    } else {
        if m["spec_errors"] == "0" {
            eq(&mut bad, "lookups = impl_graphs", n("lookups"), n("impl_graphs"));
            if m["impl_end"] != "StateSpaceExhausted" {
                bad.push(format!("impl_end {}", m["impl_end"]));
            }
        }
        eq(&mut bad, "spawned_at_stop (not stopped)", n("spawned_at_stop"), 0);
        eq(&mut bad, "uncovered_at_stop (not stopped)", n("uncovered_at_stop"), 0);
    }
    if m["spec_end"] != "StateSpaceExhausted" {
        bad.push(format!("spec_end {}", m["spec_end"]));
    }
    if n("spec_flushes") < n("spec_tasks") || n("impl_flushes") < n("impl_tasks") {
        bad.push("flushes < tasks".to_owned());
    }
    if i4_opt(m, "impl_distinct_summaries").is_some() {
        eq(
            &mut bad,
            "seen flush + worker duplicates",
            n("impl_seen_flush_entries") + n("impl_seen_worker_duplicates"),
            n("impl_graphs"),
        );
    }
    // (d) the first report: blank iff no report; the exact bound (ruling 6); the sum ≤ the wall
    let w = i4_opt(m, "wall_ms_at_first_report");
    let h = i4_opt(m, "vmhwm_kb_at_first_report");
    if w.is_some() != (n("reports") > 0) || h.is_some() != (n("reports") > 0) {
        bad.push(format!("first-report columns {w:?} {h:?} with {} reports", n("reports")));
    }
    if let Some(w) = w {
        if w > n("impl_wall_time_ms") {
            bad.push(format!("first report {w} ms > impl wall {} ms", n("impl_wall_time_ms")));
        }
        let sum = n("spec_wall_time_ms") + n("freeze_wall_time_ms") + w;
        if sum > n("wall_ms") {
            bad.push(format!("first-report sum {sum} ms > wall {} ms", n("wall_ms")));
        }
    }
    let class = if m["spec_errors"] != "0" {
        "Err"
    } else if n("uncovered_multiplicity") > 0 {
        "Reported"
    } else {
        "Conforms"
    };
    if m["verdict"] != class {
        bad.push(format!("verdict {} by run's rule {class}", m["verdict"]));
    }
    bad
}

/// I4-1 (a), (b), (d): the two engines' labels round-trip, three thread counts give three keys,
/// the non-canonical spellings are refused, and `conf_config` carries the knobs.
#[test]
fn i4_1_the_labels_round_trip_and_refuse_what_is_not_canonical() {
    let mut bad = Vec::new();
    let mut keys = BTreeSet::new();
    for t in [1, 2, 4, 16] {
        for fe in [7, 4096] {
            for distinct in [false, true] {
                for stop in [false, true] {
                    let c = GridConfig::new(GridEngine::SverifyP)
                        .threads(t)
                        .flush_entries(fe)
                        .impl_distinct(distinct)
                        .stop(stop);
                    let l = c.label();
                    if parse_label(&l) != Some(c.clone()) {
                        bad.push(format!("no round trip: {l}"));
                    }
                    keys.insert(l);
                }
            }
        }
        let e = GridConfig::new(GridEngine::ExploreP).threads(t);
        if parse_label(&e.label()) != Some(e.clone()) {
            bad.push(format!("no round trip: {}", e.label()));
        }
        keys.insert(e.label());
    }
    // 4 t × 2 F × 2 distinct × 2 stop, and 4 baselines: every label distinct
    if keys.len() != 32 + 4 {
        bad.push(format!("{} distinct keys of 36", keys.len()));
    }
    let base = "SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set";
    let ebase = "ExploreP/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep";
    for (got, want) in [
        (GridConfig::new(GridEngine::SverifyP).threads(4).label(), format!("{base}/threads=4")),
        (
            GridConfig::new(GridEngine::SverifyP).threads(4).flush_entries(7).label(),
            format!("{base}/threads=4/flush=7"),
        ),
        (
            GridConfig::new(GridEngine::SverifyP).threads(1).impl_distinct(true).label(),
            format!("{base}/threads=1/distinct=on"),
        ),
        (GridConfig::new(GridEngine::ExploreP).threads(16).label(), format!("{ebase}/threads=16")),
    ] {
        if got != want {
            bad.push(format!("label {got} != {want}"));
        }
    }
    let stateful = GridConfig::new(GridEngine::Stateful).label();
    for l in [
        format!("{base}/threads=0"),
        format!("{base}/threads=04"),
        format!("{base}/threads=+4"),
        base.to_owned(),
        format!("{base}/threads=4/flush=4096"),
        format!("{base}/threads=4/flush=0"),
        format!("{base}/threads=4/flush=07"),
        format!("{base}/flush=7/threads=4"),
        format!("{base}/threads=4/explore=sequential"),
        format!("{}/threads=4", base.replace("/index=set", "/index=compact/anti=true/pmemo=false")),
        format!("{}/threads=4", base.replace("/w=inf/quiet=false/index=set", "")),
        format!("{stateful}/threads=4"),
        format!("{ebase}/threads=0"),
        format!("{ebase}/threads=4/flush=7"),
        format!("{ebase}/w=inf/quiet=false/index=set/threads=4"),
        ebase.to_owned(),
    ] {
        if let Some(c) = parse_label(&l) {
            bad.push(format!("accepted: {l} as threads {} flush {}", c.threads, c.flush_entries));
        }
    }
    let f = fx("apps/a1/correct/spec/n2r2");
    let cc = GridConfig::new(GridEngine::SverifyP).threads(4).flush_entries(7).conf_config(&f);
    if (cc.engine, cc.threads, cc.flush_entries, cc.phase_peaks) != (Engine::SverifyP, 4, 7, false) {
        bad.push(format!(
            "conf_config: {:?} {} {} {}",
            cc.engine, cc.threads, cc.flush_entries, cc.phase_peaks
        ));
    }
    assert_eq!(LABEL_PIN, GridConfig::new(GridEngine::Enumerator).label());
    assert!(bad.is_empty(), "conformance: I4-1: {bad:#?}");
}

/// I4-1 (c): every key in every `rows*.csv` under `log/eval/` (the plan's stores) parses and
/// reprints byte for byte, as before I4: `parse_label` takes its new branch only on a label whose
/// engine field is `SverifyP` or `ExploreP`, and only the stores written since I4 (I4's, V-S's two)
/// hold one; on every other key the new fields are at their defaults.
#[test]
fn i4_1_c_every_stored_key_reprints() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../plan/traceForge/log/eval");
    let mut files = Vec::new();
    let mut stack = vec![root.clone()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap_or_else(|e| panic!("conformance: {}: {e}", d.display())) {
            let p = e.unwrap().path();
            if p.is_dir() {
                if p.file_name().is_some_and(|n| n != "runs") {
                    stack.push(p);
                }
            } else if p.file_name().and_then(|n| n.to_str()).is_some_and(|n| {
                n.starts_with("rows") && n.ends_with(".csv")
            }) {
                files.push(p);
            }
        }
    }
    files.sort();
    let mut bad = Vec::new();
    let (mut parsed, mut refused, mut new_engines) = (0usize, 0usize, 0usize);
    let mut per_store: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for p in &files {
        let Ok(rows) = read_rows(p) else {
            continue;
        };
        let name = p.strip_prefix(&root).unwrap().display().to_string();
        for r in rows {
            let Some(key) = r.get("key") else { continue };
            let label = key.split('|').nth(1).unwrap_or("");
            let entry = per_store.entry(name.clone()).or_default();
            match parse_key(key) {
                Some((_, c, ..)) => {
                    parsed += 1;
                    entry.0 += 1;
                    if c.label() != label {
                        bad.push(format!("{name}: {key} reprints as {}", c.label()));
                    }
                    let partitioned = matches!(c.engine, GridEngine::SverifyP | GridEngine::ExploreP);
                    if partitioned {
                        new_engines += 1;
                        // the stores written since I4 (I4's own; V-S's two, tester re-pin
                        // at V-S gate 3): no earlier store holds an I4 engine's key
                        let since_i4 = ["sverify-p-i4/", "sverify-p-vs/", "sverify-p-vs-curve/"];
                        if !since_i4.iter().any(|d| name.starts_with(d)) {
                            bad.push(format!("{name}: an I4 engine outside the stores since I4: {key}"));
                        }
                    } else if (c.threads, c.flush_entries, c.phase_peaks) != (1, 4096, false) {
                        bad.push(format!("{name}: {key}: the new fields not at their defaults"));
                    }
                }
                None => {
                    refused += 1;
                    entry.1 += 1;
                    if label.starts_with("SverifyP/") || label.starts_with("ExploreP/") {
                        bad.push(format!("{name}: an I4 key refused: {key}"));
                    }
                }
            }
        }
    }
    note!(
        "P41C\tstores {}\tkeys parsed {parsed}\trefused (legacy formats) {refused}\tI4 engines {new_engines}",
        files.len()
    );
    for (s, (a, b)) in &per_store {
        note!("P41C\t{s}\tparsed {a}\trefused {b}");
    }
    assert!(files.len() >= 5 && parsed > 1000, "conformance: non-vacuity: {} files, {parsed} keys", files.len());
    assert!(bad.is_empty(), "conformance: I4-1 (c): {bad:#?}");
}

/// I4-2 (a): every column either new arm pushes is declared (a missing name is dropped silently by
/// the store's layout).
#[test]
fn i4_2_a_every_pushed_column_is_declared() {
    let _g = serial();
    let f = fx("apps/a3/never-grant/spec/k2q2");
    let h: BTreeSet<&str> = header().into_iter().collect();
    let mut bad = Vec::new();
    for c in [
        GridConfig::new(GridEngine::SverifyP).threads(2).impl_distinct(true),
        GridConfig::new(GridEngine::ExploreP).threads(2),
    ] {
        let r = i4_run(&f, &c);
        for (k, _) in row_of(&r) {
            if !h.contains(k) {
                bad.push(format!("{:?}: {k}", c.engine));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: I4-2 (a): {bad:#?}");
}

/// I4-2 (b): the row is the outcome, column by column, on the five size-2 cells at t = 1 and 4
/// (the derivation's two tables), and the comparable columns equal the stateful row's on the same
/// cell.
#[test]
fn i4_2_b_the_row_is_the_outcome_and_the_comparable_columns_the_stateful_rows() {
    let _g = serial();
    let mut bad = Vec::new();
    for name in SIZE2_CELLS {
        let f = fx(name);
        let s = i4_cells(&i4_run(&f, &GridConfig::new(GridEngine::Stateful)));
        for t in [1, 4] {
            let r = i4_run(&f, &GridConfig::new(GridEngine::SverifyP).threads(t));
            let m = i4_cells(&r);
            let GridRaw::SverifyP(run) = &r.raw else { unreachable!() };
            let (o, c) = (&run.outcome, &run.outcome.counters);
            let ss = c.spec_set;
            let tag = format!("{name} t{t}");
            let mut want: Vec<(&str, String)> = vec![
                ("reports", c.reports.to_string()),
                ("spec_graphs", c.spec_graphs.to_string()),
                ("impl_graphs", c.impl_graphs.to_string()),
                ("orders_held", c.orders_held.to_string()),
                ("signatures", c.signatures.to_string()),
                ("lookups", c.lookups.to_string()),
                ("lookups_signature_miss", c.lookups_signature_miss.to_string()),
                ("lookups_succeeded", c.lookups_succeeded.to_string()),
                ("lookups_failed_after_tests", c.lookups_failed_after_tests.to_string()),
                ("lookups_containment_tested", c.lookups_containment_tested.to_string()),
                ("executions", o.executions.to_string()),
                ("entries", ss.entries.to_string()),
                ("buckets", ss.buckets.to_string()),
                ("bucket_max", ss.slot_max.to_string()),
                ("admitted", ss.admitted.to_string()),
                ("summary_bytes", ss.summary_bytes.to_string()),
                ("sig_bytes_est", ss.sig_bytes_est.to_string()),
                ("signatures_seen", ss.signatures_seen.to_string()),
                ("sig_aliases", ss.sig_aliases.to_string()),
                ("duplicates", (c.spec_worker_duplicates + c.spec_merge_duplicates).to_string()),
                ("sig_tests", (ss.sig_tests + c.sig_tests).to_string()),
                ("containment_tests", c.containment_tests.to_string()),
                ("coordinates_compared", c.coordinates_compared.to_string()),
                ("exact_hits", c.exact_hits.to_string()),
                ("index_kind", "set".to_owned()),
                ("threads", t.to_string()),
                ("flush_entries", "4096".to_owned()),
                ("iterations_until_split", f.config.iterations_until_split.to_string()),
                ("warmup", f.config.warmup.to_string()),
                ("state_batch_size", f.config.state_batch_size.to_string()),
                ("freeze_wall_time_ms", c.freeze_wall_time_ms.to_string()),
                ("spec_complete", c.spec_complete.to_string()),
                ("spec_blocked", c.spec_blocked.to_string()),
                ("impl_complete", c.impl_complete.to_string()),
                ("impl_blocked", c.impl_blocked.to_string()),
                ("spec_tasks", c.spec_tasks.to_string()),
                ("impl_tasks", c.impl_tasks.to_string()),
                ("spec_flushes", c.spec_flushes.to_string()),
                ("impl_flushes", c.impl_flushes.to_string()),
                ("spec_flush_entries", c.spec_flush_entries.to_string()),
                ("spec_worker_duplicates", c.spec_worker_duplicates.to_string()),
                ("spec_merge_duplicates", c.spec_merge_duplicates.to_string()),
                ("uncovered_distinct", c.uncovered_distinct.to_string()),
                ("uncovered_multiplicity", c.uncovered_multiplicity.to_string()),
                ("stopped_early", "false".to_owned()),
                ("spawned_at_stop", "0".to_owned()),
                ("phase_peaks", "process".to_owned()),
                ("spec_vmhwm_kb", String::new()),
                ("freeze_vmhwm_kb", String::new()),
                ("impl_vmhwm_kb", String::new()),
                ("impl_distinct_summaries", String::new()),
                ("verdict", "Conforms".to_owned()),
                ("spec_end", format!("{:?}", o.spec_end)),
                ("impl_end", format!("{:?}", o.impl_end)),
            ];
            want.push(("spec_wall_time_ms", c.spec_wall_time_ms.to_string()));
            for (k, v) in want {
                if m.get(k) != Some(&v) {
                    bad.push(format!("{tag}: {k} = {:?}, the outcome {v:?}", m.get(k)));
                }
            }
            if i4_opt(&m, "vm_peak_kb").is_none_or(|v| v == 0 || v > 10_000_000) {
                bad.push(format!("{tag}: vm_peak_kb {:?}", m.get("vm_peak_kb")));
            }
            for k in [
                "spec_graphs", "impl_graphs", "orders_held", "signatures", "lookups",
                "lookups_signature_miss", "lookups_succeeded", "lookups_failed_after_tests",
                "lookups_containment_tested", "reports", "counter_reports", "executions", "entries",
                "buckets", "bucket_max", "admitted", "duplicates", "summary_bytes", "sig_bytes_est",
                "signatures_seen", "sig_aliases", "exact_hits", "index_kind", "antichain_effective",
                "insert_tests", "impl_distinct_summaries", "spec_end", "impl_end", "spec_errors",
            ] {
                if m.get(k) != s.get(k) {
                    bad.push(format!("{tag}: {k} {:?}, the stateful row {:?}", m.get(k), s.get(k)));
                }
            }
            bad.extend(i4_identities(&m).into_iter().map(|b| format!("{tag}: {b}")));
        }
    }
    assert!(bad.is_empty(), "conformance: I4-2 (b): {bad:#?}");
}

/// The two-thread specification-error program of I3 test 23, as a fixture.
fn i4_spec_error_fixture() -> Fixture {
    let mut f = fx("apps/a1/correct/spec/n2r2");
    f.name = "i4:spec-error/bag".to_owned();
    f.specification = prog(|| {
        let _x = named("x", || {});
        let _a = named("a", || crate::assert(false));
    });
    f.implementation = prog(|| {
        let _x = named("x", || {});
        let _a = named("a", || {});
    });
    f.visible = vec!["a".to_owned(), "x".to_owned()];
    f.config = Config::builder().with_cons_type(ConsType::Bag).with_seed(0).build();
    f
}

/// I4-6 (a)–(e): one row of each verdict class, the ends, the identities and the first-report
/// columns, and the class equal to `sverify_p::run`'s (the public verdict) on the same
/// configuration.
#[test]
fn i4_6_the_verdict_classes_the_ends_and_the_identities() {
    let _g = serial();
    let mut bad = Vec::new();
    let cases = [
        (fx("apps/a1/correct/spec/n2r2"), 4, false, "Conforms"),
        (fx("apps/a3/never-grant/spec/k2q2"), 4, false, "Reported"),
        (i4_spec_error_fixture(), 2, false, "Err"),
        (fx("apps/a1/silent/spec/n2r3"), 4, true, "Reported"),
    ];
    for (f, t, stop, class) in cases {
        let c = GridConfig::new(GridEngine::SverifyP).threads(t).stop(stop);
        let m = i4_cells(&i4_run(&f, &c));
        let tag = format!("{} t{t} stop {stop}", f.name);
        if m["verdict"] != class {
            bad.push(format!("{tag}: verdict {}", m["verdict"]));
        }
        let (i, s) = (Arc::clone(&f.implementation), Arc::clone(&f.specification));
        let public = match crate::conformance::verify(c.conf_config(&f), move || i(), move || s()) {
            Ok(ConfVerdict::Conforms(_)) => "Conforms",
            Ok(ConfVerdict::Reported(_)) => "Reported",
            Ok(ConfVerdict::Inconclusive(_)) => "Inconclusive",
            Err(_) => "Err",
        };
        if public != class {
            bad.push(format!("{tag}: the public verdict {public}"));
        }
        let want_end = match (class, stop) {
            ("Err", _) => "Unknown",
            (_, true) => "StoppedAtFirstReport",
            _ => "StateSpaceExhausted",
        };
        if m["impl_end"] != want_end {
            bad.push(format!("{tag}: impl_end {}", m["impl_end"]));
        }
        if class == "Reported" && !stop && m["reports"] != "8" {
            bad.push(format!("{tag}: reports {} (the record's 8)", m["reports"]));
        }
        if stop && m["stopped_early"] != "true" {
            bad.push(format!("{tag}: stopped_early {}", m["stopped_early"]));
        }
        if class != "Err" {
            bad.extend(i4_identities(&m).into_iter().map(|b| format!("{tag}: {b}")));
        } else if m["spec_errors"] == "0" {
            bad.push(format!("{tag}: no specification error recorded"));
        }
        note!(
            "P46\t{tag}\tverdict {}\treports {}\timpl_end {}\tW {:?}\timpl_wall {}\tspawned_at_stop {}",
            m["verdict"],
            m["reports"],
            m["impl_end"],
            m.get("wall_ms_at_first_report"),
            m["impl_wall_time_ms"],
            m["spawned_at_stop"]
        );
    }
    assert!(bad.is_empty(), "conformance: I4-6: {bad:#?}");
}

/// I4-4 (a)–(d) on exhaustive pairs (`stop` off), the five size-2 cells at t = 1 and 4: the
/// baseline's per-side complete/blocked/graphs and task counts equal the sverify-p row's;
/// `vm_peak_kb` present and within the limit; the peaks off (R1).
#[test]
fn i4_4_the_baseline_equals_the_exhaustive_row_per_side() {
    let _g = serial();
    let mut bad = Vec::new();
    for name in SIZE2_CELLS {
        let f = fx(name);
        for t in [1, 4] {
            let p = i4_cells(&i4_run(&f, &GridConfig::new(GridEngine::SverifyP).threads(t)));
            let b = i4_cells(&i4_run(&f, &GridConfig::new(GridEngine::ExploreP).threads(t)));
            let tag = format!("{name} t{t}");
            for k in [
                "spec_complete", "spec_blocked", "impl_complete", "impl_blocked", "spec_graphs",
                "impl_graphs", "spec_tasks", "impl_tasks", "threads", "warmup",
                "iterations_until_split", "state_batch_size",
            ] {
                if p.get(k) != b.get(k) {
                    bad.push(format!("{tag}: {k} {:?}, the baseline {:?}", p.get(k), b.get(k)));
                }
            }
            if i4_opt(&b, "vm_peak_kb").is_none_or(|v| v == 0 || v > 10_000_000) {
                bad.push(format!("{tag}: the baseline's vm_peak_kb {:?}", b.get("vm_peak_kb")));
            }
            if b["phase_peaks"] != "process" || !b["spec_vmhwm_kb"].is_empty() || !b["impl_vmhwm_kb"].is_empty() {
                bad.push(format!("{tag}: the baseline reset in the suite"));
            }
            if b["executions"] != b["impl_graphs"] {
                bad.push(format!("{tag}: executions {} vs impl_graphs {}", b["executions"], b["impl_graphs"]));
            }
            note!(
                "P44\t{tag}\tspec {}/{}\timpl {}/{}\ttasks {}/{}",
                b["spec_complete"],
                b["spec_blocked"],
                b["impl_complete"],
                b["impl_blocked"],
                b["spec_tasks"],
                b["impl_tasks"]
            );
        }
    }
    assert!(bad.is_empty(), "conformance: I4-4: {bad:#?}");
}

/// The text of the item that starts at the line beginning `start` and ends at its closing brace
/// (the first later line that is exactly `}`), comment lines dropped. Not the next column-0 line:
/// rustfmt puts a multi-line signature's `) -> T {` at column 0.
fn i4_item(src: &str, start: &str) -> Option<String> {
    let lines: Vec<&str> = src.lines().collect();
    let a = lines.iter().position(|l| l.starts_with(start))?;
    let b = (a + 1..lines.len()).find(|&i| lines[i] == "}")?;
    Some(
        lines[a..=b]
            .iter()
            .filter(|l| !l.trim_start().starts_with("//"))
            .copied()
            .collect::<Vec<_>>()
            .join("\n"),
    )
}

/// Every `phase(` call's text in `body`, from `phase(` to its matching `)`.
fn i4_phase_calls(body: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut from = 0;
    while let Some(at) = body[from..].find("phase(") {
        let s = from + at;
        let before = body[..s].chars().last();
        from = s + "phase(".len();
        if before.is_some_and(|c| c.is_alphanumeric() || c == '_') {
            continue;
        }
        let mut depth = 0i32;
        for (i, ch) in body[s..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        out.push(body[s..s + i + 1].to_owned());
                        break;
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// The F1 source shape (rev 1.2 I4-9) of an engine source: the failures, empty when the shape holds.
fn i4_f1_shape(src: &str) -> Vec<String> {
    let mut bad = Vec::new();
    let Some(phase) = i4_item(src, "fn phase(") else {
        return vec!["no `fn phase(` item".to_owned()];
    };
    // non-vacuity: the slice is the whole item, not its signature
    if !phase.contains("-> PhaseResult {") || !phase.contains("verify_partitioned_rayon_with(") {
        bad.push("the phase slice is not the whole item".to_owned());
    }
    let sig = &phase[..phase.find("-> PhaseResult {").unwrap_or(phase.len())];
    if !sig.contains("started: Instant") {
        bad.push("(i) `phase` declares no `started: Instant`".to_owned());
    }
    if phase.contains("Instant::now()") {
        bad.push(format!("(ii) `phase` reads {} clock(s) of its own", phase.matches("Instant::now()").count()));
    }
    let Some(rw) = i4_item(src, "pub(crate) fn run_with(") else {
        bad.push("no `run_with` item".to_owned());
        return bad;
    };
    for b in ["let impl_started = Instant::now();", "let spec_started = Instant::now();"] {
        if rw.matches(b).count() != 1 {
            bad.push(format!("(iii) `run_with` binds `{b}` {} times", rw.matches(b).count()));
        }
    }
    if rw.contains("impl_started: Instant::now()")
        || !(rw.contains("impl_started,") || rw.contains("impl_started: impl_started,"))
    {
        bad.push("(iii) the `Frozen` literal does not take the `impl_started` binding".to_owned());
    }
    let calls = i4_phase_calls(&rw);
    for (side, binding) in [("\"implementation\"", "impl_started"), ("\"specification\"", "spec_started")] {
        match calls.iter().find(|c| c.contains(side)) {
            Some(c) if c.contains(binding) => {}
            Some(c) => bad.push(format!("(iii) the {side} call passes no `{binding}`: {c}")),
            None => bad.push(format!("(iii) no {side} `phase(` call")),
        }
    }
    bad
}

/// I4-9, the F1 pin (rev 1.2): the one-instant shape holds on this tree's engine.
#[test]
fn i4_9_f1_the_phase_clock_is_the_callers_instant() {
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/sverify_p.rs"),
    )
    .unwrap();
    let bad = i4_f1_shape(&src);
    assert!(bad.is_empty(), "conformance: I4-9 F1: {bad:#?}");
}

/// I4-9, the pin's red evidence: the same check on another engine source (`I4_OLD_SVERIFY_P`, I3's
/// f081e3ca) fails each of (i), (ii) and (iii). Ignored: the file is not part of the tree.
#[test]
#[ignore]
fn i4_9_f1_the_shape_is_red_on_the_two_clock_engine() {
    let Ok(path) = std::env::var("I4_OLD_SVERIFY_P") else {
        return;
    };
    let bad = i4_f1_shape(&std::fs::read_to_string(path).unwrap());
    note!("P49\t{bad:?}");
    for item in ["(i)", "(ii)", "(iii)"] {
        assert!(bad.iter().any(|b| b.starts_with(item)), "conformance: {item} not red: {bad:#?}");
    }
}

/// I4-3 (a), and (b) on two runs with the knob on — ignored, its own process (R1): the reset
/// drops `VmHWM` after a freed 64 MiB allocation; then a reporting sverify-p run and its baseline
/// with `phase_peaks` on: each phase peak ≤ `vmhwm_kb_max`, the first-report memory ≥ the
/// specification phase's peak (R3), the grid's `after` reading ≥ `vmhwm_kb_max` (R4).
#[test]
#[ignore]
fn i4_3_a_the_reset_and_the_peaks() {
    let Ok(_) = std::env::var("I4_RESET") else {
        return;
    };
    let hwm = crate::conformance::grid::vm_hwm_kb;
    let h0 = hwm().unwrap();
    let mut v: Vec<u8> = vec![0; 64 << 20];
    for i in (0..v.len()).step_by(4096) {
        v[i] = 1;
    }
    let h1 = hwm().unwrap();
    std::hint::black_box(&v);
    drop(v);
    let ok = sverify_p::reset_vm_hwm();
    let h2 = hwm().unwrap();
    note!("P43A\tVmHWM before {h0} kB, after touching 64 MiB {h1} kB, after free and reset {h2} kB, reset {ok}");
    assert!(ok, "conformance: the reset failed");
    assert!(h1 >= h0 + 60 * 1024, "conformance: non-vacuity: the allocation did not show");
    assert!(h2 + 32 * 1024 < h1, "conformance: the reset did not drop VmHWM");
    let mut bad = Vec::new();
    for (name, engine) in [
        ("apps/a3/never-grant/spec/k2q2", GridEngine::SverifyP),
        ("apps/a4/hash/a4a/k3q3m3", GridEngine::SverifyP),
        ("apps/a4/hash/a4a/k3q3m3", GridEngine::ExploreP),
    ] {
        let f = fx(name);
        let r = i4_run(&f, &GridConfig::new(engine).threads(4).phase_peaks(true));
        let m = i4_cells(&r);
        let max = i4_opt(&m, "vmhwm_kb_max").unwrap_or(0);
        let tag = format!("{name} {engine:?}");
        if m["phase_peaks"] != "per-phase" {
            bad.push(format!("{tag}: phase_peaks {}", m["phase_peaks"]));
        }
        let phases: &[&str] = if engine == GridEngine::SverifyP {
            &["spec_vmhwm_kb", "freeze_vmhwm_kb", "impl_vmhwm_kb"]
        } else {
            &["spec_vmhwm_kb", "impl_vmhwm_kb"]
        };
        for k in phases {
            match i4_opt(&m, k) {
                Some(p) if p <= max => {}
                other => bad.push(format!("{tag}: {k} {other:?} against max {max}")),
            }
        }
        if i4_opt(&m, "vm_hwm_kb_after").is_none_or(|a| a < max) {
            bad.push(format!("{tag}: vm_hwm_kb_after {:?} < max {max}", m.get("vm_hwm_kb_after")));
        }
        if let (Some(h), Some(s)) = (i4_opt(&m, "vmhwm_kb_at_first_report"), i4_opt(&m, "spec_vmhwm_kb")) {
            if h < s {
                bad.push(format!("{tag}: first-report memory {h} < the specification's peak {s}"));
            }
        }
        note!(
            "P43B\t{tag}\tspec {:?}\tfreeze {:?}\timpl {:?}\tmax {max}\tafter {:?}\tat first report {:?}\tvm_peak {:?}",
            m.get("spec_vmhwm_kb"),
            m.get("freeze_vmhwm_kb"),
            m.get("impl_vmhwm_kb"),
            m.get("vm_hwm_kb_after"),
            m.get("vmhwm_kb_at_first_report"),
            m.get("vm_peak_kb")
        );
    }
    assert!(bad.is_empty(), "conformance: I4-3: {bad:#?}");
}

/// The 52 rows of I4-8 (b): the main matrix (eight fixtures × t ∈ {1, 4, 16} × {sverify-p,
/// baseline}, `stop` off) and the four diagnostics (A3 never-grant k2q2 and A1 silent n2r3 at
/// t = 4, `stop` off and on, sverify-p only).
fn i4_store_rows() -> Vec<RowSpec> {
    let row = |fixture: &str, config: GridConfig, variant: &str| RowSpec {
        fixture: fixture.to_owned(),
        config,
        rep: 0,
        tier: Tier::default_tier(),
        run_kind: RunKind::Timed,
        family: "sverify-p-i4".to_owned(),
        knobs: String::new(),
        k: [None; 4],
        variant: variant.to_owned(),
        twin_key: String::new(),
        series: None,
    };
    let mut rows = Vec::new();
    let main = SIZE2_CELLS
        .iter()
        .copied()
        .chain(["apps/a3/fifo/spec/k3q3", "2pc/leader/conf/n4", "apps/a4/hash/a4a/k3q3m3"]);
    for name in main {
        for t in [1, 4, 16] {
            rows.push(row(name, GridConfig::new(GridEngine::SverifyP).threads(t), "conforming"));
            rows.push(row(name, GridConfig::new(GridEngine::ExploreP).threads(t), "baseline"));
        }
    }
    for name in ["apps/a3/never-grant/spec/k2q2", "apps/a1/silent/spec/n2r3"] {
        for stop in [false, true] {
            rows.push(row(
                name,
                GridConfig::new(GridEngine::SverifyP).threads(4).stop(stop),
                "violating",
            ));
        }
    }
    rows
}

/// I4-8 (b): the store, through the driver (one child process per row, the driver's own
/// sampling, censoring and record) — ignored; `I4_STORE` the output directory. The git probe is
/// replaced: the lead copy is not a repository; the commit column names the build instead.
#[test]
#[ignore]
fn i4_8_b_the_store() {
    let Ok(out) = std::env::var("I4_STORE") else {
        return;
    };
    let rows = i4_store_rows();
    assert_eq!(rows.len(), 52);
    let spec = Spec {
        name: "SVERIFY-P-I4".to_owned(),
        rows,
    };
    let mut probes = Probes::real();
    let commit = std::env::var("I4_COMMIT").unwrap_or_else(|_| "unknown".to_owned());
    probes.git = Box::new(move || (commit.clone(), false));
    let d = Driver {
        spec: spec.clone(),
        specs: vec![spec],
        out_dir: std::path::PathBuf::from(out),
        sample_period: std::time::Duration::from_millis(100),
        probes,
        allow_mixed: false,
        only: std::env::var("EVAL_ONLY").ok(),
    };
    match d.run() {
        Ok(s) => note!(
            "P48\tran {}\tskipped present {}\tcensored {}\tstore {}",
            s.ran,
            s.skipped_present,
            s.censored,
            s.store.display()
        ),
        Err(e) => panic!("conformance: the driver refused: {}", e.text()),
    }
}

/// I4-8 (b)'s checks on the store (`I4_STORE`) — ignored: every row ok and per-phase; the 24
/// exhaustive pairs with I4-4 (a)–(d) and P0's three splits; every sverify-p row's identities
/// (I4-6); the four diagnostics' first-report and stop fields; the peaks (I4-3 (b)).
#[test]
#[ignore]
fn i4_8_b_the_store_checks() {
    let Ok(out) = std::env::var("I4_STORE") else {
        return;
    };
    let rows = read_rows(&std::path::Path::new(&out).join("rows.csv"))
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let mut bad = Vec::new();
    if rows.len() != 52 {
        bad.push(format!("{} rows", rows.len()));
    }
    let by_key: BTreeMap<String, &BTreeMap<String, String>> =
        rows.iter().map(|r| (r["key"].clone(), r)).collect();
    for spec in i4_store_rows() {
        let key = spec.key("release");
        let Some(m) = by_key.get(&key) else {
            bad.push(format!("missing {key}"));
            continue;
        };
        let t = spec.config.threads;
        let tag = format!("{} {:?} t{t} stop {}", spec.fixture, spec.config.engine, spec.config.stop_at_first_report);
        if m["end_class"] != "ok" {
            bad.push(format!("{tag}: end_class {}", m["end_class"]));
            continue;
        }
        if m["phase_peaks"] != "per-phase" {
            bad.push(format!("{tag}: phase_peaks {}", m["phase_peaks"]));
        }
        let max = i4_opt(m, "vmhwm_kb_max").unwrap_or(0);
        let child = i4_opt(m, "rss_child_hwm_kb").unwrap_or(0);
        let peaks: &[&str] = if spec.config.engine == GridEngine::SverifyP {
            &["spec_vmhwm_kb", "freeze_vmhwm_kb", "impl_vmhwm_kb"]
        } else {
            &["spec_vmhwm_kb", "impl_vmhwm_kb"]
        };
        for k in peaks {
            if i4_opt(m, k).is_none_or(|p| p > max) {
                bad.push(format!("{tag}: {k} {:?} against max {max}", m.get(*k)));
            }
        }
        if max > child {
            bad.push(format!("{tag}: vmhwm_kb_max {max} > rss_child_hwm_kb {child}"));
        }
        if i4_opt(m, "vm_peak_kb").is_none_or(|v| v == 0 || v > 10_000_000) {
            bad.push(format!("{tag}: vm_peak_kb {:?}", m.get("vm_peak_kb")));
        }
        if spec.config.engine == GridEngine::ExploreP {
            continue;
        }
        bad.extend(i4_identities(m).into_iter().map(|b| format!("{tag}: {b}")));
        if let (Some(h), Some(s)) = (i4_opt(m, "vmhwm_kb_at_first_report"), i4_opt(m, "spec_vmhwm_kb")) {
            if h < s {
                bad.push(format!("{tag}: first-report memory {h} < the specification's peak {s}"));
            }
        }
        if spec.variant == "violating" {
            note!(
                "P48D\t{tag}\tverdict {}\treports {}\tuncovered {}\timpl_graphs {}\timpl_end {}\tW {} ms\tH {} kB\tsum {} ms\tstopped {}\tspawned_at_stop {}\timpl_tasks {}\tuncovered_at_stop {}",
                m["verdict"], m["reports"], m["uncovered_distinct"], m["impl_graphs"], m["impl_end"],
                m["wall_ms_at_first_report"], m["vmhwm_kb_at_first_report"],
                i4_num(m, "spec_wall_time_ms") + i4_num(m, "freeze_wall_time_ms") + i4_opt(m, "wall_ms_at_first_report").unwrap_or(0),
                m["stopped_early"], m["spawned_at_stop"], m["impl_tasks"], m["uncovered_at_stop"]
            );
            continue;
        }
        // an exhaustive main-matrix row: its pair
        let pair = RowSpec {
            config: GridConfig::new(GridEngine::ExploreP).threads(t),
            variant: "baseline".to_owned(),
            ..spec.clone()
        };
        let Some(b) = by_key.get(&pair.key("release")) else {
            bad.push(format!("{tag}: no baseline"));
            continue;
        };
        for k in [
            "spec_complete", "spec_blocked", "impl_complete", "impl_blocked", "spec_graphs",
            "impl_graphs", "spec_tasks", "impl_tasks",
        ] {
            if m.get(k) != b.get(k) {
                bad.push(format!("{tag}: {k} {:?}, the baseline {:?}", m.get(k), b.get(k)));
            }
        }
        let p0 = match spec.fixture.as_str() {
            "apps/a3/fifo/spec/k3q3" => Some(("impl", 330_252, 0)),
            "2pc/leader/conf/n4" => Some(("impl", 1_839_744, 0)),
            "apps/a4/hash/a4a/k3q3m3" => Some(("spec", 0, 45_360)),
            _ => None,
        };
        if let Some((side, c, bl)) = p0 {
            let got = (i4_num(b, &format!("{side}_complete")), i4_num(b, &format!("{side}_blocked")));
            if got != (c, bl) {
                bad.push(format!("{tag}: the baseline's {side} {got:?}, P0's {:?}", (c, bl)));
            }
        }
        if m["verdict"] != "Conforms" || m["reports"] != "0" {
            bad.push(format!("{tag}: verdict {} reports {}", m["verdict"], m["reports"]));
        }
        note!(
            "P48P\t{tag}\tspec {}/{} impl {}/{}\ttasks {}/{}\twall spec {} freeze {} impl {} | base {} {}\tpeaks spec {} freeze {} impl {} max {} | base {} {} {}\tvm_peak {} | {}\tchild {} | {}",
            m["spec_complete"], m["spec_blocked"], m["impl_complete"], m["impl_blocked"],
            m["spec_tasks"], m["impl_tasks"],
            m["spec_wall_time_ms"], m["freeze_wall_time_ms"], m["impl_wall_time_ms"],
            b["spec_wall_time_ms"], b["impl_wall_time_ms"],
            m["spec_vmhwm_kb"], m["freeze_vmhwm_kb"], m["impl_vmhwm_kb"], m["vmhwm_kb_max"],
            b["spec_vmhwm_kb"], b["impl_vmhwm_kb"], b["vmhwm_kb_max"],
            m["vm_peak_kb"], b["vm_peak_kb"], m["rss_child_hwm_kb"], b["rss_child_hwm_kb"]
        );
    }
    assert!(bad.is_empty(), "conformance: I4-8 (b): {bad:#?}");
}

/// I4 gate 4 round 01 M1 (I4-3 R5 on both returns of `run_with`): with `phase_peaks` on and every
/// reset failing (the engine's seam `set_reset_fails_for_test`), the specification-error return and
/// the normal return both leave `phase_peaks` false and the three phase columns blank, and keep the
/// process peak (`vmhwm_kb_max` `Some`). Red on a2f124e5 (with the seam): its specification-error
/// return set `phase_peaks` false but kept `spec_vmhwm_kb`. The knob is on in this test only; with
/// the seam on nothing is written to `/proc/self/clear_refs` (R1). The seam is process-wide: the
/// test holds `serial()` and turns it off on every exit.
#[test]
fn i4_3_r5_a_failed_reset_blanks_the_phase_columns_on_both_returns() {
    let _g = serial();
    struct SeamOff;
    impl Drop for SeamOff {
        fn drop(&mut self) {
            sverify_p::set_reset_fails_for_test(false);
        }
    }
    sverify_p::set_reset_fails_for_test(true);
    let _off = SeamOff;
    let mut bad = Vec::new();
    for (f, error_return) in [(i4_spec_error_fixture(), true), (fx("apps/a2/pb/spec/k2q2"), false)] {
        let cc = GridConfig::new(GridEngine::SverifyP).threads(2).phase_peaks(true).conf_config(&f);
        assert!(cc.phase_peaks, "conformance: the knob reaches the engine");
        let o = sverify_p::run_with(&cc, &f.implementation, &f.specification);
        let c = &o.counters;
        // non-vacuity: the two returns
        let took = !o.spec_errors.is_empty();
        if took != error_return {
            bad.push(format!("{}: the specification-error return taken: {took}", f.name));
        }
        if c.phase_peaks
            || c.spec_vmhwm_kb.is_some()
            || c.freeze_vmhwm_kb.is_some()
            || c.impl_vmhwm_kb.is_some()
            || c.vmhwm_kb_max.is_none()
        {
            bad.push(format!(
                "{}: phase_peaks {} spec {:?} freeze {:?} impl {:?} max {:?}",
                f.name,
                c.phase_peaks,
                c.spec_vmhwm_kb,
                c.freeze_vmhwm_kb,
                c.impl_vmhwm_kb,
                c.vmhwm_kb_max
            ));
        }
        note!(
            "P43R5\t{}\terror return {took}\tphase_peaks {}\tspec {:?}\tfreeze {:?}\timpl {:?}\tmax {:?}",
            f.name,
            c.phase_peaks,
            c.spec_vmhwm_kb,
            c.freeze_vmhwm_kb,
            c.impl_vmhwm_kb,
            c.vmhwm_kb_max
        );
    }
    assert!(bad.is_empty(), "conformance: I4-3 R5: {bad:#?}");
}

// =========================================================================
// SVERIFY-P V-S (gate 3, the tester): the parallel stateful engine against the sequential one on
// the 144-fixture catalogue, and the speed-up curves — criteria `SVERIFY-P-VS.md` rev 1.2 and
// `log/dev/SVERIFY-P.derived-vs.md` (efb90b18). The references are MIN-ENGINES §4's package
// (`log/dev/MIN-ENGINES.validation/`, made on `c884d2e`), read by extracting its record tarballs into
// `TMPDIR` through `tar`; nothing sequential is re-run (ruling 3).
// =========================================================================

/// The catalogue's twelve fixtures beyond the pilot (§4's C1), the four `e1:*` last.
const VS_EXTRA: [&str; 12] = [
    "2pc/leader/conf/n2",
    "2pc/leader/conf/n3",
    "apps/a1/correct/spec/n3r3",
    "apps/a2/pb/spec/k2q2",
    "apps/a2/pb/spec/k3q3",
    "apps/a3/fifo/spec/k3q3",
    "apps/a4/hash/a4a/k2q2m2",
    "apps/a4/hash/a4a/k3q3m3",
    "e1:chain/bag",
    "e1:nested4/self",
    "e1:race-bad/bag",
    "e1:race/bag",
];

/// The 144 catalogue fixtures: the pilot, then the twelve.
fn vs_catalogue() -> Vec<&'static str> {
    PILOT_NAMES.iter().copied().chain(VS_EXTRA).collect()
}

/// One fixture's record from the package.
#[derive(Clone, Debug, Default)]
struct VsRecord {
    verdict: String,
    reports: u128,
    spec_graphs: u128,
    impl_graphs: u128,
    /// (side, execs, block), plain Must (`E1P`).
    spec_split: (u128, u128),
    impl_split: (u128, u128),
    /// The distinct `(Sig, counts)` per side (`E1E`).
    spec_distinct: u128,
    impl_distinct: u128,
    /// SVerify-S's lookup classes (`E1S`): succeeded, failed after tests, signature miss.
    lookups: (u128, u128, u128),
    /// The uncovered summaries of SVerify-S on `Set` (`UNCSET`), with multiplicities.
    uncovered: BTreeMap<(String, String), usize>,
    /// `E9 … e9s Set … first some|none`.
    first_some: Option<bool>,
}

/// The package's records, keyed by fixture name: `part1-rerun.tar.gz` and `part1-aux.tar.gz`
/// extracted into a fresh directory under `TMPDIR` through `tar` (ruling 10), read, and left there.
fn vs_records() -> BTreeMap<String, VsRecord> {
    let pkg = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../plan/traceForge/log/dev/MIN-ENGINES.validation");
    let tmp = std::env::var("TMPDIR").expect("conformance: V-S reads the package under TMPDIR");
    let dir = std::path::Path::new(&tmp).join(format!("vs-package-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("conformance: the extraction directory");
    for t in ["part1-rerun.tar.gz", "part1-aux.tar.gz"] {
        let st = std::process::Command::new("tar")
            .arg("xzf")
            .arg(pkg.join(t))
            .arg("-C")
            .arg(&dir)
            .status()
            .expect("conformance: tar");
        assert!(st.success(), "conformance: tar xzf {t}");
    }
    let field = |p: &[&str], i: usize| -> u128 {
        p[i].split(' ').nth(1).unwrap_or_else(|| panic!("conformance: field {i} of {p:?}")).parse().unwrap()
    };
    let mut out: BTreeMap<String, VsRecord> = BTreeMap::new();
    for sub in ["rerun", "aux"] {
        for e in std::fs::read_dir(dir.join(sub)).expect("conformance: the extracted records") {
            let text = std::fs::read_to_string(e.unwrap().path()).unwrap();
            let mut name = String::new();
            let mut unc: Vec<(String, String)> = Vec::new();
            for l in text.lines() {
                let p: Vec<&str> = l.split('\t').collect();
                if p.len() > 1 && p[0].starts_with("E") {
                    name = p[1].to_owned();
                }
                let r = out.entry(name.clone()).or_default();
                match p[0] {
                    "E1T" => {
                        r.verdict = p[3].split(' ').nth(1).unwrap().to_owned();
                        r.reports = field(&p, 4);
                        r.spec_graphs = field(&p, 5);
                        r.impl_graphs = field(&p, 6);
                    }
                    "E1P" => {
                        let v = (field(&p, 3), field(&p, 4));
                        if p[2] == "specification" {
                            r.spec_split = v;
                        } else {
                            r.impl_split = v;
                        }
                    }
                    "E1E" => {
                        if p[3] == "specification" {
                            r.spec_distinct = field(&p, 5);
                        } else {
                            r.impl_distinct = field(&p, 5);
                        }
                    }
                    "E1S" => {
                        let l3: Vec<u128> =
                            p[7].split(' ').nth(1).unwrap().split('/').map(|x| x.parse().unwrap()).collect();
                        r.lookups = (l3[0], l3[1], l3[2]);
                    }
                    "E9" if p[3] == "e9s" && p[4] == "Set" => {
                        r.first_some = Some(p[6] == "first some");
                    }
                    "UNCSET" => unc.push((p[1].to_owned(), p[2].to_owned())),
                    _ => {}
                }
            }
            if sub == "rerun" {
                // `UNCSET` lines precede the file's `E1T` line: keyed by the file's fixture.
                let r = out.get_mut(&name).unwrap();
                for k in unc {
                    *r.uncovered.entry(k).or_default() += 1;
                }
            }
        }
    }
    out.remove("");
    out
}

/// SVerify-P's uncovered summaries as the record writes them: `Sig` Debug, the counts comma-joined.
fn vs_uncovered(o: &SverifyPOutcome) -> BTreeMap<(String, String), usize> {
    o.counters
        .uncovered
        .iter()
        .map(|u| {
            let c = u.counts();
            let inner = c
                .trim_start_matches("U8(")
                .trim_start_matches("U16(")
                .trim_start_matches('[')
                .trim_end_matches(')')
                .trim_end_matches(']');
            let counts = inner.split(", ").collect::<Vec<_>>().join(",");
            ((u.signature().to_owned(), counts), u.multiplicity())
        })
        .collect()
}

/// V-S1's checks of one sverify-p row (store cells or an in-process row) against its record: the
/// failures, one per column.
fn vs_row_checks(m: &BTreeMap<String, String>, r: &VsRecord) -> Vec<(&'static str, String)> {
    let mut bad: Vec<(&'static str, String)> = Vec::new();
    let mut eq = |col: &'static str, got: u128, want: u128| {
        if got != want {
            bad.push((col, format!("{got} vs the record's {want}")));
        }
    };
    eq("reports", i4_num(m, "reports"), r.reports);
    eq("uncovered_multiplicity", i4_num(m, "uncovered_multiplicity"), r.reports);
    eq("spec_graphs", i4_num(m, "spec_graphs"), r.spec_graphs);
    eq("impl_graphs", i4_num(m, "impl_graphs"), r.impl_graphs);
    eq("spec_complete", i4_num(m, "spec_complete"), r.spec_split.0);
    eq("spec_blocked", i4_num(m, "spec_blocked"), r.spec_split.1);
    eq("impl_complete", i4_num(m, "impl_complete"), r.impl_split.0);
    eq("impl_blocked", i4_num(m, "impl_blocked"), r.impl_split.1);
    eq("orders_held", i4_num(m, "orders_held"), r.spec_distinct);
    eq(
        "impl_distinct_summaries",
        i4_opt(m, "impl_distinct_summaries").unwrap_or(u128::MAX),
        r.impl_distinct,
    );
    eq("lookups_succeeded", i4_num(m, "lookups_succeeded"), r.lookups.0);
    eq("lookups_failed_after_tests", i4_num(m, "lookups_failed_after_tests"), r.lookups.1);
    eq("lookups_signature_miss", i4_num(m, "lookups_signature_miss"), r.lookups.2);
    let want = if r.verdict == "conforms" { "Conforms" } else { "Reported" };
    if m["verdict"] != want {
        bad.push(("verdict", format!("{} vs the record's {}", m["verdict"], r.verdict)));
    }
    let some = i4_opt(m, "wall_ms_at_first_report").is_some();
    if Some(some) != r.first_some || i4_opt(m, "vmhwm_kb_at_first_report").is_some() != some {
        bad.push(("first_report", format!("{some} vs the record's {:?}", r.first_some)));
    }
    for (b, _) in i4_identities(m).into_iter().map(|b| (b, ())) {
        bad.push(("identities", b));
    }
    // V-S gate 4 round 01 M1: VS-1's two search ends (`end_class == "ok"` says only that the child
    // completed)
    for col in ["spec_end", "impl_end"] {
        if m.get(col).map(String::as_str) != Some("StateSpaceExhausted") {
            bad.push((col, format!("{:?}, not StateSpaceExhausted", m.get(col))));
        }
    }
    bad
}

/// V-S's store rows by part: `catalogue` (140 × t ∈ {1, 4, 16}, `distinct=on`), `curves` (lock
/// k3q3 and leader n4 × t ∈ {1, 2, 4, 8, 16} × {SverifyP, ExploreP}, `distinct` off), `k4q4` (lock
/// k4q4 × t ∈ {1, 16} × both, `distinct` off, the tier `k4q4-16g`: 3 600 s / 16 000 000 kB).
fn vs_store_rows(part: &str) -> Vec<RowSpec> {
    let row = |fixture: &str, config: GridConfig, tier: Tier, variant: &str| RowSpec {
        fixture: fixture.to_owned(),
        config,
        rep: 0,
        tier,
        run_kind: RunKind::Timed,
        family: "sverify-p-vs".to_owned(),
        knobs: String::new(),
        k: [None; 4],
        variant: variant.to_owned(),
        twin_key: String::new(),
        series: None,
    };
    let mut rows = Vec::new();
    match part {
        "catalogue" => {
            for name in vs_catalogue().into_iter().filter(|n| !n.starts_with("e1:")) {
                for t in [1, 4, 16] {
                    let c = GridConfig::new(GridEngine::SverifyP).threads(t).impl_distinct(true);
                    rows.push(row(name, c, Tier::default_tier(), "catalogue"));
                }
            }
        }
        "curves" => {
            for name in ["apps/a3/fifo/spec/k3q3", "2pc/leader/conf/n4"] {
                for t in [1, 2, 4, 8, 16] {
                    for e in [GridEngine::SverifyP, GridEngine::ExploreP] {
                        rows.push(row(name, GridConfig::new(e).threads(t), Tier::default_tier(), "curve"));
                    }
                }
            }
        }
        "k4q4" => {
            let tier = Tier {
                name: "k4q4-16g".to_owned(),
                wall: std::time::Duration::from_secs(3600),
                mem_kb: 16_000_000,
            };
            for t in [1, 16] {
                for e in [GridEngine::SverifyP, GridEngine::ExploreP] {
                    rows.push(row("apps/a3/fifo/spec/k4q4", GridConfig::new(e).threads(t), tier.clone(), "k4q4"));
                }
            }
        }
        other => panic!("conformance: VS_PART {other}: catalogue | curves | k4q4"),
    }
    rows
}

/// `Max address space` from `/proc/self/limits`, in bytes (`None` = unlimited).
fn vs_address_limit() -> Option<u64> {
    let t = std::fs::read_to_string("/proc/self/limits").expect("conformance: /proc/self/limits");
    let l = t.lines().find(|l| l.starts_with("Max address space")).expect("conformance: the limit");
    l.split_whitespace().nth(3).and_then(|v| v.parse().ok())
}

/// The 1-minute load average (`/proc/loadavg`'s first field).
fn vs_load_1m() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .expect("conformance: /proc/loadavg")
        .split_whitespace()
        .next()
        .and_then(|v| v.parse().ok())
        .expect("conformance: the load average")
}

/// Every other process above 2 GiB resident, and every `java`, `javac`, `gradle`, `cargo` or `rustc`
/// process, as `(pid, name, kB)`: a scan of `/proc/<pid>/status` (`Name`, `VmRSS`), never a pattern
/// match on command lines.
fn vs_heavy_processes() -> Vec<(u32, String, u64)> {
    let me = std::process::id();
    let mut out = Vec::new();
    for e in std::fs::read_dir("/proc").expect("conformance: /proc").flatten() {
        let Some(pid) = e.file_name().to_str().and_then(|n| n.parse::<u32>().ok()) else {
            continue;
        };
        if pid == me {
            continue;
        }
        let Ok(st) = std::fs::read_to_string(e.path().join("status")) else {
            continue;
        };
        let name = st.lines().find_map(|l| l.strip_prefix("Name:")).unwrap_or("").trim().to_owned();
        let rss: u64 = st
            .lines()
            .find_map(|l| l.strip_prefix("VmRSS:"))
            .and_then(|v| v.split_whitespace().next())
            .and_then(|v| v.parse().ok())
            .unwrap_or(0);
        // above 2 GiB resident, or a foreign build or benchmark (the coordinator's gate of
        // 10:4x: no `java`, `gradle` or other session's `cargo` while a timed part runs)
        let foreign = matches!(name.as_str(), "java" | "javac" | "gradle" | "cargo" | "rustc");
        if rss > 2 * 1024 * 1024 || foreign {
            out.push((pid, name, rss));
        }
    }
    out
}

/// V-S's store (VS-1, VS-2), through the driver: `VS_PART` = `catalogue` (420 rows, spec
/// `SVERIFY-P-VS`), `curves` (20) or `k4q4` (4, the tier `k4q4-16g`), the last two spec
/// `SVERIFY-P-VS-CURVE` into their own store (the coordinator's decision of 10:3x); `VS_STORE` the
/// store directory; `VS_COMMIT` the commit column. The part refuses to start under the other parts'
/// address-space limit: `k4q4` only under 16 384 000 000 B (`ulimit -v 16000000`), the others only
/// under 10 240 000 000 B (ruling 9). A timed part (`curves`, `k4q4`) starts only after a minute of
/// 1-minute load averages under 2 (read every 5 s, recorded) with no `java`, `javac`, `gradle`,
/// `cargo` or `rustc` process and none above 2 GiB, and runs its rows one driver run each, every
/// row only when that process check holds again (the load recorded beside it); a failed check stops
/// the part before that row, and a re-run resumes at the first row the store lacks.
#[test]
#[ignore]
fn vs_the_store() {
    let (Ok(out), Ok(part)) = (std::env::var("VS_STORE"), std::env::var("VS_PART")) else {
        return;
    };
    let want = if part == "k4q4" { 16_384_000_000 } else { 10_240_000_000 };
    let got = vs_address_limit();
    assert_eq!(got, Some(want), "conformance: VS_PART {part} runs only under its address-space limit");
    let rows = vs_store_rows(&part);
    note!("PVS\tpart {part}\trows {}\taddress limit {got:?}", rows.len());
    let timed = part != "catalogue";
    let spec = Spec {
        name: if timed { "SVERIFY-P-VS-CURVE" } else { "SVERIFY-P-VS" }.to_owned(),
        rows: rows.clone(),
    };
    let commit = std::env::var("VS_COMMIT").ok();
    let driver = |only: Option<String>| {
        let mut probes = Probes::real();
        if let Some(c) = commit.clone() {
            probes.git = Box::new(move || (c.clone(), false));
        }
        Driver {
            spec: spec.clone(),
            specs: vec![spec.clone()],
            out_dir: std::path::PathBuf::from(&out),
            sample_period: std::time::Duration::from_millis(100),
            probes,
            allow_mixed: false,
            only,
        }
    };
    let report = |d: &Driver| match d.run() {
        Ok(s) => note!(
            "PVS\tran {}\tskipped present {}\tcensored {}\tstore {}",
            s.ran,
            s.skipped_present,
            s.censored,
            s.store.display()
        ),
        Err(e) => panic!("conformance: the driver refused: {}", e.text()),
    };
    if !timed {
        report(&driver(std::env::var("EVAL_ONLY").ok()));
        return;
    }
    // the quiet minute
    let mut readings = Vec::new();
    for i in 0..13 {
        if i > 0 {
            std::thread::sleep(std::time::Duration::from_secs(5));
        }
        readings.push(vs_load_1m());
    }
    let foreign = vs_heavy_processes();
    note!("PVSQ\tpart {part}\tthe minute's 1-minute load averages {readings:?}\tforeign or above 2 GiB {foreign:?}");
    assert!(
        readings.iter().all(|l| *l < 2.0) && foreign.is_empty(),
        "conformance: VS_PART {part}: the machine is not quiet: {readings:?} {foreign:?}"
    );
    for r in &rows {
        let key = r.key(crate::conformance::eval::profile_name());
        let (load, heavy) = (vs_load_1m(), vs_heavy_processes());
        // The load average lags: before a row it still carries this part's previous rows (a
        // 16-thread row leaves it near 10 for a minute), so it is recorded, not gated; the gate
        // before each row is the foreign processes and the 2 GiB rule (the first run of 10:46
        // stopped on its own rows' load at the eighth row).
        note!("PVSQ\t{key}\tload {load}\tforeign or above 2 GiB {heavy:?}");
        assert!(
            heavy.is_empty(),
            "conformance: VS_PART {part}: not quiet before {key}: {heavy:?}"
        );
        report(&driver(Some(key)));
    }
}

/// VS-1's checks on the store's catalogue rows (`VS_STORE`): every column of V-S1 against the
/// record, I4-6's identities; the result per column class (equal / unequal / censored rows); the
/// curves' and the k4q4 rows' tables. Ignored.
#[test]
#[ignore]
fn vs_the_store_checks() {
    let Ok(out) = std::env::var("VS_STORE") else {
        return;
    };
    let parts = std::env::var("VS_PARTS").unwrap_or_else(|_| "catalogue,curves,k4q4".to_owned());
    let rec = vs_records();
    let rows = read_rows(&std::path::Path::new(&out).join("rows.csv"))
        .unwrap_or_else(|e| panic!("conformance: {}", e.text()));
    let by_key: BTreeMap<String, &BTreeMap<String, String>> =
        rows.iter().map(|r| (r["key"].clone(), r)).collect();
    let mut bad = Vec::new();
    // the catalogue
    let mut classes: BTreeMap<&'static str, (usize, usize)> = BTreeMap::new();
    let (mut ok_rows, mut censored, mut missing) = (0, Vec::new(), Vec::new());
    let catalogue = if parts.contains("catalogue") { vs_store_rows("catalogue") } else { Vec::new() };
    // V-S gate 4 round 01 (the sweep): every part counts the expected keys it examined
    let catalogue_expected = catalogue.len();
    for spec in catalogue {
        let key = spec.key("release");
        let Some(m) = by_key.get(&key) else {
            missing.push(key);
            continue;
        };
        if m["end_class"] != "ok" {
            censored.push(format!("{} t{}: {}", spec.fixture, spec.config.threads, m["end_class"]));
            continue;
        }
        ok_rows += 1;
        let r = rec.get(&spec.fixture).unwrap_or_else(|| panic!("conformance: no record for {}", spec.fixture));
        let fails = vs_row_checks(m, r);
        for col in [
            "verdict", "reports", "uncovered_multiplicity", "spec_graphs", "impl_graphs",
            "spec_complete", "spec_blocked", "impl_complete", "impl_blocked", "orders_held",
            "impl_distinct_summaries", "lookups_succeeded", "lookups_failed_after_tests",
            "lookups_signature_miss", "first_report", "identities", "spec_end", "impl_end",
        ] {
            let e = classes.entry(col).or_default();
            if fails.iter().any(|(c, _)| *c == col) {
                e.1 += 1;
            } else {
                e.0 += 1;
            }
        }
        for (c, w) in fails {
            bad.push(format!("{} t{}: {c}: {w}", spec.fixture, spec.config.threads));
        }
    }
    note!("PVSC\tcatalogue rows ok {ok_rows}\tcensored {}\tmissing {}", censored.len(), missing.len());
    if parts.contains("catalogue") {
        assert_eq!(catalogue_expected, 420, "conformance: the catalogue's expected rows");
    }
    for (c, (e, u)) in &classes {
        note!("PVSC\t{c}\tequal {e}\tunequal {u}");
    }
    for c in &censored {
        note!("PVSC\tcensored\t{c}");
    }
    // the curves
    let curves = if parts.contains("curves") { vs_store_rows("curves") } else { Vec::new() };
    let mut walls: BTreeMap<(String, String, usize), (u128, u128, u128)> = BTreeMap::new();
    let curves_expected = curves.len();
    // the four complete/blocked columns of each completed curve row, by (fixture, engine, t)
    let mut splits: BTreeMap<(String, String, usize), [u128; 4]> = BTreeMap::new();
    for spec in curves {
        let Some(m) = by_key.get(&spec.key("release")) else {
            missing.push(spec.key("release"));
            continue;
        };
        if m["end_class"] != "ok" {
            bad.push(format!("curve {} {:?} t{}: {}", spec.fixture, spec.config.engine, spec.config.threads, m["end_class"]));
            continue;
        }
        if spec.config.engine == GridEngine::SverifyP {
            bad.extend(i4_identities(m).into_iter().map(|b| format!("curve {} t{}: {b}", spec.fixture, spec.config.threads)));
            // V-S gate 4 round 01 (the sweep): a completed SverifyP curve row's two ends (the
            // baseline's row carries none: Must alone has no search end in the row)
            for col in ["spec_end", "impl_end"] {
                if m.get(col).map(String::as_str) != Some("StateSpaceExhausted") {
                    bad.push(format!("curve {} t{}: {col} {:?}", spec.fixture, spec.config.threads, m.get(col)));
                }
            }
        }
        splits.insert(
            (spec.fixture.clone(), format!("{:?}", spec.config.engine), spec.config.threads),
            ["spec_complete", "spec_blocked", "impl_complete", "impl_blocked"].map(|c| i4_num(m, c)),
        );
        walls.insert(
            (spec.fixture.clone(), format!("{:?}", spec.config.engine), spec.config.threads),
            (i4_num(m, "spec_wall_time_ms"), i4_num(m, "impl_wall_time_ms"), i4_num(m, "wall_ms")),
        );
        note!(
            "PVSK\t{}\t{:?}\tt {}\tspec {}\tfreeze {}\timpl {}\twall {}\tspec/impl c/b {}/{} {}/{}\ttasks {}/{}\tlock held {}/{} wait {}/{}\tpeaks {} {} {} max {}\tvm_peak {}",
            spec.fixture, spec.config.engine, spec.config.threads,
            m["spec_wall_time_ms"], m.get("freeze_wall_time_ms").map(String::as_str).unwrap_or(""),
            m["impl_wall_time_ms"], m["wall_ms"],
            m["spec_complete"], m["spec_blocked"], m["impl_complete"], m["impl_blocked"],
            m["spec_tasks"], m["impl_tasks"],
            m.get("spec_merge_lock_held_ms").map(String::as_str).unwrap_or(""),
            m.get("impl_merge_lock_held_ms").map(String::as_str).unwrap_or(""),
            m.get("spec_merge_lock_wait_ms").map(String::as_str).unwrap_or(""),
            m.get("impl_merge_lock_wait_ms").map(String::as_str).unwrap_or(""),
            m["spec_vmhwm_kb"], m.get("freeze_vmhwm_kb").map(String::as_str).unwrap_or(""),
            m["impl_vmhwm_kb"], m["vmhwm_kb_max"], m["vm_peak_kb"]
        );
    }
    // the baseline enumerates the graphs SverifyP enumerates, per side (I4-4): its split equals
    // the SverifyP row's at the same fixture and t
    for ((f, e, t), s) in &splits {
        if e == "ExploreP" {
            match splits.get(&(f.clone(), "SverifyP".to_owned(), *t)) {
                Some(sp) if sp == s => {}
                other => bad.push(format!("curve {f} t{t}: the baseline's split {s:?} vs SverifyP's {other:?}")),
            }
        }
    }
    if parts.contains("curves") {
        assert_eq!(curves_expected, 20, "conformance: the curves' expected rows");
    }
    for ((f, e, t), (sw, iw, w)) in &walls {
        if let Some((s1, i1, w1)) = walls.get(&(f.clone(), e.clone(), 1)) {
            let r = |a: &u128, b: &u128| if *b == 0 { f64::NAN } else { *a as f64 / *b as f64 };
            note!(
                "PVSS\t{f}\t{e}\tt {t}\tspec {sw} ms (×{:.2})\timpl {iw} ms (×{:.2})\twall {w} ms (×{:.2})",
                r(s1, sw),
                r(i1, iw),
                r(w1, w)
            );
        }
    }
    // the k4q4 rows (present only after part 3)
    let k4 = if parts.contains("k4q4") { vs_store_rows("k4q4") } else { Vec::new() };
    let mut k4_examined = 0;
    for spec in k4 {
        // V-S gate 4 round 01 M2: an absent k4q4 key is missing, never skipped
        let Some(m) = by_key.get(&spec.key("release")) else {
            missing.push(spec.key("release"));
            continue;
        };
        k4_examined += 1;
        let class = m["end_class"].clone();
        let stderr = std::fs::read_to_string(std::path::Path::new(&out).join(&m["run_dir"]).join("stderr"))
            .unwrap_or_default();
        let alloc = stderr.lines().find(|l| l.contains("memory allocation of")).unwrap_or("");
        let outcome = match class.as_str() {
            "ok" => "completed".to_owned(),
            "capped_wall" | "capped_memory" => format!("{class} (not checkable)"),
            c if c.starts_with("crashed") && !alloc.is_empty() => format!("allocation abort, memory-censored: {alloc}"),
            c => {
                bad.push(format!("k4q4 {:?} t{}: {c}", spec.config.engine, spec.config.threads));
                format!("{c} (a failure)")
            }
        };
        note!(
            "PVS4\t{:?}\tt {}\toutcome {outcome}\tproc_wall_ms {}\trss_sampled_hwm_kb {} (a lower bound)\trss_child_hwm_kb {}",
            spec.config.engine, spec.config.threads, m["proc_wall_ms"], m["rss_sampled_hwm_kb"], m["rss_child_hwm_kb"]
        );
    }
    note!("PVSC\tk4q4 rows examined {k4_examined}\tmissing in all {}", missing.len());
    assert!(missing.is_empty(), "conformance: rows missing from the store: {missing:#?}");
    if parts.contains("k4q4") {
        assert_eq!(k4_examined, 4, "conformance: V-S gate 4 round 01 M2: exactly the four k4q4 rows");
    }
    assert!(bad.is_empty(), "conformance: V-S store: {bad:#?}");
}

/// VS-1 in process, one process per thread count (`VS_T`): the four `e1:*` fixtures (ruling 2) as
/// store rows would be (`run_grid`, `distinct=on`), every V-S1 column against the record; and the
/// uncovered multiset of every violating catalogue fixture against
/// the record's `UNCSET` lines (the 55 include `e1:race-bad/bag`). Ignored.
#[test]
#[ignore]
fn vs_in_process_e1_rows_and_the_uncovered_multisets() {
    let Ok(t) = std::env::var("VS_T") else {
        return;
    };
    let t: usize = t.parse().expect("conformance: VS_T is a number");
    let _g = serial();
    let rec = vs_records();
    assert_eq!(rec.len(), 144, "conformance: the package's 144 records");
    let mut bad = Vec::new();
    // V-S gate 4 round 01 (the sweep): exactly the four `e1:*` fixtures
    assert_eq!(VS_EXTRA.iter().filter(|n| n.starts_with("e1:")).count(), 4, "conformance: the e1 fixtures");
    for name in VS_EXTRA.iter().filter(|n| n.starts_with("e1:")) {
        let f = crate::conformance::compact_tests::e1_fixture(name);
        let r = i4_run(&f, &GridConfig::new(GridEngine::SverifyP).threads(t).impl_distinct(true));
        let m = i4_cells(&r);
        for (c, w) in vs_row_checks(&m, &rec[*name]) {
            bad.push(format!("{name} t{t}: {c}: {w}"));
        }
        note!("PVSE\t{name}\tt {t}\tverdict {}\treports {}\tspec {}\timpl {}", m["verdict"], m["reports"], m["spec_graphs"], m["impl_graphs"]);
    }
    let (mut fixtures, mut lines) = (0, 0usize);
    for name in vs_catalogue() {
        let r = &rec[name];
        if r.verdict != "reported" {
            continue;
        }
        let f = if name.starts_with("e1:") {
            crate::conformance::compact_tests::e1_fixture(name)
        } else {
            fx(name)
        };
        let cc = GridConfig::new(GridEngine::SverifyP).threads(t).conf_config(&f);
        let o = sverify_p::run_with(&cc, &f.implementation, &f.specification);
        let got = vs_uncovered(&o);
        fixtures += 1;
        lines += r.uncovered.values().sum::<usize>();
        if got != r.uncovered {
            let only_p: Vec<_> = got.iter().filter(|(k, v)| r.uncovered.get(*k) != Some(*v)).take(2).collect();
            let only_r: Vec<_> = r.uncovered.iter().filter(|(k, v)| got.get(*k) != Some(*v)).take(2).collect();
            bad.push(format!("{name} t{t}: the uncovered multiset differs: SVerify-P {only_p:?} … the record {only_r:?}"));
        }
    }
    note!("PVSU\tt {t}\tviolating fixtures {fixtures}\tuncovered lines {lines}");
    assert!(bad.is_empty(), "conformance: V-S in process: {bad:#?}");
    // non-vacuity: the catalogue's 55 violating fixtures (`e1:race-bad/bag` among them), 3 353 lines
    assert_eq!((fixtures, lines), (55, 3353), "conformance: non-vacuity");
}
