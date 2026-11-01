//! `MEAS-KEYS`'s tests (`criteria/MEAS-KEYS.md` MK-1; the derivation
//! `log/dev/MEAS-KEYS.derived.md`): the four keys `spec_graphs_explored`, `sweeps`,
//! `cache_tests`, `cache_hits`, on hand values. In-process. At most two threads.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::thread::ThreadId;
use std::time::{Duration, Instant};

use crate::conformance::config::{ConfBuilder, Engine, IndexKind};
use crate::conformance::interchange_default_tests::{named, record_cells, scratch, split_block};
use crate::conformance::measure;
use crate::conformance::record::{self, Subject};
use crate::conformance::report::{ConfError, ConfVerdict};
use crate::program::{run_cli_with_model, Entry, Program};
use crate::{Config, ConsType};

const FOUR: [&str; 4] = [
    "spec_graphs_explored",
    "sweeps",
    "cache_tests",
    "cache_hits",
];

macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

#[derive(Clone, Debug, PartialEq)]
enum PMsg {
    V(i32),
    Call(usize, i32),
}

type Run = Result<ConfVerdict, ConfError>;

fn verify<I, S>(engine: Engine, threads: usize, visible: &[&str], imp: I, spec: S) -> Run
where
    I: Fn() + Send + Sync + 'static,
    S: Fn() + Send + Sync + 'static,
{
    let mut b = ConfBuilder::new()
        .config(
            Config::builder()
                .with_cons_type(ConsType::Bag)
                .with_verbose(0)
                .with_seed(0)
                .build(),
        )
        .cons_type(ConsType::Bag)
        .visible_threads(visible.iter().map(|s| (*s).to_owned()))
        .engine(engine)
        .threads(threads);
    if matches!(
        engine,
        Engine::Stateful | Engine::SverifyP | Engine::CompleteFirst | Engine::CFirstP
    ) {
        b = b.index(IndexKind::Set);
    }
    let cc = b.build().expect("conformance: MK: a configuration");
    crate::conformance::verify(cc, imp, spec)
}

/// The block's lines, by this file's own reading: order kept.
fn lines(block: &str) -> Vec<(String, String)> {
    block
        .lines()
        .filter_map(|l| l.split_once(':'))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect()
}

fn four(block: &str) -> [String; 4] {
    let l = lines(block);
    FOUR.map(|k| {
        l.iter()
            .find(|(a, _)| a == k)
            .unwrap_or_else(|| panic!("conformance: MK: no key {k}: {block}"))
            .1
            .clone()
    })
}

fn nums(a: usize, b: usize, c: usize, d: usize) -> [String; 4] {
    [a.to_string(), b.to_string(), c.to_string(), d.to_string()]
}

fn empty() -> [String; 4] {
    [String::new(), String::new(), String::new(), String::new()]
}

fn block_of(r: &Run) -> String {
    measure::of_verdict(r).render()
}

fn key(block: &str, k: &str) -> String {
    lines(block)
        .into_iter()
        .find(|(a, _)| a == k)
        .unwrap_or_else(|| panic!("conformance: MK: no key {k}: {block}"))
        .1
}

// =========================================================================
// Fixtures
// =========================================================================

/// `v` waits for `go`, then sends `value` on a channel made first, so the numbering of what
/// `v` touches is one on every fixture.
fn v_after_go(value: i32, between: impl FnOnce() -> i32) {
    let (tx, _rx) = crate::channel::Builder::<PMsg>::new().build();
    let (go, wait) = crate::channel::Builder::<PMsg>::new().build();
    let shared = Arc::new(AtomicUsize::new(value as usize));
    let s2 = Arc::clone(&shared);
    let v = named("v", move || {
        let _: PMsg = wait.recv_msg_block();
        tx.send_msg(PMsg::V(s2.load(Ordering::SeqCst) as i32));
    });
    let w = between();
    if w >= 0 {
        shared.store(w as usize, Ordering::SeqCst);
    }
    go.send_msg(PMsg::V(0));
    v.join().unwrap();
}

/// `x, y = nondet()`: four graphs, four signatures.
fn fan(dup: bool) {
    let x = crate::nondet();
    let y = crate::nondet();
    if dup {
        let _ = crate::nondet();
    }
    v_after_go(i32::from(x) + 2 * i32::from(y), || -1);
}

/// The value that `fan` sends at each DFS position, by a position test: a single-graph
/// implementation sending that value sweeps as far as its position.
fn fan_positions() -> HashMap<i32, usize> {
    (0..4)
        .map(|val| {
            let r = verify(
                Engine::CompleteFirst,
                1,
                &["v"],
                move || v_after_go(val, || -1),
                || fan(false),
            );
            let c = r
                .as_ref()
                .unwrap_or_else(|e| panic!("conformance: MK: {e:?}"))
                .outcome()
                .cfirst_counters
                .clone()
                .expect("conformance: MK: the counters");
            (val, c.sweep_graphs)
        })
        .collect()
}

/// `a` and `b` send one value each; `ordered`: `b` joins `a` first, so the same words with
/// one more order.
fn pair(ordered: bool) {
    let (tx, _rx) = crate::channel::Builder::<PMsg>::new().build();
    let t2 = tx.clone();
    let a = named("a", move || tx.send_msg(PMsg::V(1)));
    if ordered {
        let b = named("b", move || {
            a.join().unwrap();
            t2.send_msg(PMsg::V(2));
        });
        b.join().unwrap();
    } else {
        let b = named("b", move || t2.send_msg(PMsg::V(2)));
        a.join().unwrap();
        b.join().unwrap();
    }
}

/// Which value `nondet()` gives first, on a plain run.
fn nondet_first() -> bool {
    let first: Arc<OnceLock<bool>> = Arc::new(OnceLock::new());
    let f2 = Arc::clone(&first);
    let _ = verify(
        Engine::CompleteFirst,
        1,
        &["v"],
        move || {
            let x = crate::nondet();
            f2.get_or_init(|| x);
            v_after_go(1, || -1);
        },
        || v_after_go(1, || -1),
    );
    *first.get().expect("conformance: MK: a run")
}

/// The spec's `blocked_first`: its first ending blocked, or its second.
fn may_block(blocked_on: bool) {
    let x = crate::nondet();
    if x == blocked_on {
        let (_tx, rx) = crate::channel::Builder::<PMsg>::new().build();
        let v = named("v", move || {
            let _: PMsg = rx.recv_msg_block();
        });
        let _ = v;
    } else {
        v_after_go(1, || -1);
    }
}

// =========================================================================
// MK-1.1, 1.3: the keys and their order, in every form; empty where stated
// =========================================================================

fn cli(args: &[&str]) -> (String, u8) {
    let imp = |_: &[String]| -> Entry { Arc::new(|| fan(false)) };
    let spec = |_: &[String]| -> Entry { Arc::new(|| fan(false)) };
    let visible = |_: &[String]| vec!["v".to_owned()];
    let p = Program {
        visible: &visible,
        spec: &spec,
        imp: &imp,
    };
    let a: Vec<String> = args.iter().map(|s| (*s).to_owned()).collect();
    run_cli_with_model(&p, ConsType::Bag, &a)
}

fn tail_is_four(block: &str, what: &str) {
    let l = lines(block);
    let n = l.len();
    assert!(n >= 4, "conformance: MK: {what}: {block}");
    let names: Vec<&str> = l[n - 4..].iter().map(|(k, _)| k.as_str()).collect();
    assert_eq!(
        names, FOUR,
        "conformance: MK: {what}: the last four in order"
    );
}

/// The whole order, pinned to the base's 37 and the four.
#[test]
fn mk1_keys_pinned() {
    assert_eq!(measure::KEYS.len(), 41, "conformance: MK: the count");
    assert_eq!(measure::KEYS[37..], FOUR, "conformance: MK: the last four");
}

#[test]
fn mk1_mk3_cli_forms() {
    let d = scratch("mk-cli");
    let out = d.join("s.jsonl");
    let s = out.display().to_string();
    let i = d.join("i.jsonl").display().to_string();
    let forms: Vec<(&str, Vec<&str>)> = vec![
        ("count spec", vec!["count", "spec", "--seed", "0"]),
        (
            "count impl",
            vec!["count", "impl", "--seed", "0", "--threads", "2"],
        ),
        (
            "export spec",
            vec!["export", "spec", "--out", &s, "--seed", "0"],
        ),
        (
            "export impl",
            vec![
                "export",
                "impl",
                "--out",
                &i,
                "--seed",
                "0",
                "--threads",
                "2",
            ],
        ),
        ("online", vec!["online", "--spec", &s, "--seed", "0"]),
    ];
    for (what, a) in forms {
        let (t, code) = cli(&a);
        assert_eq!(code, 0, "conformance: MK: {what}: {t}");
        let block = split_block(&t)
            .1
            .unwrap_or_else(|| panic!("conformance: MK: {what}: {t}"));
        tail_is_four(&block, what);
        assert_eq!(four(&block), empty(), "conformance: MK: {what}: empty");
    }
}

#[test]
fn mk1_mk3_conf_forms() {
    let want4 = |engine: Engine, threads: usize, want: [String; 4]| {
        let r = verify(engine, threads, &["v"], || fan(false), || fan(false));
        let b = block_of(&r);
        let what = format!("{engine:?} t{threads}");
        tail_is_four(&b, &what);
        assert!(r.is_ok(), "conformance: MK: {what}: {r:?}");
        assert_eq!(four(&b), want, "conformance: MK: {what}");
    };
    // The DFS order of `fan`: position i for the i-th graph, on both sides.
    want4(
        Engine::Stateful,
        1,
        nums(4, 0, 0, 0).map(|x| if x == "4" { x } else { String::new() }),
    );
    want4(
        Engine::SverifyP,
        2,
        nums(4, 0, 0, 0).map(|x| if x == "4" { x } else { String::new() }),
    );
    want4(Engine::CompleteFirst, 1, nums(10, 4, 0, 0));
    want4(Engine::CFirstP, 1, nums(10, 4, 0, 0));
    want4(Engine::Gated, 1, empty());
    want4(Engine::Enumerator, 1, empty());
}

// =========================================================================
// MK-1.2: values
// =========================================================================

fn stateless_counters(r: &Run) -> crate::conformance::report::CFirstCounters {
    let o = r
        .as_ref()
        .unwrap_or_else(|e| panic!("conformance: MK: {e:?}"))
        .outcome();
    match (&o.cfirst_counters, &o.counters.cfirst_p) {
        (Some(c), _) => c.clone(),
        (None, Some(p)) => p.base.clone(),
        _ => panic!("conformance: MK: no counters"),
    }
}

/// The engine's exact hits, on `CFirstP`; the sequential engine's outcome does not carry them.
fn exact_of(r: &Run) -> Option<usize> {
    let o = r
        .as_ref()
        .unwrap_or_else(|e| panic!("conformance: MK: {e:?}"))
        .outcome();
    o.counters.cfirst_p.as_ref().map(|p| p.exact_hits)
}

/// §2's table on one stateless engine: (`spec_graphs_explored`, `sweeps`, `cache_tests`,
/// `cache_hits`), exact hits, and the identity.
fn check_stateless(
    r: &Run,
    want: (usize, usize, usize, usize),
    exact: usize,
    impl_graphs: usize,
    what: &str,
) {
    let b = block_of(r);
    assert!(r.is_ok(), "conformance: MK: {what}: {r:?}");
    assert_eq!(
        four(&b),
        nums(want.0, want.1, want.2, want.3),
        "conformance: MK: {what}: the block"
    );
    let c = stateless_counters(r);
    assert_eq!(
        c.sweep_graphs, want.0,
        "conformance: MK: {what}: sweep_graphs"
    );
    assert_eq!(
        c.cache_hits + c.sweeps,
        impl_graphs,
        "conformance: MK: {what}: hits + sweeps"
    );
    assert_eq!(
        c.impl_graphs, impl_graphs,
        "conformance: MK: {what}: impl_graphs"
    );
    if let Some(e) = exact_of(r) {
        assert_eq!(e, exact, "conformance: MK: {what}: exact hits");
    }
    note!(
        "MK: {what}: {:?} exact {:?} sizes {:?}",
        four(&b),
        exact_of(r),
        c.sweep_sizes
    );
}

/// Repeated sweeps: the sum exceeds the spec's own 4; a cache hit on a duplicate.
#[test]
fn mk2_fan() {
    let pos = fan_positions();
    let mut got: Vec<usize> = pos.values().copied().collect();
    got.sort();
    assert_eq!(
        got,
        vec![1, 2, 3, 4],
        "conformance: MK: the positions: {pos:?}"
    );
    for (engine, tag) in [
        (Engine::CompleteFirst, "CompleteFirst"),
        (Engine::CFirstP, "CFirstP t1"),
    ] {
        let r = verify(engine, 1, &["v"], || fan(false), || fan(false));
        check_stateless(&r, (10, 4, 0, 0), 0, 4, &format!("{tag} fan"));
        let r = verify(engine, 1, &["v"], || fan(true), || fan(false));
        check_stateless(&r, (10, 4, 0, 4), 4, 8, &format!("{tag} fan-dup"));
    }
    // The stateful key is the spec's own, whatever the implementation.
    let r = verify(Engine::Stateful, 1, &["v"], || fan(true), || fan(false));
    assert_eq!(four(&block_of(&r))[0], "4", "conformance: MK: stateful");
    let c = verify(Engine::SverifyP, 2, &["v"], || fan(true), || fan(false));
    assert_eq!(four(&block_of(&c))[0], "4", "conformance: MK: SverifyP");
    assert_eq!(
        key(&block_of(&c), "iterations"),
        "8",
        "conformance: MK: distinct from the impl's"
    );
}

/// An exact hit adds to `cache_hits`, not `cache_tests`; a non-exact one to both; a non-exact
/// miss adds a test and sweeps.
#[test]
fn mk2_exact_and_non_exact() {
    let nf = nondet_first();
    for (engine, tag) in [
        (Engine::CompleteFirst, "CompleteFirst"),
        (Engine::CFirstP, "CFirstP t1"),
    ] {
        // Ordered first, then unordered; the spec holds the unordered: the witness is the
        // unordered, so the unordered query is exact.
        let imp = move |ordered_first: bool| {
            move || pair(crate::nondet() == (if ordered_first { nf } else { !nf }))
        };
        let spec = || pair(false);
        let r = verify(engine, 1, &["a", "b"], imp(true), spec);
        check_stateless(&r, (1, 1, 0, 1), 1, 2, &format!("{tag} exact"));
        let r = verify(engine, 1, &["a", "b"], imp(false), spec);
        check_stateless(&r, (1, 1, 1, 1), 0, 2, &format!("{tag} non-exact"));
        // The spec has both, ordered first: the witness for the ordered query is the
        // ordered graph, which does not cover the unordered: a test, then a second sweep.
        let spec2 = move || pair(crate::nondet() == nf);
        let r = verify(engine, 1, &["a", "b"], imp(true), spec2);
        check_stateless(&r, (3, 2, 1, 0), 0, 2, &format!("{tag} non-exact miss"));
    }
}

/// A spec with blocked endings: the stateful key is `execs + blocked`, and the sweep counts
/// a blocked ending it tests.
#[test]
fn mk2_blocked_endings() {
    let nf = nondet_first();
    // Counted by the spec side's `count`.
    let imp = |_: &[String]| -> Entry { Arc::new(|| v_after_go(1, || -1)) };
    let spec = move |_: &[String]| -> Entry { Arc::new(move || may_block(nf)) };
    let visible = |_: &[String]| vec!["v".to_owned()];
    let p = Program {
        visible: &visible,
        spec: &spec,
        imp: &imp,
    };
    let args: Vec<String> = ["count", "spec", "--seed", "0"]
        .iter()
        .map(|s| (*s).to_owned())
        .collect();
    let (t, code) = run_cli_with_model(&p, ConsType::Bag, &args);
    assert_eq!(code, 0, "conformance: MK: {t}");
    assert!(
        t.contains("execs=1 blocked=1"),
        "conformance: MK: the count: {t}"
    );
    let r = verify(
        Engine::Stateful,
        1,
        &["v"],
        || v_after_go(1, || -1),
        move || may_block(nf),
    );
    assert_eq!(
        four(&block_of(&r))[0],
        "2",
        "conformance: MK: stateful: {r:?}"
    );
    let r = verify(
        Engine::SverifyP,
        2,
        &["v"],
        || v_after_go(1, || -1),
        move || may_block(nf),
    );
    let b = block_of(&r);
    assert_eq!(four(&b)[0], "2", "conformance: MK: SverifyP: {b}");
    assert_eq!(
        (key(&b, "spec_complete"), key(&b, "spec_blocked")),
        ("1".to_owned(), "1".to_owned()),
        "conformance: MK: SverifyP's split: {b}"
    );
    // The stateless key: the blocked ending first, so it is tested; then second, not reached.
    for (engine, tag) in [
        (Engine::CompleteFirst, "CompleteFirst"),
        (Engine::CFirstP, "CFirstP t1"),
    ] {
        let r = verify(
            engine,
            1,
            &["v"],
            || v_after_go(1, || -1),
            move || may_block(nf),
        );
        check_stateless(&r, (2, 1, 0, 0), 0, 1, &format!("{tag} blocked first"));
        let r = verify(
            engine,
            1,
            &["v"],
            || v_after_go(1, || -1),
            move || may_block(!nf),
        );
        check_stateless(&r, (1, 1, 0, 0), 0, 1, &format!("{tag} blocked second"));
    }
}

/// The state of the abandon fixture.
#[derive(Default)]
struct Ab {
    root: OnceLock<ThreadId>,
    runs: AtomicUsize,
    task_runs: AtomicUsize,
    spec_runs: AtomicUsize,
    armed: AtomicBool,
    in_sweep: AtomicBool,
    admitted: AtomicBool,
}

fn wait_for(f: &AtomicBool) -> bool {
    let start = Instant::now();
    while !f.load(Ordering::SeqCst) {
        if start.elapsed() > Duration::from_secs(20) {
            return false;
        }
        std::thread::sleep(Duration::from_millis(1));
    }
    true
}

/// `k` clients call a server `q` times: `(kq)! / (q!)^k` endings, 1 680 at (3, 3). The server
/// and clients are invisible.
fn serve(k: usize, q: usize) {
    let (req, inbox) = crate::channel::Builder::<PMsg>::new().build();
    let mut replies = Vec::new();
    let mut waits = Vec::new();
    for _ in 0..k {
        let (tx, rx) = crate::channel::Builder::<PMsg>::new().build();
        replies.push(tx);
        waits.push(rx);
    }
    let server = named("server", move || {
        for _ in 0..k * q {
            let m: PMsg = inbox.recv_msg_block();
            if let PMsg::Call(c, v) = m {
                replies[c].send_msg(PMsg::V(v));
            }
        }
    });
    let clients: Vec<_> = waits
        .into_iter()
        .enumerate()
        .map(|(c, rx)| {
            let req = req.clone();
            named(&format!("c{c}"), move || {
                for i in 0..q {
                    req.send_msg(PMsg::Call(c, i as i32));
                    let _: PMsg = rx.recv_msg_block();
                }
            })
        })
        .collect();
    server.join().unwrap();
    for c in clients {
        c.join().unwrap();
    }
}

/// The implementation: `v` sends `first` always, but `last` on the root's 101st execution and
/// a task's first. The task waits until the root is in its sweep; the root's sweep holds at
/// its second spec run until the task has admitted: an abandoned sweep, by a watch re-probe.
fn ab_impl(h: &Arc<Ab>, first: i32, last: i32) {
    let me = std::thread::current().id();
    let is_root = *h.root.get_or_init(|| me) == me;
    let special = if is_root {
        let n = h.runs.fetch_add(1, Ordering::SeqCst) + 1;
        if n == 101 {
            h.armed.store(true, Ordering::SeqCst);
        }
        n == 101
    } else {
        let k = h.task_runs.fetch_add(1, Ordering::SeqCst) + 1;
        if k == 1 {
            wait_for(&h.in_sweep);
        } else if k == 2 {
            h.admitted.store(true, Ordering::SeqCst);
        }
        k == 1
    };
    v_after_go(0, || {
        serve(3, 3);
        if special {
            last
        } else {
            first
        }
    });
}

fn ab_spec(h: &Arc<Ab>) {
    if h.armed.load(Ordering::SeqCst) && h.root.get() == Some(&std::thread::current().id()) {
        let s = h.spec_runs.fetch_add(1, Ordering::SeqCst) + 1;
        if s == 1 {
            h.in_sweep.store(true, Ordering::SeqCst);
        } else if s == 2 {
            wait_for(&h.admitted);
        }
    }
    fan(false);
}

/// At N = 2: an abandoned sweep's graphs are in the sum and the abandoning completion is not;
/// the re-probe is in `watch_probes`, in neither `cache_tests` nor `cache_hits`.
#[test]
fn mk2_abandoned_and_watch() {
    let pos = fan_positions();
    let at = |p: usize| *pos.iter().find(|(_, q)| **q == p).unwrap().0;
    let (first, last) = (at(1), at(4));
    let h = Arc::new(Ab::default());
    let (h1, h2) = (Arc::clone(&h), Arc::clone(&h));
    let r = verify(
        Engine::CFirstP,
        2,
        &["v"],
        move || ab_impl(&h1, first, last),
        move || ab_spec(&h2),
    );
    let o = r
        .as_ref()
        .unwrap_or_else(|e| panic!("conformance: MK: {e:?}"))
        .outcome();
    let p = o
        .counters
        .cfirst_p
        .as_ref()
        .expect("conformance: MK: the counters");
    let c = &p.base;
    note!(
        "MK: abandon: sweeps {} abandoned {} watch {} graphs {} sizes {:?} hits {} \
         tests {} exact {} impl {} verdict {:?}",
        c.sweeps,
        p.sweeps_abandoned,
        p.watch_probes,
        c.sweep_graphs,
        c.sweep_sizes,
        c.cache_hits,
        c.cache_tests,
        p.exact_hits,
        c.impl_graphs,
        o.report_count
    );
    assert_eq!(p.sweeps_abandoned, 1, "conformance: MK: an abandoned sweep");
    assert_eq!(p.watch_probes, 1, "conformance: MK: a re-probe");
    assert_eq!(c.impl_graphs, 1680, "conformance: MK: the outer run");
    assert_eq!(
        four(&block_of(&r)),
        nums(6, 3, 0, 1677),
        "conformance: MK: warmup's 1, the task's 4, the abandoned 1"
    );
    assert_eq!(
        c.cache_hits + c.sweeps,
        1680,
        "conformance: MK: hits + sweeps"
    );
    assert_eq!(p.exact_hits, 1677, "conformance: MK: the hits are exact");
}

// =========================================================================
// MK-1.2, 1.4: `row`
// =========================================================================

const STOPLESS: &str = "stop=false/Exhaustive/Always/memo=false/Default/precheck=false/\
                        instr=false/cut=false/cover=Sweep";

fn row_json(label: &str) -> String {
    format!(
        concat!(
            r#"{{"fixture":"b-mk","label":"{label}","rep":0,"#,
            r#""tier":{{"name":"c1h","wall_ms":3600000,"mem_kb":262144000}},"#,
            r#""run_kind":"timed","family":"b","knobs":"","k":[null,null,null,null],"#,
            r#""variant":"x","twin_key":""}}"#
        ),
        label = label
    )
}

fn row_of(
    label: &str,
    imp: Arc<dyn Fn() + Send + Sync>,
    spec: Arc<dyn Fn() + Send + Sync>,
    visible: &[&str],
) -> (String, HashMap<String, String>) {
    let visible: Vec<String> = visible.iter().map(|s| (*s).to_owned()).collect();
    let l = record::run_row(&row_json(label), "B", |name: &str| Subject {
        name: name.to_owned(),
        config: Config::builder()
            .with_cons_type(ConsType::Bag)
            .with_seed(0)
            .build(),
        visible: visible.clone(),
        implementation: Arc::clone(&imp),
        specification: Arc::clone(&spec),
    })
    .unwrap_or_else(|e| panic!("conformance: MK: {label}: refused: {e}"));
    let cells: HashMap<String, String> = record::header()
        .iter()
        .map(|h| (*h).to_owned())
        .zip(record_cells(&l.record))
        .collect();
    (l.measurements.render(), cells)
}

fn fan_arc(dup: bool) -> Arc<dyn Fn() + Send + Sync> {
    Arc::new(move || fan(dup))
}

/// `conf` and `row` agree, per engine, at N = 1: the same four values. On the fixture with
/// hits; the record's cells give them too.
#[test]
fn mk4_conf_and_row_agree() {
    let set = "/w=inf/quiet=false/index=set";
    let cases: Vec<(Engine, String, [String; 4])> = vec![
        (
            Engine::Stateful,
            format!("Stateful/Plain/{STOPLESS}{set}"),
            [4.to_string(), String::new(), String::new(), String::new()],
        ),
        (
            Engine::SverifyP,
            format!("SverifyP/Plain/{STOPLESS}{set}/threads=1"),
            [4.to_string(), String::new(), String::new(), String::new()],
        ),
        (
            Engine::CompleteFirst,
            format!("CompleteFirst/Plain/{STOPLESS}{set}"),
            nums(10, 4, 0, 4),
        ),
        (
            Engine::CFirstP,
            format!("CFirstP/Plain/{STOPLESS}{set}/threads=1"),
            nums(10, 4, 0, 4),
        ),
        (Engine::Gated, format!("Gated/Ltr/{STOPLESS}"), empty()),
        (
            Engine::Enumerator,
            format!("Enumerator/Ltr/{STOPLESS}"),
            empty(),
        ),
    ];
    for (engine, label, want) in cases {
        let r = verify(engine, 1, &["v"], || fan(true), || fan(false));
        let a = block_of(&r);
        let (b, cells) = row_of(&label, fan_arc(true), fan_arc(false), &["v"]);
        note!("MK: {engine:?}: conf {:?}, row {:?}", four(&a), four(&b));
        assert_eq!(four(&a), want, "conformance: MK: {engine:?}: conf");
        assert_eq!(four(&b), want, "conformance: MK: {engine:?}: row");
        if matches!(engine, Engine::CompleteFirst | Engine::CFirstP) {
            for (k, c) in [
                (0, "sweep_graphs"),
                (1, "sweeps"),
                (2, "cache_tests"),
                (3, "cache_hits"),
            ] {
                assert_eq!(
                    cells.get(c).map(String::as_str),
                    Some(want[k].as_str()),
                    "conformance: MK: {engine:?}: the record's {c}"
                );
            }
        }
    }
}

/// The stateful key is the spec's graphs, not what its index holds: a spec with duplicates, 8
/// graphs and 4 orders, on both routes.
#[test]
fn mk4_stateful_is_graphs_not_orders() {
    let set = "/w=inf/quiet=false/index=set";
    for (engine, label) in [
        (Engine::Stateful, format!("Stateful/Plain/{STOPLESS}{set}")),
        (
            Engine::SverifyP,
            format!("SverifyP/Plain/{STOPLESS}{set}/threads=1"),
        ),
    ] {
        let r = verify(engine, 1, &["v"], || fan(false), || fan(true));
        let a = block_of(&r);
        let (b, cells) = row_of(&label, fan_arc(false), fan_arc(true), &["v"]);
        assert_eq!(four(&a)[0], "8", "conformance: MK: {engine:?}: conf: {a}");
        assert_eq!(four(&b)[0], "8", "conformance: MK: {engine:?}: row: {b}");
        assert_eq!(
            key(&a, "spec_summaries"),
            "4",
            "conformance: MK: {engine:?}: conf: {a}"
        );
        assert_eq!(
            cells.get("orders_held").map(String::as_str),
            Some("4"),
            "conformance: MK: {engine:?}"
        );
        assert_eq!(
            key(&a, "iterations"),
            "4",
            "conformance: MK: {engine:?}: the impl's: {a}"
        );
    }
}

/// `Explore`: the plain Must's blocks are empty, on `row`.
#[test]
fn mk3_plain_must_row() {
    let (b, _) = row_of(
        &format!("Explore/Ltr/{STOPLESS}"),
        fan_arc(false),
        fan_arc(false),
        &["v"],
    );
    assert_eq!(four(&b), empty(), "conformance: MK: Explore");
    tail_is_four(&b, "Explore");
}

/// A spec failing on its third graph, a query on its fourth.
fn asserts_at(bad: i32) {
    let x = crate::nondet();
    let y = crate::nondet();
    let val = i32::from(x) + 2 * i32::from(y);
    v_after_go(val, || -1);
    crate::assert(val != bad);
}

/// An aborted sweep. `row` without the precheck has the engine-only route: what the keys say.
/// `conf` with the precheck refuses: every key empty.
#[test]
fn mk2_aborted() {
    let pos = fan_positions();
    let at = |p: usize| *pos.iter().find(|(_, q)| **q == p).unwrap().0;
    let (third, last) = (at(3), at(4));
    let (b, cells) = row_of(
        &format!("CompleteFirst/Plain/{STOPLESS}/w=inf/quiet=false/index=set"),
        Arc::new(move || v_after_go(last, || -1)),
        Arc::new(move || asserts_at(third)),
        &["v"],
    );
    note!(
        "MK: aborted, row: {:?}; cells aborted {:?} graphs {:?} sweeps {:?} stop {}",
        four(&b),
        cells.get("sweeps_aborted"),
        cells.get("sweep_graphs"),
        cells.get("sweeps"),
        key(&b, "stop_reason")
    );
    assert_eq!(
        cells.get("sweeps_aborted").map(String::as_str),
        Some("1"),
        "conformance: MK: aborted"
    );
    // The failure does not stop the sweep: it runs on to its witness, the fourth graph, and
    // the error then decides (C3's table). So all four, the failing one among them.
    assert_eq!(four(&b)[1], "1", "conformance: MK: one sweep");
    assert_eq!(
        four(&b)[0],
        *cells.get("sweep_graphs").unwrap(),
        "conformance: MK: the key is the cell"
    );
    let tested: usize = four(&b)[0].parse().unwrap();
    assert_eq!(
        tested, 4,
        "conformance: MK: the aborted sweep goes on to its witness"
    );
    // `conf`: the precheck refuses; nothing is written.
    let r = verify(
        Engine::CompleteFirst,
        1,
        &["v"],
        move || v_after_go(last, || -1),
        move || asserts_at(third),
    );
    assert!(r.is_err(), "conformance: MK: conf: {r:?}");
    assert_eq!(four(&block_of(&r)), empty(), "conformance: MK: conf: empty");
    let r = verify(
        Engine::CFirstP,
        2,
        &["v"],
        move || v_after_go(last, || -1),
        move || asserts_at(third),
    );
    assert!(r.is_err(), "conformance: MK: conf t2: {r:?}");
    assert_eq!(
        four(&block_of(&r)),
        empty(),
        "conformance: MK: conf t2: empty"
    );
}
