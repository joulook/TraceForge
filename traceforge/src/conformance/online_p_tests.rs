//! `PAR-ONLINE`'s tests (`criteria/PAR-ONLINE.md` PO-1; the derivation
//! `log/dev/PAR-ONLINE.derived.md`): `online --threads N` on the partitioned Must, against
//! `online::online`. In-process where the report is the observable; a child process (this
//! test binary on `po_child`) where the runner's stdout or the CLI's whole text is.
//! Fixture state is per test. At most two threads.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::thread::ThreadId;
use std::time::{Duration, Instant};

use crate::conformance::config::{ConfBuilder, ConfConfig, Engine, IndexKind};
use crate::conformance::export_p::{export_partitioned_with, ExportPSeams};
use crate::conformance::interchange::{conf_join, export_with, ExportHeader, ExportSeams};
use crate::conformance::interchange_default_tests::{named, read_jsonl, scratch, split_block};
use crate::conformance::measure;
use crate::conformance::online::{
    self, End, FirstMiss, MissKind, Mode, OnlineError, OnlineOpts, OnlineOut, OnlineReport,
};
use crate::conformance::online_p::{earlier, online_partitioned_with, OnlinePRun, OnlinePSeams};
use crate::program::{run_cli_with_model, Entry, Program};
use crate::thread::{construct_thread_id, ThreadId as TfThreadId};
use crate::{Config, ConsType};

#[derive(Clone, Debug, PartialEq)]
enum PMsg {
    V(i32),
    Call(usize, i32),
    Owner(TfThreadId),
}

/// `k` clients call a server `q` times each, waiting for each reply: `(kq)! / (q!)^k`
/// endings. Returns the client of the server's first message.
fn serve(k: usize, q: usize) -> usize {
    let (req, inbox) = crate::channel::Builder::<PMsg>::new().build();
    let (dtx, drx) = crate::channel::Builder::<PMsg>::new().build();
    let mut replies = Vec::new();
    let mut waits = Vec::new();
    for _ in 0..k {
        let (tx, rx) = crate::channel::Builder::<PMsg>::new().build();
        replies.push(tx);
        waits.push(rx);
    }
    let server = named("server", move || {
        for i in 0..k * q {
            let m: PMsg = inbox.recv_msg_block();
            if let PMsg::Call(c, v) = m {
                if i == 0 {
                    dtx.send_msg(PMsg::V(c as i32));
                }
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
    let first = match drx.recv_msg_block() {
        PMsg::V(c) => c as usize,
        other => panic!("conformance: PO: {other:?}"),
    };
    server.join().unwrap();
    for c in clients {
        c.join().unwrap();
    }
    first
}

/// `v` is spawned first (a visible thread precedes the program's communication), runs after
/// `serve`, and acts on what the program read.
fn gated<F>(k: usize, q: usize, act: F)
where
    F: FnOnce(usize) + Send + 'static,
{
    let first = Arc::new(AtomicUsize::new(0));
    let (go, wait) = crate::channel::Builder::<PMsg>::new().build();
    let f2 = Arc::clone(&first);
    let v = named("v", move || {
        let _: PMsg = wait.recv_msg_block();
        act(f2.load(Ordering::SeqCst));
    });
    let c = serve(k, q);
    first.store(c, Ordering::SeqCst);
    go.send_msg(PMsg::V(0));
    v.join().unwrap();
}

fn send_one<T: crate::Message + Clone + std::fmt::Debug + PartialEq + Send + 'static>(value: T) {
    let (tx, _rx) = crate::channel::Builder::<T>::new().build();
    tx.send_msg(value);
}

fn v_sends<T: crate::Message + Clone + std::fmt::Debug + PartialEq + Send + 'static>(value: T) {
    let (tx, _rx) = crate::channel::Builder::<T>::new().build();
    let v = named("v", move || tx.send_msg(value));
    v.join().unwrap();
}

/// A value the encoder refuses: its `Debug` is not an encodable form.
#[derive(Clone, PartialEq)]
struct W(bool);

impl std::fmt::Debug for W {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.0 { "@@" } else { "Fine" })
    }
}

/// Two graphs, one thread number, two names.
fn names_fixture() {
    let name = if crate::nondet() { "a" } else { "b" };
    let t = named(name, || {});
    let id = t.thread().id();
    t.join().unwrap();
    v_sends(PMsg::Owner(id));
}

/// The same, chosen past the warmup, and which OS thread ran each name.
fn names_tasks_fixture(seen: Arc<Mutex<HashSet<(String, ThreadId)>>>) {
    let idc = Arc::new(Mutex::new(None));
    let i2 = Arc::clone(&idc);
    let (go, wait) = crate::channel::Builder::<PMsg>::new().build();
    let v = named("v", move || {
        let _: PMsg = wait.recv_msg_block();
        let id = (*i2.lock().unwrap()).expect("conformance: PO: the id");
        send_one(PMsg::Owner(id));
    });
    let c = serve(3, 3);
    let name = if c == 2 { "b" } else { "a" };
    seen.lock()
        .unwrap()
        .insert((name.to_owned(), std::thread::current().id()));
    let t = named(name, || {});
    *idc.lock().unwrap() = Some(t.thread().id());
    t.join().unwrap();
    go.send_msg(PMsg::V(0));
    v.join().unwrap();
}

const ALL: [&str; 5] = ["c0", "c1", "c2", "server", "v"];

fn vis(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| (*s).to_owned()).collect()
}

fn config(seed: u64) -> Config {
    Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(seed)
        .build()
}

fn cc(visible: &[&str], engine: Engine) -> ConfConfig {
    let mut b = ConfBuilder::new()
        .config(config(0))
        .visible_threads(visible.iter().map(|s| (*s).to_owned()))
        .engine(engine)
        .index(IndexKind::Set)
        .flush_entries(4096);
    if matches!(engine, Engine::SverifyP) {
        b = b.threads(2);
    }
    b.build().expect("conformance: PO: a configuration")
}

fn header(program: &str) -> ExportHeader {
    ExportHeader {
        program: program.to_owned(),
        size: "s".to_owned(),
    }
}

/// A specification file from the sequential export.
fn spec_seq<P: Fn() + Send + Sync + 'static>(visible: &[&str], path: &Path, p: P) {
    export_with(
        &cc(visible, Engine::Stateful),
        p,
        &header("spec"),
        path,
        ExportSeams::default(),
    )
    .unwrap_or_else(|e| panic!("conformance: PO: the specification: {e}"));
}

/// A specification file from the parallel export, for what sequential refuses.
fn spec_par<P: Fn() + Send + Sync + 'static>(visible: &[&str], path: &Path, p: P) {
    export_partitioned_with(
        &cc(visible, Engine::SverifyP),
        p,
        &header("spec"),
        path,
        ExportPSeams::default(),
    )
    .map(|_| ())
    .unwrap_or_else(|e| panic!("conformance: PO: the specification: {e}"));
}

fn out_of(path: &Path) -> OnlineOut {
    OnlineOut {
        path: path.to_owned(),
        header: header("impl"),
    }
}

fn seq<P: Fn() + Send + Sync + 'static>(
    visible: &[&str],
    spec: &Path,
    out: Option<&Path>,
    p: P,
) -> OnlineReport {
    online::online(
        &config(0),
        &vis(visible),
        Arc::new(p),
        spec,
        OnlineOpts::new(Mode::Full, None, out.map(out_of)),
    )
    .unwrap_or_else(|e| panic!("conformance: PO: sequential: {e:?}"))
}

fn par<P: Fn() + Send + Sync + 'static>(
    visible: &[&str],
    spec: &Path,
    out: Option<&Path>,
    seams: OnlinePSeams,
    p: P,
) -> OnlinePRun {
    par_seed(0, visible, spec, out, seams, p)
}

fn par_seed<P: Fn() + Send + Sync + 'static>(
    seed: u64,
    visible: &[&str],
    spec: &Path,
    out: Option<&Path>,
    seams: OnlinePSeams,
    p: P,
) -> OnlinePRun {
    online_partitioned_with(
        &config(seed),
        2,
        &vis(visible),
        Arc::new(p),
        spec,
        out.map(out_of),
        seams,
    )
    .unwrap_or_else(|e| panic!("conformance: PO: parallel: {e:?}"))
}

/// Every counter, the verdict and the end, on two reports.
fn same(a: &OnlineReport, b: &OnlineReport, tag: &str) {
    let k = |r: &OnlineReport| {
        (
            r.iterations,
            r.lookups,
            r.found,
            r.signature_misses,
            r.not_found,
            r.uncovered_total,
            r.uncovered_distinct,
            r.graphs_complete,
            r.graphs_blocked,
            r.impl_lines,
            r.held,
            r.spec_lines,
        )
    };
    assert_eq!(k(a), k(b), "conformance: PO: {tag}: the counters");
    assert_eq!(
        a.verdict(),
        b.verdict(),
        "conformance: PO: {tag}: the verdict"
    );
    assert_eq!(a.end, b.end, "conformance: PO: {tag}: the end");
    assert_eq!(a.failure, b.failure, "conformance: PO: {tag}: the failure");
    assert_eq!(
        a.exit_code(),
        b.exit_code(),
        "conformance: PO: {tag}: the exit"
    );
    assert_eq!(a.shape, b.shape, "conformance: PO: {tag}: the shape");
    assert_eq!(
        a.first.is_some(),
        b.first.is_some(),
        "conformance: PO: {tag}: a miss"
    );
    assert_eq!(
        a.first.as_ref().map(|f| f.kind),
        b.first.as_ref().map(|f| f.kind),
        "conformance: PO: {tag}: the first's kind, on a fixture with one kind"
    );
}

fn counters(r: &OnlineReport) -> (usize, usize, usize, usize, usize, usize) {
    (
        r.iterations,
        r.found,
        r.signature_misses,
        r.not_found,
        r.uncovered_total,
        r.uncovered_distinct,
    )
}

fn lines_of(path: &Path) -> Vec<String> {
    read_jsonl(path).1
}

fn is_sorted(v: &[String]) -> bool {
    v.windows(2).all(|w| w[0] < w[1])
}

fn sorted(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v
}

fn uncovered_set(spec: &Path, imp: &Path) -> BTreeSet<String> {
    conf_join(spec, imp)
        .unwrap_or_else(|e| panic!("conformance: PO: the join: {e:?}"))
        .uncovered
        .iter()
        .map(|(_, l)| l.clone())
        .collect()
}

macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

// =========================================================================
// The child: what the runner prints, the CLI's whole text
// =========================================================================

fn entry(fixture: &str) -> Entry {
    match fixture {
        "ok" | "ok-all" => Arc::new(|| gated(3, 3, |_| send_one(PMsg::V(0)))),
        "bad" | "bad-all" => Arc::new(|| {
            gated(3, 3, |first| {
                send_one(PMsg::V(if first == 2 { 1 } else { 0 }))
            })
        }),
        "assert-in-task" => Arc::new(|| gated(3, 3, |first| crate::assert(first != 2))),
        "encode-in-task" => Arc::new(|| gated(3, 3, |first| send_one(W(first == 2)))),
        "absent-in-task" => Arc::new(|| {
            gated(3, 3, |first| {
                send_one(PMsg::Owner(construct_thread_id(if first == 2 {
                    99
                } else {
                    0
                })))
            })
        }),
        "panic-in-task" => Arc::new(|| {
            gated(3, 3, |first| {
                if first == 2 {
                    panic!("conformance: PO: the program's panic");
                }
                send_one(W(false));
            })
        }),
        "assert-off-root" => Arc::new(|| rootless(|off| crate::assert(!off))),
        "encode-off-root" => Arc::new(|| rootless(|off| send_one(W(off)))),
        "panic-off-root" => Arc::new(|| {
            rootless(|off| {
                if off {
                    panic!("conformance: PO: the program's panic");
                }
                send_one(W(false));
            })
        }),
        other => panic!("conformance: PO: no fixture {other}"),
    }
}

static RUNS: AtomicUsize = AtomicUsize::new(0);
static ROOT: OnceLock<ThreadId> = OnceLock::new();
static SEEN: AtomicBool = AtomicBool::new(false);
const OFF_ROOT: &str = "rootless: a failure on a worker that is not the root's";

/// `gated(3, 3)` whose failure can come only off the root: the root's warmup and loop run on
/// one OS thread, the first execution's. Past the warmup that thread waits until another
/// worker has run, so the failure is a task's.
fn rootless(act: fn(bool)) {
    let n = RUNS.fetch_add(1, Ordering::SeqCst) + 1;
    let me = std::thread::current().id();
    let root = *ROOT.get_or_init(|| me);
    if me != root {
        if !SEEN.swap(true, Ordering::SeqCst) {
            use std::io::Write as _;
            let _ = writeln!(std::io::stdout(), "{OFF_ROOT}");
        }
    } else if n > 100 {
        let start = Instant::now();
        while !SEEN.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(20) {
            std::thread::sleep(Duration::from_millis(1));
        }
        SEEN.store(true, Ordering::SeqCst);
    }
    let off = me != root;
    gated(3, 3, move |_| act(off));
}

fn spec_entry(fixture: &str) -> Entry {
    match fixture {
        "encode-off-root" | "panic-off-root" => Arc::new(|| gated(3, 3, |_| send_one(W(false)))),
        "assert-off-root" => Arc::new(|| gated(3, 3, |_| {})),
        "bad" | "ok" => entry("ok"),
        "bad-all" | "ok-all" => entry("ok-all"),
        // A specification with no failure, whose line is the failing fixtures' other one.
        "encode-in-task" | "panic-in-task" => Arc::new(|| gated(3, 3, |_| send_one(W(false)))),
        "absent-in-task" => {
            Arc::new(|| gated(3, 3, |_| send_one(PMsg::Owner(construct_thread_id(0)))))
        }
        "assert-in-task" => Arc::new(|| gated(3, 3, |_| {})),
        other => panic!("conformance: PO: no fixture {other}"),
    }
}

fn visible_of_fixture(fixture: &str) -> Vec<String> {
    if fixture.ends_with("-all") {
        vis(&ALL)
    } else {
        vis(&["v"])
    }
}

/// The child's part: one run, through `run_cli_with_model`. No-op in the suite.
#[test]
fn po_child() {
    let Ok(fixture) = std::env::var("PO_FIXTURE") else {
        return;
    };
    let args: Vec<String> = std::env::var("PO_ARGS")
        .expect("conformance: PO: the child's arguments")
        .split(' ')
        .map(str::to_owned)
        .collect();
    let imp = |_: &[String]| entry(&fixture);
    let spec = |_: &[String]| spec_entry(&fixture);
    let visible = |_: &[String]| visible_of_fixture(&fixture);
    let p = Program {
        visible: &visible,
        spec: &spec,
        imp: &imp,
    };
    let (text, code) = run_cli_with_model(&p, ConsType::Bag, &args);
    std::fs::write(
        std::env::var("PO_OUT").expect("conformance: PO: the child's result file"),
        format!("{code}\n{text}"),
    )
    .expect("conformance: PO: the child's write");
}

struct Run {
    code: Option<u8>,
    text: String,
    stdout: String,
    stderr: String,
}

impl Run {
    fn task_execs(&self) -> Vec<u64> {
        self.stdout
            .lines()
            .filter_map(|l| {
                let (head, tail) = l.trim_start().split_once(": ")?;
                if !head.starts_with("rt") {
                    return None;
                }
                tail.split_once(" execs").and_then(|(k, _)| k.parse().ok())
            })
            .collect()
    }
    fn a_task_ran(&self) -> bool {
        self.task_execs().iter().any(|k| *k > 0)
    }
    fn parallel_banner(&self) -> bool {
        self.stdout.contains("Pool size: 2,")
    }
    fn say(&self) -> String {
        let cut = |s: &str| {
            let c: Vec<char> = s.chars().collect();
            c[c.len().saturating_sub(800)..].iter().collect::<String>()
        };
        format!(
            "code {:?}, text {}\n--- stdout\n{}\n--- stderr\n{}",
            self.code,
            cut(&self.text),
            cut(&self.stdout),
            cut(&self.stderr)
        )
    }
    fn body(&self) -> String {
        split_block(&self.text).0
    }
    fn block(&self) -> Vec<(String, String)> {
        split_block(&self.text)
            .1
            .expect("conformance: PO: a block")
            .lines()
            .filter_map(|l| l.split_once(':'))
            .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
            .collect()
    }
    fn key(&self, k: &str) -> String {
        self.block()
            .into_iter()
            .find(|(a, _)| a == k)
            .unwrap_or_else(|| panic!("conformance: PO: no key {k}"))
            .1
    }
    fn untimed(&self) -> Vec<(String, String)> {
        self.block()
            .into_iter()
            .filter(|(k, _)| !k.ends_with("_ms") && !k.contains("rss"))
            .collect()
    }
}

fn child(fixture: &str, args: &str, out: &Path) -> Run {
    let c = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "conformance::online_p_tests::po_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("PO_FIXTURE", fixture)
        .env("PO_ARGS", args)
        .env("PO_OUT", out)
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let got = std::fs::read_to_string(out).ok();
    let (code, text) = match got.as_deref().and_then(|s| s.split_once('\n')) {
        Some((c, t)) => (c.parse().ok(), t.to_owned()),
        None => (None, String::new()),
    };
    Run {
        code,
        text,
        stdout: String::from_utf8_lossy(&c.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&c.stderr).into_owned(),
    }
}

fn dir(name: &str) -> PathBuf {
    scratch(&format!("po-{name}"))
}

/// The fixture's specification through the CLI's sequential export.
fn spec_cli(fixture: &str, d: &Path) -> PathBuf {
    let s = d.join("spec.jsonl");
    let r = child(
        fixture,
        &format!("export spec --out {} --seed 0", s.display()),
        &d.join("spec.res"),
    );
    assert_eq!(r.code, Some(0), "conformance: PO: the spec: {}", r.say());
    s
}

// =========================================================================
// PO-1.1: equal to sequential
// =========================================================================

fn equal_cli(fixture: &str, name: &str, want: (u64, u64, u64, u64, u64, u64), verdict: &str) {
    let d = dir(name);
    let s = spec_cli(fixture, &d);
    let (sf, pf) = (d.join("s.jsonl"), d.join("p.jsonl"));
    let a = child(
        fixture,
        &format!(
            "online --spec {} --seed 0 --out {}",
            s.display(),
            sf.display()
        ),
        &d.join("a"),
    );
    let b = child(
        fixture,
        &format!(
            "online --spec {} --seed 0 --threads 2 --out {}",
            s.display(),
            pf.display()
        ),
        &d.join("b"),
    );
    assert_eq!(a.code, Some(0), "conformance: PO: sequential: {}", a.say());
    assert_eq!(b.code, Some(0), "conformance: PO: parallel: {}", b.say());
    assert!(b.a_task_ran(), "conformance: PO: no task ran: {}", b.say());
    assert!(
        b.parallel_banner(),
        "conformance: PO: the banner: {}",
        b.say()
    );
    assert!(
        !a.parallel_banner(),
        "conformance: PO: sequential's: {}",
        a.say()
    );
    let num = |r: &Run, k: &str| r.key(k).parse::<u64>().unwrap_or(0);
    let got = |r: &Run| {
        (
            num(r, "iterations"),
            num(r, "graphs_complete"),
            num(r, "graphs_blocked"),
            num(r, "uncovered_total"),
            num(r, "summaries_distinct"),
            num(r, "spec_summaries"),
        )
    };
    assert_eq!(
        got(&a),
        want,
        "conformance: PO: {fixture}: sequential against the hand table"
    );
    assert_eq!(
        got(&b),
        want,
        "conformance: PO: {fixture}: parallel against the hand table"
    );
    let drop_first = |v: Vec<(String, String)>| {
        v.into_iter()
            .filter(|(k, _)| k != "first_miss_iteration")
            .collect::<Vec<_>>()
    };
    assert_eq!(
        drop_first(a.untimed()),
        drop_first(b.untimed()),
        "conformance: PO: {fixture}: the block's untimed keys"
    );
    assert!(
        a.body().contains(&format!("verdict:    {verdict}\n"))
            && b.body().contains(&format!("verdict:    {verdict}\n")),
        "conformance: PO: {fixture}: the verdict: {} {}",
        a.body(),
        b.body()
    );
    let (ls, lp) = (lines_of(&sf), lines_of(&pf));
    assert_eq!(ls, lp, "conformance: PO: {fixture}: the --out lines");
    assert_eq!(
        uncovered_set(&s, &sf),
        uncovered_set(&s, &pf),
        "conformance: PO: {fixture}: the uncovered lines"
    );
    // The text's own lookups and uncovered lines, verbatim.
    let pick = |t: String, h: &str| {
        t.lines()
            .find(|l| l.starts_with(h))
            .unwrap_or_else(|| panic!("conformance: PO: no {h}: {t}"))
            .to_owned()
    };
    for h in ["lookups:", "uncovered:", "mode:"] {
        assert_eq!(
            pick(a.body(), h),
            pick(b.body(), h),
            "conformance: PO: {fixture}: {h}"
        );
    }
}

/// `v` alone visible: one or two lines, 1 680 graphs.
#[test]
fn po1_equal_ok() {
    equal_cli("ok", "po1a", (1680, 1680, 0, 0, 1, 1), "conforms");
}

#[test]
fn po1_equal_bad() {
    equal_cli("bad", "po1b", (1680, 1680, 0, 560, 2, 1), "reports");
}

/// All visible: a line per ending.
#[test]
fn po1_equal_ok_all() {
    equal_cli("ok-all", "po1c", (1680, 1680, 0, 0, 1680, 1680), "conforms");
}

#[test]
fn po1_equal_bad_all() {
    equal_cli(
        "bad-all",
        "po1d",
        (1680, 1680, 0, 560, 1680, 1680),
        "reports",
    );
}

/// The report's every counter, in-process, with the hand values.
#[test]
fn po1_report_fields() {
    let d = dir("po1e");
    let s = d.join("spec.jsonl");
    spec_seq(&ALL, &s, || gated(3, 3, |_| send_one(PMsg::V(0))));
    let bad = || {
        gated(3, 3, |first| {
            send_one(PMsg::V(if first == 2 { 1 } else { 0 }))
        })
    };
    let a = seq(&ALL, &s, None, bad);
    let b = par(&ALL, &s, None, OnlinePSeams::default(), bad);
    assert_eq!(
        counters(&a),
        (1680, 1120, 560, 0, 560, 560),
        "conformance: PO: sequential against the hand table"
    );
    same(&a, &b.report, "bad");
    assert_eq!(b.report.lookups, 1680, "conformance: PO: the lookups");
}

// =========================================================================
// PO-1.2: the first miss
// =========================================================================

/// What the text says, with an iteration on sequential and none on this path.
#[test]
fn po2_text_and_block() {
    let d = dir("po2a");
    let s = spec_cli("bad-all", &d);
    let (sf, pf) = (d.join("s.jsonl"), d.join("p.jsonl"));
    let a = child(
        "bad-all",
        &format!(
            "online --spec {} --seed 0 --out {}",
            s.display(),
            sf.display()
        ),
        &d.join("a"),
    );
    let b = child(
        "bad-all",
        &format!(
            "online --spec {} --seed 0 --threads 2 --out {}",
            s.display(),
            pf.display()
        ),
        &d.join("b"),
    );
    assert_eq!(a.code, Some(0), "conformance: PO: {}", a.say());
    assert_eq!(b.code, Some(0), "conformance: PO: {}", b.say());
    let body = b.body();
    assert!(
        !body.contains("iteration"),
        "conformance: PO: an iteration in the text: {body}"
    );
    assert!(
        a.body().contains("first miss: iteration ") && a.body().contains("iteration "),
        "conformance: PO: sequential's text: {}",
        a.body()
    );
    // The block: the key is there, as every unmeasured cell, and it is empty.
    assert_eq!(
        b.key("first_miss_iteration"),
        "",
        "conformance: PO: the block"
    );
    assert_ne!(
        a.key("first_miss_iteration"),
        "",
        "conformance: PO: sequential's block"
    );
    let w: u128 = b.key("first_miss_wall_ms").parse().unwrap();
    let all: u128 = b.key("wall_ms").parse().unwrap();
    assert!(
        w <= all,
        "conformance: PO: the wall {w} against the run's {all}"
    );
    let line = |t: &str, h: &str| {
        t.lines()
            .find(|l| l.starts_with(h))
            .unwrap_or_else(|| panic!("conformance: PO: no {h}: {t}"))
            .to_owned()
    };
    assert_eq!(
        line(&body, "first miss:"),
        format!("first miss: {w} ms"),
        "conformance: PO: the line"
    );
    // `at:` as sequential's with its iteration cut.
    let at = line(&a.body(), "at:");
    let cut = at
        .split_once(", ")
        .expect("conformance: PO: sequential's at")
        .1;
    assert_eq!(
        line(&body, "at:"),
        format!("at:         {cut}"),
        "conformance: PO: at"
    );
    // The file's header: the lead's question. 0 there is "none" in JMC's fields.
    let (h, _) = read_jsonl(&pf);
    assert_eq!(
        h["first_miss_iteration"], 0,
        "conformance: PO: the header: {h}"
    );
    assert_eq!(
        h["first_miss_wall_ms"], w as u64,
        "conformance: PO: the header: {h}"
    );
    assert_eq!(
        h["uncovered_total"], 560,
        "conformance: PO: the header: {h}"
    );
    let (sh, _) = read_jsonl(&sf);
    assert!(
        sh["first_miss_iteration"].as_u64().unwrap() >= 1,
        "conformance: PO: sequential's header: {sh}"
    );
}

/// PO-0.7's order on two workers' misses: the smaller wall, then on equal walls the smaller
/// line, in either operand order, so the line reported does not depend on who flushed first.
/// Each operand has its own kind, so the whole miss is seen to come through.
#[test]
fn po2_earlier_is_the_smaller_wall_then_the_smaller_line() {
    let miss = |wall_ms: u64, line: &str, kind: MissKind| FirstMiss {
        iteration: 0,
        wall_ms,
        line: line.to_owned(),
        kind,
    };
    let early = miss(5, "z", MissKind::NoSig);
    let late = miss(7, "a", MissKind::NotFound);
    let small = miss(5, "a", MissKind::NotFound);
    let large = miss(5, "b", MissKind::NoSig);
    let cases = [
        (
            "smaller wall first",
            Some(&early),
            Some(&late),
            Some(&early),
        ),
        (
            "smaller wall second",
            Some(&late),
            Some(&early),
            Some(&early),
        ),
        (
            "equal walls, smaller line first",
            Some(&small),
            Some(&large),
            Some(&small),
        ),
        (
            "equal walls, smaller line second",
            Some(&large),
            Some(&small),
            Some(&small),
        ),
        ("none, then a miss", None, Some(&small), Some(&small)),
        ("a miss, then none", Some(&large), None, Some(&large)),
        ("none, then none", None, None, None),
    ];
    for (what, a, b, want) in cases {
        assert_eq!(
            earlier(a.cloned(), b.cloned()).as_ref(),
            want,
            "conformance: PO: {what}"
        );
    }
}

/// On a conforming run the block's first miss cells: empty iteration, wall 0.
#[test]
fn po2_conforming_block() {
    let d = dir("po2b");
    let s = spec_cli("ok", &d);
    let b = child(
        "ok",
        &format!("online --spec {} --seed 0 --threads 2", s.display()),
        &d.join("b"),
    );
    assert_eq!(b.code, Some(0), "conformance: PO: {}", b.say());
    assert_eq!(
        b.key("first_miss_iteration"),
        "",
        "conformance: PO: the block"
    );
    assert_eq!(
        b.key("first_miss_wall_ms"),
        "0",
        "conformance: PO: the block"
    );
    assert!(
        !b.body().contains("first miss"),
        "conformance: PO: {}",
        b.body()
    );
}

/// The state of [`hold_fixture`].
#[derive(Default)]
struct Hold {
    t_first: OnceLock<Instant>,
    a: OnceLock<ThreadId>,
    t_a: OnceLock<Instant>,
    t_y: OnceLock<Instant>,
    runs: AtomicUsize,
    a_runs: AtomicUsize,
    y_runs: AtomicUsize,
    held: AtomicBool,
}

/// The warmup's 100 executions are covered, so its flush holds no miss. Every later one
/// misses. `A`, the OS thread of the first of these, misses first; its task splits after 100
/// and ends one execution later (`rt0: 101 execs`), so at its 101st `A` holds, with its
/// earliest miss still in its worker's map, until the other worker has come and gone quiet.
/// That worker waits before its first run, so all its misses are later, and they reach the
/// merged set first.
fn hold_fixture(h: Arc<Hold>) {
    let me = std::thread::current().id();
    h.t_first.get_or_init(Instant::now);
    let n = h.runs.fetch_add(1, Ordering::SeqCst) + 1;
    let value = i32::from(n > 100);
    if n > 100 {
        let a = *h.a.get_or_init(|| me);
        if me == a {
            h.t_a.get_or_init(Instant::now);
            let k = h.a_runs.fetch_add(1, Ordering::SeqCst) + 1;
            if k == 101 {
                let start = Instant::now();
                let mut last = (0, Instant::now());
                while start.elapsed() < Duration::from_secs(20) {
                    let y = h.y_runs.load(Ordering::SeqCst);
                    if y != last.0 {
                        last = (y, Instant::now());
                    }
                    if y > 0 && last.1.elapsed() > Duration::from_millis(500) {
                        h.held.store(true, Ordering::SeqCst);
                        break;
                    }
                    std::thread::sleep(Duration::from_millis(5));
                }
            }
        } else {
            if h.t_y.get().is_none() {
                h.t_y.get_or_init(Instant::now);
                std::thread::sleep(Duration::from_millis(200));
            }
            h.y_runs.fetch_add(1, Ordering::SeqCst);
        }
    }
    gated(3, 3, move |_| send_one(PMsg::V(value)));
}

/// The minimum over workers, with the later miss flushed first.
#[test]
fn po2_minimum_over_workers() {
    let d = dir("po2c");
    let s = d.join("spec.jsonl");
    spec_seq(&ALL, &s, || gated(3, 3, |_| send_one(PMsg::V(0))));
    let h = Arc::new(Hold::default());
    let h2 = Arc::clone(&h);
    let r = par(&ALL, &s, None, OnlinePSeams::default(), move || {
        hold_fixture(Arc::clone(&h2))
    });
    let f = r.report.first.as_ref().expect("conformance: PO: a miss");
    let t0 = *h.t_first.get().expect("conformance: PO: a run");
    let ta = *h.t_a.get().expect("conformance: PO: a post-warmup run");
    let ty = *h
        .t_y
        .get()
        .expect("conformance: PO: the other worker ran nothing");
    assert!(
        h.held.load(Ordering::SeqCst),
        "conformance: PO: the placement: no hold"
    );
    let since = |t: Instant| t.duration_since(t0).as_millis() as u64;
    note!(
        "PO: first miss {} ms; A's first run {} ms, the other's {} ms, its misses from {} ms",
        f.wall_ms,
        since(ta),
        since(ty),
        since(ty) + 200
    );
    assert_eq!(
        counters(&r.report).0,
        1680,
        "conformance: PO: the run went to its end: {:?}",
        r.report.failure
    );
    assert_eq!(
        r.report.found, 100,
        "conformance: PO: the warmup is covered"
    );
    assert_eq!(
        r.report.uncovered_total, 1580,
        "conformance: PO: every later graph misses"
    );
    assert!(
        f.wall_ms >= since(ta),
        "conformance: PO: {} ms is before A's first run, {}",
        f.wall_ms,
        since(ta)
    );
    assert!(
        f.wall_ms < since(ty) + 200,
        "conformance: PO: {} ms is the other worker's, not the minimum, from {}",
        f.wall_ms,
        since(ty) + 200
    );
    assert!(
        f.wall_ms as u128 <= r.report.enumerate_ms,
        "conformance: PO: within the run"
    );
}

/// The clock starts after the index: a delay in the index phase is not in the wall.
#[test]
fn po2_clock() {
    let d = dir("po2d");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(2, 2, |_| send_one(PMsg::V(0))));
    let delay = Duration::from_millis(1500);
    let mut seams = OnlinePSeams::default();
    seams.index_delay = Some(delay);
    let bad = || gated(2, 2, |first| send_one(PMsg::V(first as i32 + 1)));
    let r = par(&["v"], &s, None, seams, bad);
    let f = r.report.first.as_ref().expect("conformance: PO: a miss");
    assert!(
        r.report.index_ms >= delay.as_millis(),
        "conformance: PO: index_ms {}",
        r.report.index_ms
    );
    assert!(
        (f.wall_ms as u128) < delay.as_millis(),
        "conformance: PO: the wall {} holds the index's delay",
        f.wall_ms
    );
    assert!(
        r.report.enumerate_ms < delay.as_millis(),
        "conformance: PO: enumerate_ms {} holds the index's delay",
        r.report.enumerate_ms
    );
    // The control: no delay, the index is small.
    let c = par(&["v"], &s, None, OnlinePSeams::default(), bad);
    assert!(
        c.report.index_ms < delay.as_millis(),
        "conformance: PO: the control's index_ms {}",
        c.report.index_ms
    );
}

// =========================================================================
// PO-1.3: refusals
// =========================================================================

fn in_process(args: &[&str], runs: Arc<AtomicUsize>, spec_file: &Path) -> (String, u8) {
    let _ = spec_file;
    let imp = move |_: &[String]| -> Entry {
        let r = Arc::clone(&runs);
        Arc::new(move || {
            r.fetch_add(1, Ordering::SeqCst);
            let x = crate::nondet();
            let y = crate::nondet();
            v_sends(PMsg::V(i32::from(x) + 2 * i32::from(y)));
        })
    };
    let spec = |_: &[String]| -> Entry { Arc::new(|| v_sends(PMsg::V(0))) };
    let visible = |_: &[String]| vis(&["v"]);
    let p = Program {
        visible: &visible,
        spec: &spec,
        imp: &imp,
    };
    let a: Vec<String> = args.iter().map(|s| (*s).to_owned()).collect();
    run_cli_with_model(&p, ConsType::Bag, &a)
}

#[test]
fn po3_flags_refused_above_one() {
    let d = dir("po3a");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || v_sends(PMsg::V(0)));
    let sp = s.display().to_string();
    for extra in [vec!["--stop-at-first"], vec!["--budget", "2"]] {
        let runs = Arc::new(AtomicUsize::new(0));
        let mut a = vec![
            "online",
            "--spec",
            sp.as_str(),
            "--seed",
            "0",
            "--threads",
            "2",
        ];
        a.extend(extra.iter().copied());
        let (t, code) = in_process(&a, Arc::clone(&runs), &s);
        assert_eq!(code, 2, "conformance: PO: {extra:?}: {t}");
        assert!(
            t.contains("--stop-at-first") && t.contains("--budget"),
            "conformance: PO: {extra:?}: the message names them: {t}"
        );
        assert_eq!(
            runs.load(Ordering::SeqCst),
            0,
            "conformance: PO: {extra:?}: a run"
        );
    }
}

#[test]
fn po3_flags_work_at_one() {
    let d = dir("po3b");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || v_sends(PMsg::V(0)));
    let sp = s.display().to_string();
    // 4 graphs, value 0 covered: the first miss by the 2nd or a later one.
    let runs = Arc::new(AtomicUsize::new(0));
    let (t, code) = in_process(
        &[
            "online",
            "--spec",
            &sp,
            "--seed",
            "0",
            "--threads",
            "1",
            "--stop-at-first",
        ],
        Arc::clone(&runs),
        &s,
    );
    assert_eq!(code, 0, "conformance: PO: {t}");
    assert!(t.contains("mode:       bug-finder"), "conformance: PO: {t}");
    assert!(t.contains("first miss: iteration "), "conformance: PO: {t}");
    let n = runs.load(Ordering::SeqCst);
    assert!((1..4).contains(&n), "conformance: PO: {n} runs: {t}");
    let runs = Arc::new(AtomicUsize::new(0));
    let (t, code) = in_process(
        &[
            "online",
            "--spec",
            &sp,
            "--seed",
            "0",
            "--threads",
            "1",
            "--budget",
            "2",
        ],
        Arc::clone(&runs),
        &s,
    );
    assert_eq!(code, 0, "conformance: PO: {t}");
    assert!(t.contains("stop_reason: budget"), "conformance: PO: {t}");
    assert!(runs.load(Ordering::SeqCst) <= 3, "conformance: PO: {t}");
    // `--threads 0` is refused as ever.
    let (t, code) = in_process(
        &["online", "--spec", &sp, "--threads", "0"],
        Arc::new(AtomicUsize::new(0)),
        &s,
    );
    assert_eq!(code, 2, "conformance: PO: {t}");
    assert!(
        t.contains("--threads needs at least 1"),
        "conformance: PO: {t}"
    );
}

/// The four refusals, on both paths: equal, before any execution.
#[test]
fn po3_spec_refusals() {
    let d = dir("po3c");
    let good = d.join("spec.jsonl");
    spec_seq(&["v"], &good, || v_sends(PMsg::V(0)));
    let (h, lines) = read_jsonl(&good);
    let text = std::fs::read_to_string(&good).unwrap();
    let first = text.lines().next().unwrap();
    let aborted = d.join("aborted.jsonl");
    std::fs::write(
        &aborted,
        format!(
            "{}\n{}\n",
            first.replace("\"complete\"", "\"aborted\""),
            lines.join("\n")
        ),
    )
    .unwrap();
    assert_eq!(h["enumeration"], "complete", "conformance: PO: {h}");
    let junk = d.join("junk.jsonl");
    std::fs::write(&junk, "not json\n").unwrap();
    let cases: Vec<(&str, PathBuf, Vec<&str>, ConsType, bool)> = vec![
        (
            "Spec, no file",
            d.join("absent.jsonl"),
            vec!["v"],
            ConsType::Bag,
            false,
        ),
        ("Spec, junk", junk, vec!["v"], ConsType::Bag, false),
        ("NotComplete", aborted, vec!["v"], ConsType::Bag, false),
        (
            "Visible",
            good.clone(),
            vec!["v", "w"],
            ConsType::Bag,
            false,
        ),
        ("Model", good, vec!["v"], ConsType::MO, true),
    ];
    for (tag, spec, visible, model, with_out) in cases {
        let o = d.join("o.jsonl");
        let mut cfg = config(0);
        cfg.cons_type = model;
        let n = Arc::new(AtomicUsize::new(0));
        let (n1, n2) = (Arc::clone(&n), Arc::clone(&n));
        let a = online::online(
            &cfg,
            &vis(&visible),
            Arc::new(move || {
                n1.fetch_add(1, Ordering::SeqCst);
            }),
            &spec,
            OnlineOpts::new(Mode::Full, None, with_out.then(|| out_of(&o))),
        );
        let b = online_partitioned_with(
            &cfg,
            2,
            &vis(&visible),
            Arc::new(move || {
                n2.fetch_add(1, Ordering::SeqCst);
            }),
            &spec,
            with_out.then(|| out_of(&o)),
            OnlinePSeams::default(),
        );
        let e1 = a
            .err()
            .unwrap_or_else(|| panic!("conformance: PO: {tag}: sequential ran"));
        let e2 = b
            .err()
            .unwrap_or_else(|| panic!("conformance: PO: {tag}: parallel ran"));
        assert_eq!(e1, e2, "conformance: PO: {tag}");
        let right = match tag {
            "NotComplete" => matches!(e2, OnlineError::NotComplete { .. }),
            "Visible" => matches!(e2, OnlineError::Visible { .. }),
            "Model" => matches!(e2, OnlineError::Model(_)),
            _ => matches!(e2, OnlineError::Spec(_)),
        };
        assert!(right, "conformance: PO: {tag}: {e2:?}");
        assert_eq!(n.load(Ordering::SeqCst), 0, "conformance: PO: {tag}: a run");
        assert!(!o.exists(), "conformance: PO: {tag}: a file");
    }
}

// =========================================================================
// PO-1.4: per-graph names
// =========================================================================

fn names_spec(d: &Path) -> PathBuf {
    let s = d.join("spec.jsonl");
    spec_par(&["v"], &s, names_fixture);
    let ls = lines_of(&s);
    assert_eq!(ls.len(), 2, "conformance: PO: the spec's lines: {ls:?}");
    s
}

/// A copy of `spec` with only the lines naming `name`.
fn only(spec: &Path, name: &str, to: &Path) {
    let text = std::fs::read_to_string(spec).unwrap();
    let mut it = text.lines();
    let mut t = format!("{}\n", it.next().unwrap());
    for l in it {
        if l.contains(&format!("\"{name}\"")) {
            t.push_str(l);
            t.push('\n');
        }
    }
    std::fs::write(to, t).unwrap();
}

#[test]
fn po4_names_one_worker() {
    let d = dir("po4a");
    let s = names_spec(&d);
    let o = d.join("o.jsonl");
    let r = par(&["v"], &s, Some(&o), OnlinePSeams::default(), names_fixture);
    assert_eq!(
        r.max_worker_lines, 2,
        "conformance: PO: one worker before a flush"
    );
    assert_eq!(
        counters(&r.report),
        (2, 2, 0, 0, 0, 0),
        "conformance: PO: covered"
    );
    assert_eq!(
        r.report.end,
        End::Exhausted,
        "conformance: PO: {:?}",
        r.report.failure
    );
    assert_eq!(lines_of(&o), lines_of(&s), "conformance: PO: the lines");
    let a = d.join("a.jsonl");
    only(&s, "a", &a);
    let r = par(&["v"], &a, None, OnlinePSeams::default(), names_fixture);
    assert_eq!(
        counters(&r.report),
        (2, 1, 1, 0, 1, 1),
        "conformance: PO: a alone"
    );
    let f = r.report.first.as_ref().expect("conformance: PO: a miss");
    assert!(f.line.contains("\"b\""), "conformance: PO: {}", f.line);
    assert!(!f.line.contains("\"a\""), "conformance: PO: {}", f.line);
}

#[test]
fn po4_names_across_a_flush() {
    let d = dir("po4b");
    let s = names_spec(&d);
    let mut seams = OnlinePSeams::default();
    seams.flush_entries = Some(1);
    let o = d.join("o.jsonl");
    let r = par(&["v"], &s, Some(&o), seams, names_fixture);
    assert_eq!(r.max_worker_lines, 1, "conformance: PO: a flush between");
    assert_eq!(
        counters(&r.report),
        (2, 2, 0, 0, 0, 0),
        "conformance: PO: covered"
    );
    assert_eq!(lines_of(&o), lines_of(&s), "conformance: PO: the lines");
}

#[test]
fn po4_names_across_workers() {
    let d = dir("po4c");
    let s = d.join("spec.jsonl");
    let seen0 = Arc::new(Mutex::new(HashSet::new()));
    let s0 = Arc::clone(&seen0);
    spec_par(&["v"], &s, move || names_tasks_fixture(Arc::clone(&s0)));
    assert_eq!(lines_of(&s).len(), 2, "conformance: PO: the spec's lines");
    let seen = Arc::new(Mutex::new(HashSet::new()));
    let s2 = Arc::clone(&seen);
    let o = d.join("o.jsonl");
    let r = par(&["v"], &s, Some(&o), OnlinePSeams::default(), move || {
        names_tasks_fixture(Arc::clone(&s2))
    });
    assert_eq!(
        counters(&r.report),
        (1680, 1680, 0, 0, 0, 0),
        "conformance: PO: covered"
    );
    assert_eq!(lines_of(&o), lines_of(&s), "conformance: PO: the lines");
    let seen = seen.lock().unwrap();
    let on = |n: &str| {
        seen.iter()
            .filter(|(m, _)| m == n)
            .map(|(_, t)| *t)
            .collect::<HashSet<_>>()
    };
    let (a, b) = (on("a"), on("b"));
    assert!(
        a.len() + b.len() >= 3 && a.iter().any(|x| b.iter().any(|y| x != y)),
        "conformance: PO: the placement: {a:?} {b:?}"
    );
    // With `a` alone, the misses are `b`'s 560, under `b`'s name.
    let aa = d.join("a.jsonl");
    only(&s, "a", &aa);
    let seen = Arc::new(Mutex::new(HashSet::new()));
    let r = par(&["v"], &aa, None, OnlinePSeams::default(), move || {
        names_tasks_fixture(Arc::clone(&seen))
    });
    assert_eq!(
        counters(&r.report),
        (1680, 1120, 560, 0, 560, 1),
        "conformance: PO: a alone"
    );
    assert!(
        r.report.first.as_ref().unwrap().line.contains("\"b\""),
        "conformance: PO: the miss's name"
    );
}

/// PAR-EXPORT's difference (c) on this path: an id absent from its graph refuses.
#[test]
fn po4_absent_thread() {
    let d = dir("po4d");
    let s = spec_cli("absent-in-task", &d);
    let o = d.join("o.jsonl");
    let b = child(
        "absent-in-task",
        &format!(
            "online --spec {} --seed 0 --threads 2 --out {}",
            s.display(),
            o.display()
        ),
        &d.join("b"),
    );
    assert_eq!(b.code, Some(1), "conformance: PO: {}", b.say());
    assert!(
        b.body().contains("is not a thread of this graph"),
        "conformance: PO: {}",
        b.body()
    );
    assert_eq!(
        read_jsonl(&o).0["enumeration"],
        "aborted",
        "conformance: PO: the header"
    );
}

// =========================================================================
// PO-1.5: failures
// =========================================================================

/// `fixture` fails in a task on both paths: exit 1, the same text, an `aborted` file.
fn fails_in_a_task(fixture: &str, name: &str, want: &str) {
    let d = dir(name);
    let s = spec_cli(fixture, &d);
    let (sf, pf) = (d.join("s.jsonl"), d.join("p.jsonl"));
    std::fs::write(&pf, "earlier\n").unwrap();
    let a = child(
        fixture,
        &format!(
            "online --spec {} --seed 0 --out {}",
            s.display(),
            sf.display()
        ),
        &d.join("a"),
    );
    let b = child(
        fixture,
        &format!(
            "online --spec {} --seed 0 --threads 2 --out {}",
            s.display(),
            pf.display()
        ),
        &d.join("b"),
    );
    assert_eq!(a.code, Some(1), "conformance: PO: sequential: {}", a.say());
    assert_eq!(b.code, Some(1), "conformance: PO: parallel: {}", b.say());
    let failed = |r: &Run| {
        r.body()
            .lines()
            .find(|l| l.starts_with("FAILED:"))
            .unwrap_or_else(|| panic!("conformance: PO: no FAILED: {}", r.say()))
            .to_owned()
    };
    assert!(failed(&b).contains(want), "conformance: PO: {}", failed(&b));
    note!(
        "PO: {fixture}: sequential `{}`; parallel `{}`",
        failed(&a),
        failed(&b)
    );
    assert_eq!(b.key("stop_reason"), "error", "conformance: PO: the block");
    assert_eq!(
        a.key("stop_reason"),
        "error",
        "conformance: PO: sequential's block"
    );
    assert!(
        b.parallel_banner() || b.stdout.contains("rt"),
        "conformance: PO: the path: {}",
        b.say()
    );
    assert!(b.a_task_ran(), "conformance: PO: no task ran: {}", b.say());
    for (f, tag) in [(&sf, "sequential"), (&pf, "parallel")] {
        let (h, ls) = read_jsonl(f);
        assert_eq!(
            h["enumeration"], "aborted",
            "conformance: PO: {tag}: the header"
        );
        assert!(is_sorted(&ls), "conformance: PO: {tag}: sorted");
    }
    assert_eq!(failed(&a), failed(&b), "conformance: PO: the text");
}

#[test]
fn po5_assert_in_a_task() {
    fails_in_a_task("assert-in-task", "po5a", "assertion failure on thread `v`");
}

#[test]
fn po5_encode_in_a_task() {
    fails_in_a_task("encode-in-task", "po5b", "@@");
}

#[test]
fn po5_program_panic_in_a_task() {
    fails_in_a_task("panic-in-task", "po5c", "the program's panic");
}

/// The failure on a task, by construction: only a worker off the root can fail. Sequential
/// has no such worker, so the hand text is the reference.
fn fails_off_the_root(fixture: &str, name: &str, want: &str) {
    let d = dir(name);
    let s = spec_cli(fixture, &d);
    let pf = d.join("p.jsonl");
    std::fs::write(&pf, "earlier\n").unwrap();
    let b = child(
        fixture,
        &format!(
            "online --spec {} --seed 0 --threads 2 --out {}",
            s.display(),
            pf.display()
        ),
        &d.join("b"),
    );
    assert_eq!(b.code, Some(1), "conformance: PO: {}", b.say());
    assert!(
        b.stdout.contains(OFF_ROOT),
        "conformance: PO: off the root: {}",
        b.say()
    );
    assert!(
        b.parallel_banner(),
        "conformance: PO: the banner: {}",
        b.say()
    );
    assert!(
        b.body()
            .lines()
            .any(|l| l.starts_with("FAILED:") && l.contains(want)),
        "conformance: PO: the text: {}",
        b.body()
    );
    assert!(
        b.body().contains("verdict:    partial\n"),
        "conformance: PO: {}",
        b.body()
    );
    assert_eq!(b.key("stop_reason"), "error", "conformance: PO: the block");
    assert_eq!(
        b.key("first_miss_iteration"),
        "",
        "conformance: PO: the block"
    );
    let (h, ls) = read_jsonl(&pf);
    assert_eq!(h["enumeration"], "aborted", "conformance: PO: the header");
    assert!(is_sorted(&ls), "conformance: PO: sorted");
    assert!(
        !ls.is_empty() || fixture == "assert-off-root",
        "conformance: PO: the lines held"
    );
    note!(
        "PO: {fixture}: {} lines held, iterations {}",
        ls.len(),
        b.key("iterations")
    );
}

#[test]
fn po5_assert_off_the_root() {
    fails_off_the_root("assert-off-root", "po5j", "assertion failure on thread `v`");
}

#[test]
fn po5_encode_off_the_root() {
    fails_off_the_root("encode-off-root", "po5k", "@@");
}

#[test]
fn po5_panic_off_the_root() {
    fails_off_the_root("panic-off-root", "po5l", "the program's panic");
}

/// A panic in a sink on a worker: the seam on the failure path panics, so past the runner's
/// re-raise the run's thread catches it. The file is written from what the flushes held.
#[test]
fn po5_worker_panic_in_the_sink() {
    let d = dir("po5d");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(3, 3, |_| {}));
    let o = d.join("o.jsonl");
    std::fs::write(&o, "earlier\n").unwrap();
    let on: Arc<Mutex<Option<ThreadId>>> = Arc::new(Mutex::new(None));
    let on2 = Arc::clone(&on);
    let mut seams = OnlinePSeams::default();
    seams.before_fail = Some(Arc::new(move || {
        *on2.lock().unwrap() = Some(std::thread::current().id());
        panic!("conformance: PO: the sink's panic");
    }));
    let root: Arc<OnceLock<ThreadId>> = Arc::new(OnceLock::new());
    let r2 = Arc::clone(&root);
    let r = par(&["v"], &s, Some(&o), seams, move || {
        r2.get_or_init(|| std::thread::current().id());
        gated(3, 3, |first| crate::assert(first != 2));
    });
    assert_eq!(r.report.end, End::Failed, "conformance: PO: the end");
    assert_eq!(
        r.report.failure.as_deref(),
        Some("conformance: PO: the sink's panic"),
        "conformance: PO: the text"
    );
    assert_eq!(r.report.exit_code(), 1, "conformance: PO: the exit");
    let (h, ls) = read_jsonl(&o);
    assert_eq!(h["enumeration"], "aborted", "conformance: PO: the header");
    assert!(is_sorted(&ls), "conformance: PO: sorted");
    assert!(
        on.lock().unwrap().is_some(),
        "conformance: PO: the seam ran"
    );
}

/// An assertion on a thread not visible: both paths fail alike.
#[test]
fn po5_assert_on_an_invisible_thread() {
    let d = dir("po5e");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(3, 3, |_| {}));
    let bad = || {
        gated(3, 3, |first| {
            let x = named("x", move || crate::assert(first != 2));
            x.join().unwrap();
        })
    };
    let a = seq(&["v"], &s, None, bad);
    let b = par(&["v"], &s, None, OnlinePSeams::default(), bad);
    note!("PO: invisible: {:?} / {:?}", a.failure, b.report.failure);
    assert_eq!(a.end, End::Failed, "conformance: PO: sequential");
    assert_eq!(b.report.end, End::Failed, "conformance: PO: parallel");
    assert_eq!(a.failure, b.report.failure, "conformance: PO: the text");
}

/// The cancel curtails: executions and iterations, far below the control's. One failure,
/// the first off the root; without the cancel the root runs on.
#[test]
fn po5_cancel_is_effective() {
    let d = dir("po5f");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(3, 4, |_| {}));
    let runs = |bad: bool| {
        let n = Arc::new(AtomicUsize::new(0));
        let m = Arc::clone(&n);
        let who = Arc::new(Who::default());
        let once = Arc::new(AtomicBool::new(false));
        let r = par(&["v"], &s, None, OnlinePSeams::default(), move || {
            m.fetch_add(1, Ordering::SeqCst);
            let (is_root, _) = who.enter();
            let fail = bad && !is_root && !once.swap(true, Ordering::SeqCst);
            gated(3, 4, move |_| crate::assert(!fail));
        });
        (n.load(Ordering::SeqCst), r)
    };
    let (control, c) = runs(false);
    assert_eq!(c.report.end, End::Exhausted, "conformance: PO: the control");
    assert_eq!(control, 34650, "conformance: PO: the control's endings");
    assert_eq!(
        c.report.iterations, 34650,
        "conformance: PO: the control's iterations"
    );
    let (curtailed, f) = runs(true);
    assert_eq!(f.report.end, End::Failed, "conformance: PO: the end");
    note!(
        "PO: {curtailed} executions, {} iterations, {} turned away, against the control's \
         {control}",
        f.report.iterations,
        f.stopped_at_head
    );
    assert!(
        curtailed * 2 < control,
        "conformance: PO: {curtailed} executions against the control's {control}"
    );
    assert!(
        f.report.iterations * 2 < control,
        "conformance: PO: {} iterations against the control's {control}",
        f.report.iterations
    );
}

/// The seam: a cancel with no failure is `End::Failed` with the stated message.
#[test]
fn po5_cancel_at_seam() {
    let d = dir("po5g");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(3, 3, |_| send_one(PMsg::V(0))));
    let o = d.join("o.jsonl");
    let mut seams = OnlinePSeams::default();
    seams.cancel_at = Some(10);
    let r = par(&["v"], &s, Some(&o), seams, || {
        gated(3, 3, |_| send_one(PMsg::V(0)))
    });
    assert_eq!(r.report.end, End::Failed, "conformance: PO: the end");
    assert_eq!(
        r.report.failure.as_deref(),
        Some("the run was cancelled"),
        "conformance: PO: the text"
    );
    assert_eq!(
        r.report.iterations, 9,
        "conformance: PO: the iterations before it"
    );
    assert!(r.stopped_at_head >= 1, "conformance: PO: turned away");
    assert_eq!(
        read_jsonl(&o).0["enumeration"],
        "aborted",
        "conformance: PO: the header"
    );
    assert_eq!(r.report.exit_code(), 1, "conformance: PO: the exit");
}

/// The failure path's meeting place: each party waits for the other, bounded, so that a
/// run with one party fails its assertion, not hangs.
#[derive(Default)]
struct Meet {
    state: Mutex<Vec<(ThreadId, String)>>,
    cv: Condvar,
}

impl Meet {
    /// Records this thread with what it fails on, and waits until there are two.
    fn arrive(&self, what: String) -> usize {
        let mut g = self.state.lock().unwrap();
        g.push((std::thread::current().id(), what));
        let me = g.len();
        self.cv.notify_all();
        let start = Instant::now();
        while g.len() < 2 && start.elapsed() < Duration::from_secs(20) {
            g = self
                .cv
                .wait_timeout(g, Duration::from_millis(20))
                .unwrap()
                .0;
        }
        me
    }
}

/// The root's OS thread, and how many executions it has begun. The root's warmup and loop
/// run on one OS thread, the first execution's; another OS thread is a task's.
#[derive(Default)]
struct Who {
    root: OnceLock<ThreadId>,
    runs: AtomicUsize,
}

impl Who {
    /// (this is the root, its execution number).
    fn enter(&self) -> (bool, usize) {
        let me = std::thread::current().id();
        let is_root = *self.root.get_or_init(|| me) == me;
        let n = if is_root {
            self.runs.fetch_add(1, Ordering::SeqCst) + 1
        } else {
            0
        };
        (is_root, n)
    }
}

/// Two workers fail with different texts past the warmup (the root on `v`, a task on `x`),
/// held at a meeting in the failure path; the second to arrive enters the lock later, by a
/// delay. The text kept is the first's, and both entries count.
#[test]
fn po5_race_first_stays() {
    let d = dir("po5h");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(3, 3, |_| {}));
    let meet = Arc::new(Meet::default());
    let m2 = Arc::clone(&meet);
    let what: Arc<Mutex<std::collections::HashMap<ThreadId, String>>> = Arc::default();
    let w2 = Arc::clone(&what);
    let mut seams = OnlinePSeams::default();
    seams.before_fail = Some(Arc::new(move || {
        let t = w2
            .lock()
            .unwrap()
            .get(&std::thread::current().id())
            .cloned()
            .unwrap_or_default();
        if m2.arrive(t) == 2 {
            std::thread::sleep(Duration::from_millis(100));
        }
    }));
    let who = Arc::new(Who::default());
    let w3 = Arc::clone(&what);
    let r = par(&["v"], &s, None, seams, move || {
        let (is_root, n) = who.enter();
        let os = std::thread::current().id();
        let fails = !is_root || n > 100;
        let w4 = Arc::clone(&w3);
        gated(3, 3, move |_| {
            if fails {
                if is_root {
                    w4.lock().unwrap().insert(os, "v".to_owned());
                    crate::assert(false);
                } else {
                    w4.lock().unwrap().insert(os, "x".to_owned());
                    let x = named("x", || crate::assert(false));
                    x.join().unwrap();
                }
            }
        });
    });
    let got = meet.state.lock().unwrap().clone();
    note!(
        "PO: race: arrivals {got:?}, kept {:?}, iterations {}, turned away {}",
        r.report.failure,
        r.report.iterations,
        r.stopped_at_head
    );
    let two: HashSet<_> = got.iter().map(|(t, _)| *t).collect();
    assert_eq!(two.len(), 2, "conformance: PO: two workers met: {got:?}");
    assert_eq!(r.report.end, End::Failed, "conformance: PO: the end");
    let text = r
        .report
        .failure
        .clone()
        .expect("conformance: PO: a failure");
    assert!(
        text.contains(&format!("`{}`", got[0].1)),
        "conformance: PO: kept `{text}`, the first to arrive was {}",
        got[0].1
    );
    assert_eq!(
        r.report.iterations, 102,
        "conformance: PO: the warmup's 100 and the two that entered"
    );
}

/// A task fails while the root is inside an execution. The root's completes after the
/// cancel, so its sink is entered after it: turned away, and `iterations` doesn't count it.
#[test]
fn po5_sink_after_the_cancel() {
    let d = dir("po5i");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(3, 3, |_| {}));
    let release = Arc::new(AtomicBool::new(false));
    let holding = Arc::new(AtomicBool::new(false));
    let (r3, h3) = (Arc::clone(&release), Arc::clone(&holding));
    let mut seams = OnlinePSeams::default();
    seams.before_fail = Some(Arc::new(move || {
        let start = Instant::now();
        while !h3.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(20) {
            std::thread::sleep(Duration::from_millis(1));
        }
        r3.store(true, Ordering::SeqCst);
    }));
    let who = Arc::new(Who::default());
    let (r2, h2) = (Arc::clone(&release), Arc::clone(&holding));
    let r = par(&["v"], &s, None, seams, move || {
        let (is_root, n) = who.enter();
        if is_root && n == 101 {
            h2.store(true, Ordering::SeqCst);
            let start = Instant::now();
            while !r2.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(20) {
                std::thread::sleep(Duration::from_millis(1));
            }
            // Long enough for the cancel to be set after the seam returns.
            std::thread::sleep(Duration::from_millis(200));
        }
        gated(3, 3, move |_| {
            if !is_root {
                crate::assert(false);
            }
        });
    });
    note!(
        "PO: after the cancel: held {}, turned away {}, iterations {}, end {:?}",
        holding.load(Ordering::SeqCst),
        r.stopped_at_head,
        r.report.iterations,
        r.report.end
    );
    assert!(
        holding.load(Ordering::SeqCst),
        "conformance: PO: the root held"
    );
    assert_eq!(r.report.end, End::Failed, "conformance: PO: the end");
    assert!(
        r.report
            .failure
            .as_deref()
            .is_some_and(|t| t.contains("`v`")),
        "conformance: PO: the failure: {:?}",
        r.report.failure
    );
    assert_eq!(
        r.stopped_at_head, 1,
        "conformance: PO: the root's sink turned away"
    );
    assert_eq!(
        r.report.iterations, 101,
        "conformance: PO: the warmup's 100 and the task's failing one, not the root's"
    );
}

// =========================================================================
// PO-1.6: `--out`
// =========================================================================

#[test]
fn po6_out_sorted_stable_equal_joinable() {
    let d = dir("po6");
    let s = d.join("spec.jsonl");
    spec_seq(&ALL, &s, || gated(3, 3, |_| send_one(PMsg::V(0))));
    let ok = || gated(3, 3, |_| send_one(PMsg::V(0)));
    let bad = || {
        gated(3, 3, |first| {
            send_one(PMsg::V(if first == 2 { 1 } else { 0 }))
        })
    };
    // Conforming: whole bytes over two seeds.
    let (a, b, q) = (d.join("a"), d.join("b"), d.join("q"));
    let r1 = par_seed(0, &ALL, &s, Some(&a), OnlinePSeams::default(), ok);
    let r2 = par_seed(1, &ALL, &s, Some(&b), OnlinePSeams::default(), ok);
    assert_eq!(
        r1.report.out_written.as_ref().map(|x| x.1),
        Some(1680),
        "conformance: PO: the count"
    );
    assert_eq!(r2.report.end, End::Exhausted, "conformance: PO: the end");
    assert_eq!(
        std::fs::read(&a).unwrap(),
        std::fs::read(&b).unwrap(),
        "conformance: PO: two seeds"
    );
    assert!(is_sorted(&lines_of(&a)), "conformance: PO: sorted");
    let z = seq(&ALL, &s, Some(&q), ok);
    assert_eq!(z.end, End::Exhausted, "conformance: PO: sequential");
    assert_eq!(
        std::fs::read(&a).unwrap(),
        std::fs::read(&q).unwrap(),
        "conformance: PO: sequential's bytes, conforming"
    );
    // Violating: the lines over two seeds and against sequential, the header but the wall.
    let (va, vb, vq) = (d.join("va"), d.join("vb"), d.join("vq"));
    let r1 = par_seed(0, &ALL, &s, Some(&va), OnlinePSeams::default(), bad);
    let r2 = par_seed(1, &ALL, &s, Some(&vb), OnlinePSeams::default(), bad);
    assert_eq!(
        r1.report.uncovered_total, 560,
        "conformance: PO: a violation"
    );
    assert_eq!(
        r2.report.uncovered_total, 560,
        "conformance: PO: a violation"
    );
    let _ = seq(&ALL, &s, Some(&vq), bad);
    assert_eq!(lines_of(&va), lines_of(&vb), "conformance: PO: two seeds");
    assert_eq!(
        lines_of(&va),
        lines_of(&vq),
        "conformance: PO: sequential's"
    );
    assert_eq!(
        sorted(lines_of(&va)),
        lines_of(&va),
        "conformance: PO: sorted"
    );
    let norm = |p: &Path| {
        let (mut h, _) = read_jsonl(p);
        let o = h.as_object_mut().unwrap();
        o.remove("first_miss_wall_ms");
        h
    };
    assert_eq!(
        norm(&va),
        norm(&vb),
        "conformance: PO: the header but the wall"
    );
    // Against sequential the header differs by the iteration only.
    let drop_it = |p: &Path| {
        let (mut h, _) = read_jsonl(p);
        let o = h.as_object_mut().unwrap();
        o.remove("first_miss_wall_ms");
        o.remove("first_miss_iteration");
        h
    };
    assert_eq!(
        drop_it(&va),
        drop_it(&vq),
        "conformance: PO: the header against sequential"
    );
    // Joinable, and the join agrees.
    let j = conf_join(&s, &va).unwrap_or_else(|e| panic!("conformance: PO: the join: {e:?}"));
    assert_eq!(
        j.uncovered.len(),
        560,
        "conformance: PO: the join's uncovered"
    );
    assert_eq!(j.exit_code(), 1, "conformance: PO: the join's verdict");
    let j = conf_join(&s, &a).unwrap_or_else(|e| panic!("conformance: PO: the join: {e:?}"));
    assert_eq!(
        j.uncovered.len(),
        0,
        "conformance: PO: the join on the conforming"
    );
    assert_eq!(j.exit_code(), 0, "conformance: PO: the join's verdict");
}

/// A replacing write: an earlier file gives way, no temporary stays, and a bad path is a
/// failed run, as sequential's.
#[test]
fn po6_write() {
    let d = dir("po6b");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || gated(2, 2, |_| send_one(PMsg::V(0))));
    let ok = || gated(2, 2, |_| send_one(PMsg::V(0)));
    let o = d.join("o.jsonl");
    std::fs::write(&o, "earlier\n").unwrap();
    let r = par(&["v"], &s, Some(&o), OnlinePSeams::default(), ok);
    assert_eq!(r.report.end, End::Exhausted, "conformance: PO: the end");
    assert_eq!(
        read_jsonl(&o).0["enumeration"],
        "complete",
        "conformance: PO: the header"
    );
    let names: Vec<_> = std::fs::read_dir(&d)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .collect();
    assert!(
        names.iter().all(|n| !n.contains("tmp")),
        "conformance: PO: a temporary stayed: {names:?}"
    );
    let bad = d.join("no-such-dir").join("o.jsonl");
    let r = par(&["v"], &s, Some(&bad), OnlinePSeams::default(), ok);
    let q = seq(&["v"], &s, Some(&bad), ok);
    assert_eq!(r.report.end, End::Failed, "conformance: PO: the end");
    assert_eq!(q.end, End::Failed, "conformance: PO: sequential's end");
    note!("PO: bad path: {:?} / {:?}", r.report.failure, q.failure);
    assert_eq!(r.report.exit_code(), 1, "conformance: PO: the exit");
}

// =========================================================================
// PO-1.8: the sequential path
// =========================================================================

#[test]
fn po8_threads_one_is_sequential() {
    let d = dir("po8");
    let s = spec_cli("bad-all", &d);
    let run = |n: &str, extra: &str| {
        let o = d.join(n);
        let r = child(
            "bad-all",
            &format!(
                "online --spec {} --seed 0{extra} --out {}",
                s.display(),
                o.display()
            ),
            &d.join(format!("{n}.res")),
        );
        assert_eq!(r.code, Some(0), "conformance: PO: {}", r.say());
        (r, o)
    };
    let (a, ao) = run("a", "");
    let (b, bo) = run("b", " --threads 1");
    assert!(
        !b.parallel_banner(),
        "conformance: PO: a banner at one: {}",
        b.say()
    );
    assert!(
        !b.stdout.contains("Pool size"),
        "conformance: PO: a pool at one: {}",
        b.say()
    );
    assert_eq!(a.untimed(), b.untimed(), "conformance: PO: the block");
    assert_ne!(
        b.key("first_miss_iteration"),
        "",
        "conformance: PO: an iteration at one"
    );
    let cut = |t: String| {
        // Apart from the wall in `first miss:` and the same-run `--out` path.
        t.lines()
            .filter(|l| !l.starts_with("first miss:"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    assert_eq!(cut(a.body()), cut(b.body()), "conformance: PO: the text");
    assert_eq!(lines_of(&ao), lines_of(&bo), "conformance: PO: the lines");
    let (mut h1, mut h2) = (read_jsonl(&ao).0, read_jsonl(&bo).0);
    h1.as_object_mut().unwrap().remove("first_miss_wall_ms");
    h2.as_object_mut().unwrap().remove("first_miss_wall_ms");
    assert_eq!(h1, h2, "conformance: PO: the header");
}

// =========================================================================
// PO-1.10: storage
// =========================================================================

#[test]
fn po10_storage() {
    let d = dir("po10");
    let s = d.join("spec.jsonl");
    spec_seq(&ALL, &s, || gated(3, 3, |_| send_one(PMsg::V(0))));
    let ok = || gated(3, 3, |_| send_one(PMsg::V(0)));
    for flush in [3usize, 64, 4096] {
        let o = d.join(format!("o{flush}"));
        let mut seams = OnlinePSeams::default();
        seams.flush_entries = Some(flush);
        let r = par(&ALL, &s, Some(&o), seams, ok);
        let ls = lines_of(&o);
        assert_eq!(ls.len(), 1680, "conformance: PO: {flush}: the lines");
        let bytes: usize = ls.iter().map(String::len).sum();
        assert_eq!(
            r.merged_bytes, bytes,
            "conformance: PO: {flush}: one string per line"
        );
        assert!(
            r.max_worker_lines <= flush,
            "conformance: PO: {flush}: a worker map held {}",
            r.max_worker_lines
        );
        if flush < 1680 / 2 {
            assert_eq!(
                r.max_worker_lines, flush,
                "conformance: PO: {flush}: it filled"
            );
        }
        note!(
            "PO: flush {flush}: max worker lines {}, merged bytes {}",
            r.max_worker_lines,
            r.merged_bytes
        );
    }
}

/// The block's name for the path's own report function, by a direct call.
#[test]
fn po10_block_of_a_report() {
    let d = dir("po10b");
    let s = d.join("spec.jsonl");
    spec_seq(&["v"], &s, || v_sends(PMsg::V(0)));
    let r = par(&["v"], &s, None, OnlinePSeams::default(), || {
        v_sends(PMsg::V(1))
    });
    let block = measure::of_online(&r.report, 0).render();
    assert!(
        block.contains("first_miss_iteration: \n"),
        "conformance: PO: {block}"
    );
    assert!(
        block.contains("uncovered_total: 1\n"),
        "conformance: PO: {block}"
    );
    let t = r.report.render();
    assert!(
        t.contains("uncovered:  1 graphs (1 distinct summaries)"),
        "conformance: PO: {t}"
    );
}
