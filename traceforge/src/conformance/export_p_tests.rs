//! `PAR-EXPORT`'s tests (`criteria/PAR-EXPORT.md` PE-1; the derivation
//! `log/dev/PAR-EXPORT.derived.md`): `export --threads N` on the partitioned Must, lines
//! encoded per graph and sorted, against `export_with`. In-process where the result is the
//! observable; a child process (this test binary on `pe_child`) where the runner's stdout is.
//! Fixture counters are per test. At most two threads.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::conformance::config::{ConfBuilder, ConfConfig, Engine, IndexKind};
use crate::conformance::export_p::{export_partitioned_with, ExportPRun, ExportPSeams};
use crate::conformance::interchange::{export_with, ExportError, ExportSeams};
use crate::conformance::interchange_default_tests::{
    header, named, read_jsonl, scratch, split_block,
};
use crate::program::{run_cli_with_model, Entry, Program};
use crate::thread::{construct_thread_id, ThreadId};
use crate::{Config, ConsType};

#[derive(Clone, Debug, PartialEq)]
enum PMsg {
    V(i32),
    Call(usize, i32),
    Owner(ThreadId),
}

/// `k` clients call a server `q` times each, waiting for each reply: `(kq)! / (q!)^k`
/// endings. Returns the client of the server's first message: a deterministic condition,
/// on what the program read, that falls past the runner's warmup.
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
        other => panic!("conformance: PE: {other:?}"),
    };
    server.join().unwrap();
    for c in clients {
        c.join().unwrap();
    }
    first
}

fn serve_visible() -> Vec<&'static str> {
    vec!["server", "c0", "c1", "c2"]
}

/// `v` is spawned first (a visible thread precedes the program's communication, §8), runs
/// `serve`, and is told when to act; what it acts on is written first, fresh per execution.
/// Its word holds the same `Go` either way, so the action alone decides its line.
fn gated<F>(k: usize, q: usize, act: F)
where
    F: FnOnce(usize, Option<ThreadId>) + Send + 'static,
{
    gated_with(k, q, |_| None, act);
}

fn gated_with<B, F>(k: usize, q: usize, before: B, act: F)
where
    B: FnOnce(usize) -> Option<ThreadId>,
    F: FnOnce(usize, Option<ThreadId>) + Send + 'static,
{
    let first = Arc::new(AtomicUsize::new(0));
    let id = Arc::new(Mutex::new(None));
    let (go, wait) = crate::channel::Builder::<PMsg>::new().build();
    let (f2, i2) = (Arc::clone(&first), Arc::clone(&id));
    let v = named("v", move || {
        let _: PMsg = wait.recv_msg_block();
        let i = *i2.lock().unwrap();
        act(f2.load(Ordering::SeqCst), i);
    });
    let c = serve(k, q);
    first.store(c, Ordering::SeqCst);
    *id.lock().unwrap() = before(c);
    go.send_msg(PMsg::V(0));
    v.join().unwrap();
}

fn send_one<T: crate::Message + Clone + std::fmt::Debug + PartialEq + Send + 'static>(value: T) {
    let (tx, _rx) = crate::channel::Builder::<T>::new().build();
    tx.send_msg(value);
}

/// `v` sends one value.
fn v_sends<T: crate::Message + Clone + std::fmt::Debug + PartialEq + Send + 'static>(value: T) {
    let (tx, _rx) = crate::channel::Builder::<T>::new().build();
    let v = named("v", move || tx.send_msg(value));
    v.join().unwrap();
}

/// A thread named by the condition, and `v` sending its id. The number is the same.
fn owner_of(name: &'static str) {
    let t = named(name, || {});
    let id = t.thread().id();
    t.join().unwrap();
    v_sends(PMsg::Owner(id));
}

/// Two graphs, one thread number, two names.
fn names_fixture() {
    owner_of(if crate::nondet() { "a" } else { "b" });
}

/// The same, chosen past the warmup, and which OS thread ran each name.
fn names_tasks_fixture(seen: Arc<Mutex<HashSet<(String, std::thread::ThreadId)>>>) {
    gated_with(
        3,
        3,
        move |first| {
            let name = if first == 2 { "b" } else { "a" };
            seen.lock()
                .unwrap()
                .insert((name.to_owned(), std::thread::current().id()));
            let t = named(name, || {});
            let id = t.thread().id();
            t.join().unwrap();
            Some(id)
        },
        |_, id| send_one(PMsg::Owner(id.expect("conformance: PE: the id"))),
    );
}

/// `v` sends an id that names a thread in one branch only.
fn absent_fixture(present_when: bool) {
    let mut xs = Vec::new();
    if crate::nondet() == present_when {
        for i in 0..3 {
            xs.push(named(&format!("x{i}"), || {}));
        }
    }
    for x in xs {
        x.join().unwrap();
    }
    v_sends(PMsg::Owner(construct_thread_id(3)));
}

/// Equal rendering, two concrete types.
fn x1_fixture(u: bool) {
    if u {
        v_sends(1u32);
    } else {
        v_sends(1i32);
    }
}

#[derive(Clone, Debug, PartialEq)]
struct K<T> {
    owner: ThreadId,
    key: T,
}

/// The same with an unrelated thread id in both summaries.
fn x1_owner_fixture(u: bool) {
    let t = named("t", || {});
    let owner = t.thread().id();
    t.join().unwrap();
    if u {
        v_sends(K { owner, key: 1u32 });
    } else {
        v_sends(K { owner, key: 1i32 });
    }
}

/// Two numbers for `p`, one name.
fn renum_fixture() {
    let (p, q) = if crate::nondet() {
        let p = named("p", || {});
        let q = named("q", || {});
        (p, q)
    } else {
        let q = named("q", || {});
        let p = named("p", || {});
        (p, q)
    };
    let id = p.thread().id();
    p.join().unwrap();
    q.join().unwrap();
    v_sends(PMsg::Owner(id));
}

/// One concrete type, unequal values, one rendering.
#[derive(Clone, PartialEq)]
struct H(i32);
impl std::fmt::Debug for H {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "H")
    }
}

/// A value outside the `Debug` grammar when `bad`.
#[derive(Clone, PartialEq)]
struct W(bool);
impl std::fmt::Debug for W {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.0 { "@@" } else { "Fine" })
    }
}

fn cc(visible: &[&str], engine: Engine, seed: u64, flush: usize, model: ConsType) -> ConfConfig {
    let mut b = ConfBuilder::new()
        .config(
            Config::builder()
                .with_cons_type(model)
                .with_seed(seed)
                .build(),
        )
        .visible_threads(visible.iter().map(|s| (*s).to_owned()))
        .engine(engine)
        .index(IndexKind::Set)
        .flush_entries(flush);
    if matches!(engine, Engine::SverifyP) {
        b = b.threads(2);
    }
    b.build().expect("conformance: PE: a configuration")
}

const DEFAULT_FLUSH: usize = 4096;

fn par<P>(
    visible: &[&str],
    flush: usize,
    seed: u64,
    seams: ExportPSeams,
    path: &Path,
    p: P,
) -> Result<ExportPRun, ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    export_partitioned_with(
        &cc(visible, Engine::SverifyP, seed, flush, ConsType::Bag),
        p,
        &header("pe"),
        path,
        seams,
    )
}

fn seq<P>(visible: &[&str], path: &Path, p: P) -> Result<(), ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    export_with(
        &cc(visible, Engine::Stateful, 0, DEFAULT_FLUSH, ConsType::Bag),
        p,
        &header("pe"),
        path,
        ExportSeams::default(),
    )
    .map(|_| ())
}

fn lines_of(path: &Path) -> Vec<String> {
    read_jsonl(path).1
}

fn sorted(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v
}

fn mentions(lines: &[String], name: &str) -> usize {
    let q = format!("\"{name}\"");
    lines.iter().filter(|l| l.contains(&q)).count()
}

// =========================================================================
// The child: what the runner prints
// =========================================================================

fn entry(fixture: &str) -> Entry {
    match fixture {
        "serve" => Arc::new(|| {
            serve(3, 3);
        }),
        "assert-in-task" => Arc::new(|| gated(3, 3, |first, _| crate::assert(first != 2))),
        "encode-in-task" => Arc::new(|| gated(3, 3, |first, _| send_one(W(first == 2)))),
        other => panic!("conformance: PE: no fixture {other}"),
    }
}

fn visible_of_fixture(fixture: &str) -> Vec<String> {
    let v: Vec<&str> = match fixture {
        "serve" => serve_visible(),
        _ => vec!["v"],
    };
    v.into_iter().map(str::to_owned).collect()
}

/// The child's part: one run, through `run_cli_with_model`. No-op in the suite.
#[test]
fn pe_child() {
    let Ok(fixture) = std::env::var("PE_FIXTURE") else {
        return;
    };
    let args: Vec<String> = std::env::var("PE_ARGS")
        .expect("conformance: PE: the child's arguments")
        .split(' ')
        .map(str::to_owned)
        .collect();
    let imp = |_: &[String]| entry(&fixture);
    let spec = |_: &[String]| entry(&fixture);
    let visible = |_: &[String]| visible_of_fixture(&fixture);
    let p = Program {
        visible: &visible,
        spec: &spec,
        imp: &imp,
    };
    let (text, code) = run_cli_with_model(&p, ConsType::Bag, &args);
    std::fs::write(
        std::env::var("PE_OUT").expect("conformance: PE: the child's result file"),
        format!("{code}\n{text}"),
    )
    .expect("conformance: PE: the child's write");
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
}

fn child(fixture: &str, args: &str, out: &Path) -> Run {
    let c = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "conformance::export_p_tests::pe_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("PE_FIXTURE", fixture)
        .env("PE_ARGS", args)
        .env("PE_OUT", out)
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
    scratch(&format!("pe-{name}"))
}

// =========================================================================
// PE-1.1, 1.2, 1.7, 1.8, 1.10 on the inline server
// =========================================================================

/// Check 1: header, sorted lines, graph counts, against sequential; a task ran endings.
#[test]
fn pe1_equal_on_serve() {
    let d = dir("pe1");
    let (s, p) = (d.join("s.jsonl"), d.join("p.jsonl"));
    let a = child(
        "serve",
        &format!(
            "export impl --out {} --seed 0 --program pe --size k1",
            s.display()
        ),
        &d.join("a"),
    );
    assert_eq!(a.code, Some(0), "conformance: PE: sequential: {}", a.say());
    let b = child(
        "serve",
        &format!(
            "export impl --out {} --seed 0 --threads 2 --program pe --size k1",
            p.display()
        ),
        &d.join("b"),
    );
    assert_eq!(b.code, Some(0), "conformance: PE: parallel: {}", b.say());
    assert!(
        b.stdout.contains("Pool size: 2,"),
        "conformance: PE: the parallel path: {}",
        b.say()
    );
    assert!(
        b.task_execs().iter().any(|k| *k > 0),
        "conformance: PE: no task ran endings: {}",
        b.say()
    );
    let (hs, ls) = read_jsonl(&s);
    let (hp, lp) = read_jsonl(&p);
    assert_eq!(hs, hp, "conformance: PE: the header");
    assert_eq!(sorted(ls), sorted(lp), "conformance: PE: the sorted lines");
    let exported = |r: &Run| {
        r.text
            .lines()
            .next()
            .unwrap_or("")
            .split(" to ")
            .next()
            .unwrap_or("")
            .to_owned()
    };
    assert_eq!(
        exported(&a),
        exported(&b),
        "conformance: PE: lines and graphs"
    );
}

/// Check 2: sorted; two runs and two seeds give the same bytes.
#[test]
fn pe2_sorted_and_stable() {
    let d = dir("pe2");
    let v = serve_visible();
    let run = |n: &str, seed: u64| {
        let p = d.join(n);
        par(&v, DEFAULT_FLUSH, seed, ExportPSeams::default(), &p, || {
            serve(3, 3);
        })
        .unwrap_or_else(|e| panic!("conformance: PE: {e}"));
        std::fs::read(&p).unwrap()
    };
    let a = run("a", 0);
    assert_eq!(a, run("b", 0), "conformance: PE: two runs");
    assert_eq!(a, run("c", 1), "conformance: PE: another seed");
    let ls = lines_of(&d.join("a"));
    assert!(ls.len() > 1, "conformance: PE: lines to sort");
    assert_eq!(ls, sorted(ls.clone()), "conformance: PE: bytewise order");
}

/// Check 7: every untimed key of the block against sequential.
#[test]
fn pe7_block() {
    let d = dir("pe7");
    let run = |n: &str, extra: &str| {
        let r = child(
            "serve",
            &format!("export impl --out {} --seed 0{extra}", d.join(n).display()),
            &d.join(format!("{n}.res")),
        );
        assert_eq!(r.code, Some(0), "conformance: PE: {}", r.say());
        let block = split_block(&r.text).1.expect("conformance: PE: a block");
        block
            .lines()
            .filter_map(|l| l.split_once(": "))
            .filter(|(k, _)| !k.ends_with("_ms") && !k.contains("rss"))
            .map(|(k, v)| (k.to_owned(), v.to_owned()))
            .collect::<Vec<_>>()
    };
    let (s, p) = (run("s", ""), run("p", " --threads 2"));
    assert_eq!(s, p, "conformance: PE: the block's untimed keys");
    assert!(
        s.iter().any(|(k, _)| k == "summaries_distinct"),
        "conformance: PE: the block's names: {s:?}"
    );
}

/// Check 8: `--threads 1` is the sequential export; since `SORTED-JOIN`
/// (2026-11-02) both exporters write the lines in byte order.
#[test]
fn pe8_threads_one_is_sequential() {
    let d = dir("pe8");
    let run = |n: &str, extra: &str| {
        let r = child(
            "serve",
            &format!("export impl --out {} --seed 0{extra}", d.join(n).display()),
            &d.join(format!("{n}.res")),
        );
        assert_eq!(r.code, Some(0), "conformance: PE: {}", r.say());
        assert!(
            !r.stdout.contains("RAYON"),
            "conformance: PE: the runner on the sequential path: {}",
            r.say()
        );
        std::fs::read(d.join(n)).unwrap()
    };
    let none = run("a", " --program pe --size k1");
    assert_eq!(
        none,
        run("b", " --threads 1 --program pe --size k1"),
        "conformance: PE: --threads 1"
    );
    let ls = lines_of(&d.join("a"));
    assert_eq!(
        ls,
        sorted(ls.clone()),
        "conformance: PE: the sequential export is in byte order (SORTED-JOIN)"
    );
}

/// Check 10: the storage record, at two flush sizes.
#[test]
fn pe10_storage() {
    let d = dir("pe10");
    let v = serve_visible();
    for flush in [DEFAULT_FLUSH, 5] {
        let p = d.join(format!("f{flush}"));
        let r = par(&v, flush, 0, ExportPSeams::default(), &p, || {
            serve(3, 3);
        })
        .unwrap_or_else(|e| panic!("conformance: PE: {e}"));
        assert!(
            r.max_worker_lines <= flush,
            "conformance: PE: {} lines in a worker at flush {flush}",
            r.max_worker_lines
        );
        let ls = lines_of(&p);
        assert_eq!(r.stats.lines, ls.len(), "conformance: PE: lines");
        assert_eq!(
            r.stats.orders_held,
            ls.len(),
            "conformance: PE: orders_held"
        );
        assert_eq!(
            r.merged_bytes,
            ls.iter().map(String::len).sum::<usize>(),
            "conformance: PE: the merged strings' bytes"
        );
    }
}

// =========================================================================
// PE-1.3: values holding thread ids
// =========================================================================

/// Both lines, in one worker's map before a flush; sequential's `Conflict` pinned.
#[test]
fn pe3_names_one_worker() {
    let d = dir("pe3a");
    let e = seq(&["v"], &d.join("s"), names_fixture).expect_err("conformance: PE: sequential");
    assert!(
        format!("{e}").contains("conflict")
            || format!("{e}").contains("Conflict")
            || matches!(e, ExportError::Thread { .. }),
        "conformance: PE: sequential's refusal: {e}"
    );
    let p = d.join("p");
    let r = par(
        &["v"],
        DEFAULT_FLUSH,
        0,
        ExportPSeams::default(),
        &p,
        names_fixture,
    )
    .unwrap_or_else(|e| panic!("conformance: PE: {e}"));
    assert_eq!(
        r.max_worker_lines, 2,
        "conformance: PE: both in one worker's map"
    );
    let ls = lines_of(&p);
    assert_eq!(ls.len(), 2, "conformance: PE: two lines: {ls:?}");
    assert_eq!(
        (mentions(&ls, "a"), mentions(&ls, "b")),
        (1, 1),
        "conformance: PE: {ls:?}"
    );
}

/// Both lines, across a flush.
#[test]
fn pe3_names_across_a_flush() {
    let d = dir("pe3b");
    let p = d.join("p");
    let r = par(&["v"], 1, 0, ExportPSeams::default(), &p, names_fixture)
        .unwrap_or_else(|e| panic!("conformance: PE: {e}"));
    assert_eq!(
        r.max_worker_lines, 1,
        "conformance: PE: a flush at every line"
    );
    let ls = lines_of(&p);
    assert_eq!(
        (mentions(&ls, "a"), mentions(&ls, "b"), ls.len()),
        (1, 1, 2),
        "conformance: PE: {ls:?}"
    );
}

/// Both lines, across workers: the fixture records which OS thread ran each name.
#[test]
fn pe3_names_across_workers() {
    let d = dir("pe3c");
    let p = d.join("p");
    let seen = Arc::new(Mutex::new(HashSet::new()));
    let s2 = Arc::clone(&seen);
    par(
        &["v"],
        DEFAULT_FLUSH,
        0,
        ExportPSeams::default(),
        &p,
        move || names_tasks_fixture(Arc::clone(&s2)),
    )
    .unwrap_or_else(|e| panic!("conformance: PE: {e}"));
    let ls = lines_of(&p);
    assert_eq!(
        (mentions(&ls, "a"), mentions(&ls, "b"), ls.len()),
        (1, 1, 2),
        "conformance: PE: {ls:?}"
    );
    let seen = seen.lock().unwrap();
    let on = |n: &str| {
        seen.iter()
            .filter(|(m, _)| m == n)
            .map(|(_, t)| *t)
            .collect::<HashSet<_>>()
    };
    let (a, b) = (on("a"), on("b"));
    assert!(
        a.iter().any(|x| b.iter().any(|y| x != y)),
        "conformance: PE: the two names on one worker only: {a:?} {b:?}"
    );
    let c = |ts: &HashSet<std::thread::ThreadId>| ts.len();
    assert!(
        c(&a) + c(&b) >= 3,
        "conformance: PE: the placement: {a:?} {b:?}"
    );
}

/// The precondition: an id named only in another graph. Sequential writes; this path
/// refuses, whichever branch runs first.
#[test]
fn pe3_absent_thread() {
    let d = dir("pe3d");
    for present_when in [true, false] {
        let s = d.join(format!("s{present_when}"));
        seq(&["v"], &s, move || absent_fixture(present_when))
            .unwrap_or_else(|e| panic!("conformance: PE: sequential: {e}"));
        let p = d.join(format!("p{present_when}"));
        let e = par(
            &["v"],
            DEFAULT_FLUSH,
            0,
            ExportPSeams::default(),
            &p,
            move || absent_fixture(present_when),
        )
        .err()
        .expect("conformance: PE: the precondition's refusal");
        assert!(
            matches!(&e, ExportError::Thread { reason, .. } if reason.contains("t3 is not a thread of this graph")),
            "conformance: PE: {present_when}: {e}"
        );
        assert!(!p.exists(), "conformance: PE: no file");
    }
}

// =========================================================================
// PE-1.4: X1
// =========================================================================

fn collision(e: Result<ExportPRun, ExportError>, what: &str) {
    assert!(
        matches!(&e, Err(ExportError::Collision { .. })),
        "conformance: PE: {what}: {:?}",
        e.as_ref().map(|r| r.stats.lines).map_err(|x| x.to_string())
    );
}

#[test]
fn pe4_x1_one_worker_and_across_a_flush() {
    let d = dir("pe4a");
    let f = || x1_fixture(crate::nondet());
    collision(
        par(
            &["v"],
            DEFAULT_FLUSH,
            0,
            ExportPSeams::default(),
            &d.join("a"),
            f,
        ),
        "one worker",
    );
    collision(
        par(&["v"], 1, 0, ExportPSeams::default(), &d.join("b"), f),
        "across a flush",
    );
    assert!(
        !d.join("a").exists() && !d.join("b").exists(),
        "conformance: PE: no file"
    );
    let e = seq(&["v"], &d.join("s"), f).expect_err("conformance: PE: sequential refuses");
    assert!(
        matches!(e, ExportError::Collision { .. }),
        "conformance: PE: sequential: {e}"
    );
}

#[test]
fn pe4_x1_across_workers() {
    let d = dir("pe4b");
    let f = || {
        gated(3, 3, |first, _| {
            if first == 2 {
                send_one(1u32);
            } else {
                send_one(1i32);
            }
        })
    };
    collision(
        par(
            &["v"],
            DEFAULT_FLUSH,
            0,
            ExportPSeams::default(),
            &d.join("a"),
            f,
        ),
        "across workers",
    );
}

#[test]
fn pe4_x1_owner() {
    let d = dir("pe4c");
    let f = || x1_owner_fixture(crate::nondet());
    collision(
        par(
            &["v"],
            DEFAULT_FLUSH,
            0,
            ExportPSeams::default(),
            &d.join("a"),
            f,
        ),
        "with a thread id",
    );
    collision(
        par(&["v"], 1, 0, ExportPSeams::default(), &d.join("b"), f),
        "with a thread id, across a flush",
    );
}

#[test]
fn pe4_renumbered() {
    let d = dir("pe4d");
    let p = d.join("p");
    par(
        &["v"],
        DEFAULT_FLUSH,
        0,
        ExportPSeams::default(),
        &p,
        renum_fixture,
    )
    .unwrap_or_else(|e| panic!("conformance: PE: renumbered: {e}"));
    let ls = lines_of(&p);
    assert_eq!(ls.len(), 1, "conformance: PE: one line: {ls:?}");
    // Sequential's refusal, the stated difference (a): one number, two names.
    let e = seq(&["v"], &d.join("s"), renum_fixture).expect_err("conformance: PE: sequential");
    assert!(
        matches!(e, ExportError::Thread { .. }),
        "conformance: PE: sequential: {e}"
    );
}

#[test]
fn pe4_residual() {
    let d = dir("pe4e");
    let f = || v_sends(H(i32::from(crate::nondet())));
    let e = seq(&["v"], &d.join("s"), f).expect_err("conformance: PE: sequential refuses");
    assert!(
        matches!(e, ExportError::Collision { .. }),
        "conformance: PE: sequential: {e}"
    );
    let p = d.join("p");
    par(&["v"], DEFAULT_FLUSH, 0, ExportPSeams::default(), &p, f)
        .unwrap_or_else(|e| panic!("conformance: PE: the residual writes: {e}"));
    assert_eq!(lines_of(&p).len(), 1, "conformance: PE: one line");
}

// =========================================================================
// PE-1.5: refusals and the stop
// =========================================================================

/// `fixture` refuses on both paths, by the CLI: exit 2, no file on a fresh path, an earlier
/// file kept. The parallel run shows a task that ran. Returns both messages.
fn refused_in_a_task(fixture: &str, name: &str) -> (String, String) {
    let d = dir(name);
    let (s, p) = (d.join("s"), d.join("p"));
    std::fs::write(&s, "earlier\n").unwrap();
    std::fs::write(&p, "earlier\n").unwrap();
    let a = child(
        fixture,
        &format!("export impl --out {} --seed 0", s.display()),
        &d.join("a"),
    );
    let b = child(
        fixture,
        &format!("export impl --out {} --seed 0 --threads 2", p.display()),
        &d.join("b"),
    );
    assert_eq!(a.code, Some(2), "conformance: PE: sequential: {}", a.say());
    assert_eq!(b.code, Some(2), "conformance: PE: parallel: {}", b.say());
    assert!(
        b.task_execs().iter().any(|k| *k > 0),
        "conformance: PE: no task ran: {}",
        b.say()
    );
    assert_eq!(
        std::fs::read_to_string(&s).unwrap(),
        "earlier\n",
        "conformance: PE: sequential's earlier file"
    );
    assert_eq!(
        std::fs::read_to_string(&p).unwrap(),
        "earlier\n",
        "conformance: PE: the earlier file"
    );
    let fresh = d.join("fresh");
    let c = child(
        fixture,
        &format!("export impl --out {} --seed 0 --threads 2", fresh.display()),
        &d.join("c"),
    );
    assert_eq!(c.code, Some(2), "conformance: PE: fresh: {}", c.say());
    assert!(!fresh.exists(), "conformance: PE: no file");
    let one = |r: &Run| split_block(&r.text).0;
    (one(&a), one(&b))
}

#[test]
fn pe5_spec_errors_in_a_task() {
    let (a, b) = refused_in_a_task("assert-in-task", "pe5a");
    assert_eq!(a, b, "conformance: PE: the message");
}

#[test]
fn pe5_encode_in_a_task() {
    let (a, b) = refused_in_a_task("encode-in-task", "pe5b");
    assert_eq!(a, b, "conformance: PE: the message");
}

#[test]
fn pe5_not_set() {
    let d = dir("pe5c");
    let mk = |engine| {
        let mut b = ConfBuilder::new()
            .config(
                Config::builder()
                    .with_cons_type(ConsType::Bag)
                    .with_seed(0)
                    .build(),
            )
            .visible_threads(["v".to_owned()])
            .engine(engine)
            .index(IndexKind::Current);
        if matches!(engine, Engine::SverifyP) {
            b = b.threads(2);
        }
        b.build()
    };
    if let Ok(c) = mk(Engine::SverifyP).or_else(|_| mk(Engine::Stateful)) {
        let p = d.join("p");
        let r = export_partitioned_with(&c, || {}, &header("pe"), &p, ExportPSeams::default());
        assert!(
            matches!(r, Err(ExportError::NotSet)),
            "conformance: PE: NotSet"
        );
        assert!(!p.exists(), "conformance: PE: no file");
    } else {
        panic!("conformance: PE: no configuration with another index");
    }
}

#[test]
fn pe5_model() {
    let d = dir("pe5d");
    let p = d.join("p");
    // The builder refuses this model, so the configuration is changed after it.
    let mk = |engine| {
        let mut c = cc(&["v"], engine, 0, DEFAULT_FLUSH, ConsType::Bag);
        c.config.cons_type = ConsType::MO;
        c
    };
    let r = export_partitioned_with(
        &mk(Engine::SverifyP),
        || {},
        &header("pe"),
        &p,
        ExportPSeams::default(),
    );
    assert!(
        matches!(r, Err(ExportError::Model(_))),
        "conformance: PE: Model"
    );
    let r = export_with(
        &mk(Engine::Stateful),
        || {},
        &header("pe"),
        &p,
        ExportSeams::default(),
    );
    assert!(
        matches!(r, Err(ExportError::Model(_))),
        "conformance: PE: sequential's Model"
    );
    assert!(!p.exists(), "conformance: PE: no file");
}

/// The cancel curtails the run: executions, by a counter, far below the control's.
#[test]
fn pe5_cancel_is_effective() {
    let d = dir("pe5e");
    let runs = |bad: bool, name: &str| {
        let n = Arc::new(AtomicUsize::new(0));
        let m = Arc::clone(&n);
        let r = par(
            &["v"],
            DEFAULT_FLUSH,
            0,
            ExportPSeams::default(),
            &d.join(name),
            move || {
                m.fetch_add(1, Ordering::SeqCst);
                gated(3, 4, move |first, _| send_one(W(bad && first == 2)));
            },
        );
        (
            n.load(Ordering::SeqCst),
            r.map(|_| ()).map_err(|e| e.to_string()),
        )
    };
    let (control, ok) = runs(false, "c");
    assert!(ok.is_ok(), "conformance: PE: the control: {ok:?}");
    assert_eq!(control, 34650, "conformance: PE: the control's endings");
    let (curtailed, refused) = runs(true, "e");
    assert!(
        refused.as_ref().is_err_and(|e| e.contains("@@")),
        "conformance: PE: the refusal: {refused:?}"
    );
    {
        use std::io::Write as _;
        let _ = writeln!(
            std::io::stderr(),
            "PE: {curtailed} executions against the control's {control}"
        );
    }
    assert!(
        curtailed * 2 < control,
        "conformance: PE: {curtailed} executions against the control's {control}"
    );
}

/// The seam: a cancel with no error is `NotExhausted`; with an error, the error.
#[test]
fn pe5_seam() {
    let d = dir("pe5f");
    let seams = |n| {
        let mut s = ExportPSeams::default();
        s.cancel_at = Some(n);
        s
    };
    let p = d.join("a");
    let r = par(&serve_visible(), DEFAULT_FLUSH, 0, seams(10), &p, || {
        serve(3, 3);
    });
    assert!(
        matches!(r, Err(ExportError::NotExhausted(_))),
        "conformance: PE: NotExhausted"
    );
    assert!(!p.exists(), "conformance: PE: no file");
    let q = d.join("b");
    let r = par(&["v"], DEFAULT_FLUSH, 0, seams(2), &q, || v_sends(W(true)));
    assert!(
        matches!(r, Err(ExportError::Unparsed { .. })),
        "conformance: PE: the error first"
    );
    assert!(!q.exists(), "conformance: PE: no file");
}
