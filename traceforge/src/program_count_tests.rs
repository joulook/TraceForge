//! `PAR-COUNT`'s tests (`criteria/PAR-COUNT.md` PC-1; the derivation
//! `log/dev/PAR-COUNT.derived.md`): `count --threads N` on the partitioned Must.
//! A child module of `program`, so it reads `count_config`. The runner prints to
//! the real stdout and a task's panic re-raises, so each run is a child process:
//! this test binary on `pc_child` alone, with the run given through its environment.
//! The child writes its exit code and text to a file: a child that ran nothing, or
//! whose run re-raised a panic, leaves none. At most two threads.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use super::{count_config, parse_opts, run_cli_with_model, Entry, Opts, Program};
use crate::ConsType;

#[derive(Clone, Debug, PartialEq)]
enum PMsg {
    V(i32),
    Call(usize, i32),
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> crate::thread::JoinHandle<()> {
    crate::thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

/// `r` receives `n` values that `w` sends on one channel: 1 ending under `fifo`, `n!`
/// under `bag`. These receives have forward choices only, so the runner's root does it all.
fn perm(n: i32) {
    let (tx, rx) = crate::channel::Builder::<PMsg>::new().build();
    let r = named("r", move || {
        for _ in 0..n {
            let _: PMsg = rx.recv_msg_block();
        }
    });
    let w = named("w", move || {
        for i in 0..n {
            tx.send_msg(PMsg::V(i));
        }
    });
    r.join().unwrap();
    w.join().unwrap();
}

/// `k` clients each make `q` calls to one server and wait for each reply, so the
/// server's receive order is a merge of the clients' sequences: `(kq)! / (q!)^k`
/// endings under either model. A later client's send revisits a receive the server has
/// already made, so these are backward revisits, which give the runner its work items.
/// With `fail`, the server fails an assertion at every ending.
fn serve(k: usize, q: usize, fail: bool) {
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
        if fail {
            crate::assert(false);
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

static RUNS: AtomicUsize = AtomicUsize::new(0);
static FIRST: OnceLock<std::thread::ThreadId> = OnceLock::new();
static SEEN: AtomicBool = AtomicBool::new(false);
const OFF_ROOT: &str = "rootless: an assertion on a worker that is not the root's";

/// `serve(3, 3)` whose assertion can fail only outside the root (derivation §2): the
/// root's warmup and loop run on one OS thread, the first execution's. A later
/// execution on that thread waits until another worker has reached the assertion.
fn rootless() {
    let n = RUNS.fetch_add(1, Ordering::SeqCst) + 1;
    let me = std::thread::current().id();
    let first = *FIRST.get_or_init(|| me);
    if me != first {
        if !SEEN.swap(true, Ordering::SeqCst) {
            println!("{OFF_ROOT}");
        }
    } else if n > 100 {
        let start = Instant::now();
        while !SEEN.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(20) {
            std::thread::sleep(Duration::from_millis(1));
        }
        // No second worker came: stop waiting for good, so a mutant fails, not hangs.
        SEEN.store(true, Ordering::SeqCst);
    }
    // The server's last action, as a keep-going assertion must be: the thread runs on.
    serve(3, 3, me != first);
}

/// One thread with more events than the default thread bound of 1 000.
fn long() {
    let (tx, rx) = crate::channel::Builder::<PMsg>::new().build();
    let w = named("w", move || {
        for i in 0..1100 {
            tx.send_msg(PMsg::V(i));
        }
    });
    w.join().unwrap();
    drop(rx);
}

fn entry(fixture: &str) -> Entry {
    match fixture {
        "perm4" => Arc::new(|| perm(4)),
        "perm6" => Arc::new(|| perm(6)),
        "serve" => Arc::new(|| serve(3, 3, false)),
        "servefail" => Arc::new(|| serve(3, 3, true)),
        "rootless" => Arc::new(rootless),
        "long" => Arc::new(long),
        other => panic!("conformance: PC: no fixture {other}"),
    }
}

/// The child's part: one run, through `run_cli_with_model`. No-op in the suite.
#[test]
fn pc_child() {
    let Ok(fixture) = std::env::var("PC_FIXTURE") else {
        return;
    };
    let declared = match std::env::var("PC_DECLARED").unwrap().as_str() {
        "bag" => ConsType::Bag,
        _ => ConsType::FIFO,
    };
    let args: Vec<String> = std::env::var("PC_ARGS")
        .unwrap()
        .split(' ')
        .map(str::to_owned)
        .collect();
    let imp = |_: &[String]| entry(&fixture);
    let spec = |_: &[String]| entry(&fixture);
    let visible = |_: &[String]| vec!["server".to_owned()];
    let p = Program {
        visible: &visible,
        spec: &spec,
        imp: &imp,
    };
    let (text, code) = run_cli_with_model(&p, declared, &args);
    std::fs::write(std::env::var("PC_OUT").unwrap(), format!("{code}\n{text}")).unwrap();
}

struct Run {
    /// The child process's own exit status.
    success: bool,
    /// `run_cli`'s exit code and text; `None` when the run wrote no result.
    result: Option<(u8, String)>,
    stdout: String,
    stderr: String,
}

impl Run {
    fn counts(&self) -> (u64, u64) {
        let t = &self
            .result
            .as_ref()
            .unwrap_or_else(|| panic!("conformance: PC: no result: {}", self.tail()))
            .1;
        let l = t
            .lines()
            .find(|l| l.starts_with("execs="))
            .unwrap_or_else(|| panic!("conformance: PC: no count line: {t}"));
        let n: Vec<u64> = l
            .split(|c: char| !c.is_ascii_digit())
            .filter(|s| !s.is_empty())
            .map(|s| s.parse().unwrap())
            .collect();
        (n[0], n[1])
    }
    /// The executions of the tasks that ran some: the runner's `  rt<N>: <k> execs`.
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
    fn tail(&self) -> String {
        let out = |s: &str| {
            let c: Vec<char> = s.chars().collect();
            c[c.len().saturating_sub(1500)..].iter().collect::<String>()
        };
        format!(
            "success {} result {:?}\n--- stdout tail\n{}\n--- stderr tail\n{}",
            self.success,
            self.result.as_ref().map(|r| r.0),
            out(&self.stdout),
            out(&self.stderr)
        )
    }
}

fn run(fixture: &str, declared: &str, args: &str) -> Run {
    let dir = std::env::temp_dir().join(format!("pc-tests-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    static N: AtomicUsize = AtomicUsize::new(0);
    let out = dir.join(format!("r{}", N.fetch_add(1, Ordering::SeqCst)));
    let c = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "program::count_tests::pc_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("PC_FIXTURE", fixture)
        .env("PC_DECLARED", declared)
        .env("PC_ARGS", args)
        .env("PC_OUT", &out)
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap();
    let result = std::fs::read_to_string(&out).ok().map(|s| {
        let (code, text) = s.split_once('\n').unwrap();
        (code.parse().unwrap(), text.to_owned())
    });
    Run {
        success: c.status.success(),
        result,
        stdout: String::from_utf8_lossy(&c.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&c.stderr).into_owned(),
    }
}

const BANNER: &str = "=== RAYON PARALLEL EXPLORATION ===";

fn parallel_ok(r: &Run, what: &str) {
    assert!(
        r.success && r.result.as_ref().is_some_and(|x| x.0 == 0),
        "conformance: PC: {what}: exit: {}",
        r.tail()
    );
    assert!(
        r.stdout.contains(BANNER) && r.stdout.contains("Pool size: 2,"),
        "conformance: PC: {what}: the parallel path, pool 2: {}",
        r.tail()
    );
}

/// Check 1: the counts, by hand, on 3 seeds, under `--threads 2` and no flag.
#[test]
fn pc1_counts() {
    for (fixture, declared, want) in [
        ("perm4", "bag", (24, 0)),
        ("perm6", "bag", (720, 0)),
        ("perm6", "fifo", (1, 0)),
        ("serve", "bag", (1680, 0)),
        ("serve", "fifo", (1680, 0)),
    ] {
        for seed in [0, 1, 2] {
            let what = format!("{fixture} {declared} seed {seed}");
            let s = run(fixture, declared, &format!("count impl --seed {seed}"));
            assert_eq!(s.counts(), want, "conformance: PC: {what}: sequential");
            let p = run(
                fixture,
                declared,
                &format!("count impl --threads 2 --seed {seed}"),
            );
            parallel_ok(&p, &what);
            assert_eq!(
                p.counts(),
                want,
                "conformance: PC: {what}: --threads 2: {}",
                p.tail()
            );
        }
    }
}

/// Check 1: every ending fails, well over 100 endings: a task's line with k > 0 is a
/// task that ran failing endings, the run exits 0, and the counts are sequential's.
#[test]
fn pc1_assertion_in_a_task() {
    // A keep-going assertion ends its execution as a complete one, in `execs`.
    let s = run("servefail", "bag", "count impl --seed 0");
    assert_eq!(
        s.counts(),
        (1680, 0),
        "conformance: PC: sequential: {}",
        s.tail()
    );
    let p = run("servefail", "bag", "count impl --threads 2 --seed 0");
    parallel_ok(&p, "servefail");
    assert_eq!(
        p.counts(),
        s.counts(),
        "conformance: PC: --threads 2: {}",
        p.tail()
    );
    assert!(
        p.task_execs().iter().any(|k| *k > 0),
        "conformance: PC: no task ran a failing ending: {}",
        p.tail()
    );
}

/// Check 1's failing direction, unmutated: the assertion fails only outside the root;
/// keep-going carries the task past it. Its counts aren't compared with sequential.
#[test]
fn pc1_rootless() {
    let p = run("rootless", "bag", "count impl --threads 2 --seed 0");
    assert!(
        !p.stderr.contains("PANIC in rayon"),
        "conformance: PC: rootless: a panic: {}",
        p.tail()
    );
    parallel_ok(&p, "rootless");
    assert!(
        p.stdout.contains(OFF_ROOT),
        "conformance: PC: rootless: no worker reached the assertion: {}",
        p.tail()
    );
    assert!(
        p.task_execs().iter().any(|k| *k > 0),
        "conformance: PC: rootless: no task line: {}",
        p.tail()
    );
    p.counts();
}

/// Check 2: no flag, and `--threads 1`: no banner, no task line, the same counts.
#[test]
fn pc2_sequential_has_no_banner() {
    for a in ["count impl --seed 0", "count impl --threads 1 --seed 0"] {
        let s = run("serve", "bag", a);
        assert_eq!(s.counts(), (1680, 0), "conformance: PC: {a}");
        assert!(
            !s.stdout.contains("RAYON")
                && !s.stdout.contains("RevisitQueueRayon")
                && s.task_execs().is_empty(),
            "conformance: PC: {a}: the runner's lines: {}",
            s.tail()
        );
    }
}

/// Check 3: the runner's banner names the pool size.
#[test]
fn pc3_banner_names_the_pool() {
    let p = run("serve", "bag", "count impl --threads 2 --seed 0");
    parallel_ok(&p, "serve");
}

fn cfg(args: &[&str], default: ConsType) -> crate::Config {
    let a: Vec<String> = args.iter().map(|s| (*s).to_owned()).collect();
    let o: Opts = parse_opts(&a, default).unwrap_or_else(|e| panic!("conformance: PC: {e}"));
    count_config(&o)
}

/// Check 5: `count_config`'s result, at N = none, 1, 2.
#[test]
fn pc5_config_read() {
    use ConsType::{Bag, FIFO};
    for (threads, parallel, num) in [
        (&[][..], false, None),
        (&["--threads", "1"][..], false, None),
        (&["--threads", "2"][..], true, Some(2)),
    ] {
        let what = format!("{threads:?}");
        let with = |extra: &[&'static str]| {
            let mut v: Vec<&str> = threads.to_vec();
            v.extend_from_slice(extra);
            v
        };
        // The default model, each way.
        for d in [Bag, FIFO] {
            let c = cfg(&with(&[]), d);
            assert!(
                c.cons_type == d,
                "conformance: PC: {what}: the default model"
            );
            assert!(
                c.keep_going_after_error,
                "conformance: PC: {what}: keep-going"
            );
            assert_eq!(
                c.partitioned_parallelization, parallel,
                "conformance: PC: {what}: parallel"
            );
            assert_eq!(
                c.partitioned_num_threads, num,
                "conformance: PC: {what}: pool"
            );
        }
        // `--model` over the default, each way.
        assert!(
            cfg(&with(&["--model", "bag"]), FIFO).cons_type == Bag,
            "conformance: PC: {what}: --model bag"
        );
        assert!(
            cfg(&with(&["--model", "fifo"]), Bag).cons_type == FIFO,
            "conformance: PC: {what}: --model fifo"
        );
        // `--seed` and `--threshold`, both.
        let c = cfg(&with(&["--seed", "4242", "--threshold", "65536"]), Bag);
        assert_eq!(c.seed, 4242, "conformance: PC: {what}: --seed");
        assert_eq!(
            c.thread_threshold, 65536,
            "conformance: PC: {what}: --threshold"
        );
        // Not set anywhere else.
        assert!(!c.parallel, "conformance: PC: {what}: never with_parallel");
        assert_eq!(c.warmup, 100, "conformance: PC: {what}: warmup");
        assert_eq!(
            c.iterations_until_split, 100,
            "conformance: PC: {what}: split"
        );
        assert_eq!(c.state_batch_size, 1, "conformance: PC: {what}: batch");
    }
}

/// Check 5: `--threads 0` is refused, exit 2.
#[test]
fn pc5_threads_zero() {
    let r = run("perm4", "bag", "count impl --threads 0");
    let (code, text) = r
        .result
        .clone()
        .unwrap_or_else(|| panic!("conformance: PC: {}", r.tail()));
    assert_eq!(code, 2, "conformance: PC: --threads 0: {text}");
    assert!(
        text.contains("--threads needs at least 1"),
        "conformance: PC: the message: {text}"
    );
}

/// Check 5: the model changes a run, under `--threads 2`.
#[test]
fn pc5_model_changes_a_run() {
    for (declared, args, want) in [
        ("bag", "count impl --threads 2 --seed 0", (24, 0)),
        ("fifo", "count impl --threads 2 --seed 0", (1, 0)),
        (
            "bag",
            "count impl --threads 2 --seed 0 --model fifo",
            (1, 0),
        ),
        (
            "fifo",
            "count impl --threads 2 --seed 0 --model bag",
            (24, 0),
        ),
    ] {
        let p = run("perm4", declared, args);
        parallel_ok(&p, args);
        assert_eq!(
            p.counts(),
            want,
            "conformance: PC: declared {declared}, {args}"
        );
    }
}

/// Check 5: the threshold changes a run, under `--threads 2`.
#[test]
fn pc5_threshold_changes_a_run() {
    let w = "Large thread size";
    let cut = run("long", "fifo", "count impl --threads 2 --seed 0");
    parallel_ok(&cut, "long, the default bound");
    assert!(
        cut.stderr.contains(w),
        "conformance: PC: no warning under the default bound: {}",
        cut.tail()
    );
    let full = run(
        "long",
        "fifo",
        "count impl --threads 2 --seed 0 --threshold 65536",
    );
    parallel_ok(&full, "long, --threshold");
    assert!(
        !full.stderr.contains(w),
        "conformance: PC: the warning under --threshold: {}",
        full.tail()
    );
}
