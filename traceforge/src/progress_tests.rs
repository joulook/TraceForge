use super::*;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
use std::sync::Barrier;
use std::time::Duration;

static SWEEP_ENDINGS: AtomicU64 = AtomicU64::new(0);
static SWEEP_ELIGIBLE: AtomicU64 = AtomicU64::new(0);

pub(crate) fn observe_ending(must: &Must, total: u64) {
    use conformance::ctx::ConfMode;
    if must
        .conf_ctx()
        .is_some_and(|c| matches!(c.mode(), ConfMode::CFirstSweep | ConfMode::GatedSweep))
    {
        SWEEP_ENDINGS.fetch_add(1, SeqCst);
        let n = must.config.progress_report;
        if n != usize::MAX
            && (if n == 0 {
                Must::should_report(total)
            } else {
                total.is_multiple_of(n as u64)
            })
        {
            SWEEP_ELIGIBLE.fetch_add(1, SeqCst);
        }
    }
}

fn clock(ms: u64) {
    PROGRESS_CLOCK.store(ms, SeqCst);
}

fn lines(bytes: &[u8]) -> Vec<String> {
    String::from_utf8_lossy(bytes)
        .lines()
        .filter_map(|s| {
            s.find("Executions attempted so far:")
                .map(|i| s[i..].to_owned())
        })
        .collect()
}

fn child(case: &str) -> std::process::Output {
    let out = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "progress_tests::progress_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("TF_PROGRESS_CASE", case)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{case}: {}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    out
}

fn reporter(interval: usize) -> Must {
    Must::new(
        Config::builder().with_progress_report(interval).build(),
        false,
    )
}

fn ending(must: &Must, n: u64) {
    must.report_progress(n, 0, Duration::ZERO);
}

#[test]
fn spacing_count_schedule() {
    let out = child("count");
    let got = lines(&out.stdout);
    let counts: Vec<_> = got
        .iter()
        .map(|s| s.split_whitespace().nth(4).unwrap())
        .collect();
    assert_eq!(counts, ["1", "3", "4", "5", "6"]);
    assert!(lines(&out.stderr).is_empty());
}

#[test]
fn spacing_positive_interval_both_streams() {
    let out = child("interval");
    let got = lines(&out.stdout);
    assert_eq!(got.len(), 5);
    assert_eq!(got, lines(&out.stderr));
}

#[test]
fn spacing_sample_schedule() {
    let out = child("sample");
    assert_eq!(
        lines(&out.stdout),
        [1, 3, 4, 5].map(|i| format!("Executions attempted so far: {i}"))
    );
    assert!(lines(&out.stderr).is_empty());
}

#[test]
fn disabled_including_zero() {
    let out = child("disabled");
    assert!(lines(&out.stdout).is_empty());
    assert!(lines(&out.stderr).is_empty());
}

#[test]
fn spacing_across_runs_phases_and_reuse() {
    let out = child("lifecycle");
    assert_eq!(lines(&out.stdout).len(), 3);
    assert_eq!(lines(&out.stderr).len(), 3);
}

#[test]
fn simultaneous_workers_one_print_each_stream() {
    let out = child("race");
    assert_eq!(lines(&out.stdout).len(), 1);
    assert_eq!(lines(&out.stderr).len(), 1);
}

#[test]
fn streams_have_independent_limits() {
    let out = child("streams");
    assert_eq!(lines(&out.stdout).len(), 2);
    assert_eq!(lines(&out.stderr).len(), 2);
}

#[test]
fn sweeps_silent_before_throttling() {
    for engine in ["sequential", "inline", "gate", "completion"] {
        for quiet in [false, true] {
            for interval in [0, 1] {
                let out = child(&format!("sweep:{engine}:{quiet}:{interval}"));
                if engine == "inline" {
                    let text = String::from_utf8_lossy(&out.stdout);
                    assert!(
                        text.lines().any(|line| {
                            let fields: Vec<_> = line.split_whitespace().collect();
                            fields.len() >= 3
                                && fields[0].starts_with("rt")
                                && fields[0].ends_with(':')
                                && fields[1].parse::<u64>().is_ok_and(|n| n > 0)
                                && fields[2].starts_with("execs")
                        }),
                        "a genuine task must print nonzero executions: {text}"
                    );
                }
            }
        }
    }
}

#[test]
fn ordered_non_progress_output_survives() {
    let out = child("sweep:inline:false:0");
    let text = String::from_utf8_lossy(&out.stdout);
    let markers = [
        "RevisitQueueRayon: root seeded ",
        "RevisitQueueRayon per-worker stats:",
        "=== Rayon Exploration Results ===",
        "Total time:",
        "Number of workers:",
        "Total executions:",
        "Max graph events:",
    ];
    let mut remaining = text.as_ref();
    for marker in markers {
        let (_, after) = remaining
            .split_once(marker)
            .unwrap_or_else(|| panic!("missing or reordered {marker}: {text}"));
        remaining = after;
    }
}

fn choice_program(bits: usize) -> Arc<dyn Fn() + Send + Sync> {
    Arc::new(move || {
        thread::Builder::new()
            .name("v".to_owned())
            .spawn(move || {
                for _ in 0..bits {
                    let _: bool = nondet();
                }
                send_msg(thread::current().id(), 1i32);
            })
            .unwrap()
            .join()
            .unwrap();
    })
}

fn split_program() -> Arc<dyn Fn() + Send + Sync> {
    Arc::new(|| {
        let (go, wait) = channel::Builder::<usize>::new().build();
        let visible = thread::Builder::new()
            .name("v".to_owned())
            .spawn(move || {
                let _ = wait.recv_msg_block();
                send_msg(thread::current().id(), 1i32);
            })
            .unwrap();
        let (tx, rx) = channel::Builder::<usize>::new().build();
        let mut replies = Vec::new();
        let mut waits = Vec::new();
        for _ in 0..3 {
            let (reply, wait) = channel::Builder::<usize>::new().build();
            replies.push(reply);
            waits.push(wait);
        }
        let server = thread::spawn(move || {
            for _ in 0..6 {
                let client = rx.recv_msg_block();
                replies[client].send_msg(0);
            }
        });
        let clients: Vec<_> = waits
            .into_iter()
            .enumerate()
            .map(|(i, wait)| {
                let tx = tx.clone();
                thread::spawn(move || {
                    for _ in 0..2 {
                        tx.send_msg(i);
                        let _ = wait.recv_msg_block();
                    }
                })
            })
            .collect();
        server.join().unwrap();
        for client in clients {
            client.join().unwrap();
        }
        go.send_msg(0);
        visible.join().unwrap();
    })
}

fn sweep_case(case: &str) {
    use conformance::config::Capacity;
    use conformance::{cfirst, cfirst_p, gated, ConfBuilder, Engine, GatePolicy};
    let fields: Vec<_> = case.split(':').collect();
    let engine = fields[1];
    let quiet = fields[2].parse::<bool>().unwrap();
    let interval = fields[3].parse::<usize>().unwrap();
    let mut config = Config::builder().with_progress_report(interval).build();
    config.warmup = 1;
    config.iterations_until_split = 1;
    config.state_batch_size = 1;
    let mut cc = ConfBuilder::new()
        .config(config)
        .visible_threads(vec!["v".to_owned()])
        .engine(match engine {
            "sequential" => Engine::CompleteFirst,
            "inline" => Engine::CFirstP,
            _ => Engine::Gated,
        })
        .threads(2)
        .quiet_sweeps(quiet)
        .witness_cache(Capacity::Zero)
        .gate_policy(if engine == "completion" {
            GatePolicy::Never
        } else {
            GatePolicy::Always
        })
        .build()
        .unwrap();
    cc.skip_spec_errfree_check = true;
    let (imp, spec) = if engine == "inline" {
        (split_program(), split_program())
    } else {
        (choice_program(4), choice_program(0))
    };
    match engine {
        "sequential" => {
            let out = cfirst::run_with(&cc, &imp, &spec, false);
            assert!(out.counters.sweeps > 0);
        }
        "inline" => {
            let out = cfirst_p::run_with(&cc, &imp, &spec);
            assert!(out.counters.sweeps_in_tasks > 0, "a worker must sweep");
            assert!(out.counters.tasks_nonempty > 0);
        }
        _ => {
            let out = gated::run_with(&cc, &imp, &spec, false);
            if engine == "gate" {
                assert!(out.counters.gate_sweeps > 0);
            } else {
                assert!(out.counters.completion_sweeps > 0);
                assert_eq!(out.counters.gate_sweeps, 0);
            }
        }
    }
    assert!(
        SWEEP_ENDINGS.load(SeqCst) > 0,
        "a sweep ending must be observed"
    );
    assert_eq!(
        SWEEP_ELIGIBLE.load(SeqCst),
        0,
        "sweep eligible before throttling"
    );
}

#[test]
fn telemetry_survives_throttling() {
    child("telemetry");
}

#[test]
fn progress_child() {
    let Ok(case) = std::env::var("TF_PROGRESS_CASE") else {
        return;
    };
    clock(0);
    match case.as_str() {
        "count" | "interval" => {
            let interval = if case == "count" { 0 } else { 1 };
            let must = reporter(interval);
            for (ms, n) in [(0, 1), (999, 2), (1000, 3), (2001, 4), (3002, 5), (9000, 6)] {
                clock(ms);
                ending(&must, n);
            }
        }
        "sample" => {
            // Each inner exploration has one ending, below its interval of two.
            let cfg = Config::builder().with_progress_report(2).build();
            let sample = AtomicU64::new(0);
            test(
                cfg,
                move || {
                    let i = sample.fetch_add(1, SeqCst) as usize;
                    clock([0, 0, 999, 1000, 2001, 9000][i]);
                    assume!(false);
                },
                6,
            );
        }
        "disabled" => {
            let must = reporter(usize::MAX);
            ending(&must, 0);
            clock(2000);
            ending(&must, 1);
            test(
                Config::builder().with_progress_report(usize::MAX).build(),
                || {},
                3,
            );
        }
        "lifecycle" => {
            let mut must = reporter(1);
            ending(&must, 1);
            clock(100);
            ending(&reporter(1), 1);
            must.reset_for_sample(1);
            ending(&must, 1);
            must.reset_for_reuse();
            ending(&must, 1);
            clock(1000);
            ending(&must, 1);
            // Two phases per run; both runs share the process limiter.
            for ms in [1100, 2100] {
                clock(ms);
                verify(Config::builder().with_progress_report(1).build(), || {});
                verify(Config::builder().with_progress_report(1).build(), || {});
                let cc = conformance::ConfBuilder::new()
                    .config(Config::builder().with_progress_report(1).build())
                    .engine(conformance::Engine::Stateful)
                    .visible_threads(["v"])
                    .build()
                    .unwrap();
                let program = choice_program(0);
                let spec = program.clone();
                conformance::verify(cc, move || program(), move || spec()).unwrap();
            }
        }
        "telemetry" => {
            let program = choice_program(4);
            let stats = verify(
                Config::builder().with_progress_report(1).build(),
                move || program(),
            );
            assert_eq!((stats.execs, stats.block), (16, 0));
        }
        "race" => {
            let barrier = Arc::new(Barrier::new(2));
            let workers: Vec<_> = (0..2)
                .map(|_| {
                    let barrier = barrier.clone();
                    std::thread::spawn(move || {
                        let must = reporter(1);
                        barrier.wait();
                        ending(&must, 1);
                    })
                })
                .collect();
            for worker in workers {
                worker.join().unwrap();
            }
        }
        "streams" => {
            ending(&reporter(0), 1);
            clock(500);
            ending(&reporter(1), 2);
            clock(1000);
            ending(&reporter(1), 3);
            clock(1500);
            ending(&reporter(1), 4);
        }
        _ if case.starts_with("sweep:") => {
            PROGRESS_CLOCK_STEP.store(true, SeqCst);
            sweep_case(&case);
        }
        _ => panic!("unknown progress case: {case}"),
    }
}
