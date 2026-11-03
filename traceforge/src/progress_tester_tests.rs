//! `ENG-PROGRESS`'s tests, the tester's (`criteria/ENG-PROGRESS.md` EP-1; the derivation
//! `log/dev/ENG-PROGRESS.derived.md`). Each case runs in a child process, as the limiter is
//! process-wide: this test binary on `tester_child` alone, the case in `TF_TESTER_CASE`.

use super::*;
use std::process::Command;
use std::sync::atomic::Ordering::SeqCst;

fn counts(bytes: &[u8]) -> Vec<u64> {
    String::from_utf8_lossy(bytes)
        .lines()
        .filter_map(|l| {
            let i = l.find("Executions attempted so far: ")?;
            l[i + 29..].split_whitespace().next()?.parse().ok()
        })
        .collect()
}

fn child(case: &str) -> std::process::Output {
    let out = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "progress_tester_tests::tester_child",
            "--nocapture",
        ])
        .args(["--test-threads=1"])
        .env("TF_TESTER_CASE", case)
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

/// `v` makes `bits` binary choices, then sends one value: 2^bits graphs, one summary.
fn choices(bits: usize) -> Arc<dyn Fn() + Send + Sync> {
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

/// With a clock that moves 1 000 ms at every reading, every eligible ending prints, so the
/// lines are exactly the eligible ones: the specification side's 8 endings (the precheck or
/// the specification phase) then the implementation's 4, by the default schedule. A sweep
/// that printed would add its own `1`, `2`, ….
#[test]
fn tp1_only_the_outer_reporters_print() {
    for engine in [
        "stateful",
        "sverify-p",
        "complete-first",
        "cfirst-p",
        "gated",
        "gated-never",
    ] {
        let out = child(&format!("outer:{engine}"));
        let want: Vec<u64> = (1..=8).chain(1..=4).collect();
        assert_eq!(counts(&out.stdout), want, "{engine}: stdout");
        assert!(counts(&out.stderr).is_empty(), "{engine}: stderr");
        let text = String::from_utf8_lossy(&out.stdout);
        assert!(text.contains("SWEEPS "), "{engine}: {text}");
    }
}

/// The real clock: runs of more than two seconds in all, with an eligible ending at every
/// execution (`progress_report = 1`, both streams), print at least two lines and at most
/// `floor(wall s) + 1` per stream. Each run's count starts again, so the counts needn't rise.
#[test]
fn tp2_the_real_clock_bound() {
    let out = child("real");
    let text = String::from_utf8_lossy(&out.stdout);
    let wall: f64 = text
        .lines()
        .find_map(|l| l.strip_prefix("WALL "))
        .expect("the wall")
        .trim()
        .parse()
        .unwrap();
    let bound = wall.floor() as usize + 1;
    let (o, e) = (counts(&out.stdout), counts(&out.stderr));
    assert!(wall >= 2.0, "the fixture ran {wall} s");
    assert!(
        o.len() >= 2 && o.len() <= bound,
        "stdout {} lines in {wall} s",
        o.len()
    );
    assert!(
        e.len() >= 2 && e.len() <= bound,
        "stderr {} lines in {wall} s",
        e.len()
    );
}

#[test]
fn tester_child() {
    let Ok(case) = std::env::var("TF_TESTER_CASE") else {
        return;
    };
    if let Some(engine) = case.strip_prefix("outer:") {
        use conformance::{ConfBuilder, Engine, GatePolicy};
        PROGRESS_CLOCK.store(0, SeqCst);
        PROGRESS_CLOCK_STEP.store(true, SeqCst);
        let (e, threads) = match engine {
            "stateful" => (Engine::Stateful, 1),
            "sverify-p" => (Engine::SverifyP, 2),
            "complete-first" => (Engine::CompleteFirst, 1),
            "cfirst-p" => (Engine::CFirstP, 2),
            _ => (Engine::Gated, 1),
        };
        let mut b = ConfBuilder::new()
            .config(Config::builder().build())
            .visible_threads(vec!["v".to_owned()])
            .engine(e)
            .threads(threads);
        if engine.starts_with("gated") {
            b = b.gate_policy(if engine == "gated" {
                GatePolicy::Always
            } else {
                GatePolicy::Never
            });
        }
        let cc = b.build().unwrap();
        let (imp, spec) = (choices(2), choices(3));
        let v = conformance::verify(cc, move || imp(), move || spec()).unwrap();
        let o = v.outcome();
        let sweeps = o
            .cfirst_counters
            .as_ref()
            .map(|c| c.sweeps)
            .or_else(|| o.counters.cfirst_p.as_ref().map(|p| p.base.sweeps))
            .or_else(|| {
                o.gated_counters
                    .as_ref()
                    .map(|g| g.gate_sweeps + g.completion_sweeps)
            })
            .unwrap_or(0);
        println!("SWEEPS {sweeps}");
        if !engine.starts_with("state") && engine != "sverify-p" {
            assert!(sweeps > 0, "{engine}: no sweep ran");
        }
    } else if case == "real" {
        let started = std::time::Instant::now();
        let mut bits = 10;
        while started.elapsed().as_secs_f64() < 2.5 {
            let p = choices(bits);
            let stats = verify(
                Config::builder().with_progress_report(1).build(),
                move || p(),
            );
            assert_eq!(stats.execs, 1 << bits);
            bits = (bits + 1).min(16);
        }
        println!("WALL {}", started.elapsed().as_secs_f64());
    }
}
