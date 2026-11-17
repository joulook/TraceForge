//! `ENG-THRESHOLD`'s tests, the tester's (`criteria/ENG-THRESHOLD.md` ET-0.1 to ET-0.3,
//! ET-1.2, ET-1.3; the derivation `log/dev/ENG-THRESHOLD.derived.md` §1 to §3).
//!
//! 1. **The boundary is the base's rule.** A label is added to a thread of size `s` (its
//!    length before the label); the run crosses when `s > threshold`. A thread whose final
//!    length is `L` therefore crosses exactly when `threshold ≤ L − 2`.
//! 2. **A count above 16 bits through the files and both joins.** `b` receives the last of
//!    `a`'s `n` sends (its coordinate is `n`), or the first (its coordinate is 1); the two
//!    programs have one signature. A specification graph covers an implementation graph of
//!    its signature when its counts are `≤` the implementation's (less order allows more):
//!    `early` (1) covers `late` (`n`); `late` (`n`) does not cover `early` (1).
//!    `n = 65 536` is 0 in 16 bits, so a narrowing anywhere on the export, read or join
//!    path makes `late` cover `early`: the violation turns into silence.
//! 3. **A genuine miss before the crossing gives no verdict.** One branch is uncovered and
//!    short, the other crosses: every engine ends with the threshold, `online` with partial.
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::compact::CompactSummary;
use super::config::{ConfBuilder, Engine, IndexKind};
use super::ctx::{ConfMode, SinkVerdict};
use super::interchange::parse_line;
use super::report::{ConfError, SearchEnd};
use super::stateful::{enumerate, EnumRun};
use crate::program::{run_cli, Program};
use crate::{Config, ConsType};

type Prog = Arc<dyn Fn() + Send + Sync>;

fn cli(imp: &Prog, spec: &Prog, visible: &[String], args: &[&str]) -> (String, u8) {
    run_cli(
        &Program {
            visible: &|_| visible.to_vec(),
            imp: &|_| Arc::clone(imp),
            spec: &|_| Arc::clone(spec),
        },
        &args.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
    )
}

/// A directory of mine under `TMPDIR`, removed by the caller.
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("ett-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("conformance: ENG-THRESHOLD: a scratch directory");
    d
}

/// `main` makes one channel and sends `k` messages on it.
fn sends(k: usize) -> Prog {
    Arc::new(move || {
        let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
        for i in 0..k {
            tx.send_msg(i as i32);
        }
    })
}

/// `main`'s final length, from the graph at completion of a run that cannot cross.
fn main_length(p: &Prog) -> usize {
    let sizes = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let got = std::rc::Rc::clone(&sizes);
    let run = enumerate(
        EnumRun {
            config: Config::builder()
                .with_cons_type(ConsType::FIFO)
                .with_thread_threshold(1 << 20)
                .build(),
            visible: vec![],
            mode: ConfMode::Enumerate,
            sink: Box::new(move |g, _| {
                got.borrow_mut()
                    .push(g.thread_size(crate::thread::main_thread_id()));
                SinkVerdict::Continue
            }),
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        p,
    );
    assert_eq!(
        run.end,
        SearchEnd::StateSpaceExhausted,
        "conformance: ENG-THRESHOLD: end"
    );
    let sizes = sizes.borrow();
    assert_eq!(sizes.len(), 1, "conformance: ENG-THRESHOLD: one execution");
    sizes[0]
}

#[test]
fn ett1_the_boundary_is_the_base_rule() {
    for k in [10, 24] {
        let p = sends(k);
        let l = main_length(&p);
        assert!(
            l > k,
            "conformance: ENG-THRESHOLD: main's length {l} for {k} sends"
        );
        for t in (l - 4)..=(l + 1) {
            let q = Arc::clone(&p);
            let stats = crate::verify(
                Config::builder()
                    .with_cons_type(ConsType::FIFO)
                    .with_thread_threshold(t as u32)
                    .build(),
                move || q(),
            );
            let crosses = t + 2 <= l;
            match &stats.threshold {
                Some(r) => {
                    assert!(
                        crosses,
                        "conformance: ENG-THRESHOLD: k={k} L={l} t={t} crossed"
                    );
                    assert_eq!(
                        (r.thread.as_str(), r.limit, stats.execs, stats.block),
                        ("main", t as u32, 0, 0),
                        "conformance: ENG-THRESHOLD: k={k} L={l} t={t}"
                    );
                }
                None => {
                    assert!(
                        !crosses,
                        "conformance: ENG-THRESHOLD: k={k} L={l} t={t} did not"
                    );
                    assert_eq!(
                        (stats.execs, stats.block),
                        (1, 0),
                        "conformance: ENG-THRESHOLD: k={k} L={l} t={t} completes"
                    );
                }
            }
        }
    }
}

/// `b` receives on `done`. `last`: `a` sends `n − 1` on its own channel, then `done`
/// (`b`'s coordinate `n`); otherwise `done` first (`b`'s coordinate 1).
fn ab(n: usize, last: bool) -> Prog {
    Arc::new(move || {
        let (done, wait) = crate::channel::Builder::<i32>::new().build();
        crate::thread::Builder::new()
            .name("b".into())
            .spawn(move || {
                let _: i32 = wait.recv_msg_block();
            })
            .unwrap();
        crate::thread::Builder::new()
            .name("a".into())
            .spawn(move || {
                let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
                if !last {
                    done.send_msg(0);
                }
                for _ in 1..n {
                    tx.send_msg(0);
                }
                if last {
                    done.send_msg(0);
                }
            })
            .unwrap();
    })
}

fn summary_of(path: &Path, names: &[String]) -> CompactSummary {
    let text = std::fs::read_to_string(path).expect("conformance: ENG-THRESHOLD: the file");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines.len(),
        2,
        "conformance: ENG-THRESHOLD: a header and one line"
    );
    parse_line(lines[1], names)
        .expect("conformance: ENG-THRESHOLD: the line reads")
        .1
}

#[test]
fn ett2_a_count_above_16_bits_through_the_files_and_both_joins() {
    let names = vec!["a".to_string(), "b".to_string()];
    for n in [65_535usize, 65_536] {
        let dir = scratch(&format!("wide-{n}"));
        let f = |s: &str| dir.join(s).to_str().unwrap().to_string();
        let (late, early) = (ab(n, true), ab(n, false));
        let opts = ["--model", "fifo", "--seed", "0", "--threshold", "200000"];
        for (side, file, imp, spec) in [
            ("spec", f("spec-late.jsonl"), &early, &late),
            ("impl", f("impl-early.jsonl"), &early, &late),
            ("spec", f("spec-early.jsonl"), &late, &early),
            ("impl", f("impl-late.jsonl"), &late, &early),
        ] {
            let mut args = vec!["export", side, "--out", file.as_str()];
            args.extend(opts);
            let (text, code) = cli(imp, spec, &names, &args);
            assert_eq!(
                code, 0,
                "conformance: ENG-THRESHOLD: export {side} {n}: {text}"
            );
        }
        let late = summary_of(Path::new(&f("impl-late.jsonl")), &names);
        let early = summary_of(Path::new(&f("impl-early.jsonl")), &names);
        assert_eq!(
            late.sig, early.sig,
            "conformance: ENG-THRESHOLD: one signature"
        );
        assert_eq!(
            (late.ord.len(), late.ord.at(n), early.ord.at(n)),
            (n + 1, n as u32, 1),
            "conformance: ENG-THRESHOLD: b's coordinate read back at {n}"
        );
        for merge in [false, true] {
            let join = |s: &str, i: &str| {
                let (s, i) = (PathBuf::from(f(s)), PathBuf::from(f(i)));
                let r = if merge {
                    super::conf_join_merge(&s, &i)
                } else {
                    super::conf_join(&s, &i)
                };
                r.expect("conformance: ENG-THRESHOLD: the join reads")
                    .exit_code()
            };
            assert_eq!(
                (
                    join("spec-late.jsonl", "impl-early.jsonl"),
                    join("spec-early.jsonl", "impl-late.jsonl")
                ),
                (1, 0),
                "conformance: ENG-THRESHOLD: n={n} merge={merge}: not covered, then covered"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}

/// `nondet() == cross` spawns an invisible thread `long` that sends 40 messages (crosses 16)
/// while `main` stays silent, a prefix of the specification's word, so even a search that
/// stops at the first uncovered visible event reaches the crossing; the other branch has
/// `main` send a value the specification never sends (short, uncovered). `cross` swaps
/// the branches, so either exploration order is tried.
fn miss_or_cross(cross: bool) -> Prog {
    Arc::new(move || {
        if crate::nondet() == cross {
            crate::thread::Builder::new()
                .name("long".into())
                .spawn(|| {
                    let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
                    for i in 0..40 {
                        tx.send_msg(i);
                    }
                })
                .unwrap();
        } else {
            let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
            tx.send_msg(-1);
        }
    })
}

/// `main` sends -1 only: the miss alone, the control.
fn miss() -> Prog {
    Arc::new(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
        tx.send_msg(-1);
    })
}

/// The specification: one execution, one message 0 (never crosses 16).
fn one() -> Prog {
    Arc::new(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
        tx.send_msg(0);
    })
}

#[test]
fn ett3_a_miss_before_the_crossing_gives_no_verdict() {
    let mut bad = Vec::new();
    for engine in [
        Engine::Stateful,
        Engine::CompleteFirst,
        Engine::Gated,
        Engine::Enumerator,
        Engine::SverifyP,
        Engine::CFirstP,
    ] {
        let index = if matches!(engine, Engine::Enumerator | Engine::Gated) {
            IndexKind::Current
        } else {
            IndexKind::Set
        };
        let cc = || {
            let mut b = ConfBuilder::new()
                .config(
                    Config::builder()
                        .with_seed(0)
                        .with_thread_threshold(16)
                        .build(),
                )
                .visible_threads(["main"])
                .engine(engine)
                .index(index);
            if matches!(engine, Engine::SverifyP | Engine::CFirstP) {
                b = b.threads(2);
            }
            b.build()
                .expect("conformance: ENG-THRESHOLD: the configuration")
        };
        let (imp, spec) = (miss(), one());
        match super::verify(cc(), move || imp(), move || spec()) {
            Ok(super::ConfVerdict::Reported(_)) => {}
            other => bad.push(format!("{engine:?}: the miss alone gave {other:?}")),
        }
        for cross in [false, true] {
            let (imp, spec) = (miss_or_cross(cross), one());
            match super::verify(cc(), move || imp(), move || spec()) {
                Err(ConfError::Threshold(r)) if (r.thread.as_str(), r.limit) == ("long", 16) => {}
                other => bad.push(format!("{engine:?} (cross = {cross}) gave {other:?}")),
            }
        }
    }
    assert!(bad.is_empty(), "conformance: ENG-THRESHOLD: {bad:#?}");
    let dir = scratch("online");
    let good = dir.join("spec.jsonl").to_str().unwrap().to_string();
    let in_visible = |p: Prog| -> Prog {
        Arc::new(move || {
            let p = Arc::clone(&p);
            crate::thread::Builder::new()
                .name("visible".into())
                .spawn(move || p())
                .unwrap()
                .join()
                .unwrap();
        })
    };
    let (imp, spec) = (in_visible(miss_or_cross(false)), in_visible(one()));
    let visible = vec!["visible".to_string()];
    let (text, code) = cli(&imp, &spec, &visible, &["export", "spec", "--out", &good]);
    assert_eq!(code, 0, "conformance: ENG-THRESHOLD: export: {text}");
    for threads in ["1", "2"] {
        let args = [
            "online",
            "--spec",
            &good,
            "--threads",
            threads,
            "--threshold",
            "16",
        ];
        let (text, code) = cli(&imp, &spec, &visible, &args);
        assert_eq!(
            code, 0,
            "conformance: ENG-THRESHOLD: online {threads}: {text}"
        );
        for want in [
            "verdict:    partial",
            "stop_reason: threshold",
            "thread `long` passed limit 16",
        ] {
            assert!(
                text.contains(want),
                "conformance: ENG-THRESHOLD: online {threads}: {text}"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// As [`miss_or_cross`], but the 40 messages are `main`'s, visible: the crossing branch's
/// word leaves the specification's at its second send.
fn miss_or_cross_visible(cross: bool) -> Prog {
    Arc::new(move || {
        let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
        if crate::nondet() == cross {
            for i in 0..40 {
                tx.send_msg(i);
            }
        } else {
            tx.send_msg(-1);
        }
    })
}

fn conf_of(engine: Engine, limit: u32) -> super::config::ConfConfig {
    let index = if matches!(engine, Engine::Enumerator | Engine::Gated) {
        IndexKind::Current
    } else {
        IndexKind::Set
    };
    let mut b = ConfBuilder::new()
        .config(
            Config::builder()
                .with_seed(0)
                .with_thread_threshold(limit)
                .build(),
        )
        .visible_threads(["main"])
        .engine(engine)
        .index(index);
    if matches!(engine, Engine::SverifyP | Engine::CFirstP) {
        b = b.threads(2);
    }
    b.build()
        .expect("conformance: ENG-THRESHOLD: the configuration")
}

/// The enumerator leaves an execution at its first uncovered visible event, so here the
/// crossing branch ends before `main` has 17 labels: its outcome at 16 is its outcome at
/// 1 000 (the threshold played no part). Every other engine runs the branch on and ends with
/// the threshold.
#[test]
fn ett4_a_search_that_leaves_at_the_uncovered_prefix_does_not_cross() {
    let mut bad = Vec::new();
    for engine in [
        Engine::Stateful,
        Engine::CompleteFirst,
        Engine::Gated,
        Engine::Enumerator,
        Engine::SverifyP,
        Engine::CFirstP,
    ] {
        for cross in [false, true] {
            let run = |limit: u32| {
                let (imp, spec) = (miss_or_cross_visible(cross), one());
                super::verify(conf_of(engine, limit), move || imp(), move || spec())
            };
            match (engine, run(16)) {
                (Engine::Enumerator, Ok(super::ConfVerdict::Reported(o))) => match run(1000) {
                    Ok(super::ConfVerdict::Reported(p))
                        if (o.report_count, &o.end, o.reports.len())
                            == (p.report_count, &p.end, p.reports.len())
                            && o.end == SearchEnd::StateSpaceExhausted => {}
                    other => bad.push(format!("Enumerator ({cross}): at 1000 {other:?}")),
                },
                (Engine::Enumerator, other) => {
                    bad.push(format!("Enumerator ({cross}): at 16 {other:?}"))
                }
                (_, Err(ConfError::Threshold(r)))
                    if (r.thread.as_str(), r.limit) == ("main", 16) => {}
                (_, other) => bad.push(format!("{engine:?} ({cross}): {other:?}")),
            }
        }
    }
    assert!(bad.is_empty(), "conformance: ENG-THRESHOLD: {bad:#?}");
}

/// The specification: `main` sends 0 (visible) and spawns an invisible `long` that sends 40
/// messages, crossing 16 where no visible event follows. With the precheck skipped, the
/// crossing happens inside the specification's exploration itself (for the enumerator, a
/// probe's free run); every engine must still end with the threshold, naming `long`.
fn one_and_long() -> Prog {
    Arc::new(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
        tx.send_msg(0);
        crate::thread::Builder::new()
            .name("long".into())
            .spawn(|| {
                let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
                for i in 0..40 {
                    tx.send_msg(i);
                }
            })
            .unwrap();
    })
}

#[test]
fn ett5_a_crossing_in_the_specification_off_the_visible_threads() {
    let mut bad = Vec::new();
    for engine in [
        Engine::Stateful,
        Engine::CompleteFirst,
        Engine::Gated,
        Engine::Enumerator,
        Engine::SverifyP,
        Engine::CFirstP,
    ] {
        for skip in [false, true] {
            let index = if matches!(engine, Engine::Enumerator | Engine::Gated) {
                IndexKind::Current
            } else {
                IndexKind::Set
            };
            let mut b = ConfBuilder::new()
                .config(
                    Config::builder()
                        .with_seed(0)
                        .with_thread_threshold(16)
                        .build(),
                )
                .visible_threads(["main"])
                .engine(engine)
                .index(index)
                .skip_spec_errfree_check(skip);
            if matches!(engine, Engine::SverifyP | Engine::CFirstP) {
                b = b.threads(2);
            }
            let cc = b
                .build()
                .expect("conformance: ENG-THRESHOLD: the configuration");
            let (imp, spec) = (one(), one_and_long());
            match super::verify(cc, move || imp(), move || spec()) {
                Err(ConfError::Threshold(r)) if (r.thread.as_str(), r.limit) == ("long", 16) => {}
                other => bad.push(format!("{engine:?} (skip = {skip}): {other:?}")),
            }
        }
    }
    assert!(bad.is_empty(), "conformance: ENG-THRESHOLD: {bad:#?}");
}

/// The specification creates 40 unnamed channels and nothing else: `BEGIN` and 40 `UNIQUE`
/// labels on `main`, forced bookkeeping that a probe installs without offering it. At
/// threshold 16 the 17th `UNIQUE` (existing length 17 > 16) crosses inside the first probe,
/// which then has no offer to install, so only the search's check of the probe's threshold
/// carries the reason (ENG-THRESHOLD-CODE round 01, M2). The implementation is empty. The
/// enumerator, the precheck skipped and not: the threshold naming `main` and 16; at 128 it
/// conforms.
#[test]
fn et_enumerator_probe_threshold_without_offers() {
    let channels: Prog = Arc::new(|| {
        for _ in 0..40 {
            let _ = crate::channel::Builder::<i32>::new().build();
        }
    });
    let empty: Prog = Arc::new(|| {});
    let run = |limit: u32, skip: bool| {
        let cc = ConfBuilder::new()
            .config(
                Config::builder()
                    .with_seed(0)
                    .with_thread_threshold(limit)
                    .build(),
            )
            .visible_threads(["main"])
            .engine(Engine::Enumerator)
            .index(IndexKind::Current)
            .skip_spec_errfree_check(skip)
            .build()
            .expect("conformance: ENG-THRESHOLD: the configuration");
        let (imp, spec) = (Arc::clone(&empty), Arc::clone(&channels));
        super::verify(cc, move || imp(), move || spec())
    };
    let mut bad = Vec::new();
    for skip in [true, false] {
        match run(16, skip) {
            Err(ConfError::Threshold(r)) if (r.thread.as_str(), r.limit) == ("main", 16) => {}
            other => bad.push(format!("16 (skip = {skip}): {other:?}")),
        }
    }
    match run(128, true) {
        Ok(super::ConfVerdict::Conforms(_)) => {}
        other => bad.push(format!("128: {other:?}")),
    }
    assert!(bad.is_empty(), "conformance: ENG-THRESHOLD: {bad:#?}");
}

/// The enumerator: the specification asserts false, which the first gate finds
/// (`SpecNotAssertionSafe` recorded, a stop requested); the implementation's execution goes on
/// and `main` crosses 16 by creating 40 channels. `record_end` lets the threshold supersede the
/// earlier end while the recorded specification error stays, so the result depends on which
/// one `conformance::run` checks first: the threshold, naming `main` and 16. At 128 nothing
/// crosses and the specification error stands.
#[test]
fn ett8_an_enumerator_specification_error_then_a_crossing() {
    let imp: Prog = Arc::new(|| {
        let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
        tx.send_msg(0);
        for _ in 0..40 {
            let _ = crate::channel::Builder::<i32>::new().build();
        }
    });
    let spec: Prog = Arc::new(|| crate::assert(false));
    let run = |limit: u32| {
        let cc = ConfBuilder::new()
            .config(
                Config::builder()
                    .with_seed(0)
                    .with_thread_threshold(limit)
                    .build(),
            )
            .visible_threads(["main"])
            .engine(Engine::Enumerator)
            .index(IndexKind::Current)
            .skip_spec_errfree_check(true)
            .build()
            .expect("conformance: ENG-THRESHOLD: the configuration");
        let (i, s) = (Arc::clone(&imp), Arc::clone(&spec));
        super::verify(cc, move || i(), move || s())
    };
    let mut bad = Vec::new();
    match run(16) {
        Err(ConfError::Threshold(r)) if (r.thread.as_str(), r.limit) == ("main", 16) => {}
        other => bad.push(format!("16: {other:?}")),
    }
    match run(128) {
        Err(ConfError::SpecNotAssertionSafe { .. }) => {}
        other => bad.push(format!("128: {other:?}")),
    }
    assert!(bad.is_empty(), "conformance: ENG-THRESHOLD: {bad:#?}");
}

/// A value whose rendering the interchange encoder refuses (`@@`), or accepts (`Fine`).
#[derive(Clone, PartialEq)]
struct Wt(bool);

impl std::fmt::Debug for Wt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.0 { "@@" } else { "Fine" })
    }
}

/// Three clients call one server three times each, on reply channels: a state space large
/// enough under the bag model to split after the default warmup of 100 (as `online_p_tests`'
/// `serve(3, 3)`).
fn calls() {
    let (req, inbox) = crate::channel::Builder::<(usize, i32)>::new().build();
    let mut replies = Vec::new();
    let mut waits = Vec::new();
    for _ in 0..3 {
        let (tx, rx) = crate::channel::Builder::<i32>::new().build();
        replies.push(tx);
        waits.push(rx);
    }
    let _server = crate::thread::spawn(move || {
        for _ in 0..9 {
            let (c, x): (usize, i32) = inbox.recv_msg_block();
            replies[c].send_msg(x);
        }
    });
    for (c, rx) in waits.into_iter().enumerate() {
        let req = req.clone();
        let _client = crate::thread::spawn(move || {
            for i in 0..3 {
                req.send_msg((c, i));
                let _: i32 = rx.recv_msg_block();
            }
        });
    }
}

/// `online --threads 2`: a recorded sink failure and a crossing in one run, over [`calls`].
/// A non-root worker's first execution sends `Wt(true)`, so its completion fails to encode.
/// The `before_fail` seam marks that, and holds the worker until the root is about to cross
/// and 500 ms more (the crossing sends take microseconds). The root's 101st execution, the
/// first past the warmup, waits for the mark, then crosses 32 on an invisible `sender` (40
/// sends; the server's 19 labels fit). Both are recorded; the failure decides the end
/// (`End::Failed`, `online_p.rs`'s precedence).
#[test]
fn ett9_online_p_a_sink_failure_and_a_crossing() {
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Mutex, OnceLock};
    use std::time::{Duration, Instant};
    let wait = |flag: &AtomicBool| {
        let start = Instant::now();
        while !flag.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(10) {
            std::thread::sleep(Duration::from_millis(1));
        }
    };
    let dir = scratch("onlinep-fail");
    let good = dir.join("spec.jsonl");
    let v = vec!["v".to_string()];
    let spec: Prog = Arc::new(|| {
        crate::thread::Builder::new()
            .name("v".into())
            .spawn(|| {
                let (tx, _rx) = crate::channel::Builder::<Wt>::new().build();
                tx.send_msg(Wt(false));
            })
            .unwrap();
    });
    let args = [
        "export",
        "spec",
        "--out",
        good.to_str().unwrap(),
        "--model",
        "bag",
    ];
    let (text, code) = cli(&spec, &spec, &v, &args);
    assert_eq!(code, 0, "conformance: ENG-THRESHOLD: export: {text}");
    let root = Arc::new(OnceLock::new());
    let entered = Arc::new(Mutex::new(HashMap::new()));
    let counts = Arc::clone(&entered);
    let failing = Arc::new(AtomicBool::new(false));
    let crossed = Arc::new(AtomicBool::new(false));
    let (root2, failing2, crossed2) = (
        Arc::clone(&root),
        Arc::clone(&failing),
        Arc::clone(&crossed),
    );
    let imp: Arc<dyn Fn() + Send + Sync> = Arc::new(move || {
        let me = std::thread::current().id();
        let is_root = me == *root2.get_or_init(|| me);
        let n = {
            let mut e = entered.lock().unwrap();
            let n = e.entry(me).or_insert(0usize);
            *n += 1;
            *n
        };
        let bad = !is_root && n == 1;
        crate::thread::Builder::new()
            .name("v".into())
            .spawn(move || {
                let (tx, _rx) = crate::channel::Builder::<Wt>::new().build();
                tx.send_msg(Wt(bad));
            })
            .unwrap();
        calls();
        if is_root && n == 101 {
            wait(&failing2);
            let c = Arc::clone(&crossed2);
            crate::thread::Builder::new()
                .name("sender".into())
                .spawn(move || {
                    let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
                    // The 32nd send (existing length 33) crosses 32; the run halts the
                    // execution there, so the mark goes up two sends before it.
                    for i in 0..40 {
                        if i == 29 {
                            c.store(true, Ordering::SeqCst);
                        }
                        tx.send_msg(i);
                    }
                })
                .unwrap();
        }
    });
    let (failing3, crossed3) = (Arc::clone(&failing), Arc::clone(&crossed));
    let seams = super::online_p::OnlinePSeams {
        before_fail: Some(Arc::new(move || {
            failing3.store(true, Ordering::SeqCst);
            wait(&crossed3);
            std::thread::sleep(Duration::from_millis(500));
        })),
        ..Default::default()
    };
    let config = Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .with_thread_threshold(32)
        .build();
    let run = super::online_p::online_partitioned_with(&config, 2, &v, imp, &good, None, seams)
        .expect("conformance: ENG-THRESHOLD: the online run");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failing.load(Ordering::SeqCst) && crossed.load(Ordering::SeqCst),
        "conformance: ENG-THRESHOLD: not both: failing {}, crossed {}, executions per thread {:?}",
        failing.load(Ordering::SeqCst),
        crossed.load(Ordering::SeqCst),
        counts.lock().unwrap().values().collect::<Vec<_>>()
    );
    assert!(
        matches!(run.report.end, super::online::End::Failed)
            && run
                .report
                .failure
                .as_deref()
                .is_some_and(|f| f.contains("@@")),
        "conformance: ENG-THRESHOLD: {:?} {:?}",
        run.report.end,
        run.report.failure
    );
}

/// `measure::row_stop`: a row whose run panicked is an error even when its cells carry a
/// threshold end (`impl_end`, `spec_end` or the enumerator's `end`); the panic is checked
/// first. Synthetic rows through `of_row` with `GridEnd::Panicked`, for the conformance
/// engines whose block comes from the row (code review round 02, m1).
#[test]
fn ett10_a_panicked_row_with_a_threshold_end_is_an_error() {
    use super::record::{GridConfig, GridEnd, GridEngine};
    let reason = "Threshold(ThresholdStop { thread: \"main\", limit: 16 })".to_string();
    let mut bad = Vec::new();
    for (engine, threads) in [
        (GridEngine::Enumerator, 1),
        (GridEngine::Stateful, 1),
        (GridEngine::CompleteFirst, 1),
        (GridEngine::Gated, 1),
        (GridEngine::SverifyP, 2),
        (GridEngine::CFirstP, 2),
    ] {
        for key in ["impl_end", "spec_end", "end"] {
            let row: Vec<(&'static str, String)> = vec![(key, reason.clone())];
            let end = GridEnd::Panicked {
                fixture: "ett10".into(),
                config: GridConfig::new(engine),
                payload: "conformance: a planted panic".into(),
            };
            let text = super::measure::of_row(&row, &end, engine, threads).render();
            if !text.lines().any(|l| l == "stop_reason: error") {
                bad.push(format!("{engine:?} {key}: {text}"));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: ENG-THRESHOLD: {bad:#?}");
}
