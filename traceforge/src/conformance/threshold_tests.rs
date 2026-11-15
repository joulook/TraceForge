//! ENG-THRESHOLD: cut runs and the full 32-bit count domain.
use std::sync::Arc;

use super::compact::{CompactSummary, OrdCounts, SetIndex};
use super::config::{ConfBuilder, Engine, IndexKind};
use super::ctx::{ConfMode, SinkVerdict};
type Prog = Arc<dyn Fn() + Send + Sync>;
use super::interchange::{encode_generic, line_of, parse_line, ThreadNames};
use super::report::{ConfError, SearchEnd};
use super::stateful::{enumerate, EnumRun};
use crate::program::{run_cli, Program};
use crate::thread;
use crate::{Config, ConsType};

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

fn threshold(text: &str, code: u8, expected: u8, limit: u32) {
    assert_eq!(code, expected, "{text}");
    assert!(text.contains("stop_reason: threshold"), "{text}");
    assert!(text.contains(&format!("passed limit {limit}")), "{text}");
    assert!(text.contains("thread `"), "{text}");
    assert!(!text.contains("exhausted"), "{text}");
}

#[test]
fn et_sender_cli_matrix() {
    let implementation = sender_program();
    let specification: Prog = Arc::new(|| {});
    let visible: Vec<String> = vec!["main".to_string()];
    let dir = super::interchange_default_tests::scratch("threshold-matrix");
    let good = dir.join("good.jsonl");
    let cut = dir.join("cut.jsonl");
    let good = good.to_str().unwrap();
    let cut = cut.to_str().unwrap();
    let run = |args: &[&str]| cli(&implementation, &specification, &visible, args);
    let (_, code) = run(&["export", "spec", "--out", good, "--threshold", "128"]);
    assert_eq!(code, 0);
    for threads in ["1", "2"] {
        let (text, code) = run(&["count", "impl", "--threads", threads, "--threshold", "16"]);
        threshold(&text, code, 0, 16);
        assert!(text.contains("execs=0 blocked=0"), "{text}");
        let (text, code) = run(&[
            "export",
            "impl",
            "--out",
            cut,
            "--threads",
            threads,
            "--threshold",
            "16",
        ]);
        threshold(&text, code, 2, 16);
        assert!(!std::path::Path::new(cut).exists());
        let (text, code) = run(&[
            "online",
            "--spec",
            good,
            "--threads",
            threads,
            "--threshold",
            "16",
        ]);
        threshold(&text, code, 0, 16);
        assert!(text.contains("verdict:    partial"), "{text}");
        for engine in ["stateful", "stateless", "gated", "enumerator"] {
            let args = [
                "conf",
                "--engine",
                engine,
                "--threads",
                threads,
                "--threshold",
                "16",
            ];
            let (text, code) = run(&args);
            threshold(&text, code, 2, 16);
            let mut control = args;
            control[6] = "128";
            let (text, code) = run(&control);
            assert_eq!(code, 0, "{text}");
            assert!(text.contains("stop_reason: exhausted"), "{text}");
        }
        for command in ["count", "export", "online"] {
            let mut args = match command {
                "count" => vec![command, "impl"],
                "export" => vec![command, "impl", "--out", cut],
                _ => vec![command, "--spec", good],
            };
            args.extend(["--threads", threads, "--threshold", "128"]);
            let (text, code) = run(&args);
            assert_eq!(code, 0, "{text}");
            assert!(text.contains("stop_reason: exhausted"), "{text}");
            if command == "export" {
                std::fs::remove_file(cut).unwrap();
            }
        }
    }
}

fn conf(imp: Prog, spec: Prog, skip: bool, engine: Engine, limit: u32) -> ConfError {
    let index = if matches!(engine, Engine::Enumerator | Engine::Gated) {
        IndexKind::Current
    } else {
        IndexKind::Set
    };
    let cc = ConfBuilder::new()
        .config(
            Config::builder()
                .with_seed(0)
                .with_thread_threshold(limit)
                .build(),
        )
        .engine(engine)
        .index(index)
        .skip_spec_errfree_check(skip)
        .build()
        .unwrap();
    super::verify(cc, move || imp(), move || spec()).unwrap_err()
}

fn long() {
    let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
    for i in 0..40 {
        tx.send_msg(i);
    }
}

#[test]
fn et_specification_precheck_and_sweeps() {
    for engine in [
        Engine::Stateful,
        Engine::CompleteFirst,
        Engine::Gated,
        Engine::Enumerator,
        Engine::SverifyP,
        Engine::CFirstP,
    ] {
        for skip in [false, true] {
            let error = conf(Arc::new(|| {}), Arc::new(long), skip, engine, 16);
            let ConfError::Threshold(reason) = error else {
                panic!("{error:?}")
            };
            assert_eq!(reason.limit, 16);
        }
    }
}

#[test]
fn et_named_thread_and_permanent_stop() {
    let started = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let seen = Arc::clone(&started);
    let stats = crate::verify(
        Config::builder().with_thread_threshold(16).build(),
        move || {
            seen.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            let _choice = crate::nondet();
            crate::thread::Builder::new()
                .name("long".into())
                .spawn(long)
                .unwrap();
            crate::thread::Builder::new()
                .name("twice".into())
                .spawn(long)
                .unwrap();
        },
    );
    assert_eq!(started.load(std::sync::atomic::Ordering::SeqCst), 1);
    assert_eq!((stats.execs, stats.block), (0, 0));
    assert_eq!(stats.threshold.unwrap().thread, "long");
}

#[test]
fn et_widths_exact_coordinate_and_interchange() {
    for n in [255, 256, 65535, 65536] {
        let summaries = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let got = std::rc::Rc::clone(&summaries);
        let names = vec!["a".to_string(), "b".to_string()];
        let visible = names.clone();
        let p: Prog = Arc::new(move || {
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
                    for _ in 1..n {
                        tx.send_msg(0);
                    }
                    done.send_msg(0);
                })
                .unwrap();
        });
        let run = enumerate(
            EnumRun {
                config: Config::builder()
                    .with_cons_type(ConsType::FIFO)
                    .with_thread_threshold(1 << 17)
                    .build(),
                visible: names.clone(),
                mode: ConfMode::Enumerate,
                sink: Box::new(move |g, _| {
                    got.borrow_mut()
                        .push(CompactSummary::at_completion(g, &visible, "test"));
                    SinkVerdict::Continue
                }),
                cut: false,
                stop_at_first_report: false,
                gate_sink: None,
                paper_events: false,
            },
            &p,
        );
        assert_eq!(run.end, SearchEnd::StateSpaceExhausted);
        let summary = summaries.borrow_mut().pop().unwrap();
        assert_eq!(summary.ord.len(), n + 1);
        // a's n sends precede b's receive through the final send's rf and a's po.
        assert_eq!(summary.ord.at(n), n as u32);
        assert!((0..n).all(|i| summary.ord.at(i) == 0));
        let width = match &summary.ord {
            OrdCounts::U8(_) => 1,
            OrdCounts::U16(_) => 2,
            OrdCounts::U32(_) => 4,
        };
        assert_eq!(
            width,
            if n <= 255 {
                1
            } else if n <= 65535 {
                2
            } else {
                4
            }
        );
        assert_eq!(summary.ord.payload_bytes(), (n + 1) * width);
        let line = line_of(&summary.sig, &summary.ord, &names, &|v| {
            encode_generic(v, &ThreadNames::new())
        })
        .unwrap();
        let (encoded, decoded) = parse_line(&line, &names).unwrap();
        assert_eq!(encoded, line);
        assert_eq!(decoded.ord, summary.ord);
        assert_eq!(decoded.ord.at(n), n as u32);
        if n == 65536 {
            let mut weaker = summary.clone();
            let OrdCounts::U32(counts) = &mut weaker.ord else {
                panic!("width")
            };
            counts[n] = 0;
            assert!(weaker.ord.le(&summary.ord));
            assert!(!summary.ord.le(&weaker.ord));
            assert_eq!(weaker.ord.cmp(&summary.ord), Some(std::cmp::Ordering::Less));
            assert_ne!(weaker.ord, summary.ord);
            let mut memo = std::collections::HashSet::new();
            memo.insert((0u32, weaker.ord.clone()));
            assert!(!memo.contains(&(0u32, summary.ord.clone())));
            let mut index = SetIndex::new();
            index.insert(&summary);
            assert!(!matches!(
                index.covers(&weaker).1,
                super::compact::Covers::Found(_)
            ));
            assert!(matches!(
                index.covers(&summary).1,
                super::compact::Covers::Found(_)
            ));
        }
    }
}

#[test]
fn et_u32_limit_synthetic() {
    OrdCounts::check_visible_len("limit-thread", u32::MAX as u64);
    let error = std::panic::catch_unwind(|| {
        OrdCounts::check_visible_len("limit-thread", u32::MAX as u64 + 1);
    })
    .unwrap_err();
    let text = error.downcast_ref::<String>().unwrap();
    for expected in ["limit-thread", "4294967296", "4294967295"] {
        assert!(text.contains(expected), "{text}");
    }
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
}

// BEGIN + UNIQUE + 15 sends leaves 17 labels; send 16 crosses limit 16.
// All 20 sends and END fit below limit 128.
fn sender_program() -> Prog {
    Arc::new(|| {
        named("sender", || {
            let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
            for i in 0..20 {
                tx.send_msg(i);
            }
        });
    })
}

fn assertion_before_crossing(command: &str, threads: &str) {
    let imp: Prog = Arc::new(|| {
        named("diagnostic", || crate::assert(false));
        named("sender", long);
    });
    let spec: Prog = Arc::new(|| {});
    let visible = vec!["main".to_string()];
    let dir = super::interchange_default_tests::scratch(&format!("assertion-{command}-{threads}"));
    let good = dir.join("good.jsonl");
    let cut = dir.join("cut.jsonl");
    let (text, code) = cli(
        &imp,
        &spec,
        &visible,
        &["export", "spec", "--out", good.to_str().unwrap()],
    );
    assert_eq!(code, 0, "{text}");
    let mut args = if command == "export" {
        vec![command, "impl", "--out", cut.to_str().unwrap()]
    } else {
        vec![command, "--spec", good.to_str().unwrap()]
    };
    args.extend(["--threads", threads, "--threshold", "16", "--seed", "0"]);
    let (text, code) = cli(&imp, &spec, &visible, &args);
    threshold(&text, code, if command == "export" { 2 } else { 0 }, 16);
    assert!(text.contains("thread `sender` passed limit 16"), "{text}");
    assert!(!cut.exists());
}

#[test]
fn et_assertion_export_t1() {
    assertion_before_crossing("export", "1");
}
#[test]
fn et_assertion_export_t2() {
    assertion_before_crossing("export", "2");
}
#[test]
fn et_assertion_online_t1() {
    assertion_before_crossing("online", "1");
}
#[test]
fn et_assertion_online_t2() {
    assertion_before_crossing("online", "2");
}

#[test]
fn et_worker_threshold_cancels_after_split() {
    use crate::parallel_verify::{verify_partitioned_rayon_with, PartitionHooks};
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Mutex, OnceLock};
    use std::time::{Duration, Instant};

    let root = Arc::new(OnceLock::new());
    let entered = Arc::new(Mutex::new(HashMap::new()));
    let crossed = Arc::new(AtomicBool::new(false));
    let flushed = Arc::new(Mutex::new(Vec::new()));
    let mut hooks = PartitionHooks::default();
    let saved = Arc::clone(&flushed);
    hooks.on_task_end = Arc::new(move |must| {
        saved
            .lock()
            .unwrap()
            .push((std::thread::current().id(), must.stats()));
    });
    let cancel = Arc::clone(&hooks.cancel);
    let config = Config::builder()
        .with_partitioned_parallelization(true)
        .with_partitioned_num_threads(2)
        .with_warmup(4)
        .with_iterations_until_split(4)
        .with_state_batch_size(1)
        .with_thread_threshold(32)
        .build();
    let root2 = Arc::clone(&root);
    let crossed2 = Arc::clone(&crossed);
    let run = verify_partitioned_rayon_with(
        config,
        move || {
            let me = std::thread::current().id();
            let is_root = me == *root2.get_or_init(|| me);
            let n = {
                let mut entries = entered.lock().unwrap();
                let n = entries.entry(me).or_insert(0usize);
                *n += 1;
                *n
            };
            if is_root && n == 5 {
                let start = Instant::now();
                while !crossed2.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(5) {
                    std::thread::sleep(Duration::from_millis(1));
                }
            }
            serve(3, 3);
            if !is_root && n >= 2 {
                crossed2.store(true, Ordering::SeqCst);
                long();
            }
        },
        hooks,
    );
    assert!(run.tasks_spawned > 0);
    assert!(cancel.is_cancelled());
    assert!(crossed.load(Ordering::SeqCst));
    assert_eq!(run.stats.threshold.as_ref().unwrap().limit, 32);
    assert!(run.stats.execs + run.stats.block < 100, "{:?}", run.stats);
    assert!(flushed.lock().unwrap().iter().any(|(tid, stats)| {
        tid != root.get().unwrap() && stats.threshold.is_some() && stats.execs > 0
    }));
}

#[derive(Clone, Debug, PartialEq)]
enum ThresholdMsg {
    V(i32),
    Call(usize, i32),
}

fn serve(k: usize, q: usize) -> usize {
    let (req, inbox) = crate::channel::Builder::<ThresholdMsg>::new().build();
    let (dtx, drx) = crate::channel::Builder::<ThresholdMsg>::new().build();
    let mut replies = Vec::new();
    let mut waits = Vec::new();
    for _ in 0..k {
        let (tx, rx) = crate::channel::Builder::<ThresholdMsg>::new().build();
        replies.push(tx);
        waits.push(rx);
    }
    let server = named("server", move || {
        for i in 0..k * q {
            let m: ThresholdMsg = inbox.recv_msg_block();
            if let ThresholdMsg::Call(c, v) = m {
                if i == 0 {
                    dtx.send_msg(ThresholdMsg::V(c as i32));
                }
                replies[c].send_msg(ThresholdMsg::V(v));
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
                    req.send_msg(ThresholdMsg::Call(c, i as i32));
                    let _: ThresholdMsg = rx.recv_msg_block();
                }
            })
        })
        .collect();
    let first = match drx.recv_msg_block() {
        ThresholdMsg::V(c) => c as usize,
        other => panic!("conformance: PO: {other:?}"),
    };
    server.join().unwrap();
    for c in clients {
        c.join().unwrap();
    }
    first
}

#[test]
fn et_cut_never_reaches_completion_sink() {
    let calls = std::rc::Rc::new(std::cell::Cell::new(0usize));
    let got = std::rc::Rc::clone(&calls);
    let run = enumerate(
        EnumRun {
            config: Config::builder().with_thread_threshold(16).build(),
            visible: vec!["main".to_string()],
            mode: ConfMode::Enumerate,
            sink: Box::new(move |g, _| {
                got.set(got.get() + 1);
                CompactSummary::at_completion(g, &vec!["main".to_string()], "test");
                SinkVerdict::Continue
            }),
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        &sender_program(),
    );
    assert_eq!(calls.get(), 0);
    assert_eq!(run.executions, 0);
    assert!(matches!(run.end, SearchEnd::Threshold(_)));
}

#[test]
fn et_threshold_overrides_a_partitioned_chunk_end() {
    let mut ctx = super::ctx::ConfCtx::gate_disabled(
        Config::default(),
        vec![],
        ConfMode::EnumeratePartitioned,
    );
    let first = crate::ThresholdStop {
        thread: "worker".into(),
        limit: 16,
    };
    ctx.record_end(SearchEnd::MaxIterations(1));
    ctx.record_end(SearchEnd::Threshold(first.clone()));
    ctx.record_end(SearchEnd::StateSpaceExhausted);
    ctx.record_end(SearchEnd::Threshold(crate::ThresholdStop {
        thread: "later".into(),
        limit: 16,
    }));
    assert_eq!(ctx.end(), SearchEnd::Threshold(first));
}

#[test]
fn et_inline_sweep_cancels_before_cleanup() {
    use crate::parallel_verify::CancelToken;
    use std::sync::atomic::{AtomicBool, Ordering};

    struct Guard {
        token: Option<Arc<CancelToken>>,
        observed: Arc<AtomicBool>,
    }
    impl Drop for Guard {
        fn drop(&mut self) {
            self.observed.store(
                self.token.as_ref().is_some_and(|c| c.threshold().is_some()),
                Ordering::SeqCst,
            );
        }
    }
    let observed = Arc::new(AtomicBool::new(false));
    let seen = Arc::clone(&observed);
    let specification: Prog = Arc::new(move || {
        let token = crate::must::Must::current().and_then(|m| m.borrow().threshold_cancel.clone());
        let _guard = Guard {
            token,
            observed: Arc::clone(&seen),
        };
        long();
    });
    let error = conf(Arc::new(|| {}), specification, true, Engine::CFirstP, 16);
    let ConfError::Threshold(reason) = error else {
        panic!("{error:?}")
    };
    assert!(observed.load(Ordering::SeqCst));

    let cancelled = Arc::new(CancelToken::new());
    cancelled.stop_threshold(reason.clone());
    let program: Prog = Arc::new(|| panic!("a cancelled worker executed user code"));
    let run = super::stateful::enumerate_with_cancel(
        EnumRun {
            config: Config::default(),
            visible: vec![],
            mode: ConfMode::CFirstSweep,
            sink: Box::new(|_, _| panic!("a cancelled worker reached completion")),
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        &program,
        Some(cancelled),
    );
    assert_eq!(run.end, SearchEnd::Threshold(reason));
    assert_eq!(run.executions, 0);
}

#[test]
fn et_baseline_row_threshold() {
    use super::record::{self, GridConfig, GridEnd, GridEngine, GridRaw, GridResult, Subject};

    for engine in [GridEngine::Explore, GridEngine::ExploreP] {
        for limit in [16, 128] {
            for spec_crosses in [false, true] {
                if engine == GridEngine::Explore && spec_crosses {
                    continue;
                }
                let mut config = GridConfig::new(engine);
                config.threads = 2;
                let sender = sender_program();
                let empty: Prog = Arc::new(|| {});
                let subject = Subject {
                    name: "sender".into(),
                    config: Config::builder().with_thread_threshold(limit).build(),
                    visible: vec!["main".into()],
                    implementation: if spec_crosses {
                        empty.clone()
                    } else {
                        sender.clone()
                    },
                    specification: if spec_crosses { sender } else { empty },
                };
                let raw = if engine == GridEngine::Explore {
                    let imp = subject.implementation.clone();
                    GridRaw::Explore(crate::verify(subject.config.clone(), move || imp()))
                } else {
                    GridRaw::ExploreP(Box::new(record::explore_partitioned(&subject, &config)))
                };
                let end = GridEnd::Ok(GridResult {
                    fixture: subject.name,
                    config,
                    raw,
                    wall: std::time::Duration::ZERO,
                    vm_hwm_kb: (None, None),
                    tainted_at_start: false,
                    stack_mib: 32,
                });
                let text = super::measure::of_row(&vec![], &end, engine, 2).render();
                let reason = if limit == 16 {
                    "threshold"
                } else {
                    "exhausted"
                };
                assert!(text.contains(&format!("stop_reason: {reason}")), "{text}");
            }
        }
    }
}

/// B1: hold an admission after its false token read. The threshold wrapper must publish
/// the stop only after that admission's signature and order. Channels also release the
/// held admission on a bare-cancel mutant, so the failing direction does not deadlock.
#[test]
fn et_threshold_cancel_serializes_with_cache_publication() {
    use super::compact::{Admission, SharedCache, WorkerTable};
    use super::config::Capacity;
    use crate::parallel_verify::CancelToken;
    use std::sync::{mpsc, Mutex};

    let summaries = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let got = std::rc::Rc::clone(&summaries);
    let program: Prog = Arc::new(|| {});
    let run = enumerate(
        EnumRun {
            config: Config::default(),
            visible: vec![],
            mode: ConfMode::Enumerate,
            sink: Box::new(move |g, _| {
                got.borrow_mut().push(CompactSummary::at_completion(g, &[], "test"));
                SinkVerdict::Continue
            }),
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        &program,
    );
    assert_eq!(run.end, SearchEnd::StateSpaceExhausted,
        "conformance: the summary run completes");
    let summary = summaries.borrow_mut().pop().expect("conformance: a complete summary");
    let cache = Arc::new(SharedCache::new(Capacity::Unbounded));
    let at_cancel = Arc::new(Mutex::new(None));
    let (event_tx, event_rx) = mpsc::channel();
    let token = Arc::new(CancelToken::with_threshold_cancel({
        let cache = Arc::clone(&cache);
        let at_cancel = Arc::clone(&at_cancel);
        let event_tx = event_tx.clone();
        move |token| {
            event_tx.send(false).unwrap();
            cache.under_admission(|| {
                token.cancel();
                *at_cancel.lock().unwrap() = Some((cache.len(), cache.signatures().len()));
            });
        }
    }));
    let (read_tx, read_rx) = mpsc::channel();
    let (release_tx, release_rx) = mpsc::channel();
    let admitting = {
        let cache = Arc::clone(&cache);
        let token = Arc::clone(&token);
        let summary = summary.clone();
        std::thread::spawn(move || {
            cache.admit(&mut WorkerTable::new(), &summary, &summary, || {
                let cancelled = token.is_cancelled();
                read_tx.send(cancelled).unwrap();
                release_rx.recv().unwrap();
                cancelled
            })
        })
    };
    assert!(!read_rx.recv().unwrap(), "conformance: admission reads a live token");
    let reason = crate::ThresholdStop { thread: "sweep".into(), limit: 16 };
    let stopping = {
        let token = Arc::clone(&token);
        let reason = reason.clone();
        std::thread::spawn(move || {
            token.stop_threshold(reason);
            event_tx.send(true).unwrap();
        })
    };
    // The wrapper entered, or a mutant completed its bare cancel. The admission is
    // still held in both cases. Release before asserting so either path can join.
    let completed_while_held = event_rx.recv().unwrap();
    let cancelled_while_held = token.is_cancelled();
    release_tx.send(()).unwrap();
    let admitted = admitting.join().unwrap();
    stopping.join().unwrap();
    assert!(!completed_while_held, "conformance: threshold cancel bypassed the cache lock");
    assert!(!cancelled_while_held, "conformance: cancel took effect before publication");
    assert_eq!(admitted, Admission::Admitted, "conformance: held admission publishes");
    assert_eq!(*at_cancel.lock().unwrap(), Some((1, 1)),
        "conformance: publication precedes cancellation");
    assert!(token.is_cancelled(), "conformance: threshold cancels the token");
    assert_eq!(token.threshold(), Some(reason.clone()),
        "conformance: the first threshold reason is recorded");
    assert_eq!(token.admit(|| panic!("conformance: spawn after threshold")), None::<()>,
        "conformance: no spawn after threshold");
    assert_eq!(
        cache.admit(&mut WorkerTable::new(), &summary, &summary, || token.is_cancelled()),
        Admission::UnadmittedAfterCancel,
        "conformance: no cache admission after threshold",
    );
    assert_eq!((cache.len(), cache.signatures().len()), (1, 1),
        "conformance: no publication after threshold");
    token.stop_threshold(crate::ThresholdStop { thread: "later".into(), limit: 32 });
    assert_eq!(token.threshold(), Some(reason), "conformance: the first reason wins");
}
