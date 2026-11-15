//! ENG-LARGEPRINT: separate-stream CLI and path probes.
use crate::*;
use conformance::ctx::ConfMode;
use std::cell::Cell;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;
type Prog = Arc<dyn Fn() + Send + Sync>;

static CROSSING_ACTIVE: AtomicBool = AtomicBool::new(false);
static ROOT: OnceLock<std::thread::ThreadId> = OnceLock::new();
thread_local! {
    static SPEC_CALLS: Cell<usize> = const { Cell::new(0) };
    static ARMED: Cell<bool> = const { Cell::new(false) };
}

// Only the selected nested Must crosses; the outer run and precheck remain healthy.
pub(crate) fn before_label(must: &mut Must) {
    if !ARMED.with(Cell::get) {
        return;
    }
    let mode = must.conf_ctx().map(|c| c.mode());
    if matches!(mode, Some(ConfMode::CFirstSweep | ConfMode::GatedSweep)) {
        if must.config.thread_threshold != 2 {
            eprintln!(
                "EL-PATH {mode:?} worker={} dump={}",
                ROOT.get()
                    .is_some_and(|r| *r != std::thread::current().id()),
                must.config.dump_large_graph
            );
        }
        must.config.thread_threshold = 2;
    }
}

fn child_command() -> Command {
    let mut command = Command::new("timeout");
    command
        .args([
            "45s",
            "bash",
            "-c",
            "ulimit -v 2097152; exec \"$@\"",
            "el-child",
        ])
        .arg(std::env::current_exe().unwrap());
    command
}

pub(crate) fn crossing(must: &Must) {
    if !CROSSING_ACTIVE.load(Ordering::Relaxed) {
        return;
    }
    eprintln!(
        "EL-CROSS must={:p} mode={:?} worker={} dump={}",
        must,
        must.conf_ctx().map(|c| c.mode()),
        ROOT.get()
            .is_some_and(|r| *r != std::thread::current().id()),
        must.config.dump_large_graph
    );
}

fn child(case: &str, args: &[&str], dump: bool) -> Output {
    let dir = std::env::temp_dir().join(format!("el-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let out = child_command()
        .args([
            "--exact",
            "largeprint_tests::el_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("EL_CASE", case)
        .env("EL_ARGS", serde_json::to_string(args).unwrap())
        .env("EL_DUMP", dump.to_string())
        .env("EL_DIR", &dir)
        .env("EVAL_ROW", row_json())
        .env("EVAL_COMMIT", "el-test")
        .output()
        .unwrap();
    if let Ok(dir) = std::env::var("EL_ARTIFACT_DIR") {
        let dir = std::path::Path::new(&dir);
        std::fs::create_dir_all(dir).unwrap();
        let name = format!("{case}-{}-{dump}", args.join("_").replace('/', "_"));
        std::fs::write(dir.join(format!("{name}.stdout")), &out.stdout).unwrap();
        std::fs::write(dir.join(format!("{name}.stderr")), &out.stderr).unwrap();
        std::fs::write(
            dir.join(format!("{name}.command")),
            format!(
                "case={case} args={args:?} dump={dump}\nstatus={}\n",
                out.status
            ),
        )
        .unwrap();
    }
    assert!(
        out.status.success(),
        "{case} {args:?}: {}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    out
}

fn streams(out: &Output, crossing: bool, dump: bool) {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(stderr.contains("Large thread size"), crossing, "{stderr}");
    assert_eq!(
        stderr.contains("Printing the large graph:"),
        crossing && dump,
        "{stderr}"
    );
    assert_eq!(stdout.contains("BEGIN"), crossing && dump, "{stdout}");
    assert!(!stdout.contains("Printing the large graph:"), "{stdout}");
    assert!(!stdout.contains("Large thread size"), "{stdout}");
    assert!(!stderr.contains("BEGIN"), "{stderr}");
}

fn result(out: &Output) -> Vec<String> {
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|s| s.find("EL-RESULT ").map(|i| s[i..].to_owned()))
        .collect()
}

fn pair(case: &str, args: &[&str], crossing: bool) {
    let off = child(case, args, false);
    let on = child(case, args, true);
    streams(&off, crossing, false);
    streams(&on, crossing, true);
    assert!(!result(&off).is_empty());
    assert_eq!(result(&off), result(&on));
}

#[test]
fn el_cli_matrix() {
    for threads in ["1", "2"] {
        for limit in ["16", "128"] {
            for command in ["count", "export", "online"] {
                let mut args = vec![command];
                if command != "online" {
                    args.push("impl");
                }
                args.extend(["--threads", threads, "--threshold", limit]);
                pair("cli", &args, limit == "16");
            }
            for engine in ["stateful", "stateless", "gated", "enumerator"] {
                pair(
                    "cli",
                    &[
                        "conf",
                        "--engine",
                        engine,
                        "--threads",
                        threads,
                        "--threshold",
                        limit,
                    ],
                    limit == "16",
                );
            }
        }
    }
    for threads in ["1", "2"] {
        for limit in ["8", "128"] {
            for command in ["count", "export"] {
                pair(
                    "cli",
                    &[command, "spec", "--threads", threads, "--threshold", limit],
                    limit == "8",
                );
            }
            for engine in ["stateful", "stateless", "gated", "enumerator"] {
                pair(
                    "cli",
                    &[
                        "conf",
                        "--engine",
                        engine,
                        "--threads",
                        threads,
                        "--threshold",
                        limit,
                    ],
                    limit == "8",
                );
            }
        }
    }
}

#[test]
fn el_row() {
    for limit in ["16", "128"] {
        pair(
            "cli",
            &["row", "--seed", "0", "--threshold", limit, "--"],
            limit == "16",
        );
    }
}

fn check_path(path: &str) {
    let off = child(path, &[], false);
    let on = child(path, &[], true);
    streams(&off, true, false);
    streams(&on, true, true);
    assert_eq!(result(&off), result(&on));
    let expected = match path {
        "precheck" => "mode=Some(Precheck)",
        "specification" => "mode=Some(Enumerate)",
        "gate" | "completion" => "mode=Some(GatedSweep)",
        _ => "mode=Some(CFirstSweep)",
    };
    for out in [&off, &on] {
        assert!(String::from_utf8_lossy(&out.stderr).contains(expected));
    }
    if path == "inline" {
        for out in [&off, &on] {
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert!(
                stdout.lines().any(|s| {
                    let f: Vec<_> = s.split_whitespace().collect();
                    f.len() >= 3
                        && f[0].starts_with("rt")
                        && f[0].ends_with(':')
                        && f[1].parse::<u64>().is_ok_and(|n| n > 0)
                        && f[2].starts_with("execs")
                }),
                "{stdout}"
            );
            assert!(String::from_utf8_lossy(&out.stderr).contains("worker=true"));
        }
    }
}

#[test]
fn el_path_precheck() {
    check_path("precheck");
}

#[test]
fn el_path_specification() {
    check_path("specification");
}

#[test]
fn el_path_ordinary() {
    check_path("ordinary");
}

#[test]
fn el_path_inline() {
    check_path("inline");
}

#[test]
fn el_path_gate() {
    check_path("gate");
}

#[test]
fn el_path_completion() {
    check_path("completion");
}

#[test]
fn el_other_diagnostics() {
    let out = child("verbose", &[], false);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("One more complete execution"), "{stdout}");
    assert!(stdout.contains("BEGIN"), "{stdout}");
    assert!(!String::from_utf8_lossy(&out.stderr).contains("Printing the large graph:"));
}

#[test]
fn el_seam_is_inert_outside_children() {
    let out = child_command()
        .args([
            "--exact",
            "conformance::threshold_tests::et_specification_precheck_and_sweeps",
            "--nocapture",
            "--test-threads=1",
        ])
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("Large thread size 17 events)"), "{stderr}");
    assert!(!stdout.contains("Large thread size"), "{stdout}");
    for tag in ["EL-CROSS", "EL-PATH"] {
        assert!(!stderr.contains(tag), "{stderr}");
        assert!(!stdout.contains(tag), "{stdout}");
    }
}

#[test]
fn el_warning_budget() {
    let out = child_command()
        .args([
            "--exact",
            "must::threshold_tests::el_budget_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("EL_BUDGET", "1")
        .output()
        .unwrap();
    assert!(out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(stderr.matches("Large thread size").count(), 1, "{stderr}");
    assert_eq!(
        stderr.matches("Printing the large graph:").count(),
        1,
        "{stderr}"
    );
}

#[test]
fn el_warnings_as_errors() {
    for dump in [false, true] {
        let out = child_command()
            .args([
                "--exact",
                "largeprint_tests::el_child",
                "--nocapture",
                "--test-threads=1",
            ])
            .env("EL_CASE", "werror")
            .env("EL_DUMP", dump.to_string())
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(65));
        assert!(String::from_utf8_lossy(&out.stderr).contains("Large thread size"));
        assert!(!String::from_utf8_lossy(&out.stderr).contains("Printing the large graph:"));
        assert!(!String::from_utf8_lossy(&out.stdout).contains("BEGIN"));
    }
}

#[test]
fn el_serialized_default_unchanged() {
    let json = serde_json::to_value(Config::default()).unwrap();
    assert!(json.get("dump_large_graph").is_none());
    let json = serde_json::to_value(Config::builder().with_dump_large_graph(true).build()).unwrap();
    assert_eq!(json["dump_large_graph"], true);
}

#[test]
fn el_config_compatibility() {
    assert!(!Config::default().dump_large_graph);
    let mut old = serde_json::to_value(Config::default()).unwrap();
    old.as_object_mut().unwrap().remove("dump_large_graph");
    assert!(
        !serde_json::from_value::<Config>(old)
            .unwrap()
            .dump_large_graph
    );
    for dump in [false, true] {
        let cfg = Config::builder().with_dump_large_graph(dump).build();
        let json = serde_json::to_string(&cfg).unwrap();
        assert_eq!(
            serde_json::from_str::<Config>(&json)
                .unwrap()
                .dump_large_graph,
            dump
        );
    }
}

fn row_json() -> String {
    serde_json::json!({"fixture":"channel-allocation-reporter", "label":concat!(
        "Explore/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/",
        "instr=false/cut=false/cover=Sweep"), "rep":0,
        "tier":{"name":"el", "wall_ms":30000, "mem_kb":2097152}, "run_kind":"timed",
        "family":"channel-allocation", "knobs":"", "k":[null,null,null,null],
        "variant":"conforming", "twin_key":""})
    .to_string()
}

fn cli(args: &[String]) -> (String, u8) {
    program::run_cli(
        &program::Program {
            visible: &|_| vec!["reporter".into()],
            imp: &|_| channel_allocation_reporter(18),
            spec: &|_| channel_allocation_reporter(8),
        },
        args,
    )
}

#[test]
fn el_child() {
    let Ok(case) = std::env::var("EL_CASE") else {
        return;
    };
    let dump = std::env::var("EL_DUMP").unwrap() == "true";
    if case == "cli" {
        let mut args: Vec<String> =
            serde_json::from_str(&std::env::var("EL_ARGS").unwrap()).unwrap();
        let dir = std::env::var("EL_DIR").unwrap();
        if args[0] != "row" {
            args.extend(["--seed".into(), "0".into()]);
        }
        if args[0] == "online" {
            let good = format!("{dir}/good-{}.jsonl", std::process::id());
            assert_eq!(
                cli(&[
                    "export".into(),
                    "spec".into(),
                    "--out".into(),
                    good.clone(),
                    "--threshold".into(),
                    "128".into()
                ])
                .1,
                0
            );
            args.extend(["--spec".into(), good]);
        }
        if args[0] == "export" {
            args.extend([
                "--out".into(),
                format!("{dir}/cut-{}.jsonl", std::process::id()),
            ]);
        }
        if dump {
            let at = args.iter().position(|s| s == "--").unwrap_or(args.len());
            args.insert(at, "--dump-large-graph".into());
        }
        let (text, code) = cli(&args);
        if args.windows(2).any(|a| a == ["--threshold", "128"]) {
            assert_eq!(code, 0, "{text}");
        }
        // Stable result lines; timings and process resource readings vary between children.
        println!("EL-RESULT code={code}");
        for s in text.lines().filter(|s| {
            s.contains("execs=")
                || s.contains("verdict:")
                || s.contains("passed limit")
                || s.split_once(':').is_some_and(|(key, _)| {
                    conformance::measure::KEYS.contains(&key.trim())
                        && !key.ends_with("_ms")
                        && key != "peak_rss_kb"
                })
        }) {
            println!("EL-RESULT {s}");
        }
        return;
    }
    let cfg = Config::builder().with_dump_large_graph(dump).with_seed(0);
    if case == "werror" {
        verify(
            cfg.with_thread_threshold(2)
                .with_warnings_as_errors(true)
                .build(),
            || {
                for _ in 0..10 {
                    let _: bool = nondet();
                }
            },
        );
        panic!("warnings_as_errors returned");
    }
    if case == "verbose" {
        verify(cfg.with_verbose(1).build(), || {});
        return;
    }
    path_case(&case, cfg.build());
}

fn path_case(path: &str, mut cfg: Config) {
    CROSSING_ACTIVE.store(true, Ordering::Relaxed);
    use conformance::config::Capacity;
    use conformance::{ConfBuilder, Engine, GatePolicy};
    let is_inline = path == "inline";
    cfg.thread_threshold = if matches!(path, "precheck" | "specification") {
        2
    } else {
        128
    };
    cfg.warmup = 1;
    cfg.iterations_until_split = 1;
    cfg.state_batch_size = 1;
    let cc = ConfBuilder::new()
        .config(cfg)
        .visible_threads(["v"])
        .engine(match path {
            "specification" => Engine::Stateful,
            "inline" => Engine::CFirstP,
            "gate" | "completion" => Engine::Gated,
            _ => Engine::CompleteFirst,
        })
        .threads(2)
        .skip_spec_errfree_check(path != "precheck")
        .witness_cache(Capacity::Zero)
        .gate_policy(if path == "completion" {
            GatePolicy::Never
        } else {
            GatePolicy::Always
        })
        .build()
        .unwrap();
    let imp: Prog = Arc::new(move || {
        ROOT.get_or_init(|| std::thread::current().id());
        if is_inline {
            split_program()();
        } else {
            visible_program();
        }
    });
    let nested = !matches!(path, "precheck" | "specification");
    let spec: Prog = Arc::new(move || {
        let n = SPEC_CALLS.with(|c| {
            c.set(c.get() + 1);
            c.get()
        });
        let worker = ROOT
            .get()
            .is_some_and(|r| *r != std::thread::current().id());
        ARMED.with(|a| a.set(nested && (!is_inline || (worker && n >= 2))));
        if is_inline {
            split_program()();
        } else {
            visible_program();
        }
        ARMED.with(|a| a.set(false));
    });
    if matches!(path, "precheck" | "specification") {
        let out = conformance::verify(cc, move || imp(), move || spec());
        assert!(matches!(out, Err(conformance::ConfError::Threshold(_))));
        eprintln!("EL-PATH {path}");
    } else if is_inline {
        let out = conformance::cfirst_p::run_with(&cc, &imp, &spec);
        assert!(out.counters.sweeps_in_tasks > 0);
        assert!(out.counters.tasks_nonempty > 0);
        assert!(matches!(
            out.impl_end,
            conformance::report::SearchEnd::Threshold(_)
        ));
        println!(
            "EL-RESULT threshold={}",
            matches!(out.impl_end, conformance::report::SearchEnd::Threshold(_))
        );
    } else if path == "ordinary" {
        let out = conformance::cfirst::run_with(&cc, &imp, &spec, false);
        assert!(out.counters.sweeps > 0);
        assert!(matches!(
            out.impl_end,
            conformance::report::SearchEnd::Threshold(_)
        ));
        println!(
            "EL-RESULT threshold={}",
            matches!(out.impl_end, conformance::report::SearchEnd::Threshold(_))
        );
    } else {
        let out = conformance::gated::run_with(&cc, &imp, &spec, false);
        if path == "gate" {
            assert!(out.counters.gate_sweeps > 0);
        } else {
            assert!(out.counters.completion_sweeps > 0);
            assert_eq!(out.counters.gate_sweeps, 0);
        }
        assert!(matches!(
            out.impl_end,
            conformance::report::SearchEnd::Threshold(_)
        ));
        println!(
            "EL-RESULT threshold={}",
            matches!(out.impl_end, conformance::report::SearchEnd::Threshold(_))
        );
    }
}

fn visible_program() {
    thread::Builder::new()
        .name("v".into())
        .spawn(|| {
            for _ in 0..8 {
                let _: bool = nondet();
            }
            send_msg(thread::current().id(), 1i32);
        })
        .unwrap()
        .join()
        .unwrap();
}

// Invisible allocation work precedes one visible report. Each channel adds one UNIQUE label.
fn channel_allocation_reporter(channels: usize) -> Prog {
    Arc::new(move || {
        for _ in 0..channels {
            let _ = channel::Builder::<i32>::new().build();
        }
        thread::Builder::new()
            .name("reporter".into())
            .spawn(|| send_msg(thread::current().id(), 1i32))
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
