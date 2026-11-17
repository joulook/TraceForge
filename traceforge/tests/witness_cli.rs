//! Execution witness bytes and selection through the public CLI.
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use traceforge::program::{run_cli, Entry, Program};
use traceforge::Nondet;

fn scratch() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let p = std::env::temp_dir().join(format!(
        "tf-witness-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&p).unwrap();
    p
}

fn named<F: FnOnce() + Send + 'static>(name: &str, f: F) -> traceforge::thread::JoinHandle<()> {
    traceforge::thread::Builder::new().name(name.to_owned()).spawn(f).unwrap()
}

fn spec() {
    named("v", || {}).join().unwrap();
}

fn cli(body: Entry, args: &[&str]) -> (String, u8) {
    run_cli(&Program {
        visible: &|_| vec!["v".to_owned()],
        spec: &|_| Arc::new(spec),
        imp: &|_| body.clone(),
    }, &args.iter().map(|s| s.to_string()).collect::<Vec<_>>())
}

fn fixture() {
    let v = named("v", || {
        let a = traceforge::nondet() as usize;
        let b = traceforge::nondet() as usize;
        let c = (4..6).nondet() - 4;
        let _ = (9..10).nondet();
        let _ = traceforge::recv_msg::<usize>();
        let me = traceforge::thread::current().id();
        traceforge::send_msg(me, c * 4 + a * 2 + b);
        let _ = traceforge::recv_msg_block::<usize>();
    });
    named("blocked", || { let _ = traceforge::recv_msg_block::<usize>(); });
    let d = traceforge::thread::Builder::new().name("daemon".to_owned())
        .spawn_daemon(|| {}).unwrap();
    v.join().unwrap();
    d.join().unwrap();
}

fn reference(dir: &std::path::Path) -> PathBuf {
    let p = dir.join("spec.jsonl");
    let (text, code) = cli(Arc::new(fixture), &["export", "spec", "--out", p.to_str().unwrap()]);
    assert_eq!(code, 0, "{text}");
    p
}

fn check_links(text: &str) {
    let events: HashMap<_, _> = text.lines().filter_map(|l| l.trim().split_once(": "))
        .filter(|(stamp, _)| stamp.starts_with('(')).collect();
    for event in events.values() {
        if let Some(rest) = event.strip_prefix("RECV() [(") {
            let (stamp, _) = rest.split_once(") ").unwrap();
            assert!(events[format!("({stamp})").as_str()].starts_with("SEND("));
        }
    }
}

#[test]
fn golden_both_paths_and_receive_links() {
    for online in [true, false] {
        let dir = scratch();
        let spec = reference(&dir);
        let path = format!("{}/w/", dir.display());
        let args = if online {
            vec!["online", "--spec", spec.to_str().unwrap(), "--witness", &path, "--seed", "0"]
        } else {
            vec!["conf", "--engine", "stateful", "--witness", &path, "--seed", "0"]
        };
        let (out, code) = cli(Arc::new(fixture), &args);
        assert_eq!(code, if online { 0 } else { 1 }, "{out}");
        let mut values = HashSet::new();
        let mut previous_iteration = 0;
        for n in 1..=8 {
            let text = std::fs::read_to_string(format!("{path}witness-{n}.txt")).unwrap();
            let header = text.lines().next().unwrap();
            let (iteration, summary) = header.strip_prefix("uncovered summary (iteration ")
                .unwrap().split_once("): ").unwrap();
            let count = iteration.parse::<usize>().unwrap();
            assert!(count > previous_iteration);
            previous_iteration = count;
            if n == 1 {
                assert_eq!(iteration, "1");
                if online { assert!(out.contains("first_miss_iteration: 1\n")); }
            }
            let line: serde_json::Value = serde_json::from_str(summary).unwrap();
            let value = line["words"]["v"][1]["s"].as_u64().unwrap();
            values.insert(value);
            let (a, b, c) = ((value / 2) % 2, value % 2, value / 4);
            let expected = format!(concat!(
                "uncovered summary (iteration {}): ",
                "{{\"statuses\":{{\"v\":\"done\"}},\"words\":{{\"v\":[",
                "{{\"r\":null}},{{\"s\":{}}},{{\"r\":{}}}]}},\"counts\":[]}}\n",
                "thread \"main\"[tid=0]:\n",
                "\t(0, 0): BEGIN\n\t(0, 1): TCREATE(1:\"v\")\n",
                "\t(0, 2): TCREATE(2:\"blocked\")\n\t(0, 3): TCREATE(3:\"daemon\")\n",
                "\t(0, 4): TJOIN(1)\n\t(0, 5): TJOIN(3)\n\t(0, 6): END\n",
                "thread \"v\"[tid=1]:\n\t(1, 0): BEGIN\n",
                "\t(1, 1): NONDET {}\n\t(1, 2): NONDET {}\n\t(1, 3): NONDET {}\n",
                "\t(1, 4): RECV() [TIMEOUT]\n\t(1, 5): SEND(v, {})\n",
                "\t(1, 6): RECV() [(1, 5) v]\n\t(1, 7): END\n",
                "thread \"blocked\"[tid=2]:\n\t(2, 0): BEGIN\n\t(2, 1): BLK\n",
                "thread \"daemon\"[tid=3, daemon]:\n\t(3, 0): BEGIN\n\t(3, 1): END\n"
            ), iteration, value, value, a, b, c, value);
            assert_eq!(text.as_bytes(), expected.as_bytes());
            check_links(&text);
        }
        assert_eq!(values.len(), 8);
        assert_eq!(std::fs::read_dir(&path).unwrap().count(), 8);
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 2);
    }
}

#[test]
fn distinct_directory_and_first_file() {
    for online in [true, false] {
        let dir = scratch();
        let spec = reference(&dir);
        let body: Entry = Arc::new(|| {
            let _ = traceforge::nondet();
            named("v", || {
                let me = traceforge::thread::current().id();
                traceforge::send_msg(me, traceforge::nondet());
            }).join().unwrap();
        });
        let folder = format!("{}/w/", dir.display());
        let file = dir.join("first.txt");
        let mut first = String::new();
        for path in [folder.as_str(), file.to_str().unwrap()] {
            let mut args = if online { vec!["online", "--spec", spec.to_str().unwrap()] }
                else { vec!["conf", "--engine", "stateful"] };
            args.extend(["--witness", path, "--seed", "0"]);
            let (out, code) = cli(body.clone(), &args);
            assert_eq!(code, if online { 0 } else { 1 }, "{out}");
            if path == folder.as_str() {
                assert_eq!(std::fs::read_dir(path).unwrap().count(), 2);
                first = std::fs::read_to_string(format!("{folder}witness-1.txt")).unwrap();
                let second = std::fs::read_to_string(format!("{folder}witness-2.txt")).unwrap();
                assert_ne!(first.lines().next(), second.lines().next());
                assert_ne!(first.contains("SEND(v, true)"), second.contains("SEND(v, true)"));
            } else {
                assert_eq!(std::fs::read_to_string(path).unwrap(), first);
            }
        }
        let early = format!("{}/early/", dir.display());
        let mut args = if online { vec!["online", "--spec", spec.to_str().unwrap()] }
            else { vec!["conf", "--engine", "stateful"] };
        args.extend(["--witness", &early, "--seed", "0", "--stop-at-first"]);
        cli(body.clone(), &args);
        assert_eq!(std::fs::read_dir(&early).unwrap().count(), 1);
        assert_eq!(std::fs::read_to_string(format!("{early}witness-1.txt")).unwrap(), first);
    }
}

#[test]
fn refusals_before_exploration() {
    let body: Entry = Arc::new(|| panic!("must not explore"));
    let cases = [
        (vec!["online", "--witness", "x", "--threads", "2"],
            "--witness requires --threads 1"),
        (vec!["conf", "--witness", "x", "--threads", "2"],
            "--witness requires --threads 1"),
        (vec!["conf", "--witness", "x", "--engine", "stateless"],
            "--witness requires conf --engine stateful"),
        (vec!["conf", "--witness", "x", "--engine", "gated"],
            "--witness requires conf --engine stateful"),
        (vec!["conf", "--witness", "x", "--engine", "enumerator"],
            "--witness requires conf --engine stateful"),
        (vec!["export", "spec", "--witness", "x"],
            "--witness requires online or conf --engine stateful"),
        (vec!["count", "impl", "--witness", "x"],
            "--witness requires online or conf --engine stateful"),
        (vec!["row", "--witness", "x"],
            "row takes only --model, --seed, --threshold and --dump-large-graph, not `--witness`"),
    ];
    let usage = cli(body.clone(), &[]).0.split_once('\n').unwrap().1.to_owned();
    for (args, reason) in cases {
        assert_eq!(cli(body.clone(), &args), (format!("program: {reason}\n{usage}"), 2));
    }
}

#[test]
fn unprintable_and_unnamed_stop_without_writing() {
    for online in [true, false] {
        for name in [None, Some("bad\nname"), Some("bad\u{85}name"),
            Some("bad\u{2028}name"), Some("bad\u{2029}name")] {
            let dir = scratch();
            let spec = reference(&dir);
            let path = dir.join("witness");
            let body: Entry = Arc::new(move || {
                let helper = match name {
                    Some(n) => named(n, || {}),
                    None => traceforge::thread::spawn(|| {}),
                };
                named("v", || {
                    traceforge::send_msg(traceforge::thread::current().id(), 1usize);
                }).join().unwrap();
                helper.join().unwrap();
            });
            let mut args = if online { vec!["online", "--spec", spec.to_str().unwrap()] }
                else { vec!["conf", "--engine", "stateful"] };
            args.extend(["--witness", path.to_str().unwrap()]);
            let (out, code) = cli(body, &args);
            assert_eq!(code, if online { 1 } else { 2 }, "{out}");
            let reason = if name.is_none() { "witness: an unnamed thread cannot be printed" }
                else {
                    "witness: a name or message contains a control character or line separator"
                };
            let diagnostic = if online { format!("FAILED:     {reason}") }
                else { format!("program: conformance: {reason}") };
            assert!(out.lines().any(|l| l == diagnostic), "{out}");
            assert!(!path.exists());
        }
    }
}

#[test]
fn message_controls_and_write_errors_stop() {
    for online in [true, false] {
        for bad_message in [true, false] {
            let dir = scratch();
            let spec = reference(&dir);
            let path = if bad_message { dir.join("w") } else { dir.join("missing/w") };
            let body: Entry = Arc::new(move || {
                named("v", move || {
                    traceforge::send_msg(traceforge::thread::current().id(),
                        if bad_message { "bad\nmessage" } else { "good" });
                }).join().unwrap();
            });
            let mut args = if online { vec!["online", "--spec", spec.to_str().unwrap()] }
                else { vec!["conf", "--engine", "stateful"] };
            args.extend(["--witness", path.to_str().unwrap()]);
            let (out, code) = cli(body, &args);
            assert_eq!(code, if online { 1 } else { 2 }, "{out}");
            let reason = if bad_message {
                concat!("witness: a name or message contains a control character ",
                    "or line separator").to_owned()
            } else {
                let err = std::fs::File::create(path.with_extension("tmp")).unwrap_err();
                format!("witness: {}: {err}", path.display())
            };
            let diagnostic = if online { format!("FAILED:     {reason}") }
                else { format!("program: conformance: {reason}") };
            assert!(out.lines().any(|l| l == diagnostic), "{out}");
            assert!(!path.exists());
        }
    }
}

#[test]
fn failed_join_is_a_block_and_main_has_no_end() {
    let dir = scratch();
    let spec = reference(&dir);
    let path = dir.join("w");
    let body: Entry = Arc::new(|| {
        named("v", || { let _ = traceforge::recv_msg_block::<usize>(); }).join().unwrap();
    });
    let (out, code) = cli(body, &["online", "--spec", spec.to_str().unwrap(),
        "--witness", path.to_str().unwrap()]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(std::fs::read_to_string(path).unwrap(), concat!(
        "uncovered summary (iteration 1): ",
        "{\"statuses\":{\"v\":\"blocked\"},\"words\":{\"v\":[]},\"counts\":[]}\n",
        "thread \"main\"[tid=0]:\n\t(0, 0): BEGIN\n",
        "\t(0, 1): TCREATE(1:\"v\")\n\t(0, 2): BLK\n",
        "thread \"v\"[tid=1]:\n\t(1, 0): BEGIN\n\t(1, 1): BLK\n"
    ));
}

#[test]
fn iteration_counts_covered_completions_too() {
    for online in [true, false] {
        let dir = scratch();
        let spec_path = dir.join("spec");
        let path = dir.join("w");
        let p = Program {
            visible: &|_| vec!["v".to_owned()],
            spec: &|_| Arc::new(|| {
                named("v", || {
                    traceforge::send_msg(traceforge::thread::current().id(), 0usize);
                }).join().unwrap();
            }),
            imp: &|_| Arc::new(|| {
                named("v", || {
                    let value = (0..2).nondet();
                    traceforge::send_msg(traceforge::thread::current().id(), value);
                }).join().unwrap();
            }),
        };
        let run = |args: &[&str]| {
            run_cli(&p, &args.iter().map(|s| s.to_string()).collect::<Vec<_>>())
        };
        assert_eq!(run(&["export", "spec", "--out", spec_path.to_str().unwrap()]).1, 0);
        let mut args = if online { vec!["online", "--spec", spec_path.to_str().unwrap()] }
            else { vec!["conf", "--engine", "stateful"] };
        args.extend(["--witness", path.to_str().unwrap()]);
        let (out, code) = run(&args);
        assert_eq!(code, if online { 0 } else { 1 }, "{out}");
        assert!(std::fs::read_to_string(&path).unwrap()
            .starts_with("uncovered summary (iteration 2): "));
        if online { assert!(out.contains("first_miss_iteration: 2\n")); }
    }
}

// Normalize only named wall-clock and peak-RSS values; retain field names and order.
fn stable_output(out: &str) -> String {
    const VOLATILE: &[&str] = &[
        "wall_ms", "explore_ms", "summarise_ms", "index_ms", "lookup_ms", "export_ms",
        "peak_rss_kb", "first_miss_wall_ms", "join_ms", "spec_phase_ms", "impl_phase_ms",
        "explore_spec_ms", "explore_impl_ms", "precheck_ms", "merge_ms",
    ];
    out.lines().map(|line| {
        let key = line.split(':').next().unwrap_or("").trim();
        if VOLATILE.contains(&key) { format!("{key}: <volatile>") }
        else if line.starts_with("first miss:") {
            // Preserve the completion count while excluding its human-readable wall time.
            line.rsplit_once(',').map_or("first miss: <volatile>".to_owned(),
                |(prefix, _)| format!("{prefix}, <volatile>"))
        } else { line.to_owned() }
    }).collect::<Vec<_>>().join("\n")
}

#[test]
fn absent_option_does_no_witness_work() {
    let dir = scratch();
    let spec = reference(&dir);
    let path = dir.join("w");
    let args = ["online", "--spec", spec.to_str().unwrap(), "--seed", "0"];
    // The otherwise valid run cannot be rendered as a witness.
    let body: Entry = Arc::new(|| {
        traceforge::thread::spawn(|| {}).join().unwrap();
        named("v", || {}).join().unwrap();
    });
    let before = std::fs::read_dir(&dir).unwrap().count();
    let (a, ac) = cli(body.clone(), &args);
    let (b, bc) = cli(body, &args);
    assert_eq!(ac, 0, "{a}");
    assert_eq!(ac, bc);
    assert_eq!(stable_output(&a).as_bytes(), stable_output(&b).as_bytes());
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), before);
    assert!(!path.exists());
    let miss: Entry = Arc::new(|| {
        traceforge::thread::spawn(|| {}).join().unwrap();
        named("v", || {
            traceforge::send_msg(traceforge::thread::current().id(), 1usize);
        }).join().unwrap();
    });
    let (miss_out, miss_code) = cli(miss, &args);
    assert_eq!(miss_code, 0, "{miss_out}");
    assert!(miss_out.contains("verdict:    reports\n"));
    assert!(!path.exists());
    // Covered graphs are not rendered even when a destination was requested.
    let mut with = args.to_vec();
    with.extend(["--witness", path.to_str().unwrap()]);
    let covered: Entry = Arc::new(|| {
        traceforge::thread::spawn(|| {}).join().unwrap();
        named("v", || {}).join().unwrap();
    });
    let (c, cc) = cli(covered, &with);
    assert_eq!(cc, ac, "{c}");
    assert_eq!(stable_output(&a).as_bytes(), stable_output(&c).as_bytes());
    assert!(!path.exists());
}

#[test]
fn conf_join_refuses_witness_option() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_conf-join"))
        .args(["--witness", "w", "spec", "impl"]).output().unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(String::from_utf8(out.stderr).unwrap(),
        "usage: conf-join [--merge] [--decide [--decide-budget N]] spec.jsonl impl.jsonl\n");
    assert!(out.stdout.is_empty());
}

// Mutants: publish despite refusal; skip staging cleanup; write directly to the destination.
#[test]
fn runtime_refusals_discard_staged_witnesses() {
    for kind in ["visible", "daemon", "undeclared"] {
        for directory in [false, true] {
            for existing in [false, true] {
                let mut saw_prior_miss = false;
                for orientation in [false, true] {
                    let dir = scratch();
                    let spec = dir.join("spec");
                    std::fs::write(&spec, concat!(
                        "{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",",
                        "\"program\":\"witness\",\"size\":\"1\",\"visible\":[\"v\"],",
                        "\"roles\":[\"v\"],\"model\":\"p2p\",",
                        "\"enumeration\":\"complete\",\"encoding\":1}\n"
                    )).unwrap();
                    let target = dir.join("w");
                    let destination = if directory { target.join("witness-1.txt") }
                        else { target.clone() };
                    if existing {
                        if directory {
                            std::fs::create_dir(&target).unwrap();
                            std::fs::write(target.join("other"), b"unrelated\n").unwrap();
                            std::fs::write(target.join("witness-2.txt"), b"older\n").unwrap();
                        }
                        std::fs::write(&destination, b"sentinel\n").unwrap();
                    }
                    let path = format!("{}{}", target.display(), if directory { "/" } else { "" });
                    let body: Entry = Arc::new(move || {
                        if traceforge::nondet() != orientation {
                            if kind != "visible" { named("helper", || {}); }
                            named("v", || {}).join().unwrap();
                        } else if kind == "visible" {
                            traceforge::thread::Builder::new().name("v".to_owned())
                                .spawn_daemon(|| {}).unwrap();
                        } else {
                            let helper = if kind == "daemon" {
                                traceforge::thread::Builder::new().name("helper".to_owned())
                                    .spawn_daemon(|| {}).unwrap()
                            } else { named("helper", || {}) };
                            let id = helper.thread().id();
                            named("v", move || {
                                traceforge::send_msg(traceforge::thread::current().id(), id);
                            }).join().unwrap();
                        }
                    });
                    let (out, code) = cli(body, &["online", "--spec", spec.to_str().unwrap(),
                        "--witness", &path, "--seed", "0"]);
                    let reason = match kind {
                        "visible" => "declared visible name is a daemon: \"v\"".to_owned(),
                        _ => format!(
                            "a value of type `traceforge::thread::ThreadId` holds a thread \
                             identity without a role name: {}",
                            if kind == "daemon" { "thread t1 is a daemon" }
                            else { "thread t1 named `helper` is not declared payload-nameable" },
                        ),
                    };
                    assert_eq!(code, 2, "{out}");
                    assert!(out.lines().any(|l| l == format!("FAILED:     {reason}")), "{out}");
                    assert_eq!(out.lines().filter(|l| l.starts_with("verdict:"))
                        .collect::<Vec<_>>(), ["verdict:    refused"], "{out}");
                    saw_prior_miss |= out.lines().any(|l| l.starts_with("first miss:"));
                    if existing {
                        assert_eq!(std::fs::read(&destination).unwrap(), b"sentinel\n");
                        if directory {
                            assert_eq!(std::fs::read(target.join("other")).unwrap(),
                                b"unrelated\n");
                            assert_eq!(std::fs::read(target.join("witness-2.txt")).unwrap(),
                                b"older\n");
                            assert_eq!(std::fs::read_dir(&target).unwrap().count(), 3);
                        }
                    } else {
                        assert!(!target.exists());
                    }
                    assert_eq!(std::fs::read_dir(&dir).unwrap().count(),
                        if existing { 2 } else { 1 });
                }
                assert!(saw_prior_miss, "a valid miss must precede refusal: {kind}");
            }
        }
    }
}

// Mutant: construct a stateful witness writer when the option is absent.
#[test]
fn absent_option_stateful_does_no_witness_work() {
    let dir = scratch();
    let path = dir.join("w");
    let body: Entry = Arc::new(|| {
        traceforge::thread::spawn(|| {}).join().unwrap();
        named("v", || {
            traceforge::send_msg(traceforge::thread::current().id(), 1usize);
        }).join().unwrap();
    });
    let args = ["conf", "--engine", "stateful", "--seed", "0"];
    let (a, ac) = cli(body.clone(), &args);
    let (b, bc) = cli(body.clone(), &args);
    assert_eq!((ac, bc), (1, 1), "{a}\n{b}");
    assert!(a.contains("--- measurements\n"), "{a}");
    assert_eq!(stable_output(&a).as_bytes(), stable_output(&b).as_bytes());
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 0);
    let mut with = args.to_vec();
    with.extend(["--witness", path.to_str().unwrap()]);
    let (out, code) = cli(body, &with);
    assert_eq!(code, 2, "{out}");
    assert!(out.lines().any(|l|
        l == "program: conformance: witness: an unnamed thread cannot be printed"), "{out}");
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 0);
}

// Mutant: discard the finish error in either CLI path.
#[test]
fn publication_errors_keep_cli_error_exits_and_clean_staging() {
    for online in [true, false] {
        for directory in [false, true] {
            let dir = scratch();
            let spec = reference(&dir);
            let target = dir.join("w");
            let destination = if directory { target.join("witness-1.txt") }
                else { target.clone() };
            std::fs::create_dir_all(&destination).unwrap();
            let probe = dir.join("probe");
            std::fs::write(&probe, b"probe").unwrap();
            let error = std::fs::rename(&probe, &destination).unwrap_err();
            std::fs::remove_file(probe).unwrap();
            let path = format!("{}{}", target.display(), if directory { "/" } else { "" });
            let mut args = if online { vec!["online", "--spec", spec.to_str().unwrap()] }
                else { vec!["conf", "--engine", "stateful"] };
            args.extend(["--witness", &path]);
            let (out, code) = cli(Arc::new(fixture), &args);
            assert_eq!(code, if online { 1 } else { 2 }, "{out}");
            let reason = format!("witness: {}: {error}", destination.display());
            let diagnostic = if online { format!("FAILED:     {reason}") }
                else { format!("program: conformance: {reason}") };
            assert!(out.lines().any(|l| l == diagnostic), "{out}");
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 2);
            assert_eq!(std::fs::read_dir(&target).unwrap().count(), usize::from(directory));
            assert_eq!(std::fs::read_dir(&destination).unwrap().count(), 0);
        }
    }
}
