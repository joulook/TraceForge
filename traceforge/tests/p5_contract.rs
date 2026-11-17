//! Contract refusals through the public CLI and the conf-join executable.
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use traceforge::program::{run_cli, Entry, Program};

fn scratch() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let p = std::env::temp_dir().join(format!(
        "tf-p5-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&p).unwrap();
    p
}

fn header(model: &str) -> String {
    format!(
        "{{\"format\":1,\"tool\":\"test\",\"program\":\"p\",\"size\":\"\",\
         \"visible\":[],\"model\":\"{model}\",\"enumeration\":\"complete\",\"encoding\":1}}\n"
    )
}

fn join(spec: &Path, imp: &Path, flags: &[&str]) -> std::process::Output {
    std::process::Command::new(env!("CARGO_BIN_EXE_conf-join"))
        .args(flags).arg(spec).arg(imp).output().unwrap()
}

fn cli(names: &[String], body: Entry, args: &[&str]) -> (String, u8) {
    run_cli(
        &Program {
            visible: &|_| names.to_vec(),
            spec: &|_| Arc::clone(&body),
            imp: &|_| Arc::clone(&body),
        },
        &args.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
    )
}

#[test]
fn model_joins() {
    let dir = scratch();
    let spec = dir.join("s");
    let imp = dir.join("i");
    std::fs::write(&spec, header("p2p")).unwrap();
    for flags in [vec![], vec!["--merge"], vec!["--decide"], vec!["--merge", "--decide"]] {
        std::fs::write(&imp, header("asyn")).unwrap();
        let out = join(&spec, &imp, &flags);
        assert_eq!(out.status.code(), Some(2), "conformance: model exit");
        assert_eq!(String::from_utf8(out.stderr).unwrap(),
            "conf-join: refused: the two models differ: p2p and asyn\n",
            "conformance: model diagnostic");
        std::fs::write(&imp, header("p2p")).unwrap();
        assert_eq!(join(&spec, &imp, &flags).status.code(), Some(0),
            "conformance: same model");
    }
}

#[test]
fn model_online() {
    let dir = scratch();
    let spec = dir.join("s");
    for threads in ["1", "2"] {
        std::fs::write(&spec, header("asyn")).unwrap();
        let args = ["online", "--spec", spec.to_str().unwrap(), "--threads", threads];
        let (text, code) = cli(&[], Arc::new(|| {}), &args);
        assert_eq!(code, 2, "conformance: online model exit");
        assert_eq!(text.lines().next().unwrap(),
            "program: online refused: the two models differ: asyn and p2p",
            "conformance: online model diagnostic");
        std::fs::write(&spec, header("p2p")).unwrap();
        assert_eq!(cli(&[], Arc::new(|| {}), &args).1, 0,
            "conformance: online same model");
    }
}

fn named<F: FnOnce() + Send + 'static>(name: &str, f: F) -> traceforge::thread::JoinHandle<()> {
    traceforge::thread::Builder::new().name(name.to_string()).spawn(f).unwrap()
}

#[test]
fn declared_names() {
    let dir = scratch();
    let spec = dir.join("s");
    let out = dir.join("o");
    let cases = [
        (vec!["v", "v"], "a visible name is declared twice"),
        (vec![""], "invalid declared visible name: \"\""),
        (vec!["main"], "invalid declared visible name: \"main\""),
        (vec!["~v"], "invalid declared visible name: \"~v\""),
        (vec!["é"], "invalid declared visible name: \"é\""),
    ];
    for (names, message) in cases {
        let names: Vec<String> = names.iter().map(|s| s.to_string()).collect();
        for threads in ["1", "2"] {
            for command in ["export", "online"] {
                let args = if command == "export" {
                    vec![command, "impl", "--out", out.to_str().unwrap(), "--threads", threads]
                } else {
                    vec![command, "--spec", spec.to_str().unwrap(), "--threads", threads]
                };
                let (text, code) = cli(&names, Arc::new(|| {}), &args);
                assert_eq!(code, 2, "conformance: invalid name exit: {text}");
                assert_eq!(text.lines().next().unwrap(),
                    format!("program: {command} refused: {message}"),
                    "conformance: invalid name diagnostic");
                assert!(!out.exists(), "conformance: refused export absent");
            }
        }
    }
}

#[test]
fn daemon_visible() {
    let dir = scratch();
    let spec = dir.join("s");
    let out = dir.join("o");
    let names = vec!["v".to_string()];
    let good: Entry = Arc::new(|| { named("v", || {}).join().unwrap(); });
    assert_eq!(cli(&names, good, &["export", "spec", "--out", spec.to_str().unwrap()]).1,
        0, "conformance: ordinary visible thread");
    let daemon: Entry = Arc::new(|| {
        traceforge::thread::Builder::new().name("v".to_string())
            .spawn_daemon(|| {}).unwrap();
    });
    for threads in ["1", "2"] {
        let (text, code) = cli(&names, Arc::clone(&daemon), &[
            "export", "impl", "--out", out.to_str().unwrap(), "--threads", threads,
        ]);
        assert_eq!(code, 2, "conformance: daemon export exit: {text}");
        assert_eq!(text.lines().next().unwrap(),
            "program: export refused: declared visible name is a daemon: \"v\"",
            "conformance: daemon export diagnostic");
        let (text, code) = cli(&names, Arc::clone(&daemon), &[
            "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
        ]);
        assert_eq!(code, 1, "conformance: daemon online exit: {text}");
        assert!(text.lines().any(|line| line ==
            "FAILED:     declared visible name is a daemon: \"v\""),
            "conformance: daemon online diagnostic: {text}");
    }
}

// Both choice orientations exercise a refusal after the root's accepted completion,
// independently of which boolean the seeded exploration visits first.
fn runtime_refusal(
    bad: Entry,
    reason: &str,
    run: impl Fn(Entry, &[&str]) -> (String, u8),
) {
    let good: Entry = Arc::new(|| { named("v", || {}).join().unwrap(); });
    runtime_refusal_with_good(bad, good, reason, run);
}

fn runtime_refusal_with_good(
    bad: Entry,
    good: Entry,
    reason: &str,
    run: impl Fn(Entry, &[&str]) -> (String, u8),
) {
    let dir = scratch();
    let spec = dir.join("s");
    let out = dir.join("o");
    let h = header("p2p").replace("\"visible\":[]", "\"visible\":[\"v\"]");
    std::fs::write(&spec, h).unwrap();
    for threads in ["1", "2"] {
        let mut saw_prior_miss = [false; 2];
        for delayed in [None, Some(false), Some(true)] {
            for existing in [false, true] {
                if existing {
                    std::fs::write(&out, b"sentinel\n").unwrap();
                } else if out.exists() {
                    std::fs::remove_file(&out).unwrap();
                }
                let bad = Arc::clone(&bad);
                let good = Arc::clone(&good);
                let body: Entry = Arc::new(move || {
                    if delayed.map_or(true, |b| traceforge::nondet() == b) {
                        bad();
                    } else {
                        good();
                    }
                });
                let (text, code) = run(body, &[
                    "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
                    "--seed", "0", "--out", out.to_str().unwrap(),
                ]);
                assert_eq!(code, 1, "conformance: runtime refusal exit: {text}");
                assert!(text.lines().any(|l| l == format!("FAILED:     {reason}")),
                    "conformance: runtime refusal diagnostic: {text}");
                let verdicts: Vec<_> = text.lines().filter(|l| l.starts_with("verdict:")).collect();
                assert_eq!(verdicts, ["verdict:    refused"],
                    "conformance: runtime refusal has no conformance verdict: {text}");
                saw_prior_miss[usize::from(existing)] |=
                    text.lines().any(|l| l.starts_with("first miss:"));
                if existing {
                    assert_eq!(std::fs::read(&out).unwrap(), b"sentinel\n",
                        "conformance: refused run preserves destination");
                } else {
                    assert!(!out.exists(), "conformance: refused run creates no destination");
                }
            }
        }
        assert!(saw_prior_miss.iter().all(|seen| *seen),
            "conformance: a miss must precede refusal for each destination, threads={threads}");
    }
}

#[test]
fn daemon_visible_runtime_refusal() {
    let bad: Entry = Arc::new(|| {
        traceforge::thread::Builder::new().name("v".to_string())
            .spawn_daemon(|| {}).unwrap();
    });
    runtime_refusal(bad, "declared visible name is a daemon: \"v\"", |body, args| {
        cli(&["v".to_string()], body, args)
    });
}

fn cli_roles(names: &[String], body: Entry, roles: &[&str], args: &[&str]) -> (String, u8) {
    traceforge::program::run_cli_with_payload_names(
        &Program {
            visible: &|_| names.to_vec(),
            spec: &|_| Arc::clone(&body),
            imp: &|_| Arc::clone(&body),
        },
        traceforge::ConsType::FIFO,
        &args.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        &|_| roles.iter().map(|s| s.to_string()).collect(),
    )
}

fn identity(kind: &str, visible_payload: bool) -> Entry {
    let kind = kind.to_string();
    Arc::new(move || {
        let helper = match kind.as_str() {
            "daemon" => traceforge::thread::Builder::new().name("helper".to_string())
                .spawn_daemon(|| {}).unwrap(),
            "unnamed" => traceforge::thread::spawn(|| {}),
            _ => named("helper", || {}),
        };
        let id = if kind == "main" { traceforge::thread::current().id() }
            else { helper.thread().id() };
        let v = named("v", move || {
            if visible_payload {
                let (tx, _rx) = traceforge::channel::Builder::new().build();
                tx.send_msg(id);
            }
        });
        if !visible_payload {
            let (tx, _rx) = traceforge::channel::Builder::new().build();
            tx.send_msg(id);
        }
        v.join().unwrap();
    })
}

#[test]
fn visible_payload_identities() {
    let dir = scratch();
    let spec = dir.join("s");
    let out = dir.join("o");
    let names = vec!["v".to_string()];
    let h = header("p2p").replace("\"visible\":[]", "\"visible\":[\"v\"]");
    std::fs::write(&spec, h).unwrap();
    for (kind, reason) in [
        ("daemon", "thread t1 is a daemon"),
        ("unnamed", "thread t1 has no name"),
        ("helper", "thread t1 named `helper` is not declared payload-nameable"),
    ] {
        let message = format!(
            "a value of type `traceforge::thread::ThreadId` holds a thread identity \
             without a role name: {reason}"
        );
        for threads in ["1", "2"] {
            std::fs::write(&out, b"sentinel\n").unwrap();
            let (text, code) = cli(&names, identity(kind, true), &[
                "export", "impl", "--out", out.to_str().unwrap(), "--threads", threads,
            ]);
            assert_eq!(code, 2, "conformance: payload export exit: {text}");
            assert_eq!(text.lines().next().unwrap(),
                format!("program: export refused: {message}"),
                "conformance: payload export diagnostic");
            assert_eq!(std::fs::read(&out).unwrap(), b"sentinel\n",
                "conformance: payload export preserves destination");
            let (text, code) = cli(&names, identity(kind, true), &[
                "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
            ]);
            assert_eq!(code, 1, "conformance: payload online exit: {text}");
            assert!(text.lines().any(|line| line.ends_with(&message)),
                "conformance: payload online diagnostic: {text}");
        }
    }
    for threads in ["1", "2"] {
        for (kind, visible, roles) in [
            ("daemon", false, vec![]),
            ("helper", true, vec!["helper"]),
            ("main", true, vec![]),
        ] {
            let args = ["export", "spec", "--out", out.to_str().unwrap(), "--threads", threads];
            let (text, code) = cli_roles(&names, identity(kind, visible), &roles, &args);
            assert_eq!(code, 0, "conformance: payload neighbour: {text}");
            let (text, code) = cli_roles(&names, identity(kind, visible), &roles, &[
                "online", "--spec", out.to_str().unwrap(), "--threads", threads,
            ]);
            assert_eq!(code, 0, "conformance: payload online neighbour: {text}");
        }
    }
}

#[test]
fn payload_identity_runtime_refusals() {
    for (kind, reason) in [
        ("daemon", "thread t1 is a daemon"),
        ("helper", "thread t1 named `helper` is not declared payload-nameable"),
    ] {
        let message = format!(
            "a value of type `traceforge::thread::ThreadId` holds a thread identity \
             without a role name: {reason}"
        );
        runtime_refusal_with_good(identity(kind, true), identity(kind, false),
            &message, |body, args| {
            cli(&["v".to_string()], body, args)
        });
    }
}

#[test]
fn changing_daemon_payload_refusal() {
    let reason = "a value of type `traceforge::thread::ThreadId` holds a thread identity \
                  without a role name: thread t1 is a daemon";
    runtime_refusal_with_good(identity("daemon", true), identity("helper", false),
        reason, |body, args| cli(&["v".to_string()], body, args));

    let dir = scratch();
    let out = dir.join("o");
    for threads in ["1", "2"] {
        for orientation in [false, true] {
            for existing in [false, true] {
                if existing {
                    std::fs::write(&out, b"sentinel\n").unwrap();
                } else if out.exists() {
                    std::fs::remove_file(&out).unwrap();
                }
                let body: Entry = Arc::new(move || {
                    if traceforge::nondet() == orientation {
                        identity("daemon", true)();
                    } else {
                        identity("helper", false)();
                    }
                });
                let (text, code) = cli(&["v".to_string()], body, &[
                    "export", "impl", "--out", out.to_str().unwrap(), "--threads", threads,
                    "--seed", "0",
                ]);
                assert_eq!(code, 2, "conformance: changing daemon export exit: {text}");
                assert_eq!(text.lines().next().unwrap(),
                    format!("program: export refused: {reason}"),
                    "conformance: changing daemon export diagnostic");
                if existing {
                    assert_eq!(std::fs::read(&out).unwrap(), b"sentinel\n",
                        "conformance: changing daemon preserves destination");
                } else {
                    assert!(!out.exists(), "conformance: changing daemon creates no destination");
                }
            }
        }
    }
}

#[test]
fn changing_daemon_invisible_payload() {
    let dir = scratch();
    let out = dir.join("o");
    let mut expected = None;
    for threads in ["1", "2"] {
        for orientation in [false, true] {
            for existing in [false, true] {
                if existing {
                    std::fs::write(&out, b"sentinel\n").unwrap();
                } else if out.exists() {
                    std::fs::remove_file(&out).unwrap();
                }
                let body: Entry = Arc::new(move || {
                    if traceforge::nondet() == orientation {
                        identity("helper", true)();
                    } else {
                        identity("daemon", false)();
                    }
                });
                let (text, code) = cli_roles(&["v".to_string()], Arc::clone(&body),
                    &["helper"], &[
                    "export", "spec", "--out", out.to_str().unwrap(), "--threads", threads,
                    "--seed", "0",
                ]);
                assert_eq!(code, 0, "conformance: invisible daemon export exit: {text}");
                let exported = std::fs::read_to_string(&out).unwrap();
                assert_eq!(exported.lines().count(), 3,
                    "conformance: both visible words exported");
                assert!(exported.contains("{\"s\":\"helper\"}"),
                    "conformance: declared helper payload");
                if let Some(ref expected) = expected {
                    assert_eq!(&exported, expected, "conformance: export independent of order");
                } else {
                    expected = Some(exported);
                }
                let (text, code) = cli_roles(&["v".to_string()], body, &["helper"], &[
                    "online", "--spec", out.to_str().unwrap(), "--threads", threads,
                    "--seed", "0",
                ]);
                assert_eq!(code, 0, "conformance: invisible daemon online exit: {text}");
                let verdicts: Vec<_> = text.lines().filter(|l| l.starts_with("verdict:")).collect();
                assert_eq!(verdicts, ["verdict:    conforms"],
                    "conformance: invisible daemon online verdict");
                assert!(!text.contains("FAILED:"), "conformance: invisible daemon no diagnostic");
            }
        }
    }
}

// The reserved Debug shape exercises the encoder's unknown-identity case.
#[derive(Clone, Debug, PartialEq)]
struct ThreadId {
    opaque_id: u32,
}

#[test]
fn legacy_identities_keep_aborted_output() {
    let dir = scratch();
    let spec = dir.join("s");
    let out = dir.join("o");
    let h = header("p2p").replace("\"visible\":[]", "\"visible\":[\"v\"]");
    std::fs::write(&spec, h).unwrap();
    for threads in ["1", "2"] {
        for kind in ["unknown", "unnamed", "helper"] {
            let unknown = kind == "unknown";
            let legacy = kind != "helper";
            let mut saw_prior_miss = [false; 2];
            for delayed in [None, Some(false), Some(true)] {
                for existing in [false, true] {
                    if existing {
                        std::fs::write(&out, b"sentinel\n").unwrap();
                    } else if out.exists() {
                        std::fs::remove_file(&out).unwrap();
                    }
                    let body: Entry = Arc::new(move || {
                        let bad = delayed.map_or(true, |b| traceforge::nondet() == b);
                        if unknown {
                            named("v", move || {
                                if bad {
                                    let (tx, _rx) = traceforge::channel::Builder::new().build();
                                    tx.send_msg(ThreadId { opaque_id: 99 });
                                }
                            }).join().unwrap();
                        } else {
                            identity(kind, bad)();
                        }
                    });
                    let (text, code) = cli(&["v".to_string()], body, &[
                        "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
                        "--seed", "0", "--out", out.to_str().unwrap(),
                    ]);
                    assert_eq!(code, 1, "conformance: identity failure exit: {text}");
                    let prior_miss = text.lines().any(|l| l.starts_with("first miss:"));
                    let verdict = if !legacy { "refused" }
                        else if prior_miss { "reports" } else { "partial" };
                    let verdicts: Vec<_> = text.lines()
                        .filter(|l| l.starts_with("verdict:")).collect();
                    assert_eq!(verdicts, [format!("verdict:    {verdict}")],
                        "conformance: identity failure verdict: {text}");
                    let ty = if unknown { std::any::type_name::<ThreadId>() }
                        else { "traceforge::thread::ThreadId" };
                    let reason = if kind == "unnamed" {
                        "thread t1 has no name"
                    } else if !unknown {
                        "thread t1 named `helper` is not declared payload-nameable"
                    } else if threads == "1" { "t99 is not a thread of the run" }
                        else { "t99 is not a thread of this graph" };
                    let failed = format!(
                        "FAILED:     a value of type `{ty}` holds a thread identity \
                         without a role name: {reason}"
                    );
                    assert!(text.lines().any(|l| l == failed),
                        "conformance: identity failure diagnostic: {text}");
                    if legacy {
                        saw_prior_miss[usize::from(existing)] |= prior_miss;
                        let output = std::fs::read_to_string(&out).unwrap();
                        let lines: Vec<_> = output.lines().collect();
                        let head: serde_json::Value = serde_json::from_str(lines[0]).unwrap();
                        assert_eq!(head["enumeration"], "aborted",
                            "conformance: legacy identity writes aborted header");
                        assert_eq!(lines.len(), if prior_miss { 2 } else { 1 },
                            "conformance: legacy identity retains earlier summaries");
                    } else if existing {
                        assert_eq!(std::fs::read(&out).unwrap(), b"sentinel\n",
                            "conformance: undeclared identity preserves destination");
                    } else {
                        assert!(!out.exists(), "conformance: undeclared identity omits output");
                    }
                }
            }
            if legacy {
                assert!(saw_prior_miss.into_iter().all(|seen| seen),
                    "conformance: {kind} follows a miss for both destinations, threads={threads}");
            }
        }
    }
}
