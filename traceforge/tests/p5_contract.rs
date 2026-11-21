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
            concat!("conf-join: pairing: C3: the two models differ: p2p and asyn\n",
                "conf-join: refused: the pairing check failed (1 checks; --no-pairing-check skips it)\n"),
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
        assert_eq!(code, 2, "conformance: daemon online exit: {text}");
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
                assert_eq!(code, 2, "conformance: runtime refusal exit: {text}");
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
            assert_eq!(code, if kind == "unnamed" { 1 } else { 2 },
                "conformance: payload online exit: {text}");
            assert!(text.lines().any(|line| line == format!("FAILED:     {message}")),
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

/// A minor-1 header in the writers' key order: `minor` after `format`, `roles` after `visible`
/// (the reader accepts no other order).
fn minor_one(roles: &str) -> String {
    header("p2p").replace("\"format\":1", "\"format\":1,\"minor\":1")
        .replace("\"visible\":[]", &format!("\"visible\":[],\"roles\":{roles}"))
}

#[test]
fn roles_joins_and_online() {
    let dir = scratch();
    let spec = dir.join("s");
    let imp = dir.join("i");
    std::fs::write(&spec, minor_one("[\"helper\"]")).unwrap();
    std::fs::write(&imp, minor_one("[]")).unwrap();
    for flags in [vec![], vec!["--merge"], vec!["--decide"], vec!["--merge", "--decide"]] {
        let out = join(&spec, &imp, &flags);
        assert_eq!(out.status.code(), Some(2), "conformance: roles join exit");
        assert_eq!(String::from_utf8(out.stderr).unwrap(),
            concat!("conf-join: pairing: C2: the two `roles` lists differ: [\"helper\"] and []\n",
                "conf-join: refused: the pairing check failed (1 checks; --no-pairing-check skips it)\n"),
            "conformance: roles join diagnostic");
    }
    std::fs::write(&imp, minor_one("[\"helper\"]")).unwrap();
    for flags in [vec![], vec!["--merge"], vec!["--decide"], vec!["--merge", "--decide"]] {
        let out = join(&spec, &imp, &flags);
        assert_eq!(out.status.code(), Some(0), "conformance: same roles join");
        assert!(out.stderr.is_empty(), "conformance: minor-1 joins need no warning");
    }
    for threads in ["1", "2"] {
        let (text, code) = cli(&[], Arc::new(|| {}), &[
            "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
        ]);
        assert_eq!(code, 2, "conformance: roles online exit");
        assert_eq!(text.lines().next().unwrap(),
            "program: online refused: the two roles lists differ: [\"helper\"] and []",
            "conformance: roles online diagnostic");
        let (text, code) = cli_roles(&[], Arc::new(|| {}), &["helper"], &[
            "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
        ]);
        assert_eq!(code, 0, "conformance: roles online neighbour: {text}");
    }
}

#[test]
fn malformed_roles() {
    let dir = scratch();
    let spec = dir.join("s");
    let imp = dir.join("i");
    std::fs::write(&imp, minor_one("[]")).unwrap();
    let mut cases = vec![
        (minor_one("null"), "the minor-1 header has no `roles` list".to_string()),
        (minor_one("\"v\""), "the minor-1 header has no `roles` list".to_string()),
        (minor_one("{}"), "the minor-1 header has no `roles` list".to_string()),
        (minor_one("[3]"), "a `roles` name is not a string".to_string()),
        (minor_one("[\"b\",\"a\"]"),
            "the header's `roles` list is not sorted and unique".to_string()),
        (minor_one("[\"a\",\"a\"]"),
            "the header's `roles` list is not sorted and unique".to_string()),
        (minor_one("[]").replace("\"visible\":[]", "\"visible\":[\"v\"]"),
            "the header's `roles` list omits a visible name".to_string()),
        // `minor` without `roles`: the reader's header-form check names the pair.
        (header("p2p").replace("\"format\":1", "\"format\":1,\"minor\":1"),
            "the header has `roles` without `minor` or `minor` without `roles`".to_string()),
    ];
    for name in ["", "main", "~a", "é"] {
        cases.push((minor_one(&format!("[{name:?}]")),
            format!("invalid declared role name: {name:?}")));
    }
    for minor in ["2", "-1", "null", "\"1\"", "1.5"] {
        cases.push((minor_one("[]").replace("\"minor\":1", &format!("\"minor\":{minor}")),
            "unsupported header `minor` (expected 1, or no `minor` for minor 0)".to_string()));
    }
    for (header, reason) in cases {
        std::fs::write(&spec, header).unwrap();
        for flags in [vec![], vec!["--merge"]] {
            let out = join(&spec, &imp, &flags);
            assert_eq!(out.status.code(), Some(2), "conformance: malformed roles exit");
            assert_eq!(String::from_utf8(out.stderr).unwrap(),
                format!("conf-join: refused: {}: line 1: {reason}\n", spec.display()),
                "conformance: malformed roles diagnostic");
        }
    }
}

#[test]
fn header_bytes_and_declared_daemon() {
    let dir = scratch();
    let spec = dir.join("s");
    let online_out = dir.join("online");
    let names = vec!["v".to_string()];
    for threads in ["1", "2"] {
        let (text, code) = cli_roles(&names, identity("helper", true), &["helper"], &[
            "export", "spec", "--out", spec.to_str().unwrap(), "--threads", threads,
        ]);
        assert_eq!(code, 0, "conformance: header export: {text}");
        let text = std::fs::read_to_string(&spec).unwrap();
        assert_eq!(text.lines().next().unwrap(), concat!(
            "{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:spec\",",
            "\"size\":\"\",\"visible\":[\"v\"],\"roles\":[\"helper\",\"v\"],",
            "\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1}"
        ), "conformance: export header bytes");
        assert!(text.lines().skip(1).any(|l| l.contains("\"s\":\"helper\"")),
            "conformance: declared identity encoded");
        let (text, code) = cli_roles(&names, identity("helper", true), &["helper"], &[
            "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
            "--out", online_out.to_str().unwrap(),
        ]);
        assert_eq!(code, 0, "conformance: online header: {text}");
        let text = std::fs::read_to_string(&online_out).unwrap();
        assert_eq!(text.lines().next().unwrap(), concat!(
            "{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:impl\",",
            "\"size\":\"\",\"visible\":[\"v\"],\"roles\":[\"helper\",\"v\"],",
            "\"model\":\"p2p\",\"enumeration\":\"complete\",\"first_miss_iteration\":0,",
            "\"first_miss_wall_ms\":0,\"uncovered_total\":0,\"encoding\":1}"
        ), "conformance: online header bytes");
        for command in ["export", "online"] {
            let before = std::fs::read(&online_out).unwrap();
            let args = if command == "export" {
                vec![command, "impl", "--out", online_out.to_str().unwrap(), "--threads", threads]
            } else {
                vec![command, "--spec", spec.to_str().unwrap(), "--threads", threads,
                    "--out", online_out.to_str().unwrap()]
            };
            let (text, code) = cli_roles(&names, identity("daemon", false), &["helper"], &args);
            assert_eq!(code, 2,
                "conformance: declared daemon exit: {text}");
            let reason = "declared payload-nameable name is a daemon: \"helper\"";
            let prefix = if command == "export" { "program: export refused: " }
                else { "FAILED:     " };
            assert!(text.lines().any(|l| l == format!("{prefix}{reason}")),
                "conformance: declared daemon diagnostic: {text}");
            assert_eq!(std::fs::read(&online_out).unwrap(), before,
                "conformance: invalid roles never overwrite an export");
        }
    }
}

#[test]
fn unspawned_helper_header_bytes() {
    let dir = scratch();
    let names = vec!["v".to_string()];
    let body: Entry = Arc::new(|| { named("v", || {}).join().unwrap(); });
    for threads in ["1", "2"] {
        let spec = dir.join(format!("spec-{threads}"));
        let online_out = dir.join(format!("online-{threads}"));
        let (text, code) = cli_roles(&names, Arc::clone(&body), &["helper"], &[
            "export", "spec", "--out", spec.to_str().unwrap(), "--threads", threads,
        ]);
        assert_eq!(code, 0, "conformance: unspawned helper export: {text}");
        let text = std::fs::read_to_string(&spec).unwrap();
        assert_eq!(text.split_inclusive('\n').next().unwrap().as_bytes(), concat!(
            "{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:spec\",",
            "\"size\":\"\",\"visible\":[\"v\"],\"roles\":[\"helper\",\"v\"],",
            "\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1}\n"
        ).as_bytes(), "conformance: unspawned helper export header bytes");
        let (text, code) = cli_roles(&names, Arc::clone(&body), &["helper"], &[
            "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
            "--out", online_out.to_str().unwrap(),
        ]);
        assert_eq!(code, 0, "conformance: unspawned helper online: {text}");
        let text = std::fs::read_to_string(&online_out).unwrap();
        assert_eq!(text.split_inclusive('\n').next().unwrap().as_bytes(), concat!(
            "{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:impl\",",
            "\"size\":\"\",\"visible\":[\"v\"],\"roles\":[\"helper\",\"v\"],",
            "\"model\":\"p2p\",\"enumeration\":\"complete\",\"first_miss_iteration\":0,",
            "\"first_miss_wall_ms\":0,\"uncovered_total\":0,\"encoding\":1}\n"
        ).as_bytes(), "conformance: unspawned helper online header bytes");
    }
}

#[test]
fn legacy_online_child() {
    let Ok(spec) = std::env::var("P5_LEGACY_SPEC") else { return; };
    let threads = std::env::var("P5_LEGACY_THREADS").unwrap();
    let (text, code) = cli(
        &[], Arc::new(|| {}), &["online", "--spec", &spec, "--threads", &threads],
    );
    print!("{text}");
    std::process::exit(i32::from(code));
}

#[test]
fn legacy_warning_stays_on_stderr() {
    let dir = scratch();
    let spec = dir.join("s");
    let imp = dir.join("i");
    let warning = "warning: roles were not compared (minor-0 header)\n";
    for flags in [vec![], vec!["--merge"], vec!["--decide"], vec!["--merge", "--decide"]] {
        for (s, i) in [(header("p2p"), header("p2p")),
            (header("p2p"), minor_one("[\"helper\"]")),
            (minor_one("[\"helper\"]"), header("p2p"))] {
            std::fs::write(&spec, s).unwrap();
            std::fs::write(&imp, i).unwrap();
            let out = join(&spec, &imp, &flags);
            assert_eq!(out.status.code(), Some(0), "conformance: legacy exit");
            assert_eq!(String::from_utf8(out.stderr).unwrap(), warning,
                "conformance: legacy stderr");
            let stdout = String::from_utf8(out.stdout).unwrap();
            let mut expected = concat!(
                "spec: tool=test program=p size= model=p2p enumeration=complete\n",
                "impl: tool=test program=p size= model=p2p enumeration=complete\n",
                "verdict: conforms\n"
            ).to_string();
            if flags.contains(&"--merge") {
                expected.push_str("merge: spec_groups=0 impl_lines=0 max_group_lines=0\n");
            }
            expected.push_str("uncovered: 0\n");
            if flags.contains(&"--decide") {
                let ms = stdout.lines().find(|l| l.starts_with("decide: "))
                    .unwrap().split("decide_ms=").nth(1).unwrap();
                ms.parse::<u128>().expect("conformance: a numeric Decide duration");
                expected.push_str(&format!(concat!(
                    "decide: uncovered=0 violations=0 false_alarms=0 unresolved=0 ",
                    "max_group=0 states=0 budget=10000000 decide_ms={}\n"
                ), ms));
            }
            assert_eq!(stdout.split("--- measurements").next().unwrap(), expected,
                "conformance: legacy report bytes");
            assert!(!stdout.contains("warning"), "conformance: warning absent from stdout");
        }
    }
    // Minor 0 is written with no `minor` key; an explicit `"minor":0` is refused by the reader.
    std::fs::write(&spec, header("p2p").replace("\"format\":1", "\"format\":1,\"minor\":0")).unwrap();
    std::fs::write(&imp, header("p2p")).unwrap();
    for flags in [vec![], vec!["--merge"]] {
        let out = join(&spec, &imp, &flags);
        assert_eq!(out.status.code(), Some(2), "conformance: explicit minor 0 exit");
        assert_eq!(String::from_utf8(out.stderr).unwrap(), format!(
            "conf-join: refused: {}: line 1: the header has `\"minor\":0`; a minor-0 header has no `minor` key\n",
            spec.display()), "conformance: explicit minor 0 diagnostic");
    }
    std::fs::write(&spec, header("p2p")).unwrap();
    for threads in ["1", "2"] {
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "legacy_online_child", "--nocapture"])
            .env("P5_LEGACY_SPEC", &spec).env("P5_LEGACY_THREADS", threads)
            .output().unwrap();
        assert_eq!(out.status.code(), Some(0), "conformance: legacy online exit");
        assert_eq!(String::from_utf8(out.stderr).unwrap(), warning,
            "conformance: legacy online stderr");
        assert!(!String::from_utf8(out.stdout).unwrap().contains("warning"),
            "conformance: legacy online stdout");
    }
}

#[test]
fn payload_declarations_are_valid_roles() {
    let dir = scratch();
    let spec = dir.join("s");
    let out = dir.join("o");
    let names = vec!["v".to_string()];
    let body: Entry = Arc::new(|| { named("v", || {}).join().unwrap(); });
    for (roles, reason) in [
        (vec!["helper", "helper"], "a visible name is declared twice"),
        (vec!["v"], "role is declared twice: \"v\""),
        (vec![""], "invalid declared visible name: \"\""),
        (vec!["main"], "invalid declared visible name: \"main\""),
        (vec!["~helper"], "invalid declared visible name: \"~helper\""),
        (vec!["é"], "invalid declared visible name: \"é\""),
    ] {
        for threads in ["1", "2"] {
            for command in ["export", "online"] {
                let args = if command == "export" {
                    vec![command, "spec", "--out", out.to_str().unwrap(), "--threads", threads]
                } else {
                    vec![command, "--spec", spec.to_str().unwrap(), "--threads", threads]
                };
                let (text, code) = cli_roles(&names, Arc::clone(&body), &roles, &args);
                assert_eq!(code, 2, "conformance: payload declaration exit: {text}");
                assert_eq!(text.lines().next().unwrap(),
                    format!("program: {command} refused: {reason}"),
                    "conformance: payload declaration diagnostic");
            }
        }
    }
}

#[test]
fn declared_daemon_runtime_refusal() {
    runtime_refusal_with_good(identity("daemon", false), identity("helper", false),
        "declared payload-nameable name is a daemon: \"helper\"", |body, args| {
            cli_roles(&["v".to_string()], body, &["helper"], args)
        });
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
    runtime_refusal_with_good(identity("daemon", false), identity("helper", true),
        "declared payload-nameable name is a daemon: \"helper\"", |body, args| {
            cli_roles(&["v".to_string()], body, &["helper"], args)
        });
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
                assert_eq!(code, 2, "conformance: declared daemon export exit: {text}");
                assert_eq!(text.lines().next().unwrap(),
                    "program: export refused: declared payload-nameable name is a daemon: \
                     \"helper\"",
                    "conformance: declared daemon diagnostic");
                if existing {
                    assert_eq!(std::fs::read(&out).unwrap(), b"sentinel\n",
                        "conformance: declared daemon preserves destination");
                } else {
                    assert!(!out.exists(), "conformance: declared daemon creates no destination");
                }
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
                    assert_eq!(code, if legacy { 1 } else { 2 },
                        "conformance: identity failure exit: {text}");
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

// Mutants: replace `if self.refused` in exit_code with `if false` or `if true`.
#[test]
fn runtime_refusal_and_assertion_have_distinct_exits() {
    let dir = scratch();
    let spec = dir.join("s");
    let names = vec!["v".to_string()];
    let good: Entry = Arc::new(|| { named("v", || {}).join().unwrap(); });
    let (text, code) = cli(&names, good, &["export", "spec", "--out", spec.to_str().unwrap()]);
    assert_eq!(code, 0, "conformance: valid specification: {text}");
    for threads in ["1", "2"] {
        for refused in [true, false] {
            let body: Entry = Arc::new(move || {
                if refused {
                    traceforge::thread::Builder::new().name("v".to_string())
                        .spawn_daemon(|| {}).unwrap();
                } else {
                    named("v", || traceforge::assert(false)).join().unwrap();
                }
            });
            let (text, code) = cli(&names, body, &[
                "online", "--spec", spec.to_str().unwrap(), "--threads", threads,
            ]);
            assert_eq!(code, if refused { 2 } else { 1 },
                "conformance: distinct failure exits, threads={threads}: {text}");
            let reason = if refused { "declared visible name is a daemon: \"v\"" }
                else { "assertion failure on thread `v`" };
            let failed = format!("FAILED:     {reason}");
            assert!(text.lines().any(|l| if refused { l == failed }
                else { l.starts_with(&format!("{failed} at ")) }),
                "conformance: failure diagnostic: {text}");
            let verdict = if refused { "refused" } else { "partial" };
            assert!(text.lines().any(|l| l == format!("verdict:    {verdict}")),
                "conformance: failure verdict: {text}");
            assert!(text.contains("--- measurements"), "conformance: measurements: {text}");
        }
    }
}
