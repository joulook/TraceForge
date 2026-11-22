//! `online --spec`'s pairing check before the run: the specification file against the program
//! (its visible names, roles and model in the implementation's place; C13 not checked). Failures
//! refuse the run with the rows and one summary line, exit 2, no usage text; warnings go to stderr
//! and the run proceeds; `--no-pairing-check` restores the run's own refusals. Each run is a child
//! process of this test binary, so its stderr is its own.
mod wg_common;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use traceforge::program::{run_cli, Program};
use wg_common::*;

#[derive(Clone, Debug, PartialEq)]
struct Tid(u32);

#[derive(Clone, Debug, PartialEq)]
struct M(u32);

/// `two`: `a` sends 1 or 2 to itself, `b` sends 1 to itself. `three`: also `c`, sending 1.
/// `tid`: `a` sends `Tid(1)`. `tagged`: `a` sends `M(1)`.
fn body(variant: &str) {
    let b = named("b", || traceforge::send_msg(me(), 1usize));
    let a = match variant {
        "tid" => named("a", || traceforge::send_msg(me(), Tid(1))),
        "tagged" => named("a", || traceforge::send_msg(me(), M(1))),
        _ => named("a", || {
            let x = if traceforge::nondet() { 2usize } else { 1 };
            traceforge::send_msg(me(), x)
        }),
    };
    if variant == "three" {
        named("c", || traceforge::send_msg(me(), 1usize)).join().unwrap();
    }
    a.join().unwrap();
    b.join().unwrap();
}

fn program() -> Program<'static> {
    Program {
        visible: &|a| {
            let mut v = vec!["a".to_owned(), "b".to_owned()];
            if a.first().map(String::as_str) == Some("three") {
                v.push("c".to_owned());
            }
            v
        },
        spec: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
        imp: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
    }
}

/// Runs in a child process only (see `wg_common::child`).
#[test]
fn child_process_entry() {
    let Ok(_) = std::env::var("WG_CHILD") else { return };
    let args = std::env::var("WG_ARGS").unwrap();
    let args: Vec<String> = if args.is_empty() { vec![] } else { args.split('\u{1f}').map(str::to_owned).collect() };
    let (text, code) = run_cli(&program(), &args);
    std::fs::write(std::env::var("WG_OUT").unwrap(), text).unwrap();
    std::process::exit(code.into());
}

struct Env {
    dir: PathBuf,
    bin: PathBuf,
}

impl Env {
    fn new(name: &str) -> Env {
        let dir = scratch();
        let bin = child_binary(&dir, name);
        Env { dir, bin }
    }

    /// The CLI's text, the pairing lines of its stderr, and its exit code.
    fn run(&self, args: &[&str]) -> (String, Vec<String>, i32) {
        let (t, e, c) = child(&self.bin, "online-pairing", args);
        let pairing = e.lines().filter(|l| l.starts_with("program: pairing")).map(str::to_owned).collect();
        (t, pairing, c)
    }

    /// The specification file of `variant`, exported.
    fn spec(&self, variant: &str) -> PathBuf {
        let p = self.dir.join(format!("{variant}.spec.jsonl"));
        let (t, _, c) = self.run(&["export", "spec", "--out", p.to_str().unwrap(), "--", variant]);
        assert_eq!(c, 0, "{t}");
        p
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let p = self.dir.join(name);
        std::fs::write(&p, text).unwrap();
        p
    }
}

/// `online --spec <spec>` (with `flags`) on `variant`.
fn online<'a>(spec: &'a Path, variant: &'a str, flags: &[&'a str]) -> Vec<&'a str> {
    let mut a = vec!["online", "--spec", spec.to_str().unwrap(), "--seed", "0"];
    a.extend(flags);
    a.extend(["--", variant]);
    a
}

/// The usage text the CLI appends to its own refusals.
fn usage(env: &Env) -> String {
    let (t, _, c) = env.run(&[]);
    assert_eq!(c, 2);
    t.split_once('\n').unwrap().1.to_owned()
}

/// A text with every measured value masked: the clocks, the memory, the first miss's time.
fn unmeasured(t: &str) -> String {
    t.lines()
        .map(|l| match l.split_once(':') {
            Some((k, _)) if k.ends_with("_ms") || k.contains("rss") || k.starts_with("first miss") => format!("{k}: <m>"),
            _ => l.to_owned(),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn edit(text: &str, old: &str, new: &str) -> String {
    assert_eq!(text.matches(old).count(), 1, "{old} in {text}");
    text.replacen(old, new, 1)
}

const REFUSED_TAIL: &str = "checks; --no-pairing-check skips it)\n";

/// Each failing row: the refusal (rows, then the summary line, exit 2, no usage, no warning),
/// and with `--no-pairing-check` the run's own refusal, as before the check (its text and usage).
#[test]
fn each_failing_row_refuses_the_run_and_the_flag_restores_the_runs_own_refusal() {
    let env = Env::new("tf_online_pairing_rows");
    let spec = env.spec("two");
    let text = std::fs::read_to_string(&spec).unwrap();
    let (head, body) = text.split_once('\n').unwrap();
    let lines: Vec<&str> = body.lines().collect();
    assert_eq!(lines.len(), 2, "two summary lines: {text}");
    let usage = usage(&env);
    let file = |h: &str, ls: &[&str]| format!("{h}\n{}\n", ls.join("\n"));
    let c10 = edit(lines[0], "\"counts\":[", "\"counts\":[2147483648,");
    let c10 = c10.replacen("[2147483648,0,", "[2147483648,", 1).replacen("[2147483648,1,", "[2147483648,", 1);
    // (name, file text, program variant, the pairing rows, the run's own refusal without the check)
    let cases: Vec<(&str, String, &str, Vec<String>, String)> = vec![
        ("visible", text.clone(), "three",
            vec!["C2: the two `visible` lists differ: [\"a\", \"b\"] and [\"a\", \"b\", \"c\"]".into(),
                 "C2: the two `roles` lists differ: [\"a\", \"b\"] and [\"a\", \"b\", \"c\"]".into()],
            "the specification's `visible` list [\"a\", \"b\"] is not the program's [\"a\", \"b\", \"c\"]".into()),
        ("roles", file(&edit(head, "\"roles\":[\"a\",\"b\"]", "\"roles\":[\"a\",\"b\",\"z\"]"), &lines), "two",
            vec!["C2: the two `roles` lists differ: [\"a\", \"b\", \"z\"] and [\"a\", \"b\"]".into()],
            "the two roles lists differ: [\"a\", \"b\", \"z\"] and [\"a\", \"b\"]".into()),
        ("model", file(&edit(head, "\"model\":\"p2p\"", "\"model\":\"asyn\""), &lines), "two",
            vec!["C3: the two models differ: asyn and p2p".into()],
            "the two models differ: asyn and p2p".into()),
        ("bounded", file(&edit(head, "\"enumeration\":\"complete\"", "\"enumeration\":\"bounded\""), &lines), "two",
            vec!["C4: the specification is `bounded`, not `complete`".into()],
            "{S}: the specification is `bounded`, not `complete`".into()),
        ("repeat", file(head, &[lines[0], lines[1], lines[0]]), "two",
            vec!["C6: {S}: line 4 repeats line 2".into()],
            "{S}: line 4: the line repeats line 2 (each line is one distinct summary)".into()),
        ("count", file(head, &[&c10, lines[1]]), "two",
            vec!["C10: {S}: line 2: the count 2147483648 is out of bounds (both readers accept counts up to 2^31-1)".into()],
            "{S}: line 2: a count 2147483648 exceeds the length 1 of `b`'s word".into()),
    ];
    let mut bad = Vec::new();
    for (name, t, variant, rows, own) in &cases {
        let s = env.write(&format!("{name}.jsonl"), t);
        let ss = s.to_str().unwrap();
        let mut want: String = rows.iter().map(|r| format!("program: pairing: {}\n", r.replace("{S}", ss))).collect();
        want.push_str(&format!("program: refused: the pairing check failed ({} {REFUSED_TAIL}", rows.len()));
        let (got, warn, code) = env.run(&online(&s, variant, &[]));
        if (code, got.as_str(), warn.is_empty()) != (2, want.as_str(), true) {
            bad.push(format!("{name}: exit {code} {warn:?}\n{got}--- want\n{want}"));
        }
        let own_want = format!("program: online refused: {}\n{usage}", own.replace("{S}", ss));
        let (got, warn, code) = env.run(&online(&s, variant, &["--no-pairing-check"]));
        if (code, got.as_str(), warn.is_empty()) != (2, own_want.as_str(), true) {
            bad.push(format!("{name} --no-pairing-check: exit {code} {warn:?}\n{got}--- want\n{own_want}"));
        }
        if *name == "model" {
            let (got, warn, code) = env.run(&online(&s, variant, &["--threads", "2"]));
            if (code, got.as_str(), warn.is_empty()) != (2, want.as_str(), true) {
                bad.push(format!("{name} --threads 2: exit {code} {warn:?}\n{got}--- want\n{want}"));
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// A header the reader refuses: the reader's refusal once, exit 2, no warning and no usage; with
/// `--no-pairing-check`, the run's own refusal of the same header, with the usage text.
#[test]
fn a_refused_header_is_one_line() {
    let env = Env::new("tf_online_pairing_header");
    let spec = env.spec("tagged");
    let text = std::fs::read_to_string(&spec).unwrap();
    let s = env.write("header.jsonl", &edit(&text, "\"encoding\":1", "\"x\":1,\"encoding\":1"));
    let refusal = format!("program: online refused: {}: line 1: unknown header key `x` (neither writer emits it)\n", s.display());
    let (got, warn, code) = env.run(&online(&s, "two", &[]));
    assert_eq!((code, got.as_str(), warn), (2, refusal.as_str(), vec![]));
    let (got, warn, code) = env.run(&online(&s, "two", &["--no-pairing-check"]));
    assert_eq!((code, got, warn), (2, format!("{refusal}{}", usage(&env)), vec![]));
}

/// Warnings go to stderr and the run proceeds with the same result as without the check: a value
/// tagged `Tid` (C18) on the specification's line; a tag only the specification sends (no C13
/// warning: the program's tags are not known before the run); a clean file (nothing).
#[test]
fn warnings_go_to_stderr_and_the_run_is_unchanged() {
    let env = Env::new("tf_online_pairing_warn");
    for (spec_variant, run_variant, warnings) in [
        ("tid", "tid", vec![
            "program: pairing: warning: C18: {S}: line 2: a value is tagged \"Tid\", the name of an identity type; \
             if it is a process identity, the programs must send its role name instead".to_owned()]),
        ("tagged", "two", vec![]),
        ("two", "two", vec![]),
    ] {
        let s = env.spec(spec_variant);
        let want: Vec<String> = warnings.iter().map(|w| w.replace("{S}", s.to_str().unwrap())).collect();
        let (t1, w1, c1) = env.run(&online(&s, run_variant, &[]));
        let (t2, w2, c2) = env.run(&online(&s, run_variant, &["--no-pairing-check"]));
        assert_eq!(w1, want, "{spec_variant}/{run_variant}: the warnings");
        assert_eq!(w2, Vec::<String>::new(), "{spec_variant}/{run_variant}: no check, no warning");
        assert_eq!((c1, unmeasured(&t1)), (c2, unmeasured(&t2)), "{spec_variant}/{run_variant}: the run");
        assert_ne!(c1, 2, "{spec_variant}/{run_variant}: the run ran: {t1}");
    }
}

/// `--no-pairing-check` is `online`'s only.
#[test]
fn the_flag_is_refused_outside_online() {
    let env = Env::new("tf_online_pairing_flag");
    let out = env.dir.join("x.jsonl");
    for args in [
        vec!["count", "impl", "--no-pairing-check", "--", "two"],
        vec!["export", "impl", "--out", out.to_str().unwrap(), "--no-pairing-check", "--", "two"],
        vec!["conf", "--no-pairing-check", "--", "two"],
    ] {
        let (t, _, c) = env.run(&args);
        assert_eq!(c, 2, "{args:?}: {t}");
        assert!(t.starts_with("program: --no-pairing-check requires online\n"), "{args:?}: {t}");
    }
}

/// The causal model: `online` runs under it against a `cd` specification as before (the join's
/// supported-model rule is conf-join's only); a `cd` specification against a FIFO run is one C3
/// row, the models' inequality.
#[test]
fn causal_runs_and_a_cd_spec_against_fifo_is_one_row() {
    let env = Env::new("tf_online_pairing_causal");
    let s = env.dir.join("cd.spec.jsonl");
    let (t, _, c) = env.run(&["export", "spec", "--model", "causal", "--out", s.to_str().unwrap(), "--", "two"]);
    assert_eq!(c, 0, "{t}");
    assert!(std::fs::read_to_string(&s).unwrap().contains("\"model\":\"cd\""), "a cd specification");
    let (t, warn, c) = env.run(&online(&s, "two", &["--model", "causal"]));
    assert_eq!((c, warn), (0, vec![]), "online under causal: {t}");
    assert!(t.contains("conforms"), "{t}");
    let (t, warn, c) = env.run(&online(&s, "two", &[]));
    assert_eq!((c, t.as_str(), warn), (2, concat!("program: pairing: C3: the two models differ: cd and p2p\n",
        "program: refused: the pairing check failed (1 checks; --no-pairing-check skips it)\n"), vec![]));
}
