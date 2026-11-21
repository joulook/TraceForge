//! The reader accepts summary files only in the form the writers emit: each line its normal form,
//! optionally with JMC's `"n":N` last; the header compact, its keys in the writers' order, each
//! once, `minor` absent (minor 0) or 1, `roles` exactly with `minor`. One refused file per rule
//! through conf-join, plain and `--merge`; and the writers' own output accepted.
mod wg_common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use traceforge::program::{run_cli, Program};
use wg_common::*;

const HEAD: &str = concat!(r#"{"format":1,"minor":1,"tool":"t","program":"p","size":"1","visible":["A"],"#,
    r#""roles":["A"],"model":"p2p","enumeration":"complete","encoding":1}"#);
/// The normal form of one line: `A` sends `M("A", 1)`.
const LINE: &str = r#"{"statuses":{"A":"done"},"words":{"A":[{"s":{"t":"M","f":["A",1]}}]},"counts":[]}"#;

const LINE_FORM: &str = "the line is not in the form the writers emit (the normal form, then `n` if any; \
    compact, each key once, in order): it differs at byte ";
const HEAD_FORM: &str = "the header is not in the form the writers emit (compact, each key once, in the \
    order format, minor, tool, program, size, visible, roles, model, enumeration, seed, iterations, the \
    online fields, encoding): it differs at byte ";

fn conf_join(args: &[&str]) -> (String, String, i32) {
    let out = {
        let _r = spawn_guard();
        Command::new(env!("CARGO_BIN_EXE_conf-join")).args(args).output().unwrap()
    };
    let r = (String::from_utf8(out.stdout).unwrap(), String::from_utf8(out.stderr).unwrap(),
        out.status.code().unwrap_or(-1));
    println!("conf-join {args:?}: exit {}\n--- stdout\n{}--- stderr\n{}---", r.2, r.0, r.1);
    r
}

fn write(dir: &Path, name: &str, text: &str) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, text).unwrap();
    p
}

/// One refused spec file: its text, the refused line's number and the reason. The pairing
/// check passes on it (apart from warnings), except where `pairing` gives its own refusal.
struct Bad {
    name: &'static str,
    text: String,
    line: usize,
    what: String,
    /// The pairing check's own failure line, when it refuses first (plain, `--merge`).
    pairing: Option<(&'static str, &'static str)>,
}

fn bads() -> Vec<Bad> {
    let file = |lines: &[&str]| format!("{HEAD}\n{}\n", lines.join("\n"));
    let head = |h: String| format!("{h}\n{LINE}\n");
    let b = |name, text, line, what: String| Bad { name, text, line, what, pairing: None };
    vec![
        b("blank-line", format!("{HEAD}\n\n"), 2, "not JSON: EOF while parsing a value at line 1 column 0".into()),
        b("unknown-line-key", file(&[&LINE.replace("\"counts\":[]}", "\"counts\":[],\"x\":1}")]), 2,
            "unknown key `x`".into()),
        b("n-not-last", file(&[&format!("{{\"n\":1,{}", &LINE[1..])]), 2, format!("{LINE_FORM}2")),
        b("n-after-a-space", file(&[&LINE.replace("\"counts\":[]}", "\"counts\":[],\"n\": 5}")]), 2, format!("{LINE_FORM}85")),
        b("space-after-colon", file(&[&LINE.replace("\"statuses\":", "\"statuses\": ")]), 2, format!("{LINE_FORM}12")),
        b("members-reordered",
            file(&[r#"{"words":{"A":[{"s":{"t":"M","f":["A",1]}}]},"statuses":{"A":"done"},"counts":[]}"#]),
            2, format!("{LINE_FORM}2")),
        b("f-before-t", file(&[&LINE.replace(r#"{"t":"M","f":["A",1]}"#, r#"{"f":["A",1],"t":"M"}"#)]), 2,
            format!("{LINE_FORM}46")),
        b("repeated-status-key", file(&[&LINE.replace(r#"{"A":"done"}"#, r#"{"A":"done","A":"done"}"#)]), 2,
            format!("{LINE_FORM}23")),
        b("non-canonical-escape", file(&[&LINE.replace(r#"["A",1]"#, r#"["\u0041",1]"#)]), 2,
            format!("{LINE_FORM}59")),
        Bad { name: "repeated-line", text: file(&[LINE, LINE]), line: 3,
            what: "the line repeats line 2 (each line is one distinct summary)".into(),
            pairing: Some(("line 3 repeats an earlier line", "line 3 repeats line 2")) },
        b("header-unknown-key", head(HEAD.replace("\"encoding\":1", "\"x\":1,\"encoding\":1")), 1,
            "unknown header key `x` (neither writer emits it)".into()),
        b("header-minor-0", head(HEAD.replace("\"minor\":1", "\"minor\":0")), 1,
            "the header has `\"minor\":0`; a minor-0 header has no `minor` key".into()),
        b("header-roles-without-minor", head(HEAD.replace("\"minor\":1,", "")), 1,
            "the header has `roles` without `minor` or `minor` without `roles`".into()),
        b("header-out-of-order", head(HEAD.replace("\"minor\":1,\"tool\":\"t\"", "\"tool\":\"t\",\"minor\":1")), 1,
            format!("{HEAD_FORM}13")),
        b("header-space", head(HEAD.replace("\"format\":1", "\"format\": 1")), 1, format!("{HEAD_FORM}10")),
        // `seed` and `iterations`: integers, and only in a sampled file.
        b("header-seed-complete", head(HEAD.replace("\"enumeration\":\"complete\"", "\"enumeration\":\"complete\",\"seed\":1")), 1,
            "the header has `seed` in a file that is not `sampled`".into()),
        b("header-seed-string", head(HEAD.replace("\"enumeration\":\"complete\"", "\"enumeration\":\"sampled\",\"seed\":\"1\"")), 1,
            "the header's `seed` is \"1\", not an integer".into()),
        b("header-iterations-float", head(HEAD.replace("\"enumeration\":\"complete\"", "\"enumeration\":\"sampled\",\"iterations\":1.5")), 1,
            "the header's `iterations` is 1.5, not an integer".into()),
        // The online fields: all three or none, each an integer.
        b("header-online-one", head(HEAD.replace("\"enumeration\":\"complete\"", "\"enumeration\":\"complete\",\"first_miss_iteration\":3")), 1,
            "the header has some of the online fields (first_miss_iteration, first_miss_wall_ms, uncovered_total) but not all three".into()),
        b("header-online-object", head(HEAD.replace("\"enumeration\":\"complete\"",
            "\"enumeration\":\"complete\",\"first_miss_iteration\":1,\"first_miss_wall_ms\":2,\"uncovered_total\":{}")), 1,
            "the header's `uncovered_total` is {}, not an integer".into()),
        b("header-duplicate-key", head(HEAD.replace("\"model\":\"p2p\"", "\"model\":\"p2p\",\"model\":\"p2p\"")), 1,
            format!("{HEAD_FORM}103")),
    ]
}

#[test]
fn each_rule_refuses_its_file_naming_the_line() {
    let dir = scratch();
    let imp = write(&dir, "imp.jsonl", &format!("{HEAD}\n{LINE}\n"));
    let is = imp.to_str().unwrap();
    let mut bad = Vec::new();
    let cases = bads();
    assert_eq!(cases.len(), 21);
    for c in cases {
        let spec = write(&dir, &format!("{}.jsonl", c.name), &c.text);
        let ss = spec.to_str().unwrap();
        let want = format!("conf-join: refused: {ss}: line {}: {}\n", c.line, c.what);
        for merge in [false, true] {
            let flags: Vec<&str> = if merge { vec!["--merge"] } else { vec![] };
            let mut n = vec!["--no-pairing-check"];
            n.extend(flags.iter());
            n.extend([ss, is]);
            let (o, e, code) = conf_join(&n);
            if (code, e.as_str()) != (2, want.as_str()) || !o.starts_with("--- measurements\n") {
                bad.push(format!("{} merge={merge} --no-pairing-check: exit {code}\n{e}--- want\n{want}", c.name));
            }
            // With the pairing check: its warnings (if any), then the same refusal; or the
            // check's own refusal.
            let mut a = flags.clone();
            a.extend([ss, is]);
            let (_, e2, code2) = conf_join(&a);
            let ok = match &c.pairing {
                None => e2.ends_with(&want) && e2[..e2.len() - want.len()].lines()
                    .all(|l| l.starts_with("conf-join: pairing: warning: ")),
                Some((plain, merged)) => e2 == format!(concat!("conf-join: pairing: C6: {}: {}\n",
                    "conf-join: refused: the pairing check failed (1 checks; --no-pairing-check skips it)\n"),
                    ss, if merge { merged } else { plain }),
            };
            if code2 != 2 || !ok {
                bad.push(format!("{} merge={merge} with the pairing check: exit {code2}\n{e2}", c.name));
            }
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// `n` is information only: any value in last position is in writer form, and a value other than a
/// positive integer empties `uncovered_total` instead of refusing the line.
#[test]
fn any_n_in_last_position_is_accepted() {
    let dir = scratch();
    let spec = write(&dir, "spec.jsonl", &format!("{HEAD}\n"));
    let ss = spec.to_str().unwrap();
    for (name, n, total) in [("zero", "0", ""), ("minus", "-1", ""), ("string", "\"x\"", ""),
        // Numbers with no exact u64 reading: compared by their own text, accepted, the total empty.
        ("two-to-64", "18446744073709551616", ""), ("1e3", "1e3", ""),
        // Raw text with a space only inside a JSON string, and a nested value: kept as spelt.
        ("spaced-string", "\"a A\"", ""), ("nested", "{\"a b\":18446744073709551616}", ""),
        ("five", "5", "5")] {
        let imp = write(&dir, &format!("{name}.jsonl"),
            &format!("{HEAD}\n{},\"n\":{n}}}\n", &LINE[..LINE.len() - 1]));
        for merge in [false, true] {
            for check in [false, true] {
                let mut a: Vec<&str> = if merge { vec!["--merge"] } else { vec![] };
                if !check { a.push("--no-pairing-check"); }
                a.extend([ss, imp.to_str().unwrap()]);
                let (o, e, code) = conf_join(&a);
                // The pairing check warns that `M` is sent only by the implementation (the spec
                // file has no lines).
                let warn = if check { concat!("conf-join: pairing: warning: C13: the tag \"M\" (arities {2}) occurs ",
                    "only in the implementation; the join reports the lines that carry it as uncovered\n") } else { "" };
                assert_eq!((code, e.as_str()), (1, warn), "{name} {a:?}");
                assert!(o.contains("verdict: violation\n"), "{name}: {o}");
                assert!(o.lines().any(|l| l == format!("uncovered_total: {total}")), "{name}: {o}");
            }
        }
    }
}

/// Headers in the writers' form with the optional fields: a sampled file with a negative seed,
/// and the online fields at -1 (as JMC writes them when a split run has no first miss).
#[test]
fn optional_header_fields_are_accepted() {
    let dir = scratch();
    let spec = write(&dir, "spec.jsonl", &format!("{HEAD}\n{LINE}\n"));
    for (name, h, verdict) in [
        ("sampled", HEAD.replace("\"enumeration\":\"complete\"", "\"enumeration\":\"sampled\",\"seed\":-5,\"iterations\":3"),
            "verdict: no verdict (sampled)\n"),
        ("online", HEAD.replace("\"enumeration\":\"complete\"",
            "\"enumeration\":\"complete\",\"first_miss_iteration\":-1,\"first_miss_wall_ms\":-1,\"uncovered_total\":-1"),
            "verdict: conforms\n"),
    ] {
        assert_ne!(h, HEAD, "{name}");
        let imp = write(&dir, &format!("{name}.jsonl"), &format!("{h}\n{LINE}\n"));
        for merge in [false, true] {
            let mut a: Vec<&str> = if merge { vec!["--merge"] } else { vec![] };
            a.extend([spec.to_str().unwrap(), imp.to_str().unwrap()]);
            let (o, e, code) = conf_join(&a);
            assert_eq!((code, e.as_str()), (0, ""), "{name} merge={merge}");
            assert!(o.contains(verdict), "{name} merge={merge}: {o}");
        }
    }
}

// ------------------------------------------------------------------ the writers' own output --

/// `daavar/format/golden/A2Store-pb-2-1.must.jsonl` (JMC, minor 0, complete), verbatim.
const JMC_PB: &str = concat!(
    r#"{"format":1,"tool":"jmc","program":"a2-pb-k2q1","size":"k2q1","visible":["c0","c1"],"model":"p2p","enumeration":"complete","encoding":1}"#, "\n",
    r#"{"statuses":{"c0":"done","c1":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}}],"c1":[{"s":{"t":"Get","f":[1,0]}},{"r":{"t":"Val","f":[0]}}]},"counts":[0,0,0,1],"n":1}"#, "\n",
    r#"{"statuses":{"c0":"done","c1":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}}],"c1":[{"s":{"t":"Get","f":[1,0]}},{"r":{"t":"None","f":[]}}]},"counts":[0,1,0,0],"n":1}"#, "\n",
);
/// `daavar/format/golden/A2Store-early-ack-1-2.must.jsonl`, verbatim.
const JMC_EA_MUST: &str = concat!(
    r#"{"format":1,"tool":"jmc","program":"a2-early-ack-k1q2","size":"k1q2","visible":["c0"],"model":"p2p","enumeration":"complete","encoding":1}"#, "\n",
    r#"{"statuses":{"c0":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}},{"s":{"t":"Get","f":[0,0]}},{"r":{"t":"Val","f":[0]}}]},"counts":[],"n":1}"#, "\n",
    r#"{"statuses":{"c0":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}},{"s":{"t":"Get","f":[0,0]}},{"r":{"t":"None","f":[]}}]},"counts":[],"n":1}"#, "\n",
);
/// `daavar/format/golden/A2Store-early-ack-1-2.random.jsonl` (sampled: `seed`, `iterations`), verbatim.
const JMC_EA_RANDOM: &str = concat!(
    r#"{"format":1,"tool":"jmc","program":"a2-early-ack-k1q2","size":"k1q2","visible":["c0"],"model":"p2p","enumeration":"sampled","seed":1,"iterations":300,"encoding":1}"#, "\n",
    r#"{"statuses":{"c0":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}},{"s":{"t":"Get","f":[0,0]}},{"r":{"t":"Val","f":[0]}}]},"counts":[],"n":297}"#, "\n",
    r#"{"statuses":{"c0":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}},{"s":{"t":"Get","f":[0,0]}},{"r":{"t":"None","f":[]}}]},"counts":[],"n":3}"#, "\n",
);
/// A minor-1 JMC file, its header as `SummaryExporter.header` (JMC
/// core/src/main/java/org/mpi_sws/jmc/mp/summary/SummaryExporter.java, lines 203-242) writes it
/// for a complete enumeration without online fields: `{"format":1,"minor":1,"tool":"jmc",
/// "program":` (203), `,"size":` (205), `,"visible":[` (207), `],"roles":[` (216), `],"model":`
/// (225), `,"enumeration":` (227), no `seed`/`iterations` (sampled only, 229-236), no online
/// fields (237-241), `,"encoding":1}` (242); names quoted, lists sorted. Lines as the golden's.
const JMC_MINOR1: &str = concat!(
    r#"{"format":1,"minor":1,"tool":"jmc","program":"a2-early-ack-k1q2","size":"k1q2","visible":["c0"],"roles":["c0","n0"],"model":"p2p","enumeration":"complete","encoding":1}"#, "\n",
    r#"{"statuses":{"c0":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}},{"s":{"t":"Get","f":[0,0]}},{"r":{"t":"Val","f":[0]}}]},"counts":[],"n":1}"#, "\n",
    r#"{"statuses":{"c0":"done"},"words":{"c0":[{"s":{"t":"Put","f":[0,0,0]}},{"r":{"t":"Ack","f":[]}},{"s":{"t":"Get","f":[0,0]}},{"r":{"t":"None","f":[]}}]},"counts":[],"n":1}"#, "\n",
);

/// The file with its lines in byte order (for `--merge`).
fn sorted(text: &str) -> String {
    let mut lines: Vec<&str> = text.lines().collect();
    let head = lines.remove(0);
    lines.sort();
    format!("{head}\n{}\n", lines.join("\n"))
}

const MINOR0: &str = "warning: roles were not compared (minor-0 header)\n";

#[test]
fn jmc_files_are_accepted() {
    let dir = scratch();
    for (name, spec, imp, warn) in [
        ("pb", JMC_PB, JMC_PB, MINOR0),
        ("sampled", JMC_EA_MUST, JMC_EA_RANDOM, MINOR0),
        ("minor1", JMC_MINOR1, JMC_MINOR1, ""),
    ] {
        for merge in [false, true] {
            let (s, i) = if merge { (sorted(spec), sorted(imp)) } else { (spec.to_owned(), imp.to_owned()) };
            let sp = write(&dir, &format!("{name}-{merge}-s.jsonl"), &s);
            let ip = write(&dir, &format!("{name}-{merge}-i.jsonl"), &i);
            let mut a: Vec<&str> = if merge { vec!["--merge"] } else { vec![] };
            a.extend([sp.to_str().unwrap(), ip.to_str().unwrap()]);
            let (o, e, code) = conf_join(&a);
            assert_eq!((code, e.as_str()), (0, warn), "{name} merge={merge}");
            let verdict = if name == "sampled" { "verdict: no verdict (sampled)\n" } else { "verdict: conforms\n" };
            assert!(o.contains(verdict), "{name} merge={merge}: {o}");
        }
    }
}

/// `v` sends nothing (`none`) or 1 (`one`).
fn program() -> Program<'static> {
    fn body(variant: &str) {
        match variant {
            "none" => named("v", || {}).join().unwrap(),
            _ => named("v", || traceforge::send_msg(me(), 1usize)).join().unwrap(),
        }
    }
    Program {
        visible: &|_| vec!["v".to_owned()],
        spec: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
        imp: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
    }
}

fn cli(args: &[&str]) -> (String, u8) {
    let (t, c) = run_cli(&program(), &args.iter().map(|s| s.to_string()).collect::<Vec<_>>());
    println!("{args:?}: exit {c}\n{t}---");
    (t, c)
}

#[test]
fn traceforge_files_are_accepted() {
    let dir = scratch();
    let spec = dir.join("spec.jsonl");
    let (t, c) = cli(&["export", "spec", "--out", spec.to_str().unwrap(), "--", "none"]);
    assert_eq!(c, 0, "{t}");
    let exp = dir.join("exp.jsonl");
    let (t, c) = cli(&["export", "impl", "--out", exp.to_str().unwrap(), "--", "one"]);
    assert_eq!(c, 0, "{t}");
    let onl = dir.join("online.jsonl");
    let (t, c) = cli(&["online", "--spec", spec.to_str().unwrap(), "--out", onl.to_str().unwrap(), "--seed", "0", "--", "one"]);
    assert_ne!(c, 2, "{t}");
    let head = std::fs::read_to_string(&onl).unwrap();
    println!("--- online file\n{head}---");
    for k in ["\"first_miss_iteration\":", "\"first_miss_wall_ms\":", "\"uncovered_total\":"] {
        assert!(head.lines().next().unwrap().contains(k), "the online fields: {head}");
    }
    let (s, e, o) = (spec.to_str().unwrap(), exp.to_str().unwrap(), onl.to_str().unwrap());
    for merge in [false, true] {
        for (a, b, code) in [(s, s, 0), (e, e, 0), (o, o, 0), (s, e, 1), (s, o, 1)] {
            let mut args: Vec<&str> = if merge { vec!["--merge"] } else { vec![] };
            args.extend([a, b]);
            let (out, err, c) = conf_join(&args);
            assert_eq!((c, err.as_str()), (code, ""), "{args:?}");
            assert!(out.contains("verdict:"), "{args:?}: {out}");
        }
    }
}
