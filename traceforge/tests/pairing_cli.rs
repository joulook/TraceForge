//! conf-join's pairing check: `--check-pairing`, the check before every join, and
//! `--no-pairing-check`, on small hand-written summary files, one failing pair per contract row.
mod wg_common;

use std::path::{Path, PathBuf};
use std::process::Command;

use wg_common::*;

const HEAD: &str = concat!("{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"p\",\"size\":\"1\",",
    "\"visible\":[\"A\",\"B\"],\"roles\":[\"A\",\"B\"],\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1}");

/// A line where A sends `a` and B receives `b` (B's receive after A's send).
fn line(a: &str, b: &str) -> String {
    format!("{{\"statuses\":{{\"A\":\"done\",\"B\":\"done\"}},\"words\":{{\"A\":[{{\"s\":{a}}}],\"B\":[{{\"r\":{b}}}]}},\"counts\":[0,1]}}")
}

fn write(dir: &Path, name: &str, head: &str, lines: &[String]) -> PathBuf {
    let p = dir.join(name);
    let mut t = format!("{head}\n");
    for l in lines { t.push_str(l); t.push('\n'); }
    std::fs::write(&p, t).unwrap();
    p
}

fn head_with(edit: &[(&str, &str)]) -> String {
    let mut h = HEAD.to_owned();
    for (old, new) in edit {
        assert_eq!(h.matches(old).count(), 1, "{old}");
        h = h.replacen(old, new, 1);
    }
    h
}

fn run(bin: &str, args: &[&str]) -> (String, String, i32) {
    let out = {
        let _r = spawn_guard();
        Command::new(bin).args(args).output().unwrap()
    };
    let r = (String::from_utf8(out.stdout).unwrap(), String::from_utf8(out.stderr).unwrap(),
        out.status.code().unwrap_or(-1));
    println!("{bin} {args:?}: exit {}\n--- stdout\n{}--- stderr\n{}---", r.2, r.0, r.1);
    r
}

fn conf_join(args: &[&str]) -> (String, String, i32) {
    run(env!("CARGO_BIN_EXE_conf-join"), args)
}

/// One failing (or warning) pair: its files, the flags of the check, and the expected
/// `--check-pairing` stdout (paths written `{S}` and `{I}`) and exit code.
struct Case {
    name: &'static str,
    spec: (String, Vec<String>),
    imp: (String, Vec<String>),
    flags: Vec<&'static str>,
    expected: String,
    code: i32,
}

fn cases() -> Vec<Case> {
    let l1 = line("1", "1");
    let l2 = line("2", "2");
    let ok = |h: &str| (h.to_owned(), vec![l1.clone()]);
    vec![
        Case { name: "c2-unsorted-visible",
            spec: ok(&head_with(&[("\"visible\":[\"A\",\"B\"]", "\"visible\":[\"B\",\"A\"]")])), imp: ok(HEAD), flags: vec![],
            expected: concat!("pairing: C2: {S}: line 1: the `visible` list [\"B\", \"A\"] is not byte-sorted with distinct names\n",
                "pairing: C2: the two `visible` lists differ: [\"B\", \"A\"] and [\"A\", \"B\"]\n",
                "pairing: failed (2 checks)\n").into(), code: 2 },
        Case { name: "c2-unequal-roles",
            spec: ok(HEAD), imp: ok(&head_with(&[("\"roles\":[\"A\",\"B\"]", "\"roles\":[\"A\",\"B\",\"C\"]")])), flags: vec![],
            expected: concat!("pairing: C2: the two `roles` lists differ: [\"A\", \"B\"] and [\"A\", \"B\", \"C\"]\n",
                "pairing: failed (1 checks)\n").into(), code: 2 },
        Case { name: "c3-unequal-models",
            spec: ok(HEAD), imp: ok(&head_with(&[("\"model\":\"p2p\"", "\"model\":\"asyn\"")])), flags: vec![],
            expected: "pairing: C3: the two models differ: p2p and asyn\npairing: failed (1 checks)\n".into(), code: 2 },
        Case { name: "c3-cd-both",
            spec: ok(&head_with(&[("\"model\":\"p2p\"", "\"model\":\"cd\"")])),
            imp: ok(&head_with(&[("\"model\":\"p2p\"", "\"model\":\"cd\"")])), flags: vec![],
            expected: concat!("pairing: C3: the specification's model `cd` is not supported for a join (p2p or asyn)\n",
                "pairing: C3: the implementation's model `cd` is not supported for a join (p2p or asyn)\n",
                "pairing: failed (2 checks)\n").into(), code: 2 },
        Case { name: "c4-bounded-spec",
            spec: ok(&head_with(&[("\"enumeration\":\"complete\"", "\"enumeration\":\"bounded\"")])), imp: ok(HEAD), flags: vec![],
            expected: "pairing: C4: the specification is `bounded`, not `complete`\npairing: failed (1 checks)\n".into(), code: 2 },
        Case { name: "c6-repeated-line",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l1.clone(), l1.clone()]), flags: vec![],
            expected: "pairing: C6: {I}: line 3 repeats an earlier line\npairing: failed (1 checks)\n".into(), code: 2 },
        Case { name: "c6-unsorted-merge",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l2.clone(), l1.clone()]), flags: vec!["--merge"],
            expected: "pairing: C6: {I}: line 3 precedes line 2 in byte order (--merge needs sorted files)\npairing: failed (1 checks)\n".into(), code: 2 },
        Case { name: "c6-unsorted-plain",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l2.clone(), l1.clone()]), flags: vec![],
            expected: "pairing: ok\n".into(), code: 0 },
        Case { name: "c10-count-2-31",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l1.replace("\"counts\":[0,1]", "\"counts\":[0,2147483648]")]), flags: vec![],
            expected: "pairing: C10: {I}: line 2: the count 2147483648 is out of bounds (both readers accept counts up to 2^31-1)\npairing: failed (1 checks)\n".into(), code: 2 },
        Case { name: "c10-count-2-31-minus-1",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l1.replace("\"counts\":[0,1]", "\"counts\":[0,2147483647]")]), flags: vec![],
            expected: "pairing: ok\n".into(), code: 0 },
        Case { name: "c10-count-65536-decide",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l1.replace("\"counts\":[0,1]", "\"counts\":[0,65536]")]), flags: vec!["--decide"],
            expected: concat!("pairing: warning: C10: {I}: line 2: the count 65536 exceeds 65535; ",
                "--decide refuses the join if it classifies this line\npairing: ok\n").into(), code: 0 },
        Case { name: "c10-count-65536-plain",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l1.replace("\"counts\":[0,1]", "\"counts\":[0,65536]")]), flags: vec![],
            expected: "pairing: ok\n".into(), code: 0 },
        Case { name: "c10-count-65535-decide",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l1.replace("\"counts\":[0,1]", "\"counts\":[0,65535]")]), flags: vec!["--decide"],
            expected: "pairing: ok\n".into(), code: 0 },
        // Above u64: the check leaves it to the join, which refuses the line as malformed.
        Case { name: "malformed-count-above-u64",
            spec: ok(HEAD), imp: (HEAD.into(), vec![l1.replace("\"counts\":[0,1]", "\"counts\":[0,18446744073709551616]")]), flags: vec![],
            expected: "pairing: ok\n".into(), code: 0 },
        // A header the join's reader refuses: the check skips its header rows, the join refuses it.
        Case { name: "malformed-roles-unsorted",
            spec: ok(&head_with(&[("\"roles\":[\"A\",\"B\"]", "\"roles\":[\"B\",\"A\"]")])), imp: ok(HEAD), flags: vec![],
            expected: "pairing: ok\n".into(), code: 0 },
        // A malformed header field: the check leaves it to the join.
        Case { name: "malformed-role-not-a-string",
            spec: ok(&head_with(&[("\"roles\":[\"A\",\"B\"]", "\"roles\":[\"A\",7]")])), imp: ok(HEAD), flags: vec![],
            expected: "pairing: ok\n".into(), code: 0 },
        Case { name: "c13-arity-mismatch",
            spec: (HEAD.into(), vec![line("{\"t\":\"Req\",\"f\":[1]}", "1")]),
            imp: (HEAD.into(), vec![line("{\"t\":\"Req\",\"f\":[1,2]}", "1")]), flags: vec![],
            expected: "pairing: C13: the tag \"Req\" has the field arities {1} in the specification and {2} in the implementation\npairing: failed (1 checks)\n".into(), code: 2 },
        Case { name: "c13-spec-only-tag",
            spec: (HEAD.into(), vec![line("{\"t\":\"Ping\",\"f\":[]}", "1")]), imp: ok(HEAD), flags: vec![],
            expected: concat!("pairing: warning: C13: the tag \"Ping\" (arities {0}) occurs only in the specification; ",
                "the implementation never sends it, which the join does not count against it\npairing: ok\n").into(), code: 0 },
        Case { name: "c13-impl-only-tag",
            spec: ok(HEAD), imp: (HEAD.into(), vec![line("1", "{\"t\":\"Pong\",\"f\":[1,2]}")]), flags: vec![],
            expected: concat!("pairing: warning: C13: the tag \"Pong\" (arities {2}) occurs only in the implementation; ",
                "the join reports the lines that carry it as uncovered\npairing: ok\n").into(), code: 0 },
        // C18 is a warning: a value tagged with an identity type's name, at any depth.
        Case { name: "c18-nested-thread-id",
            spec: (HEAD.into(), vec![line("{\"t\":\"Msg\",\"f\":[[{\"t\":\"ThreadId\",\"f\":[3]}]]}", "1")]),
            imp: (HEAD.into(), vec![line("{\"t\":\"Msg\",\"f\":[[{\"t\":\"ThreadId\",\"f\":[3]}]]}", "1"),
                line("{\"t\":\"Msg\",\"f\":[[{\"t\":\"Tid\",\"f\":[4]}]]}", "1")]), flags: vec![],
            expected: concat!("pairing: warning: C18: {S}: line 2: a value is tagged \"ThreadId\", the name of an identity type; if it is a process identity, the programs must send its role name instead\n",
                "pairing: warning: C18: {I}: line 2: a value is tagged \"ThreadId\", the name of an identity type; if it is a process identity, the programs must send its role name instead\n",
                "pairing: warning: C18: {I}: line 3: a value is tagged \"Tid\", the name of an identity type; if it is a process identity, the programs must send its role name instead\n",
                "pairing: warning: C13: the tag \"Tid\" (arities {1}) occurs only in the implementation; the join reports the lines that carry it as uncovered\n",
                "pairing: ok\n").into(), code: 0 },
        // An ordinary tag `Tid` with one int field on both sides: a warning, and the join conforms.
        Case { name: "c18-canonical-tid",
            spec: (HEAD.into(), vec![line("{\"t\":\"Tid\",\"f\":[1]}", "1")]),
            imp: (HEAD.into(), vec![line("{\"t\":\"Tid\",\"f\":[1]}", "1")]), flags: vec![],
            expected: concat!("pairing: warning: C18: {S}: line 2: a value is tagged \"Tid\", the name of an identity type; if it is a process identity, the programs must send its role name instead\n",
                "pairing: warning: C18: {I}: line 2: a value is tagged \"Tid\", the name of an identity type; if it is a process identity, the programs must send its role name instead\n",
                "pairing: ok\n").into(), code: 0 },
        // The arity-mismatch pair with an unknown key on the implementation's line: the reader
        // refuses that line, so its tags feed neither C13 nor C18 and `Req` is spec-only.
        Case { name: "malformed-tagged-line",
            spec: (HEAD.into(), vec![line("{\"t\":\"Req\",\"f\":[1]}", "1")]),
            imp: (HEAD.into(), vec![line("{\"t\":\"Req\",\"f\":[1,2]}", "1").replacen("{", "{\"x\":0,", 1)]), flags: vec![],
            expected: concat!("pairing: warning: C13: the tag \"Req\" (arities {1}) occurs only in the specification; ",
                "the implementation never sends it, which the join does not count against it\npairing: ok\n").into(), code: 0 },
    ]
}

/// The case's files in a fresh directory: (spec, impl).
fn files(dir: &Path, c: &Case) -> (PathBuf, PathBuf) {
    (write(dir, &format!("{}-spec.jsonl", c.name), &c.spec.0, &c.spec.1),
     write(dir, &format!("{}-impl.jsonl", c.name), &c.imp.0, &c.imp.1))
}

fn expected(c: &Case, s: &Path, i: &Path) -> String {
    c.expected.replace("{S}", s.to_str().unwrap()).replace("{I}", i.to_str().unwrap())
}

#[test]
fn check_pairing_prints_each_failed_row() {
    let dir = scratch();
    let mut bad = Vec::new();
    for c in cases() {
        let (s, i) = files(&dir, &c);
        let mut a: Vec<&str> = vec!["--check-pairing"];
        a.extend(c.flags.iter());
        a.extend([s.to_str().unwrap(), i.to_str().unwrap()]);
        let (o, e, code) = conf_join(&a);
        let want = expected(&c, &s, &i);
        if (o.as_str(), e.as_str(), code) != (want.as_str(), "", c.code) {
            bad.push(format!("{}: exit {code}\n{o}{e}--- want exit {}\n{want}", c.name, c.code));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The block printed for a refused join, with every value masked.
fn shape(block: &str) -> Vec<String> {
    block.lines().map(|l| l.split_once(':').map_or(l.to_owned(), |(k, _)| k.to_owned())).collect()
}

#[test]
fn a_failing_pair_refuses_the_join() {
    let dir = scratch();
    // The refused block's shape, from a join refused for another reason (a missing file).
    let (refused_block, _, _) = conf_join(&[dir.join("none.jsonl").to_str().unwrap(), dir.join("none.jsonl").to_str().unwrap()]);
    let mut bad = Vec::new();
    for c in cases().into_iter().filter(|c| c.code == 2) {
        let (s, i) = files(&dir, &c);
        // The join itself gets the same flags (--decide, --merge) as the check.
        let mut a: Vec<&str> = c.flags.clone();
        a.extend([s.to_str().unwrap(), i.to_str().unwrap()]);
        let (o, e, code) = conf_join(&a);
        let want = expected(&c, &s, &i);
        let rows: Vec<&str> = want.lines().filter(|l| !l.starts_with("pairing: failed")).collect();
        let n = rows.iter().filter(|l| !l.starts_with("pairing: warning:")).count();
        let mut want_err: String = rows.iter().filter(|l| !l.starts_with("pairing: warning:"))
            .map(|l| format!("conf-join: {l}\n")).collect();
        want_err.push_str(&format!("conf-join: refused: the pairing check failed ({n} checks; --no-pairing-check skips it)\n"));
        if code != 2 || e != want_err || shape(&o) != shape(&refused_block) || !o.starts_with("--- measurements") {
            bad.push(format!("{}: exit {code}\n--- stderr\n{e}--- want\n{want_err}--- stdout\n{o}", c.name));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn warnings_go_to_stderr_and_the_join_runs() {
    let dir = scratch();
    let mut seen = 0;
    for c in cases().into_iter().filter(|c| c.code == 0 && c.expected.contains("pairing: warning:")) {
        seen += 1;
        let (s, i) = files(&dir, &c);
        let mut a: Vec<&str> = c.flags.clone();
        a.extend([s.to_str().unwrap(), i.to_str().unwrap()]);
        let (o, e, code) = conf_join(&a);
        // The check before a join does not take --decide: its C10 warning is --check-pairing's only.
        let warn: String = expected(&c, &s, &i).lines()
            .filter(|l| l.starts_with("pairing: warning:") && !l.starts_with("pairing: warning: C10:"))
            .map(|l| format!("conf-join: {l}\n")).collect();
        let mut n = vec!["--no-pairing-check"];
        n.extend(a.iter());
        let (o2, e2, code2) = conf_join(&n);
        // The warnings, then whatever the join itself prints, as before.
        assert_eq!(e, format!("{warn}{e2}"), "{}", c.name);
        assert_eq!((code, untimed(&o)), (code2, untimed(&o2)), "{}: the join's output", c.name);
        if c.name.starts_with("c13-") || c.name.starts_with("c18-") {
            assert_eq!(e2, "", "{}", c.name);
            assert!(o.contains("verdict:"), "{}: the join ran: {o}", c.name);
        }
        if c.name == "c18-canonical-tid" {
            assert!(o.contains("verdict: conforms\n") && code == 0, "{}: conforms: {o}", c.name);
        }
    }
    assert_eq!(seen, 6, "C13 spec-only, C13 impl-only, C10 --decide, two C18, the malformed tagged line");
}

/// Malformed input passes the check and the join refuses it with its own message, as before.
#[test]
fn malformed_input_is_left_to_the_join() {
    let dir = scratch();
    let mut seen = 0;
    for c in cases().into_iter().filter(|c| c.name.starts_with("malformed-")) {
        seen += 1;
        let (s, i) = files(&dir, &c);
        let (ss, is) = (s.to_str().unwrap(), i.to_str().unwrap());
        let want = if c.name == "malformed-role-not-a-string" {
            format!("conf-join: refused: {ss}: line 1: a `roles` name is not a string\n")
        } else if c.name == "malformed-tagged-line" {
            // The implicit check's C13 warning, then the reader's refusal.
            format!(concat!("conf-join: pairing: warning: C13: the tag \"Req\" (arities {{1}}) occurs only in the ",
                "specification; the implementation never sends it, which the join does not count against it\n",
                "conf-join: refused: {}: line 2: unknown key `x`\n"), is)
        } else if c.name == "malformed-roles-unsorted" {
            format!("conf-join: refused: {ss}: line 1: the header's `roles` list is not sorted and unique\n")
        } else {
            format!("conf-join: refused: {is}: line 2: a count is not a non-negative integer\n")
        };
        for flags in [vec![], vec!["--merge"], vec!["--decide"]] {
            let mut a: Vec<&str> = flags.clone();
            a.extend([ss, is]);
            let (o, e, code) = conf_join(&a);
            assert_eq!((code, e.as_str()), (2, want.as_str()), "{} {flags:?}", c.name);
            let mut n = vec!["--no-pairing-check"];
            n.extend(a.iter());
            let (o2, e2, code2) = conf_join(&n);
            if c.name == "malformed-tagged-line" {
                let warn = want.lines().next().unwrap();
                assert_eq!((code, e.strip_prefix(&format!("{warn}\n")).unwrap(), untimed(&o)),
                    (code2, e2.as_str(), untimed(&o2)), "{} {flags:?}", c.name);
            } else {
                assert_eq!((code, e, untimed(&o)), (code2, e2, untimed(&o2)), "{} {flags:?}", c.name);
            }
        }
    }
    assert_eq!(seen, 4);
}

fn untimed(t: &str) -> String {
    t.lines().map(|l| match l.split_once(": ") {
        Some((k, _)) if k.ends_with("_ms") || k == "peak_rss_kb" => format!("{k}: <masked>"),
        _ => match l.find(" decide_ms=") { Some(i) => format!("{} decide_ms=<masked>", &l[..i]), None => l.to_owned() },
    }).collect::<Vec<_>>().join("\n")
}

/// `--no-pairing-check` gives what the join gave before the check existed: the reference build's
/// conf-join is `WG_BASE_CONF_JOIN`. Ignored; run with that variable set.
#[test]
#[ignore]
fn no_pairing_check_is_the_previous_join() {
    let base = std::env::var("WG_BASE_CONF_JOIN").expect("WG_BASE_CONF_JOIN");
    let dir = scratch();
    let mut bad = Vec::new();
    for c in cases() {
        let (s, i) = files(&dir, &c);
        let mut a: Vec<&str> = c.flags.clone();
        a.extend([s.to_str().unwrap(), i.to_str().unwrap()]);
        let (bo, be, bc) = run(&base, &a);
        let mut n = vec!["--no-pairing-check"];
        n.extend(a.iter());
        let (no, ne, nc) = conf_join(&n);
        if (bc, untimed(&bo), be.clone()) != (nc, untimed(&no), ne.clone()) {
            bad.push(format!("{}: base exit {bc} vs {nc}\n{be}{ne}", c.name));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// A JMC golden file (minor 0, no `roles`) joined with itself.
const JMC_GOLDEN: &str = concat!(
    "{\"format\":1,\"tool\":\"jmc\",\"program\":\"a2-pb-k2q1\",\"size\":\"k2q1\",\"visible\":[\"c0\",\"c1\"],\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1}\n",
    "{\"statuses\":{\"c0\":\"done\",\"c1\":\"done\"},\"words\":{\"c0\":[{\"s\":{\"t\":\"Put\",\"f\":[0,0,0]}},{\"r\":{\"t\":\"Ack\",\"f\":[]}}],\"c1\":[{\"s\":{\"t\":\"Get\",\"f\":[1,0]}},{\"r\":{\"t\":\"Val\",\"f\":[0]}}]},\"counts\":[0,0,0,1],\"n\":1}\n",
    "{\"statuses\":{\"c0\":\"done\",\"c1\":\"done\"},\"words\":{\"c0\":[{\"s\":{\"t\":\"Put\",\"f\":[0,0,0]}},{\"r\":{\"t\":\"Ack\",\"f\":[]}}],\"c1\":[{\"s\":{\"t\":\"Get\",\"f\":[1,0]}},{\"r\":{\"t\":\"None\",\"f\":[]}}]},\"counts\":[0,1,0,0],\"n\":1}\n");

#[test]
fn passing_pairs_check_ok_and_join_as_before() {
    let dir = scratch();
    let g = dir.join("golden.jsonl");
    std::fs::write(&g, JMC_GOLDEN).unwrap();
    let gs = g.to_str().unwrap();
    // The golden file is in exploration order, not byte order: its third line
    // ("None") sorts before its second ("Val"), so --merge needs a sorted copy.
    let mut lines: Vec<&str> = JMC_GOLDEN.lines().collect();
    let head = lines.remove(0);
    lines.sort();
    let sorted = dir.join("golden-sorted.jsonl");
    std::fs::write(&sorted, format!("{head}\n{}\n", lines.join("\n"))).unwrap();
    let ss = sorted.to_str().unwrap();
    let unsorted = format!("pairing: C6: {gs}: line 3 precedes line 2 in byte order (--merge needs sorted files)\n");
    assert_eq!(
        conf_join(&["--check-pairing", "--merge", gs, gs]),
        (format!("{unsorted}{unsorted}pairing: failed (2 checks)\n"), String::new(), 2)
    );
    for flags in [vec![], vec!["--merge"], vec!["--decide"], vec!["--merge", "--decide"]] {
        let gs = if flags.contains(&"--merge") { ss } else { gs };
        let mut a = vec!["--check-pairing"];
        a.extend(flags.iter());
        a.extend([gs, gs]);
        assert_eq!(conf_join(&a), ("pairing: ok\n".to_owned(), String::new(), 0), "{flags:?}");
        let mut j = flags.clone();
        j.extend([gs, gs]);
        let (o, e, c) = conf_join(&j);
        let mut n = vec!["--no-pairing-check"];
        n.extend(j.iter());
        let (o2, e2, c2) = conf_join(&n);
        assert_eq!((c, e.as_str(), untimed(&o)), (c2, e2.as_str(), untimed(&o2)), "{flags:?}");
        // The join's own stderr (here its minor-0 roles warning) is as before.
        assert_eq!(c, 0, "{o}");
        assert_eq!(e, "warning: roles were not compared (minor-0 header)\n", "{e}");
    }
}

#[test]
fn check_pairing_refusals() {
    let dir = scratch();
    let ok = write(&dir, "ok.jsonl", HEAD, &[line("1", "1")]);
    let oks = ok.to_str().unwrap();
    // Combined with any other option: exit 2.
    for extra in [vec!["--no-pairing-check"], vec!["--witness-dir", "w"], vec!["--decide-budget", "5"]] {
        let mut a = vec!["--check-pairing"];
        a.extend(extra.iter());
        a.extend([oks, oks]);
        let (o, e, c) = conf_join(&a);
        assert_eq!((c, o.as_str()), (2, ""), "{extra:?}");
        assert_eq!(e, "conf-join: --check-pairing takes only --merge and --decide\n", "{extra:?}");
    }
    assert!(!Path::new("w").exists());
    // Unreadable or empty files, a header or a line that is not a JSON object: refused, exit 2.
    let empty = dir.join("empty.jsonl");
    std::fs::write(&empty, "").unwrap();
    let arr = write(&dir, "arr.jsonl", "[1]", &[]);
    let badline = write(&dir, "badline.jsonl", HEAD, &["7".to_owned()]);
    let notjson = write(&dir, "notjson.jsonl", HEAD, &["{".to_owned()]);
    for (f, what) in [(dir.join("missing.jsonl"), ""), (empty, "the file is empty"), (arr, "line 1: the header is not a JSON object"),
                      (badline, "line 2: the line is not a JSON object"), (notjson, "line 2: not JSON")] {
        let (o, e, c) = conf_join(&["--check-pairing", f.to_str().unwrap(), oks]);
        assert_eq!((c, o.as_str()), (2, ""), "{}", f.display());
        assert!(e.starts_with(&format!("conf-join: refused: {}: {what}", f.display())), "{e}");
        // The join is refused the same way, before it runs.
        let (o, e2, c) = conf_join(&[f.to_str().unwrap(), oks]);
        assert_eq!(c, 2);
        assert!(e2.starts_with(&format!("conf-join: refused: {}: {what}", f.display())), "{e2}");
        assert!(o.starts_with("--- measurements"), "{o}");
    }
    // A JSON line that is not a summary is left to the join.
    let odd = write(&dir, "odd.jsonl", HEAD, &["{\"x\":1}".to_owned()]);
    assert_eq!(conf_join(&["--check-pairing", odd.to_str().unwrap(), oks]).0, "pairing: ok\n");
}
