//! `JOIN-TOTAL`'s tests, the tester's (`criteria/JOIN-TOTAL.md` JT-1.1 to JT-1.3; the derivation
//! `log/dev/JOIN-TOTAL.derived.md`).
//!
//! `uncovered_total` is Σ `n` over the uncovered implementation lines when each carries an integer
//! `n` in 1 ..= `u64::MAX`, empty otherwise, 0 with no uncovered line, empty on a refusal; in both
//! join modes. The files of JT-1.1 are built from one export's lines with `n` appended by text, so
//! that the reader sees exactly the values the criteria list.
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::ctx::{ConfMode, SinkVerdict};
use super::interchange::{encode_generic, line_of, record_thread_names, JoinReport, ThreadNames};
use super::stateful::{enumerate, EnumRun};
use super::{conf_join, conf_join_merge};
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
    let d = std::env::temp_dir().join(format!("jtt-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("conformance: JOIN-TOTAL: a scratch directory");
    d
}

/// The block's `uncovered_total` cell, `None` when the key is absent.
fn total(block: &str) -> Option<String> {
    block
        .lines()
        .find_map(|l| l.strip_prefix("uncovered_total:"))
        .map(|v| v.trim().to_string())
}

fn joined(spec: &Path, imp: &Path, merge: bool) -> JoinReport {
    let r = if merge {
        conf_join_merge(spec, imp)
    } else {
        conf_join(spec, imp)
    };
    r.expect("conformance: JOIN-TOTAL: the join reads")
}

/// `v` sends the value `nondet` picks from `values`.
fn sends(values: &'static [i32]) -> Prog {
    Arc::new(move || {
        let _v = crate::thread::Builder::new()
            .name("v".into())
            .spawn(move || {
                let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
                let mut i = 0;
                while i + 1 < values.len() && crate::nondet() {
                    i += 1;
                }
                tx.send_msg(values[i]);
            })
            .unwrap();
    })
}

/// The header and lines of an export, by the line's value (`{"s":V}`).
fn export(dir: &Path, name: &str, p: &Prog) -> (String, HashMap<i32, String>) {
    let f = dir.join(name);
    let fs = f.to_str().unwrap().to_string();
    let v = vec!["v".to_string()];
    let args = [
        "export", "spec", "--out", &fs, "--model", "fifo", "--seed", "0",
    ];
    let (text, code) = cli(p, p, &v, &args);
    assert_eq!(code, 0, "conformance: JOIN-TOTAL: export: {text}");
    let text = std::fs::read_to_string(&f).unwrap();
    let mut it = text.lines();
    let head = it.next().unwrap().to_string();
    let mut by = HashMap::new();
    for l in it {
        let x: serde_json::Value = serde_json::from_str(l).unwrap();
        let val = x["words"]["v"][0]["s"].as_i64().unwrap() as i32;
        by.insert(val, l.to_string());
    }
    (head, by)
}

/// `line` with `,"n":<n>` appended inside its object, as text.
fn with_n(line: &str, n: &str) -> String {
    format!("{},\"n\":{n}}}", &line[..line.len() - 1])
}

/// Write a file of `head` and the lines for `vals` with their `n` (by text), in the
/// export's order (sorted, so `--merge` reads it too).
fn file(
    dir: &Path,
    name: &str,
    head: &str,
    by: &HashMap<i32, String>,
    lines: &[(i32, &str)],
) -> PathBuf {
    let mut l: Vec<String> = lines
        .iter()
        .map(|(v, n)| {
            if n.is_empty() {
                by[v].clone()
            } else {
                with_n(&by[v], n)
            }
        })
        .collect();
    let mut keyed: Vec<(String, String)> = lines
        .iter()
        .map(|(v, _)| by[v].clone())
        .zip(l.drain(..))
        .collect();
    keyed.sort();
    let mut out = format!("{head}\n");
    for (_, x) in keyed {
        out.push_str(&x);
        out.push('\n');
    }
    let p = dir.join(name);
    std::fs::write(&p, out).unwrap();
    p
}

#[test]
fn jtt1_the_arithmetic_on_written_files_in_both_modes() {
    let dir = scratch("arith");
    let (sh, sby) = export(&dir, "spec-export.jsonl", &sends(&[0]));
    let (ih, iby) = export(&dir, "impl-export.jsonl", &sends(&[0, 1, 2, 3]));
    let spec = file(&dir, "spec.jsonl", &sh, &sby, &[(0, "")]);
    let sampled = ih.replace(
        "\"enumeration\":\"complete\"",
        "\"enumeration\":\"sampled\"",
    );
    assert_ne!(
        sampled, ih,
        "conformance: JOIN-TOTAL: the header names its enumeration"
    );
    let max = "18446744073709551615";
    let cases: Vec<(&str, String, Vec<(i32, &str)>, &str, &str)> = vec![
        (
            "2 and 5",
            ih.clone(),
            vec![(1, "2"), (2, "5")],
            "7",
            "violation",
        ),
        (
            "2, 5 and none",
            ih.clone(),
            vec![(1, "2"), (2, "5"), (3, "")],
            "",
            "violation",
        ),
        (
            "2, 5, covered none",
            ih.clone(),
            vec![(0, ""), (1, "2"), (2, "5")],
            "7",
            "violation",
        ),
        (
            "conforms with n",
            ih.clone(),
            vec![(0, "4")],
            "0",
            "conforms",
        ),
        (
            "conforms without n",
            ih.clone(),
            vec![(0, "")],
            "0",
            "conforms",
        ),
        (
            "sampled, all covered",
            sampled,
            vec![(0, "")],
            "0",
            "no verdict",
        ),
        (
            "two u64::MAX",
            ih.clone(),
            vec![(1, max), (2, max)],
            "36893488147419103230",
            "violation",
        ),
        (
            "n = 0",
            ih.clone(),
            vec![(1, "0"), (2, "5")],
            "",
            "violation",
        ),
        (
            "n = -1",
            ih.clone(),
            vec![(1, "-1"), (2, "5")],
            "",
            "violation",
        ),
        (
            "n = 1.5",
            ih.clone(),
            vec![(1, "1.5"), (2, "5")],
            "",
            "violation",
        ),
        (
            "n = \"3\"",
            ih.clone(),
            vec![(1, "\"3\""), (2, "5")],
            "",
            "violation",
        ),
        (
            "n = 2^64",
            ih.clone(),
            vec![(1, "18446744073709551616"), (2, "5")],
            "",
            "violation",
        ),
    ];
    let mut bad = Vec::new();
    for (i, (what, head, lines, want, verdict)) in cases.iter().enumerate() {
        let imp = file(&dir, &format!("impl-{i}.jsonl"), head, &iby, lines);
        let plain: Vec<(i32, &str)> = lines.iter().map(|(v, _)| (*v, "")).collect();
        let bare = file(&dir, &format!("bare-{i}.jsonl"), head, &iby, &plain);
        for merge in [false, true] {
            let r = joined(&spec, &imp, merge);
            let got = total(&r.measurements(0));
            if got.as_deref() != Some(*want) {
                bad.push(format!(
                    "{what} (merge {merge}): uncovered_total {got:?}, want {want:?}"
                ));
            }
            let text = r.render();
            if !text.contains(&format!("verdict: {verdict}")) {
                bad.push(format!("{what} (merge {merge}): verdict, in {text}"));
            }
            // The verdict and the listing are those of the same lines without `n`.
            let b = joined(&spec, &bare, merge);
            if b.render() != text || b.exit_code() != r.exit_code() {
                bad.push(format!(
                    "{what} (merge {merge}): the report differs from the bare file's"
                ));
            }
        }
    }
    // A value the JSON parser refuses is refused as before, in both modes.
    let refused = file(&dir, "impl-1e400.jsonl", &ih, &iby, &[(1, "1e400")]);
    for merge in [false, true] {
        let r = if merge {
            conf_join_merge(&spec, &refused)
        } else {
            conf_join(&spec, &refused)
        };
        match r {
            Err(e) if e.to_string().contains("not JSON") => {}
            other => bad.push(format!(
                "1e400 (merge {merge}): {:?}",
                other.map(|r| r.render())
            )),
        }
    }
    // A refusal after uncovered lines with `n`: no report at all, so no partial sum.
    let after = file(&dir, "impl-after.jsonl", &ih, &iby, &[(1, "2"), (2, "5")]);
    let mut text = std::fs::read_to_string(&after).unwrap();
    text.push_str("{\"statuses\":\n");
    std::fs::write(&after, text).unwrap();
    for merge in [false, true] {
        let r = if merge {
            conf_join_merge(&spec, &after)
        } else {
            conf_join(&spec, &after)
        };
        if r.is_ok() {
            bad.push(format!(
                "a malformed last line (merge {merge}) was accepted"
            ));
        }
    }
    let refused_block = JoinReport::refused_measurements(0);
    if total(&refused_block).as_deref() != Some("") || !refused_block.contains("stop_reason: error")
    {
        bad.push(format!("the refused block: {refused_block}"));
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(bad.is_empty(), "conformance: JOIN-TOTAL: {bad:#?}");
}

/// Two invisible threads race to `main`'s mailbox, so each of `v`'s summaries has two graphs;
/// the implementation's `v` sends 0 (covered) or 1 (uncovered).
fn race(imp: bool) -> Prog {
    Arc::new(move || {
        let me = crate::thread::current().id();
        let _v = crate::thread::Builder::new()
            .name("v".into())
            .spawn(move || {
                let (tx, _rx) = crate::channel::Builder::<i32>::new().build();
                let x = if imp && crate::nondet() { 1 } else { 0 };
                tx.send_msg(x);
            })
            .unwrap();
        let _x = crate::thread::spawn(move || crate::send_msg(me, 7i32));
        let _y = crate::thread::spawn(move || crate::send_msg(me, 8i32));
        let _: i32 = crate::recv_msg_block();
    })
}

/// `n_s`: every completion of the implementation's exhaustive enumeration, by the line it
/// encodes to, before and apart from any coverage test.
fn multiplicities(p: &Prog, visible: &[String], model: ConsType) -> HashMap<String, u64> {
    let counts = std::rc::Rc::new(std::cell::RefCell::new(HashMap::new()));
    let got = std::rc::Rc::clone(&counts);
    let names: Vec<String> = {
        let mut n = visible.to_vec();
        n.sort();
        n
    };
    let vis = visible.to_vec();
    enumerate(
        EnumRun {
            config: Config::builder().with_cons_type(model).with_seed(0).build(),
            visible: vis.clone(),
            mode: ConfMode::Enumerate,
            sink: Box::new(move |g, _| {
                let s = super::compact::CompactSummary::at_completion(g, &vis, "test");
                let mut threads = ThreadNames::new();
                record_thread_names(g, &mut threads);
                let line = line_of(&s.sig, &s.ord, &names, &|v| encode_generic(v, &threads))
                    .expect("conformance: JOIN-TOTAL: a line");
                *got.borrow_mut().entry(line).or_insert(0u64) += 1;
                SinkVerdict::Continue
            }),
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        p,
    );
    let out = counts.borrow().clone();
    out
}

/// One fixture of JT-1.2: export both sides, write `n_s` into the implementation's lines,
/// join in both modes, and compare with `conf --engine stateful --threads 1`.
fn against_in_process(
    what: &str,
    spec: &Prog,
    imp: &Prog,
    visible: &[String],
    model: ConsType,
    args: &[&str],
    bad: &mut Vec<String>,
) {
    let dir = scratch(&format!("inproc-{what}"));
    let m = if model == ConsType::Bag {
        "bag"
    } else {
        "fifo"
    };
    let (sf, imf) = (dir.join("spec.jsonl"), dir.join("impl.jsonl"));
    for (side, f) in [("spec", &sf), ("impl", &imf)] {
        let mut a = vec![
            "export",
            side,
            "--out",
            f.to_str().unwrap(),
            "--model",
            m,
            "--seed",
            "0",
        ];
        a.push("--");
        a.extend(args);
        let (text, code) = cli(imp, spec, visible, &a);
        assert_eq!(
            code, 0,
            "conformance: JOIN-TOTAL: {what}: export {side}: {text}"
        );
    }
    let ns = multiplicities(imp, visible, model);
    let text = std::fs::read_to_string(&imf).unwrap();
    let mut it = text.lines();
    let mut out = format!("{}\n", it.next().unwrap());
    let mut lines = 0;
    for l in it {
        let n = ns.get(l).copied().unwrap_or(0);
        if n == 0 {
            bad.push(format!("{what}: an exported line has no completion: {l}"));
        }
        out.push_str(&with_n(l, &n.to_string()));
        out.push('\n');
        lines += 1;
    }
    if lines != ns.len() {
        bad.push(format!(
            "{what}: {lines} lines against {} counted summaries",
            ns.len()
        ));
    }
    let withn = dir.join("impl-n.jsonl");
    std::fs::write(&withn, out).unwrap();
    let mut a = vec![
        "conf",
        "--engine",
        "stateful",
        "--threads",
        "1",
        "--model",
        m,
        "--seed",
        "0",
    ];
    a.push("--");
    a.extend(args);
    let (ctext, _) = cli(imp, spec, visible, &a);
    let want = total(&ctext);
    let all: u64 = ns.values().sum();
    for merge in [false, true] {
        let r = joined(&sf, &withn, merge);
        let got = total(&r.measurements(0));
        let uncovered = r
            .render()
            .lines()
            .filter(|l| l.contains(" {\"statuses\""))
            .count();
        let _ = std::io::Write::write_fmt(
            &mut std::io::stderr(),
            format_args!(
                "JTT2 {what} merge {merge}: join {got:?}, in-process {want:?}, \
                 sum over every line {all}, uncovered lines {uncovered}, lines {lines}\n"
            ),
        );
        if got != want || got.is_none() {
            bad.push(format!(
                "{what} (merge {merge}): join {got:?}, in-process {want:?}"
            ));
        }
        // The fixture separates the three candidates: the total, Σ n over every line, the count.
        let g: u64 = got.as_deref().unwrap_or("0").parse().unwrap_or(0);
        if g == all || g == uncovered as u64 || uncovered == 0 || uncovered == lines {
            bad.push(format!(
                "{what} (merge {merge}): not separating: total {g}, all {all}, \
                 uncovered lines {uncovered}, lines {lines}"
            ));
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn jtt2_the_join_equals_the_in_process_count() {
    let mut bad = Vec::new();
    let v = vec!["v".to_string()];
    against_in_process(
        "race",
        &race(false),
        &race(true),
        &v,
        ConsType::FIFO,
        &[],
        &mut bad,
    );
    let p = super::online_tests::o_prog();
    let vis = super::online_tests::vis();
    let (spec, imp) = ((p.spec)(&[]), (p.imp)(&["bug".to_string()]));
    against_in_process("K3", &spec, &imp, &vis, ConsType::Bag, &["bug"], &mut bad);
    assert!(bad.is_empty(), "conformance: JOIN-TOTAL: {bad:#?}");
}
