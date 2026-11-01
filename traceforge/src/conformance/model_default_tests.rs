//! `MODEL-DEFAULT`'s tests (`criteria/MODEL-DEFAULT.md` MD-1; the derivation
//! `log/dev/MODEL-DEFAULT.derived.md` §1): a program's declared default model,
//! on all five subcommands of the shared main, in the default build, on an inline
//! program that is no benchmark (Rule 1). Expected values by hand: `w` sends three
//! values on one channel to `r`, so the implementation has 1 graph under `fifo`
//! and 3! = 6 under `bag`; the specification's channel is FIFO by construction,
//! 1 graph under both, so 5 of the 6 are signature misses under `bag`.

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use crate::conformance::interchange_default_tests::{named, record_cells, scratch, split_block};
use crate::conformance::record;
use crate::program::{run_cli, run_cli_with_model, Entry, Program};
use crate::ConsType;

#[derive(Clone, Debug, PartialEq)]
enum DMsg {
    V(i32),
}

fn d(fifo: bool) {
    let (tx, rx) = if fifo {
        crate::channel::Builder::<DMsg>::new()
            .with_comm(crate::loc::CommunicationModel::LocalOrder)
            .build()
    } else {
        crate::channel::Builder::<DMsg>::new().build()
    };
    let r = named("r", move || {
        for _ in 0..3 {
            let _: DMsg = rx.recv_msg_block();
        }
    });
    let w = named("w", move || {
        for i in 0..3 {
            tx.send_msg(DMsg::V(i));
        }
    });
    r.join().unwrap();
    w.join().unwrap();
}

fn visible(_: &[String]) -> Vec<String> {
    vec!["r".to_owned(), "w".to_owned()]
}
fn spec(_: &[String]) -> Entry {
    Arc::new(|| d(true))
}
fn imp(_: &[String]) -> Entry {
    Arc::new(|| d(false))
}
fn program() -> Program<'static> {
    Program {
        visible: &visible,
        spec: &spec,
        imp: &imp,
    }
}

/// How a run declares its default: `None` is `run_cli`.
type Declared = Option<ConsType>;

fn cli(declared: Declared, args: &[&str]) -> (String, u8) {
    let a: Vec<String> = args.iter().map(|s| (*s).to_owned()).collect();
    match declared {
        None => run_cli(&program(), &a),
        Some(m) => run_cli_with_model(&program(), m, &a),
    }
}

/// `args` with the model option in front when one is given.
fn with_model<'a>(head: &[&'a str], model: Option<&'a str>, tail: &[&'a str]) -> Vec<&'a str> {
    let mut v = head.to_vec();
    if let Some(m) = model {
        v.extend_from_slice(&["--model", m]);
    }
    v.extend_from_slice(tail);
    v
}

/// The block's value of `key`.
fn key(block: &str, k: &str) -> String {
    block
        .lines()
        .find_map(|l| l.strip_prefix(&format!("{k}: ")))
        .unwrap_or_else(|| panic!("conformance: MD: no key `{k}` in {block}"))
        .to_owned()
}

/// A subcommand's own text and its block.
fn split(text: &str, what: &str) -> (String, String) {
    let (t, b) = split_block(text);
    (
        t,
        b.unwrap_or_else(|| panic!("conformance: MD: {what}: no block: {text}")),
    )
}

/// Every declared default against every `--model`, and which column it must give.
/// `true` is the `bag` column.
const TABLE: [(Declared, Option<&str>, bool); 8] = [
    (Some(ConsType::Bag), None, true),
    (Some(ConsType::Bag), Some("bag"), true),
    (Some(ConsType::Bag), Some("fifo"), false),
    (Some(ConsType::FIFO), None, false),
    (Some(ConsType::FIFO), Some("bag"), true),
    (Some(ConsType::FIFO), Some("fifo"), false),
    (None, None, false),
    (None, Some("bag"), true),
];

/// **`count`.** Failing directions: the default ignored; the default overriding
/// `--model`; `count` not taking it; `run_cli` declaring `Bag`.
#[test]
fn md_count() {
    for (declared, model, bag) in TABLE {
        let what = format!("count {declared:?} {model:?}");
        let a = with_model(&["count", "impl"], model, &["--seed", "0"]);
        let (text, code) = cli(declared, &a);
        let (own, block) = split(&text, &what);
        let n = if bag { 6 } else { 1 };
        assert_eq!(
            (own.as_str(), code),
            (format!("execs={n} blocked=0\n").as_str(), 0),
            "conformance: MD: {what}"
        );
        assert_eq!(
            key(&block, "graphs_complete"),
            n.to_string(),
            "conformance: MD: {what}: the block"
        );
    }
}

/// **`export`:** the header's `model` and the file's lines, on the implementation;
/// the specification's header too (1 line under both). Failing directions as
/// `count`'s, on `export`.
#[test]
fn md_export() {
    let dir = scratch("md-export");
    for (i, (declared, model, bag)) in TABLE.into_iter().enumerate() {
        for (side, n) in [("impl", if bag { 6 } else { 1 }), ("spec", 1)] {
            let what = format!("export {side} {declared:?} {model:?}");
            let f = dir.join(format!("{side}{i}.jsonl"));
            let fs = f.to_string_lossy().into_owned();
            let a = with_model(&["export", side, "--out", &fs], model, &["--seed", "0"]);
            let (text, code) = cli(declared, &a);
            let (own, _) = split(&text, &what);
            assert_eq!(
                (own.as_str(), code),
                (
                    format!("exported: {n} lines from {n} graphs to {fs}\n").as_str(),
                    0
                ),
                "conformance: MD: {what}"
            );
            let file = std::fs::read_to_string(&f).expect("conformance: MD: the file");
            let head: serde_json::Value =
                serde_json::from_str(file.lines().next().expect("conformance: MD: a header"))
                    .expect("conformance: MD: the header parses");
            assert_eq!(
                head["model"],
                if bag { "asyn" } else { "p2p" },
                "conformance: MD: {what}: the header's model"
            );
            assert_eq!(
                file.lines().count(),
                n + 1,
                "conformance: MD: {what}: the lines"
            );
        }
    }
}

/// **`conf`:** conforms under `fifo` (exit 0), reports 5 of 6 under `bag` (exit 1).
/// Failing directions as `count`'s, on `conf`.
#[test]
fn md_conf() {
    for (declared, model, bag) in TABLE {
        let what = format!("conf {declared:?} {model:?}");
        let a = with_model(&["conf"], model, &["--seed", "0"]);
        let (text, code) = cli(declared, &a);
        let (_, block) = split(&text, &what);
        let (exit, n, u) = if bag { (1, "6", "5") } else { (0, "1", "0") };
        assert_eq!(code, exit, "conformance: MD: {what}: the verdict: {text}");
        assert_eq!(
            key(&block, "iterations"),
            n,
            "conformance: MD: {what}: iterations"
        );
        assert_eq!(
            key(&block, "uncovered_total"),
            u,
            "conformance: MD: {what}: uncovered_total"
        );
    }
}

fn spec_file(dir: &Path) -> String {
    let f = dir.join("S.jsonl");
    let fs = f.to_string_lossy().into_owned();
    let (t, c) = cli(
        None,
        &[
            "export", "spec", "--out", &fs, "--model", "fifo", "--seed", "0",
        ],
    );
    assert_eq!(c, 0, "conformance: MD: the specification file: {t}");
    fs
}

/// **`online`:** against the one-line specification: `conforms` under `fifo`, 5
/// signature misses of 6 under `bag`. Failing directions as `count`'s, on `online`.
#[test]
fn md_online() {
    let dir = scratch("md-online");
    let s = spec_file(&dir);
    for (declared, model, bag) in TABLE {
        let what = format!("online {declared:?} {model:?}");
        let a = with_model(&["online", "--spec", &s], model, &["--seed", "0"]);
        let (text, code) = cli(declared, &a);
        let (own, block) = split(&text, &what);
        assert_eq!(
            code, 0,
            "conformance: MD: {what}: exit 0 with a verdict: {own}"
        );
        let (lookups, verdict, unc, n) = if bag {
            (
                "lookups:    6 (1 found, 5 signature misses, 0 not found)",
                "verdict:    reports",
                "uncovered:  5 graphs (5 distinct summaries)",
                "6",
            )
        } else {
            (
                "lookups:    1 (1 found, 0 signature misses, 0 not found)",
                "verdict:    conforms",
                "uncovered:  0 graphs (0 distinct summaries)",
                "1",
            )
        };
        for l in [lookups, verdict, unc] {
            assert!(
                own.lines().any(|x| x == l),
                "conformance: MD: {what}: no `{l}` in {own}"
            );
        }
        assert_eq!(
            key(&block, "iterations"),
            n,
            "conformance: MD: {what}: iterations"
        );
    }
}

const ROW: &str = r#"{"fixture":"md-d","label":"Stateful/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"md","knobs":"","k":[null,null,null,null],"variant":"conforming","twin_key":""}"#;

/// Set only on `md_row`'s child: the index into `TABLE` it runs.
const ROW_CASE: &str = "MD_ROW_CASE";
/// Set only on `md_row`'s child: the file it writes its exit code and text to.
const ROW_OUT: &str = "MD_ROW_OUT";

/// `row` reads `EVAL_ROW` and `EVAL_COMMIT` from the process's environment, and this
/// test process must not have them (`eval_tests`' `vc0_r9…`), so each case runs in a
/// child: this test binary again, on `md_row` alone, with both variables given to the
/// child only. The existing row tests' child, `eval::eval_row`, resolves a registered
/// fixture and does not reach `program`'s `row` on an inline program, so `md_row` is
/// its own child. A file carries the result: a child that ran nothing leaves none.
fn row_in_child(dir: &Path, case: usize, what: &str) -> (String, u8) {
    let out = dir.join(format!("case-{case}"));
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "conformance::model_default_tests::md_row",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(ROW_CASE, case.to_string())
        .env(ROW_OUT, &out)
        .env("EVAL_ROW", ROW)
        .env("EVAL_COMMIT", "MD")
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap_or_else(|e| panic!("conformance: MD: {what}: the child: {e}"));
    let said = format!(
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    assert!(
        child.status.success(),
        "conformance: MD: {what}: the child failed: {said}"
    );
    let got = std::fs::read_to_string(&out).unwrap_or_else(|e| {
        panic!("conformance: MD: {what}: no result from the child ({e}): {said}")
    });
    let (code, text) = got
        .split_once('\n')
        .unwrap_or_else(|| panic!("conformance: MD: {what}: the child's result: {got}"));
    let code = code
        .parse()
        .unwrap_or_else(|_| panic!("conformance: MD: {what}: the child's exit code: {got}"));
    (text.to_owned(), code)
}

/// The child's part of `md_row`: the one case, through `run_cli` or `run_cli_with_model`.
fn row_child(case: &str) {
    let out = std::env::var(ROW_OUT).expect("conformance: MD: the child's result file");
    let case: usize = case.parse().expect("conformance: MD: the child's case");
    let (declared, model, _) = TABLE[case];
    let a = with_model(&["row"], model, &["--seed", "0", "--"]);
    let (text, code) = cli(declared, &a);
    std::fs::write(out, format!("{code}\n{text}")).expect("conformance: MD: the child's write");
}

/// **`row`** (`comm_model`): `NoOrder` with 6 graphs and 5 reports under `bag`,
/// `LocalOrder` with 1 and 0 under `fifo`. Failing directions as `count`'s, on
/// `row`.
#[test]
fn md_row() {
    if let Ok(case) = std::env::var(ROW_CASE) {
        return row_child(&case);
    }
    let dir = scratch("md-row");
    let header = record::header();
    for (case, (declared, model, bag)) in TABLE.into_iter().enumerate() {
        let what = format!("row {declared:?} {model:?}");
        let (text, code) = row_in_child(&dir, case, &what);
        let (own, _) = split(&text, &what);
        assert_eq!(code, 0, "conformance: MD: {what}: a record: {own}");
        let line = own
            .lines()
            .find(|l| l.starts_with(record::SENTINEL))
            .unwrap_or_else(|| panic!("conformance: MD: {what}: no record: {own}"));
        let cells: HashMap<&str, String> = header.iter().copied().zip(record_cells(line)).collect();
        let (comm, graphs, reports) = if bag {
            ("NoOrder", "6", "5")
        } else {
            ("LocalOrder", "1", "0")
        };
        assert_eq!(
            (
                cells["comm_model"].as_str(),
                cells["impl_graphs"].as_str(),
                cells["reports"].as_str()
            ),
            (comm, graphs, reports),
            "conformance: MD: {what}"
        );
    }
}

/// A usage error is refused the same under every declaration, and its text names the
/// default (MD-0.2); an unknown `--model` is refused whatever the default.
#[test]
fn md_usage() {
    for declared in [None, Some(ConsType::Bag), Some(ConsType::FIFO)] {
        let (text, code) = cli(declared, &["frob"]);
        assert_eq!(code, 2, "conformance: MD: {declared:?}: a usage error");
        assert!(
            text.contains("--model fifo|bag|causal (default: the program's)"),
            "conformance: MD: the option's text: {text}"
        );
        assert!(
            text.contains("<bin> row [--model fifo|bag|causal] --seed N"),
            "conformance: MD: row's text: {text}"
        );
        assert!(
            split_block(&text).1.is_none(),
            "conformance: MD: no block on a usage error"
        );
        let (text, code) = cli(declared, &["count", "impl", "--model", "mo"]);
        assert_eq!(
            code, 2,
            "conformance: MD: {declared:?}: an unknown model: {text}"
        );
    }
}
