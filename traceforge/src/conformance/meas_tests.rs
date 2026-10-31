//! B's tests (`criteria/MEAS.md` rev 1.3, MEAS-2; the derivation
//! `log/dev/MEAS.derived-2.md`): the measurement block of every printer, on
//! inline programs (C's P_o, `online_tests.rs`), in the default build (Rule
//! 1). The block is read by this file's own parser (MEAS-2's "independent of
//! the renderer"); each value is compared with an independent source: the
//! record's cells (K1), the written files (K2, K3), C's printed lines (K4),
//! `crate::verify`'s `Stats` (K5), the `ConfOutcome` of the same
//! `conformance::verify` call (K6), the hand values of the derivation's §4, and
//! the kept graphs of the offline stateful run on the same pair (graph-event
//! counts). The timing tests use the `#[cfg(test)]` delay seams.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::conformance::config::{ConfBuilder, Engine, IndexKind};
use crate::conformance::interchange::{self, conf_join_with, ExportHeader, ExportSeams, JoinSeams};
use crate::conformance::interchange_default_tests::{record_cells, scratch, split_block};
use crate::conformance::measure::{self, Side};
use crate::conformance::online::{self, Mode, OnlineOpts, OnlineOut};
use crate::conformance::interchange_default_tests::named;
use crate::conformance::online_tests::{
    body, first_miss_of, imp_of, o_prog, reference, spec_file, vis, Prog, Var, M,
};
use crate::conformance::record::{self, Subject};
use crate::exec_graph::ExecutionGraph;
use crate::{Config, ConsType};

/// Writes a line to stderr (the `s5_tests` emission scan forbids the print
/// macros under `conformance/`).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

// =========================================================================
// The parser (MEAS-2; the derivation's §5), typed from MEAS-0.1
// =========================================================================

const MARKER: &str = "--- measurements";

/// MEAS-0.1's keys, in order.
const KEYS: [&str; 37] = [
    "wall_ms",
    "explore_ms",
    "summarise_ms",
    "index_ms",
    "lookup_ms",
    "export_ms",
    "graphs_complete",
    "graphs_blocked",
    "summaries_distinct",
    "iterations",
    "stop_reason",
    "peak_rss_kb",
    "max_message_events",
    "max_porf_pairs",
    "first_miss_iteration",
    "first_miss_wall_ms",
    "uncovered_total",
    "max_graph_events",
    "mean_graph_events",
    "max_visible_events",
    "mean_visible_events",
    "max_summary_bytes",
    "max_porf_count",
    "join_ms",
    "spec_phase_ms",
    "impl_phase_ms",
    "explore_spec_ms",
    "explore_impl_ms",
    "spec_complete",
    "spec_blocked",
    "impl_complete",
    "impl_blocked",
    "spec_summaries",
    "impl_summaries",
    "precheck_ms",
    "merge_ms",
    "uncovered_distinct",
];

/// Printed only on runs with a specification.
const SPEC_KEYS: [&str; 3] = ["first_miss_iteration", "first_miss_wall_ms", "uncovered_total"];
const MEANS: [&str; 2] = ["mean_graph_events", "mean_visible_events"];
const STOPS: [&str; 5] = ["exhausted", "budget", "timeout", "first-miss", "error"];

/// A parsed block: each key's value text (empty when unmeasured).
struct Block {
    what: String,
    vals: HashMap<String, String>,
}

impl Block {
    fn get(&self, k: &str) -> &str {
        self.vals
            .get(k)
            .map(String::as_str)
            .unwrap_or_else(|| panic!("conformance: B: {}: no key `{k}`", self.what))
    }
    fn n(&self, k: &str) -> u128 {
        self.get(k)
            .parse()
            .unwrap_or_else(|_| panic!("conformance: B: {}: `{k}` is `{}`, not a number", self.what, self.get(k)))
    }
    /// Asserts each `(key, value)`; `""` is the empty value.
    fn expect(&self, want: &[(&str, String)]) {
        // Every mismatch is listed before failing (a diagnostic, not a retry).
        let bad: Vec<String> = want
            .iter()
            .filter(|(k, v)| self.get(k) != v.as_str())
            .map(|(k, v)| format!("`{k}`: block `{}`, expected `{v}`", self.get(k)))
            .collect();
        assert!(bad.is_empty(), "conformance: B: {}: {}", self.what, bad.join("; "));
    }
}

fn is_mean(v: &str) -> bool {
    match v.split_once('.') {
        Some((a, b)) => {
            !a.is_empty()
                && a.bytes().all(|c| c.is_ascii_digit())
                && b.len() == 3
                && b.bytes().all(|c| c.is_ascii_digit())
        }
        None => false,
    }
}

/// `text` must end with exactly one block: the marker once, at a line start,
/// then MEAS-0.1's keys in order (without the specification keys unless
/// `with_spec`), each `key: value` with its form, and nothing after. Returns
/// the text before the block and the block.
fn parse(text: &str, with_spec: bool, what: &str) -> (String, Block) {
    assert_eq!(text.matches(MARKER).count(), 1, "conformance: B: {what}: one marker: {text}");
    assert!(text.ends_with('\n'), "conformance: B: {what}: the block ends a line");
    let lines: Vec<&str> = text[..text.len() - 1].split('\n').collect();
    let m = lines
        .iter()
        .position(|l| *l == MARKER)
        .unwrap_or_else(|| panic!("conformance: B: {what}: the marker is not a line of its own: {text}"));
    let want: Vec<&str> = KEYS
        .iter()
        .copied()
        .filter(|k| with_spec || !SPEC_KEYS.contains(k))
        .collect();
    let kv = &lines[m + 1..];
    assert_eq!(kv.len(), want.len(), "conformance: B: {what}: the number of keys: {text}");
    let mut vals = HashMap::new();
    for (line, key) in kv.iter().zip(&want) {
        let (k, v) = line
            .split_once(": ")
            .unwrap_or_else(|| panic!("conformance: B: {what}: `{line}` is not `key: value`"));
        assert_eq!(k, *key, "conformance: B: {what}: the key order");
        if *key == "stop_reason" {
            assert!(STOPS.contains(&v), "conformance: B: {what}: stop_reason `{v}`");
        } else if MEANS.contains(key) {
            assert!(v.is_empty() || is_mean(v), "conformance: B: {what}: `{key}: {v}` is not %.3f");
        } else {
            assert!(
                v.bytes().all(|c| c.is_ascii_digit()),
                "conformance: B: {what}: `{key}: {v}` is not an integer or empty"
            );
        }
        vals.insert(k.to_owned(), v.to_owned());
    }
    let before = if m == 0 {
        String::new()
    } else {
        format!("{}\n", lines[..m].join("\n"))
    };
    (
        before,
        Block {
            what: what.to_owned(),
            vals,
        },
    )
}

fn s<T: ToString>(v: T) -> String {
    v.to_string()
}

fn mean3(sum: usize, n: usize) -> String {
    format!("{:.3}", sum as f64 / n as f64)
}

/// Σ over the threads of their label counts (MEAS-1's graph events), max and
/// mean over `gs`.
fn graph_events(gs: &[ExecutionGraph]) -> (String, String) {
    let ev: Vec<usize> = gs
        .iter()
        .map(|g| g.thread_ids().into_iter().map(|t| g.thread_size(t)).sum())
        .collect();
    (
        s(ev.iter().max().copied().unwrap_or(0)),
        mean3(ev.iter().sum(), ev.len()),
    )
}

/// A summary file's lines: count, longest line in bytes, max Σ|words|, the
/// largest order count, the most non-zero order counts.
fn file_shape(path: &Path) -> (usize, usize, usize, u64, usize) {
    let text = std::fs::read_to_string(path).expect("conformance: B: a summary file");
    let lines: Vec<&str> = text.lines().skip(1).collect();
    let mut out = (lines.len(), 0, 0, 0, 0);
    for l in &lines {
        let v: serde_json::Value = serde_json::from_str(l).expect("conformance: B: a JSON line");
        let words: usize = v["words"]
            .as_object()
            .expect("conformance: B: words")
            .values()
            .map(|w| w.as_array().expect("conformance: B: a word").len())
            .sum();
        let counts: Vec<u64> = v["counts"]
            .as_array()
            .expect("conformance: B: counts")
            .iter()
            .map(|c| c.as_u64().expect("conformance: B: a count"))
            .collect();
        out.1 = out.1.max(l.len());
        out.2 = out.2.max(words);
        out.3 = out.3.max(counts.iter().copied().max().unwrap_or(0));
        out.4 = out.4.max(counts.iter().filter(|c| **c != 0).count());
    }
    out
}

fn cli(p: &Prog, args: &[&str]) -> (String, u8) {
    let a: Vec<String> = args.iter().map(|x| (*x).to_owned()).collect();
    crate::program::run_cli(&p.program(), &a)
}

// =========================================================================
// K1: `row` through `record::run_row` (MEAS-1 K1)
// =========================================================================

const L_STATEFUL: &str = "Stateful/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set";
const L_SVP1: &str = "SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=1";
const L_CF_STOP: &str = "CompleteFirst/Plain/stop=true/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set";
const L_CF_PRE: &str = "CompleteFirst/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=true/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set";
const L_EXPLORE: &str = "Explore/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep";
const L_EXPLOREP1: &str = "ExploreP/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/threads=1";
const L_REFUSED: &str = "CompleteFirst/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Flat";

fn k1_json(label: &str) -> String {
    format!(
        r#"{{"fixture":"b-po","label":"{label}","rep":0,"tier":{{"name":"c1h","wall_ms":3600000,"mem_kb":262144000}},"run_kind":"timed","family":"b","knobs":"","k":[null,null,null,null],"variant":"bug","twin_key":""}}"#
    )
}

/// The K1 subject: P_o's specification against `bug`, Bag, seed 0.
fn k1_subject(name: &str) -> Subject {
    Subject {
        name: name.to_owned(),
        config: Config::builder()
            .with_cons_type(ConsType::Bag)
            .with_seed(0)
            .build(),
        visible: vis(),
        implementation: imp_of(Var::Bug),
        specification: Arc::new(|| body(Var::Spec)),
    }
}

/// A record cell, `Some(n)` unwrapped, `None` as empty.
fn cell(c: &HashMap<String, String>, k: &str) -> String {
    let v = c
        .get(k)
        .unwrap_or_else(|| panic!("conformance: B: K1: no cell `{k}`"))
        .clone();
    if v == "None" {
        return String::new();
    }
    match v.strip_prefix("Some(").and_then(|x| x.strip_suffix(')')) {
        Some(x) => x.to_owned(),
        None => v,
    }
}

/// MEAS-1 K1's `stop_reason` from the record.
fn k1_stop(c: &HashMap<String, String>) -> &'static str {
    let end = if cell(c, "impl_end").is_empty() {
        cell(c, "end")
    } else {
        cell(c, "impl_end")
    };
    let spec_errors: u64 = cell(c, "spec_errors").parse().unwrap_or(0);
    if cell(c, "end_class") == "panicked"
        || spec_errors > 0
        || cell(c, "verdict") == "Err"
        || end.starts_with("SpecNotAssertionSafe")
        || end.starts_with("Unknown")
    {
        "error"
    } else if end.starts_with("StoppedAtFirstReport") {
        "first-miss"
    } else if end.starts_with("MaxIterations") {
        "budget"
    } else {
        "exhausted"
    }
}

/// MEAS-1 K1's map, conformance engines on the record route (Stateful,
/// SverifyP, CompleteFirst at one thread).
fn k1_conformance(engine: &str, c: &HashMap<String, String>) -> Vec<(&'static str, String)> {
    let (spec_phase, impl_phase) = match engine {
        "Stateful" | "SverifyP" => (cell(c, "spec_wall_time_ms"), cell(c, "impl_wall_time_ms")),
        _ => (cell(c, "sweep_wall_time_ms"), cell(c, "impl_phase_wall_ms")),
    };
    let fmw = cell(c, "wall_ms_at_first_report");
    let parallel = engine == "SverifyP";
    vec![
        ("wall_ms", cell(c, "wall_ms")),
        ("explore_ms", s("")),
        ("explore_spec_ms", s("")),
        ("explore_impl_ms", s("")),
        ("spec_phase_ms", spec_phase),
        ("impl_phase_ms", impl_phase),
        ("summarise_ms", s("")),
        ("index_ms", s("")),
        ("lookup_ms", s("")),
        ("export_ms", s("0")),
        ("join_ms", s("0")),
        ("graphs_complete", cell(c, "impl_complete")),
        ("graphs_blocked", cell(c, "impl_blocked")),
        ("spec_complete", cell(c, "spec_complete")),
        ("spec_blocked", cell(c, "spec_blocked")),
        ("impl_complete", cell(c, "impl_complete")),
        ("impl_blocked", cell(c, "impl_blocked")),
        ("summaries_distinct", cell(c, "impl_distinct_summaries")),
        ("impl_summaries", cell(c, "impl_distinct_summaries")),
        (
            "spec_summaries",
            if engine == "CompleteFirst" { s("") } else { cell(c, "orders_held") },
        ),
        ("iterations", cell(c, "executions")),
        ("stop_reason", s(k1_stop(c))),
        ("peak_rss_kb", cell(c, "vm_hwm_kb_after")),
        ("first_miss_iteration", s("")),
        ("first_miss_wall_ms", if fmw.is_empty() { s("0") } else { fmw }),
        (
            "uncovered_total",
            if parallel { cell(c, "uncovered_multiplicity") } else { cell(c, "counter_reports") },
        ),
        ("max_graph_events", s("")),
        ("mean_graph_events", s("")),
        ("max_message_events", s("")),
        ("max_porf_pairs", s("")),
        ("max_visible_events", s("")),
        ("mean_visible_events", s("")),
        ("max_summary_bytes", s("")),
        ("max_porf_count", s("")),
        (
            "precheck_ms",
            if engine == "CompleteFirst" { cell(c, "precheck_wall_time_ms") } else { s("0") },
        ),
        ("merge_ms", if parallel { s("") } else { s("0") }),
        ("uncovered_distinct", s("")),
    ]
}

/// MEAS-1 K1's map for Explore and ExploreP; `xbase` is Explore's split line.
fn k1_explore(explore_p: bool, c: &HashMap<String, String>, xbase: &str) -> Vec<(&'static str, String)> {
    let x: HashMap<&str, &str> = xbase
        .trim_start_matches("xbase: ")
        .trim_end()
        .split(' ')
        .filter_map(|kv| kv.split_once('='))
        .collect();
    let mut v = vec![
        ("wall_ms", cell(c, "wall_ms")),
        ("explore_ms", s("")),
        ("explore_spec_ms", s("")),
        ("explore_impl_ms", s("")),
        ("summarise_ms", s("0")),
        ("index_ms", s("0")),
        ("lookup_ms", s("0")),
        ("export_ms", s("0")),
        ("join_ms", s("0")),
        ("summaries_distinct", s("0")),
        ("spec_summaries", s("0")),
        ("impl_summaries", s("0")),
        ("iterations", cell(c, "executions")),
        ("stop_reason", s(if cell(c, "end_class") == "panicked" { "error" } else { "exhausted" })),
        ("peak_rss_kb", cell(c, "vm_hwm_kb_after")),
        ("mean_graph_events", s("")),
        ("max_message_events", s("")),
        ("max_visible_events", s("0")),
        ("mean_visible_events", s("0.000")),
        ("max_summary_bytes", s("0")),
        ("max_porf_count", s("0")),
        ("max_porf_pairs", s("0")),
        ("precheck_ms", s("0")),
        ("merge_ms", s("0")),
        ("uncovered_distinct", s("")),
    ];
    if explore_p {
        v.extend([
            ("spec_phase_ms", cell(c, "spec_wall_time_ms")),
            ("impl_phase_ms", cell(c, "impl_wall_time_ms")),
            ("graphs_complete", cell(c, "impl_complete")),
            ("graphs_blocked", cell(c, "impl_blocked")),
            ("spec_complete", cell(c, "spec_complete")),
            ("spec_blocked", cell(c, "spec_blocked")),
            ("impl_complete", cell(c, "impl_complete")),
            ("impl_blocked", cell(c, "impl_blocked")),
        ]);
    } else {
        v.extend([
            ("spec_phase_ms", s("0")),
            ("impl_phase_ms", cell(c, "wall_ms")),
            ("graphs_complete", s(x["execs"])),
            ("graphs_blocked", s(x["block"])),
            ("spec_complete", s("0")),
            ("spec_blocked", s("0")),
            ("impl_complete", s(x["execs"])),
            ("impl_blocked", s(x["block"])),
            ("max_graph_events", s(x["max_graph_events"])),
        ]);
    }
    v
}

/// **K1** (MEAS-2): `row` on Stateful, SverifyP t1, CompleteFirst stop=true,
/// CompleteFirst with `precheck` (the `Verdict` route), Explore, ExploreP t1
/// and a refused configuration; each block against its record by K1's map and
/// against the derivation's hand values (§4). Failing directions F1, F4–F8,
/// F11, F12, an offline row filling `explore_*`.
#[test]
fn b_k1_row_blocks() {
    let header = record::header();
    let row = |label: &str| {
        let lines = record::run_row(&k1_json(label), "B", k1_subject)
            .unwrap_or_else(|e| panic!("conformance: B: K1: {label}: refused: {e}"));
        let cells: HashMap<String, String> = header
            .iter()
            .map(|h| (*h).to_owned())
            .zip(record_cells(&lines.record))
            .collect();
        (lines, cells)
    };
    // Stateful, SverifyP t1, CompleteFirst stop=true: the record route.
    for (label, engine, anchors) in [
        (
            L_STATEFUL,
            "Stateful",
            vec![("iterations", s(24)), ("uncovered_total", s(16)), ("spec_summaries", s(2)), ("graphs_complete", s(""))],
        ),
        (
            L_SVP1,
            "SverifyP",
            vec![
                ("graphs_complete", s(24)),
                ("graphs_blocked", s(0)),
                ("spec_complete", s(2)),
                ("spec_blocked", s(0)),
                ("uncovered_total", s(16)),
                ("stop_reason", s("exhausted")),
            ],
        ),
        (
            L_CF_STOP,
            "CompleteFirst",
            vec![("stop_reason", s("first-miss")), ("uncovered_total", s(1))],
        ),
    ] {
        let (lines, c) = row(label);
        let text = lines.measurements.render();
        let (before, b) = parse(&text, true, &format!("K1 {engine} {}", &label[..30.min(label.len())]));
        assert!(before.is_empty(), "conformance: B: K1: the block alone");
        b.expect(&anchors);
        b.expect(&k1_conformance(engine, &c));
        note!("K1\t{engine}\t{}", text.replace('\n', " | "));
    }
    // CompleteFirst with precheck: the `Verdict` route (K6's column).
    {
        let (lines, c) = row(L_CF_PRE);
        let text = lines.measurements.render();
        let (_, b) = parse(&text, true, "K1 CompleteFirst precheck");
        b.expect(&[
            ("wall_ms", cell(&c, "wall_ms")),
            ("peak_rss_kb", cell(&c, "vm_hwm_kb_after")),
            ("iterations", cell(&c, "executions")),
            ("uncovered_total", cell(&c, "reports")),
            ("precheck_ms", cell(&c, "precheck_wall_time_ms")),
            ("stop_reason", s(k1_stop(&c))),
            ("graphs_complete", s("")),
            ("graphs_blocked", s("")),
            ("spec_complete", s("")),
            ("spec_summaries", s("")),
            ("summaries_distinct", s("")),
            ("explore_ms", s("")),
            ("explore_spec_ms", s("")),
            ("explore_impl_ms", s("")),
            ("summarise_ms", s("")),
            ("index_ms", s("")),
            ("lookup_ms", s("")),
            ("first_miss_iteration", s("")),
            ("uncovered_distinct", s("")),
            ("max_summary_bytes", s("")),
            ("export_ms", s("0")),
            ("join_ms", s("0")),
            ("merge_ms", s("0")),
        ]);
        assert_eq!(b.get("uncovered_total"), "16", "conformance: B: K1: precheck: 16 uncovered");
        let (sp, ip) = (b.n("spec_phase_ms"), b.n("impl_phase_ms"));
        let engine_wall: u128 = cell(&c, "engine_wall_time_ms").parse().expect("conformance: B: K1: engine wall");
        assert!(
            sp + ip <= engine_wall + 1,
            "conformance: B: K1: precheck: phases {sp} + {ip} within the engine wall {engine_wall}"
        );
        note!("K1\tCompleteFirst precheck\t{}", text.replace('\n', " | "));
    }
    // Explore and ExploreP t1: no specification keys.
    for (label, explore_p) in [(L_EXPLORE, false), (L_EXPLOREP1, true)] {
        let (lines, c) = row(label);
        let text = lines.measurements.render();
        let (_, b) = parse(&text, false, if explore_p { "K1 ExploreP" } else { "K1 Explore" });
        let xbase = lines.xbase.clone().unwrap_or_default();
        b.expect(&k1_explore(explore_p, &c, &xbase));
        if explore_p {
            b.expect(&[
                ("spec_complete", s(2)),
                ("spec_blocked", s(0)),
                ("impl_complete", s(24)),
                ("impl_blocked", s(0)),
            ]);
            assert!(b.n("max_graph_events") > 0, "conformance: B: K1: ExploreP's max_graph_events");
        } else {
            b.expect(&[("iterations", s(24)), ("graphs_complete", s(24)), ("graphs_blocked", s(0))]);
        }
        note!("K1\t{label}\t{}", text.replace('\n', " | "));
    }
    // The refused configuration: `panicked`, a block with `error`.
    let (lines, c) = row(L_REFUSED);
    assert_eq!(cell(&c, "end_class"), "panicked", "conformance: B: K1: the refused row panics");
    let (_, b) = parse(&lines.measurements.render(), true, "K1 refused");
    assert_eq!(b.get("stop_reason"), "error", "conformance: B: K1: refused → error");
}

/// `w` sends `Tag(0) … Tag(n−1)` to `r` on channel K, which is FIFO by
/// construction in the specification and the run's model in the
/// implementation: one specification graph against n! implementation graphs
/// under Bag, so the implementation phase is measurably longer.
fn burst(n: i32, fifo: bool) {
    let (tx, rx) = if fifo {
        crate::channel::Builder::<M>::new()
            .with_comm(crate::loc::CommunicationModel::LocalOrder)
            .build()
    } else {
        crate::channel::Builder::<M>::new().build()
    };
    let r = named("r", move || {
        for _ in 0..n {
            let _: M = rx.recv_msg_block();
        }
    });
    let w = named("w", move || {
        for i in 0..n {
            tx.send_msg(M::Tag(i));
        }
    });
    r.join().unwrap();
    w.join().unwrap();
}

/// **K1 and K6, the sides pinned** (the derivation-1 §6.4 vacuity note): on
/// `burst(7)` (1 against 5 040 graphs) the record's (and the outcome's)
/// implementation wall is pinned above the specification's by more than 5 ms,
/// so a side swap (F4) shows; `peak_rss_kb` = `vm_hwm_kb_after` (F5).
/// Stateful and ExploreP t1 rows; K6 Stateful through `of_verdict`.
#[test]
fn b_k1_k6_sides_pinned() {
    let header = record::header();
    let subject = |name: &str| Subject {
        name: name.to_owned(),
        config: Config::builder().with_cons_type(ConsType::Bag).with_seed(0).build(),
        visible: vec!["r".to_owned(), "w".to_owned()],
        implementation: Arc::new(|| burst(7, false)),
        specification: Arc::new(|| burst(7, true)),
    };
    for (label, spec_cell, impl_cell, with_spec) in [
        (L_STATEFUL, "spec_wall_time_ms", "impl_wall_time_ms", true),
        (L_EXPLOREP1, "spec_wall_time_ms", "impl_wall_time_ms", false),
    ] {
        let lines = record::run_row(&k1_json(label), "B", subject)
            .unwrap_or_else(|e| panic!("conformance: B: pinned: {label}: refused: {e}"));
        let c: HashMap<String, String> = header
            .iter()
            .map(|h| (*h).to_owned())
            .zip(record_cells(&lines.record))
            .collect();
        let (sw, iw): (u128, u128) = (
            cell(&c, spec_cell).parse().expect("conformance: B: pinned: spec wall"),
            cell(&c, impl_cell).parse().expect("conformance: B: pinned: impl wall"),
        );
        assert!(iw > sw + 5, "conformance: B: pinned: {label}: impl wall {iw} vs spec wall {sw}");
        let (before, after): (u128, u128) = (
            cell(&c, "vm_hwm_kb_before").parse().expect("conformance: B: pinned: VmHWM before"),
            cell(&c, "vm_hwm_kb_after").parse().expect("conformance: B: pinned: VmHWM after"),
        );
        // `VmHWM` is the process's high-water mark, shared with the tests
        // running beside this one: its growth during a row is not pinned
        // (a mutant run showed ExploreP's row with before = after); the block
        // must equal `vm_hwm_kb_after` either way, which tells F5 whenever the
        // row grew the mark (every K1 run so far: the first rows do).
        let (_, b) = parse(&lines.measurements.render(), with_spec, &format!("pinned {label}"));
        b.expect(&[
            ("spec_phase_ms", s(sw)),
            ("impl_phase_ms", s(iw)),
            ("peak_rss_kb", s(after)),
            ("iterations", cell(&c, "executions")),
        ]);
        note!("PINNED	{label}	spec {sw}	impl {iw}	VmHWM {before}->{after}");
    }
    let cc = ConfBuilder::new()
        .config(Config::builder().with_cons_type(ConsType::Bag).with_verbose(0).with_seed(0).build())
        .cons_type(ConsType::Bag)
        .visible_threads(["r".to_owned(), "w".to_owned()])
        .engine(Engine::Stateful)
        .index(IndexKind::Set)
        .build()
        .expect("conformance: B: pinned: a configuration");
    let r = crate::conformance::verify(cc, || burst(7, false), || burst(7, true));
    let o = r.as_ref().expect("conformance: B: pinned: verify").outcome();
    let sc = o.stateful_counters.as_ref().expect("conformance: B: pinned: counters");
    assert!(
        sc.impl_wall_time_ms > sc.spec_wall_time_ms + 5,
        "conformance: B: pinned: K6: impl {} vs spec {}",
        sc.impl_wall_time_ms,
        sc.spec_wall_time_ms
    );
    let (_, b) = parse(&measure::of_verdict(&r).render(), true, "pinned K6");
    b.expect(&[
        ("spec_phase_ms", s(sc.spec_wall_time_ms)),
        ("impl_phase_ms", s(sc.impl_wall_time_ms)),
    ]);
}

// =========================================================================
// K2, K3, K4, K5 through the shared main and the join (MEAS-1)
// =========================================================================

/// The shape every P_o summary has (derivation §4): Σ|words| 6, 327 bytes,
/// the largest order count 2, at most 3 non-zero counts, 8 message events.
fn po_shape() -> Vec<(&'static str, String)> {
    vec![
        ("max_visible_events", s(6)),
        ("mean_visible_events", s("6.000")),
        ("max_summary_bytes", s(327)),
        ("max_porf_count", s(2)),
        ("max_porf_pairs", s(3)),
        ("max_message_events", s(8)),
    ]
}

/// **K2** (`export`): the spec and the bug/bag implementation exports, their
/// blocks against the written files, the hand values and the kept graphs; an
/// `ExportError` after the run (assert-r) still prints a block, `error`.
/// Failing directions F1, F10, F11, F12.
#[test]
fn b_k2_export_blocks() {
    let p = o_prog();
    let dir = scratch("b-k2");
    for (side, var, m, n, lines) in [
        ("spec", Var::Spec, ConsType::FIFO, 2usize, 2usize),
        ("impl", Var::Bug, ConsType::Bag, 24, 8),
    ] {
        let f = dir.join(format!("{side}.jsonl"));
        let fs = f.to_string_lossy().into_owned();
        let model = if m == ConsType::Bag { "bag" } else { "fifo" };
        let arg = if var == Var::Bug { "bug" } else { "fixed" };
        let (text, code) = cli(&p, &["export", side, "--out", &fs, "--model", model, "--seed", "0", "--", arg]);
        assert_eq!(code, 0, "conformance: B: K2 {side}: {text}");
        let (before, b) = parse(&text, false, &format!("K2 {side}"));
        assert_eq!(
            before,
            format!("exported: {lines} lines from {n} graphs to {fs}\n"),
            "conformance: B: K2 {side}: the export's own line"
        );
        let (fl, longest, words, porf, pairs) = file_shape(&f);
        assert_eq!((fl, longest, words, porf, pairs), (lines, 327, 6, 2, 3), "conformance: B: K2 {side}: the file");
        let gs = if side == "spec" {
            reference(Var::Fixed, ConsType::FIFO, false).kept_spec_graphs
        } else {
            reference(Var::Bug, ConsType::Bag, false).kept_impl_graphs
        };
        assert_eq!(gs.len(), n, "conformance: B: K2 {side}: the reference's graphs");
        let (gmax, gmean) = graph_events(&gs);
        let explore = s(b.n("explore_ms"));
        let (es, ei) = if side == "spec" { (explore.clone(), s(0)) } else { (s(0), explore.clone()) };
        let mut want = vec![
            ("iterations", s(n)),
            ("graphs_complete", s(n)),
            ("graphs_blocked", s(0)),
            ("summaries_distinct", s(fl)),
            ("stop_reason", s("exhausted")),
            ("index_ms", s(0)),
            ("lookup_ms", s(0)),
            ("join_ms", s(0)),
            ("explore_spec_ms", es),
            ("explore_impl_ms", ei),
            ("max_summary_bytes", s(longest)),
            ("max_visible_events", s(words)),
            ("max_porf_count", s(porf)),
            ("max_porf_pairs", s(pairs)),
            ("max_graph_events", gmax),
            ("mean_graph_events", gmean),
        ];
        want.extend(po_shape());
        b.expect(&want);
        b.n("summarise_ms");
        b.n("export_ms");
        assert!(b.n("wall_ms") >= b.n("explore_ms"), "conformance: B: K2 {side}: wall ≥ explore");
        note!("K2\t{side}\t{}", text.replace('\n', " | "));
    }
    // An `ExportError` after the run.
    let f = dir.join("assert.jsonl");
    let fs = f.to_string_lossy().into_owned();
    let (text, code) = cli(&p, &["export", "impl", "--out", &fs, "--model", "fifo", "--seed", "0", "--", "assert-r"]);
    assert_eq!(code, 2, "conformance: B: K2: assert-r is refused: {text}");
    let (_, b) = parse(&text, false, "K2 refused after the run");
    assert_eq!(b.get("stop_reason"), "error", "conformance: B: K2: error");
    b.n("wall_ms");
}

/// **K3** (`conf-join`'s library path, `JoinReport::measurements`): S against
/// the bug/bag export: `spec_summaries` 2, `impl_summaries` 8,
/// `uncovered_distinct` 6 (lines, not the 8 implementation lines: F9),
/// `uncovered_total` empty, the shape over the implementation file; a refused
/// file gives `error`. Failing directions F9, F10, F12.
#[test]
fn b_k3_join_blocks() {
    let p = o_prog();
    let dir = scratch("b-k3");
    let s_path = spec_file(&p, &dir);
    let e = dir.join("impl.jsonl");
    let es = e.to_string_lossy().into_owned();
    let (t, c) = cli(&p, &["export", "impl", "--out", &es, "--model", "bag", "--seed", "0", "--", "bug"]);
    assert_eq!(c, 0, "conformance: B: K3: the export: {t}");
    let (fl, longest, words, porf, pairs) = file_shape(&e);
    let started = Instant::now();
    let r = conf_join_with(&s_path, &e, JoinSeams::default()).expect("conformance: B: K3: the join");
    let text = r.measurements(started.elapsed().as_millis());
    let (_, b) = parse(&text, true, "K3");
    b.expect(&[
        ("explore_ms", s(0)),
        ("explore_spec_ms", s(0)),
        ("explore_impl_ms", s(0)),
        ("summarise_ms", s(0)),
        ("export_ms", s(0)),
        ("graphs_complete", s(0)),
        ("graphs_blocked", s(0)),
        ("iterations", s(0)),
        ("spec_summaries", s(2)),
        ("impl_summaries", s(fl)),
        ("summaries_distinct", s(fl)),
        ("first_miss_iteration", s(0)),
        ("first_miss_wall_ms", s(0)),
        ("uncovered_total", s("")),
        ("uncovered_distinct", s(6)),
        ("max_summary_bytes", s(longest)),
        ("max_visible_events", s(words)),
        ("max_porf_count", s(porf)),
        ("max_porf_pairs", s(pairs)),
        ("mean_visible_events", s("")),
        ("max_graph_events", s("")),
        ("mean_graph_events", s("")),
        ("max_message_events", s("")),
        ("stop_reason", s("exhausted")),
    ]);
    assert_eq!((fl, longest), (8, 327), "conformance: B: K3: the implementation file");
    assert!(
        b.n("join_ms") >= b.n("index_ms") + b.n("lookup_ms"),
        "conformance: B: K3: join_ms encloses its phases"
    );
    note!("K3\t{}", text.replace('\n', " | "));
    // A refused file: a block, `error`.
    let bad = dir.join("bounded.jsonl");
    let st = std::fs::read_to_string(&s_path).unwrap();
    std::fs::write(&bad, st.replacen("\"complete\"", "\"bounded\"", 1)).unwrap();
    assert!(conf_join_with(&bad, &e, JoinSeams::default()).is_err(), "conformance: B: K3: refused");
    let text = interchange::JoinReport::refused_measurements(1);
    let (_, b) = parse(&text, true, "K3 refused");
    assert_eq!(b.get("stop_reason"), "error", "conformance: B: K3: refused → error");
}

/// **K4** (`online`): full mode with and without `--out`, a conforming run,
/// bug-finder, a budget and a failure; each block against C's printed lines,
/// the hand values and the kept graphs. Failing directions F7, F8, F10, K4's
/// `summaries_distinct` empty or counted only with `--out`.
#[test]
fn b_k4_online_blocks() {
    let p = o_prog();
    let dir = scratch("b-k4");
    let s_path = spec_file(&p, &dir);
    let ss = s_path.to_string_lossy().into_owned();
    let out = dir.join("out.jsonl");
    let outs = out.to_string_lossy().into_owned();
    let bug_graphs = reference(Var::Bug, ConsType::Bag, false).kept_impl_graphs;
    let fix_graphs = reference(Var::Fixed, ConsType::FIFO, false).kept_impl_graphs;
    // (args, graphs, iterations, distinct, uncovered, stop, exit)
    let cases: Vec<(Vec<&str>, &[ExecutionGraph], usize, usize, usize, &str, u8)> = vec![
        (vec!["--model", "bag", "--seed", "0", "--", "bug"], bug_graphs.as_slice(), 24, 8, 16, "exhausted", 0),
        (vec!["--out", outs.as_str(), "--model", "bag", "--seed", "0", "--", "bug"], bug_graphs.as_slice(), 24, 8, 16, "exhausted", 0),
        (vec!["--model", "fifo", "--seed", "0", "--", "fixed"], fix_graphs.as_slice(), 12, 2, 0, "exhausted", 0),
    ];
    for (args, gs, n, d, u, stop, exit) in cases {
        let mut a = vec!["online", "--spec", ss.as_str()];
        a.extend(args.iter().copied());
        let (text, code) = cli(&p, &a);
        assert_eq!(code, exit, "conformance: B: K4 {args:?}: {text}");
        let what = format!("K4 {args:?}");
        let (before, b) = parse(&text, true, &what);
        let (fi, ft) = first_miss_of(&before).map_or((0, 0), |(i, t)| (i, t as usize));
        assert!(
            before.contains(&format!("uncovered:  {u} graphs")),
            "conformance: B: {what}: C's uncovered line: {before}"
        );
        let (gmax, gmean) = graph_events(gs);
        let explore = s(b.n("explore_ms"));
        let mut want = vec![
            ("iterations", s(n)),
            ("graphs_complete", s(n)),
            ("graphs_blocked", s(0)),
            ("impl_complete", s(n)),
            ("impl_blocked", s(0)),
            ("spec_complete", s(0)),
            ("spec_blocked", s(0)),
            ("summaries_distinct", s(d)),
            ("impl_summaries", s(d)),
            ("spec_summaries", s(2)),
            ("uncovered_total", s(u)),
            ("first_miss_iteration", s(fi)),
            ("first_miss_wall_ms", s(ft)),
            ("uncovered_distinct", s("")),
            ("explore_impl_ms", explore),
            ("explore_spec_ms", s(0)),
            ("join_ms", s(0)),
            ("spec_phase_ms", s(0)),
            ("impl_phase_ms", s(0)),
            ("precheck_ms", s(0)),
            ("merge_ms", s(0)),
            ("stop_reason", s(stop)),
            ("max_graph_events", gmax),
            ("mean_graph_events", gmean),
        ];
        want.extend(po_shape());
        if !args.contains(&"--out") {
            want.push(("export_ms", s(0)));
        }
        b.expect(&want);
        if u > 0 {
            assert!(fi >= 1, "conformance: B: {what}: a first miss");
        }
        note!("K4\t{args:?}\t{}", text.replace('\n', " | "));
    }
    // Bug-finder, a budget, a failure.
    for (args, stop, exit) in [
        (vec!["--stop-at-first", "--model", "bag", "--seed", "0", "--", "bug"], "first-miss", 0u8),
        (vec!["--budget", "3", "--model", "fifo", "--seed", "0", "--", "fixed"], "budget", 0),
        (vec!["--model", "fifo", "--seed", "0", "--", "ch2"], "error", 1),
    ] {
        let mut a = vec!["online", "--spec", ss.as_str()];
        a.extend(args.iter().copied());
        let (text, code) = cli(&p, &a);
        assert_eq!(code, exit, "conformance: B: K4 {args:?}: {text}");
        let what = format!("K4 {args:?}");
        let (before, b) = parse(&text, true, &what);
        assert_eq!(b.get("stop_reason"), stop, "conformance: B: {what}: stop_reason");
        let lookups: usize = before
            .lines()
            .find_map(|l| l.strip_prefix("lookups:    "))
            .and_then(|l| l.split(' ').next())
            .and_then(|x| x.parse().ok())
            .expect("conformance: B: K4: C's lookups line");
        match stop {
            "first-miss" => {
                let (i, _) = first_miss_of(&before).expect("conformance: B: K4: a first miss");
                b.expect(&[("iterations", s(i)), ("uncovered_total", s(1)), ("first_miss_iteration", s(i))]);
            }
            "budget" => b.expect(&[("iterations", s(3)), ("uncovered_total", s(0))]),
            _ => {
                assert_eq!(b.n("iterations"), lookups as u128 + 1, "conformance: B: {what}: the failed completion is counted");
                // MEAS-1 K4: the shape counters run over the summarised graphs,
                // i.e. the `lookups` completions before the refused one.
                let ch = reference(Var::Ch2, ConsType::FIFO, false).kept_impl_graphs;
                let (gmax, gmean) = graph_events(&ch[..lookups]);
                b.expect(&[
                    ("max_graph_events", gmax),
                    ("mean_graph_events", gmean),
                    ("graphs_complete", s(lookups + 1)),
                    ("max_summary_bytes", s(327)),
                    ("mean_visible_events", s("6.000")),
                ]);
            }
        }
        note!("K4\t{args:?}\t{}", text.replace('\n', " | "));
    }
}

/// **K5** (`count`): the block against `crate::verify`'s `Stats` on the same
/// configuration. Failing directions F11 (no specification keys), F6.
#[test]
fn b_k5_count_blocks() {
    let p = o_prog();
    for (side, var, m, model, arg) in [
        ("impl", Var::Bug, ConsType::Bag, "bag", "bug"),
        ("spec", Var::Spec, ConsType::Bag, "bag", "bug"),
    ] {
        let stats = crate::verify(
            Config::builder()
                .with_cons_type(m)
                .with_verbose(0)
                .with_seed(0)
                .with_keep_going_after_error(true)
                .build(),
            move || body(var),
        );
        let (text, code) = cli(&p, &["count", side, "--model", model, "--seed", "0", "--", arg]);
        assert_eq!(code, 0, "conformance: B: K5 {side}");
        let what = format!("K5 {side}");
        let (before, b) = parse(&text, false, &what);
        assert_eq!(
            before,
            format!("execs={} blocked={}\n", stats.execs, stats.block),
            "conformance: B: {what}: the count's own line"
        );
        let explore = s(b.n("explore_ms"));
        let (es, ei) = if side == "spec" { (explore, s(0)) } else { (s(0), explore) };
        b.expect(&[
            ("graphs_complete", s(stats.execs)),
            ("graphs_blocked", s(stats.block)),
            ("iterations", s(stats.execs + stats.block)),
            ("max_graph_events", s(stats.max_graph_events)),
            ("mean_graph_events", s("")),
            ("max_message_events", s("")),
            ("max_visible_events", s(0)),
            ("mean_visible_events", s("0.000")),
            ("max_summary_bytes", s(0)),
            ("max_porf_count", s(0)),
            ("max_porf_pairs", s(0)),
            ("summarise_ms", s(0)),
            ("index_ms", s(0)),
            ("lookup_ms", s(0)),
            ("export_ms", s(0)),
            ("join_ms", s(0)),
            ("explore_spec_ms", es),
            ("explore_impl_ms", ei),
            ("stop_reason", s("exhausted")),
        ]);
        let n = if side == "spec" { 2 } else { 24 };
        assert_eq!((stats.execs, stats.block), (n, 0), "conformance: B: {what}: the hand count");
        note!("K5\t{side}\t{}", text.replace('\n', " | "));
    }
}

// =========================================================================
// K6: `conf`, every engine (MEAS-1 K6)
// =========================================================================

fn opt_s(v: Option<u128>) -> String {
    v.map_or_else(String::new, s)
}

/// **K6** (round 01 M4): Stateful, SverifyP (t2), CompleteFirst, CFirstP (t2),
/// Gated and Enumerator, each on bug/bag (violating) and fixed/fifo
/// (conforming): the block of `measure::of_verdict` on a `verify` result
/// against the fields K6's table names in that result's `ConfOutcome`, every
/// empty and 0 cell; then `conf` through `run_cli` (its block's counts against
/// the same fields). Failing directions: a key from the wrong family; Gated or
/// Enumerator filling `uncovered_total`; F6, F8.
#[test]
fn b_k6_every_engine() {
    let p = o_prog();
    for (name, engine, threads, set) in [
        ("stateful", Engine::Stateful, 1, true),
        ("stateful", Engine::SverifyP, 2, true),
        ("stateless", Engine::CompleteFirst, 1, true),
        ("stateless", Engine::CFirstP, 2, true),
        ("gated", Engine::Gated, 1, false),
        ("enumerator", Engine::Enumerator, 1, false),
    ] {
        for (var, m, model, arg, violating) in [
            (Var::Bug, ConsType::Bag, "bag", "bug", true),
            (Var::Fixed, ConsType::FIFO, "fifo", "fixed", false),
        ] {
            let what = format!("K6 {engine:?} t{threads} {arg}/{model}");
            let mut cb = ConfBuilder::new()
                .config(Config::builder().with_cons_type(m).with_verbose(0).with_seed(0).build())
                .cons_type(m)
                .visible_threads(vis())
                .engine(engine)
                .threads(threads);
            if set {
                cb = cb.index(IndexKind::Set);
            }
            let cc = cb.build().unwrap_or_else(|e| panic!("conformance: B: {what}: {e:?}"));
            let r = crate::conformance::verify(cc, move || body(var), || body(Var::Spec));
            let text = measure::of_verdict(&r).render();
            let (_, b) = parse(&text, true, &what);
            let v = r.as_ref().unwrap_or_else(|e| panic!("conformance: B: {what}: {e:?}"));
            let o = v.outcome();
            let sf = o.stateful_counters.as_ref();
            let sv = o.counters.sverify_p.as_ref();
            let cf = o.cfirst_counters.as_ref();
            let cp = o.counters.cfirst_p.as_ref();
            let gt = o.gated_counters.as_ref();
            let e = || s("");
            let (spec_phase, impl_phase, graphs, spec_g, distinct, spec_sum, unc, fmw, pre, merge) = match engine {
                Engine::Stateful => {
                    let c = sf.expect("conformance: B: stateful counters");
                    (
                        s(c.spec_wall_time_ms),
                        s(c.impl_wall_time_ms),
                        (e(), e()),
                        (e(), e()),
                        opt_s(c.impl_distinct_summaries.map(|x| x as u128)),
                        s(c.orders_held),
                        s(o.report_count),
                        s(c.wall_ms_at_first_report.unwrap_or(0)),
                        s(0),
                        s(0),
                    )
                }
                Engine::SverifyP => {
                    let c = sv.expect("conformance: B: sverify_p counters");
                    (
                        s(c.spec_wall_time_ms),
                        s(c.impl_wall_time_ms),
                        (s(c.impl_complete), s(c.impl_blocked)),
                        (s(c.spec_complete), s(c.spec_blocked)),
                        opt_s(c.impl_distinct_summaries.map(|x| x as u128)),
                        s(c.orders_held),
                        s(o.report_count),
                        s(c.wall_ms_at_first_report.unwrap_or(0)),
                        s(0),
                        e(),
                    )
                }
                Engine::CompleteFirst => {
                    let c = cf.expect("conformance: B: cfirst counters");
                    (
                        s(c.sweep_wall_time_ms),
                        s(c.outer_wall_time_ms - c.sweep_wall_time_ms),
                        (e(), e()),
                        (e(), e()),
                        e(),
                        e(),
                        s(o.report_count),
                        s(c.wall_ms_at_first_report.unwrap_or(0)),
                        s(c.precheck_wall_time_ms),
                        s(0),
                    )
                }
                Engine::CFirstP => {
                    let c = cp.expect("conformance: B: cfirst_p counters");
                    (
                        e(),
                        e(),
                        (e(), e()),
                        (e(), e()),
                        opt_s(c.impl_distinct_summaries.map(|x| x as u128)),
                        e(),
                        s(c.uncovered_multiplicity),
                        s(c.base.wall_ms_at_first_report.unwrap_or(0)),
                        s(c.base.precheck_wall_time_ms),
                        e(),
                    )
                }
                Engine::Gated => {
                    let c = gt.expect("conformance: B: gated counters");
                    (
                        s(c.sweep_wall_time_ms),
                        e(),
                        (e(), e()),
                        (e(), e()),
                        e(),
                        e(),
                        e(),
                        e(),
                        s(c.precheck_wall_time_ms),
                        s(0),
                    )
                }
                _ => (e(), s(o.counters.wall_time_ms), (e(), e()), (e(), e()), e(), e(), e(), e(), s(0), s(0)),
            };
            b.expect(&[
                ("spec_phase_ms", spec_phase),
                ("impl_phase_ms", impl_phase),
                ("graphs_complete", graphs.0.clone()),
                ("graphs_blocked", graphs.1.clone()),
                ("impl_complete", graphs.0),
                ("impl_blocked", graphs.1),
                ("spec_complete", spec_g.0),
                ("spec_blocked", spec_g.1),
                ("summaries_distinct", distinct.clone()),
                ("impl_summaries", distinct),
                ("spec_summaries", spec_sum),
                ("uncovered_total", unc),
                ("first_miss_wall_ms", fmw),
                ("precheck_ms", pre),
                ("merge_ms", merge),
                ("iterations", s(o.counters.executions)),
                ("stop_reason", s("exhausted")),
                ("explore_ms", e()),
                ("explore_spec_ms", e()),
                ("explore_impl_ms", e()),
                ("summarise_ms", e()),
                ("index_ms", e()),
                ("lookup_ms", e()),
                ("first_miss_iteration", e()),
                ("uncovered_distinct", e()),
                ("max_graph_events", e()),
                ("mean_graph_events", e()),
                ("max_message_events", e()),
                ("max_porf_pairs", e()),
                ("max_visible_events", e()),
                ("mean_visible_events", e()),
                ("max_summary_bytes", e()),
                ("max_porf_count", e()),
                ("export_ms", s(0)),
                ("join_ms", s(0)),
            ]);
            // The hand anchors (derivation §4).
            let reported = o.report_count;
            match engine {
                Engine::Stateful | Engine::SverifyP | Engine::CompleteFirst => assert_eq!(
                    reported,
                    if violating { 16 } else { 0 },
                    "conformance: B: {what}: report_count"
                ),
                Engine::CFirstP => assert_eq!(
                    cp.unwrap().uncovered_multiplicity,
                    if violating { 16 } else { 0 },
                    "conformance: B: {what}: uncovered_multiplicity"
                ),
                _ => assert_eq!(reported > 0, violating, "conformance: B: {what}: a report count"),
            }
            if engine == Engine::SverifyP {
                b.expect(&[
                    ("impl_complete", s(if violating { 24 } else { 12 })),
                    ("spec_complete", s(2)),
                    ("spec_summaries", s(2)),
                ]);
            }
            // `conf` through the shared main: its block's counts.
            let ts = threads.to_string();
            let (ctext, code) = cli(
                &p,
                &["conf", "--engine", name, "--threads", &ts, "--model", model, "--seed", "0", "--", arg],
            );
            assert_eq!(code, if violating { 1 } else { 0 }, "conformance: B: {what}: conf's exit: {ctext}");
            let (_, cb) = parse(&ctext, true, &format!("{what} conf"));
            for k in ["uncovered_total", "spec_summaries", "graphs_complete", "graphs_blocked", "stop_reason"] {
                assert_eq!(cb.get(k), b.get(k), "conformance: B: {what}: conf's `{k}`");
            }
            if threads == 1 {
                assert_eq!(cb.get("iterations"), b.get("iterations"), "conformance: B: {what}: conf's iterations");
            }
            cb.n("wall_ms");
            note!("K6\t{what}\t{}", text.replace('\n', " | "));
        }
    }
}

// =========================================================================
// Timing (MEAS-2, round 01 M3, round 02 M2, round 03 M1)
// =========================================================================

/// The timing assertions of MEAS-2 on one printer. `run(delays)` runs once
/// with the given per-seam delay (`None` = every delay 0) and returns its
/// block and any extra check's input; `disjoint` and `enclosing` are the
/// printer's timer sets; `seams` names each seam, its target key and n.
fn timing<F>(printer: &str, disjoint: &[&str], enclosing: &[&str], seams: &[(&str, &str, u128)], mut run: F)
where
    F: FnMut(Option<(&str, Duration)>) -> Block,
{
    let mut b_k: HashMap<String, u128> = HashMap::new();
    for i in 0..3 {
        let b = run(None);
        let vals: Vec<String> = disjoint
            .iter()
            .chain(enclosing)
            .map(|k| format!("{k}={}", b.n(k)))
            .collect();
        note!("TIMING\t{printer}\tcontrol {i}\t{}", vals.join(" "));
        for k in disjoint.iter().chain(enclosing) {
            let e = b_k.entry((*k).to_owned()).or_insert(0);
            *e = (*e).max(b.n(k));
        }
    }
    let max_b = disjoint.iter().map(|k| b_k[*k]).max().unwrap_or(0);
    let d: u128 = 50u128.max(4 * max_b + 20);
    note!("TIMING\t{printer}\tB_k {b_k:?}\td {d}");
    for (seam, target, n) in seams {
        let b = run(Some((seam, Duration::from_millis(d as u64))));
        let vals: Vec<String> = disjoint
            .iter()
            .chain(enclosing)
            .map(|k| format!("{k}={}", b.n(k)))
            .collect();
        note!("TIMING\t{printer}\t{seam} (n {n})\t{}", vals.join(" "));
        let t = b.n(target);
        assert!(t >= n * d, "conformance: B: timing {printer}: {seam}: `{target}` {t} < n·d = {}", n * d);
        for k in disjoint {
            if k == target || (*target == "explore_ms" && k.starts_with("explore_")) {
                continue;
            }
            assert!(
                b.n(k) <= b_k[*k] + d / 2,
                "conformance: B: timing {printer}: {seam}: `{k}` {} > B_k {} + d/2 {}",
                b.n(k),
                b_k[*k],
                d / 2
            );
        }
        for k in enclosing {
            assert!(
                b.n(k) >= t && b.n(k) >= n * d,
                "conformance: B: timing {printer}: {seam}: enclosing `{k}` {} < target {t} or n·d",
                b.n(k)
            );
        }
    }
}

/// **Timing, K4** (`online` on fixed/fifo, the library call with C's and B's
/// seams). Two sets of controls (a test design within MEAS-2, after the
/// gate-3 finding that the `--out` write's fsync is not of the order of the
/// controls): without `--out` (`export_ms` 0, untimed) for the index (n 1),
/// summarise (n 12) and lookup (n 12) seams; with `--out` for the export seam
/// (n 1), where `export_ms` is the target and an fsync spike only adds to it.
/// On every run `explore_ms = enumerate_ms − summarise_ms − lookup_ms` within
/// 2 ms. Failing directions: the summarise timer around the lookup (or the
/// reverse); `explore_ms` not subtracting a phase; the index timer started
/// after the inserts; the export timer missing the write.
#[test]
fn b_timing_k4_online() {
    let p = o_prog();
    let dir = scratch("b-t4");
    let s_path = spec_file(&p, &dir);
    let out = dir.join("out.jsonl");
    let disjoint = ["index_ms", "summarise_ms", "lookup_ms", "export_ms", "explore_ms", "explore_impl_ms"];
    let run = |with_out: bool, delay: Option<(&str, Duration)>| -> Block {
        let mut o = OnlineOpts::new(
            Mode::Full,
            None,
            with_out.then(|| OnlineOut {
                path: out.clone(),
                header: ExportHeader {
                    program: "p".into(),
                    size: "z".into(),
                },
            }),
        );
        match delay {
            Some(("index", d)) => o.index_delay = Some(d),
            Some(("summarise", d)) => o.summarise_delay = Some(d),
            Some(("lookup", d)) => o.lookup_delay = Some(d),
            Some(("export", d)) => o.export_delay = Some(d),
            _ => {}
        }
        let started = Instant::now();
        let r = online::online(
            &Config::builder().with_cons_type(ConsType::FIFO).with_verbose(0).with_seed(0).build(),
            &vis(),
            imp_of(Var::Fixed),
            &s_path,
            o,
        )
        .expect("conformance: B: timing K4: not refused");
        let text = measure::of_online(&r, started.elapsed().as_millis()).render();
        let (_, b) = parse(&text, true, "timing K4");
        assert_eq!(b.n("iterations"), 12, "conformance: B: timing K4: twelve completions");
        let (ex, su, lo, en) = (b.n("explore_ms"), b.n("summarise_ms"), b.n("lookup_ms"), r.enumerate_ms);
        let want = en.saturating_sub(su + lo);
        assert!(
            ex.abs_diff(want) <= 2,
            "conformance: B: timing K4: explore_ms {ex} vs enumerate {en} − summarise {su} − lookup {lo}"
        );
        assert_eq!(b.get("explore_impl_ms"), b.get("explore_ms"), "conformance: B: timing K4: the copy");
        if !with_out {
            assert_eq!(b.n("export_ms"), 0, "conformance: B: timing K4: no --out, no export");
        }
        b
    };
    timing(
        "K4",
        &disjoint,
        &["wall_ms"],
        &[("index", "index_ms", 1), ("summarise", "summarise_ms", 12), ("lookup", "lookup_ms", 12)],
        |delay| run(false, delay),
    );
    timing(
        "K4 --out",
        &disjoint,
        &["wall_ms"],
        &[("export", "export_ms", 1)],
        |delay| run(true, delay),
    );
}

/// **Timing, K2** (`export_with` of the specification, the export seam, n 1).
/// Failing direction: the export timer around the render instead of the
/// write (the delay must count in `export_ms`).
#[test]
fn b_timing_k2_export() {
    let dir = scratch("b-t2");
    let f = dir.join("spec.jsonl");
    timing(
        "K2",
        &["summarise_ms", "export_ms", "explore_ms", "explore_spec_ms"],
        &["wall_ms"],
        &[("export", "export_ms", 1)],
        |delay| {
            let cc = ConfBuilder::new()
                .config(Config::builder().with_cons_type(ConsType::FIFO).with_verbose(0).with_seed(0).build())
                .cons_type(ConsType::FIFO)
                .visible_threads(vis())
                .engine(Engine::Stateful)
                .index(IndexKind::Set)
                .build()
                .expect("conformance: B: timing K2: a configuration");
            let mut seams = ExportSeams::default();
            if let Some((_, d)) = delay {
                seams.export_delay = Some(d);
            }
            let header = ExportHeader {
                program: "o".into(),
                size: "k1".into(),
            };
            let started = Instant::now();
            let r = interchange::export_with(&cc, || body(Var::Spec), &header, &f, seams);
            assert!(r.is_ok(), "conformance: B: timing K2: the export");
            let text = measure::of_export(&r, Side::Spec, started.elapsed().as_millis()).render();
            let (_, b) = parse(&text, false, "timing K2");
            assert_eq!(b.get("explore_spec_ms"), b.get("explore_ms"), "conformance: B: timing K2: the copy");
            b
        },
    );
}

/// **Timing, K3** (`conf_join_with` of S and the fixed/fifo export, the index
/// and lookup seams, n 1 each); on every run `join_ms ≥ index_ms + lookup_ms`.
#[test]
fn b_timing_k3_join() {
    let p = o_prog();
    let dir = scratch("b-t3");
    let s_path = spec_file(&p, &dir);
    let e: PathBuf = dir.join("impl.jsonl");
    let es = e.to_string_lossy().into_owned();
    let (t, c) = cli(&p, &["export", "impl", "--out", &es, "--model", "fifo", "--seed", "0", "--", "fixed"]);
    assert_eq!(c, 0, "conformance: B: timing K3: the export: {t}");
    timing(
        "K3",
        &["index_ms", "lookup_ms"],
        &["join_ms", "wall_ms"],
        &[("index", "index_ms", 1), ("lookup", "lookup_ms", 1)],
        |delay| {
            let mut seams = JoinSeams::default();
            match delay {
                Some(("index", d)) => seams.index_delay = Some(d),
                Some(("lookup", d)) => seams.lookup_delay = Some(d),
                _ => {}
            }
            let started = Instant::now();
            let r = conf_join_with(&s_path, &e, seams).expect("conformance: B: timing K3: the join");
            let text = r.measurements(started.elapsed().as_millis());
            let (_, b) = parse(&text, true, "timing K3");
            assert!(
                b.n("join_ms") >= b.n("index_ms") + b.n("lookup_ms"),
                "conformance: B: timing K3: join_ms ≥ index_ms + lookup_ms"
            );
            b
        },
    );
}

/// The parser's own controls: a block glued to the previous line, a missing
/// key, a mean with two decimals and an unknown `stop_reason` are each refused
/// (the parser is not vacuous).
#[test]
fn b_parser_controls() {
    let mut ok = String::from("x\n--- measurements\n");
    for k in KEYS.iter().filter(|k| !SPEC_KEYS.contains(k)) {
        let v = match *k {
            "stop_reason" => "exhausted",
            "mean_graph_events" | "mean_visible_events" => "1.000",
            _ => "1",
        };
        ok.push_str(&format!("{k}: {v}\n"));
    }
    let _ = parse(&ok, false, "control ok");
    let bad: Vec<(&str, String)> = vec![
        ("glued", ok.replacen("x\n--- measurements", "x--- measurements", 1)),
        ("missing key", ok.replacen("join_ms: 1\n", "", 1)),
        ("two decimals", ok.replacen("mean_graph_events: 1.000", "mean_graph_events: 1.00", 1)),
        ("unknown stop", ok.replacen("stop_reason: exhausted", "stop_reason: done", 1)),
        ("spec keys on a no-spec block", ok.replacen("max_porf_pairs: 1\n", "max_porf_pairs: 1\nuncovered_total: 1\n", 1)),
    ];
    for (what, text) in bad {
        let r = std::panic::catch_unwind(|| {
            let _ = parse(&text, false, what);
        });
        assert!(r.is_err(), "conformance: B: the parser accepted `{what}`");
    }
    let _ = split_block("");
}
