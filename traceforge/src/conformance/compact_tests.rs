//! `COMPACT-INDEX` (the Monday slice): the tester's tests.
//!
//! Tester-owned; the lead registers the module in `mod.rs`. Written against
//! the frozen signatures of `plan/traceForge/log/dev/COMPACT-INDEX.frozen.md`
//! §3 **before** `conformance/compact.rs` existed (adapted to its landed
//! `OrdCounts::of(graph, &wobs, visible)`), from the derivation in
//! `plan/traceForge/log/dev/COMPACT-INDEX.derived.md` (sha256 in
//! `backlog/changes.md`). Heavy tests are `#[ignore]`d and run one per
//! invocation.

use std::cmp::Ordering;

use crate::conformance::compact::OrdCounts;
use crate::conformance::eval::fixture_by_name;
use crate::conformance::grid::{Fixture, GridConfig, GridEngine};
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{wobs, Wobs};
use crate::conformance::sig::{Sig, Summary, VisOrder};
use crate::conformance::stateful;
use crate::exec_graph::ExecutionGraph;

macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

/// The 132 catalogued fixtures, copied from `apps_tests.rs`'s `PILOT` (whose
/// constant is private to that module), in its order.
const PILOT_NAMES: [&str; 132] = [
    "apps/a1/correct/spec/n2r1",
    "apps/a1/correct/spec/n3r1",
    "apps/a1/correct/spec/n4r1",
    "apps/a1/correct/spec/n2r2",
    "apps/a1/correct/spec/n2r3",
    "apps/a1/control-reverse/spec/n2r1",
    "apps/a1/control-reverse/spec/n3r1",
    "apps/a1/control-reverse/spec/n4r1",
    "apps/a1/control-reverse/spec/n2r2",
    "apps/a1/control-reverse/spec/n2r3",
    "apps/a1/eager/spec/n2r1",
    "apps/a1/eager/spec/n3r1",
    "apps/a1/eager/spec/n4r1",
    "apps/a1/eager/spec/n2r2",
    "apps/a1/eager/spec/n2r3",
    "apps/a1/early-abort/spec/n2r1",
    "apps/a1/early-abort/spec/n3r1",
    "apps/a1/early-abort/spec/n4r1",
    "apps/a1/early-abort/spec/n2r2",
    "apps/a1/early-abort/spec/n2r3",
    "apps/a1/silent/spec/n2r1",
    "apps/a1/silent/spec/n3r1",
    "apps/a1/silent/spec/n4r1",
    "apps/a1/silent/spec/n2r2",
    "apps/a1/silent/spec/n2r3",
    "apps/a2/pb/spec/k1q1",
    "apps/a2/pb/spec/k2q1",
    "apps/a2/pb/spec/k3q1",
    "apps/a2/pb/spec/k1q2",
    "apps/a2/pb/spec/k1q3",
    "apps/a2/pb-br/spec/k1q1",
    "apps/a2/pb-br/spec/k2q1",
    "apps/a2/pb-br/spec/k3q1",
    "apps/a2/pb-br/spec/k1q2",
    "apps/a2/pb-br/spec/k1q3",
    "apps/a2/sh/spec/k1q1s1",
    "apps/a2/sh/spec/k2q1s1",
    "apps/a2/sh/spec/k3q1s1",
    "apps/a2/sh/spec/k1q2s1",
    "apps/a2/sh/spec/k1q3s1",
    "apps/a2/sh/spec/k1q1s2",
    "apps/a2/sh/spec/k2q1s2",
    "apps/a2/sh/spec/k3q1s2",
    "apps/a2/sh/spec/k1q3s2",
    "apps/a2/early-ack/spec/k2q1",
    "apps/a2/early-ack/spec/k3q1",
    "apps/a2/early-ack/spec/k2q2",
    "apps/a2/early-ack/spec/k2q3",
    "apps/a2/early-ack/spec/k1q2",
    "apps/a2/stale-get/spec/k2q1",
    "apps/a2/stale-get/spec/k3q1",
    "apps/a2/stale-get/spec/k2q2",
    "apps/a2/stale-get/spec/k2q3",
    "apps/a2/stale-get/spec/k1q2",
    "apps/a2/silent-put/spec/k1q1",
    "apps/a2/silent-put/spec/k2q1",
    "apps/a2/silent-put/spec/k3q1",
    "apps/a2/silent-put/spec/k1q2",
    "apps/a2/silent-put/spec/k1q3",
    "apps/a2/misroute/spec/k1q2s2",
    "apps/a2/misroute/spec/k2q2s2",
    "apps/a2/misroute/spec/k3q2s2",
    "apps/a2/misroute/spec/k1q3s2",
    "apps/a2/control-early-ack-primary/spec/k1q1",
    "apps/a2/control-early-ack-primary/spec/k2q1",
    "apps/a2/control-early-ack-primary/spec/k3q1",
    "apps/a2/control-early-ack-primary/spec/k1q2",
    "apps/a2/control-early-ack-primary/spec/k1q3",
    "apps/a2/control-early-ack-fwd/spec/k1q1",
    "apps/a2/control-early-ack-fwd/spec/k2q1",
    "apps/a2/control-early-ack-fwd/spec/k3q1",
    "apps/a2/control-early-ack-fwd/spec/k1q2",
    "apps/a2/control-early-ack-fwd/spec/k1q3",
    "apps/a3/fifo/spec/k2q1",
    "apps/a3/fifo/spec/k3q1",
    "apps/a3/fifo/spec/k2q2",
    "apps/a3/control-lifo/spec/k2q1",
    "apps/a3/control-lifo/spec/k3q1",
    "apps/a3/control-lifo/spec/k2q2",
    "apps/a3/double-grant/spec/k2q1",
    "apps/a3/double-grant/spec/k3q1",
    "apps/a3/double-grant/spec/k2q2",
    "apps/a3/wrong-round/spec/k2q1",
    "apps/a3/wrong-round/spec/k3q1",
    "apps/a3/wrong-round/spec/k2q2",
    "apps/a3/never-grant/spec/k2q1",
    "apps/a3/never-grant/spec/k3q1",
    "apps/a3/never-grant/spec/k2q2",
    "apps/a4/hash/a4a/k1q1m1",
    "apps/a4/hash/a4a/k2q1m1",
    "apps/a4/hash/a4a/k3q1m1",
    "apps/a4/hash/a4a/k1q2m1",
    "apps/a4/hash/a4a/k1q1m2",
    "apps/a4/hash/a4a/k1q1m3",
    "apps/a4/hash/a4a/k2q1m2",
    "apps/a4/hash/a4b/k1q1m1",
    "apps/a4/hash/a4b/k2q1m1",
    "apps/a4/hash/a4b/k3q1m1",
    "apps/a4/hash/a4b/k1q2m1",
    "apps/a4/hash/a4b/k1q1m2",
    "apps/a4/hash/a4b/k1q1m3",
    "apps/a4/hash/a4b/k2q1m2",
    "apps/a4/rr/a4b/k1q1m1",
    "apps/a4/rr/a4b/k2q1m1",
    "apps/a4/rr/a4b/k3q1m1",
    "apps/a4/rr/a4b/k1q2m1",
    "apps/a4/rr/a4b/k1q1m2",
    "apps/a4/rr/a4b/k1q1m3",
    "apps/a4/rr/a4b/k2q1m2",
    "apps/a4/rr/a4a/k1q2m2",
    "apps/a4/rr/a4a/k2q2m2",
    "apps/a4/rr/a4a/k3q2m2",
    "apps/a4/rr/a4a/k1q2m3",
    "apps/a4/drop/a4b/k1q1m1",
    "apps/a4/drop/a4b/k2q1m1",
    "apps/a4/drop/a4b/k3q1m1",
    "apps/a4/drop/a4b/k1q2m1",
    "apps/a4/drop/a4b/k1q1m2",
    "apps/a4/drop/a4b/k1q1m3",
    "apps/a4/drop/a4b/k2q1m2",
    "apps/a4/pair-swap-hash/a4a/k2q1m1",
    "apps/a4/pair-swap-hash/a4a/k2q2m1",
    "apps/a4/pair-swap-hash/a4a/k2q1m2",
    "apps/a4/pair-swap-hash/a4a/k2q1m3",
    "apps/a4/pair-swap-hash/a4b/k2q1m1",
    "apps/a4/pair-swap-hash/a4b/k2q2m1",
    "apps/a4/pair-swap-hash/a4b/k2q1m2",
    "apps/a4/pair-swap-hash/a4b/k2q1m3",
    "apps/a4/pair-swap-rr/a4b/k2q1m1",
    "apps/a4/pair-swap-rr/a4b/k2q2m1",
    "apps/a4/pair-swap-rr/a4b/k2q1m2",
    "apps/a4/pair-swap-rr/a4b/k2q1m3",
];

/// The five size-2 cells of the slice (§5.3); three are not in `PILOT`.
const SIZE2_CELLS: [&str; 5] = [
    "apps/a1/correct/spec/n2r2",
    "apps/a2/pb/spec/k2q2",
    "apps/a3/fifo/spec/k2q2",
    "apps/a4/hash/a4a/k2q2m2",
    "2pc/leader/conf/n2",
];

fn fx(name: &str) -> Fixture {
    fixture_by_name(name).unwrap_or_else(|e| panic!("conformance: {name}: {}", e.text()))
}

/// One complete graph of either family, summarised both ways.
struct Item {
    side: &'static str,
    summary: Summary,
    counts: OrdCounts,
}

/// Both families of `f` (the stateful engine's kept graphs, `Ltr`), each
/// graph summarised by today's `Summary` (`Sig`, `VisOrder`) and by the
/// lead's `OrdCounts::of`.
fn items(f: &Fixture) -> Vec<Item> {
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(f);
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
    let vis = &f.visible;
    let mut out = Vec::new();
    for (side, gs) in [("spec", &o.kept_spec_graphs), ("impl", &o.kept_impl_graphs)] {
        for g in gs.iter() {
            out.push(item(side, g, vis));
        }
    }
    out
}

fn item(side: &'static str, g: &ExecutionGraph, vis: &[String]) -> Item {
    let w: Wobs = wobs(g, vis).expect("conformance: wobs of a complete graph");
    let exec = CompleteExecution::try_finished(g).expect("conformance: a complete graph");
    let summary = Summary::of(exec, &w, vis).expect("conformance: a summary");
    let counts = OrdCounts::of(g, &w, vis);
    Item {
        side,
        summary,
        counts,
    }
}

/// The expected `cmp` from today's containment (frozen §3.2: `Less` = `a ≤ b`
/// with a strict coordinate, i.e. `ord(a) ⊊ ord(b)`).
fn expected(a: &VisOrder, b: &VisOrder) -> Option<Ordering> {
    match (a.is_subset(b), b.is_subset(a)) {
        (true, true) => Some(Ordering::Equal),
        (true, false) => Some(Ordering::Less),
        (false, true) => Some(Ordering::Greater),
        (false, false) => None,
    }
}

/// `n · (T − 1) · width` (frozen §3.2), from the signature's words.
fn expected_payload(sig: &Sig, vis: &[String]) -> usize {
    let lens: Vec<usize> = vis.iter().map(|t| sig.word(t).len()).collect();
    let n: usize = lens.iter().sum();
    let width = if lens.iter().any(|&l| l > 255) { 2 } else { 1 };
    n * vis.len().saturating_sub(1) * width
}

#[derive(Default, Debug)]
struct T2Tally {
    graphs: usize,
    groups: usize,
    classes: usize,
    pairs: usize,
    equal_same_order: usize,
    less: usize,
    greater: usize,
    incomparable: usize,
}

/// T2 on one fixture; the failures, and the tally.
///
/// 1. **Prefix closure** of `ord` (the property counts rest on): for every
///    `((t', j), e) ∈ ord` with `t' ≠ thread(e)` and `j > 0`, also
///    `((t', j − 1), e) ∈ ord`.
/// 2. **`payload_bytes`** = `n · (T − 1) · width` on every summary.
/// 3. Within each `Sig` group, graphs with the **same** `VisOrder` give
///    `cmp = Equal` (counts are a function of the order).
/// 4. **Every pair** of distinct orders in the group: `cmp(a, b)` equals the
///    containment verdict of `expected`, and `cmp(b, a)` is its mirror.
fn t2_on(f: &Fixture, tally: &mut T2Tally) -> Vec<String> {
    let vis = &f.visible;
    let all = items(f);
    tally.graphs += all.len();
    let mut bad = Vec::new();
    for it in &all {
        let ord = &it.summary.ord;
        for (p, e) in ord {
            if p.thread != e.thread && p.index > 0 {
                let mut q = p.clone();
                q.index -= 1;
                if !ord.contains(&(q, e.clone())) {
                    bad.push(format!(
                        "{}: {} ord not prefix-closed at {p:?} → {e:?}",
                        f.name, it.side
                    ));
                    break;
                }
            }
        }
        let want = expected_payload(&it.summary.sig, vis);
        if it.counts.payload_bytes() != want {
            bad.push(format!(
                "{}: payload_bytes {} want {want}",
                f.name,
                it.counts.payload_bytes()
            ));
        }
    }
    // Group by `Sig` (`PartialEq` only); inside a group, one class per order.
    let mut groups: Vec<(&Sig, Vec<(&VisOrder, &OrdCounts)>)> = Vec::new();
    for it in &all {
        let gi = match groups.iter().position(|(s, _)| **s == it.summary.sig) {
            Some(i) => i,
            None => {
                groups.push((&it.summary.sig, Vec::new()));
                groups.len() - 1
            }
        };
        let classes = &mut groups[gi].1;
        match classes.iter().find(|(o, _)| **o == it.summary.ord) {
            Some((_, c)) => {
                tally.equal_same_order += 1;
                if OrdCounts::cmp(c, &it.counts) != Some(Ordering::Equal) {
                    bad.push(format!("{}: equal orders, counts not Equal", f.name));
                }
            }
            None => classes.push((&it.summary.ord, &it.counts)),
        }
    }
    tally.groups += groups.len();
    for (_, classes) in &groups {
        tally.classes += classes.len();
        for i in 0..classes.len() {
            for j in (i + 1)..classes.len() {
                let (oa, ca) = classes[i];
                let (ob, cb) = classes[j];
                let want = expected(oa, ob);
                let got = OrdCounts::cmp(ca, cb);
                let back = OrdCounts::cmp(cb, ca);
                tally.pairs += 1;
                match want {
                    Some(Ordering::Less) => tally.less += 1,
                    Some(Ordering::Greater) => tally.greater += 1,
                    None => tally.incomparable += 1,
                    Some(Ordering::Equal) => {}
                }
                if got != want || back != want.map(Ordering::reverse) {
                    bad.push(format!(
                        "{}: classes {i},{j}: cmp {got:?} / {back:?}, containment {want:?}",
                        f.name
                    ));
                }
            }
        }
    }
    bad
}

/// T2 (§5.2; frozen §3.2) on the five size-2 cells: counts containment equals
/// `VisOrder` containment on every pair of distinct orders with equal `Sig`,
/// both directions, `Equal` exactly on equal orders, `payload_bytes` per the
/// formula, and `ord` prefix-closed per thread.
#[test]
fn t2_counts_containment_on_the_size2_cells() {
    let mut tally = T2Tally::default();
    let mut bad = Vec::new();
    for name in SIZE2_CELLS {
        bad.extend(t2_on(&fx(name), &mut tally));
    }
    note!("t2 size-2 cells: {tally:?}");
    assert!(
        bad.is_empty(),
        "conformance: T2: {:#?}",
        &bad[..bad.len().min(20)]
    );
}

/// T2 on the 132 catalogued fixtures (`PILOT`) and the five size-2 cells,
/// both families of each. Non-vacuity: the corpus must contain strictly
/// ordered pairs and incomparable pairs. Heavy (the `n2r3` fixtures hold 4096
/// Spec graphs each); run alone.
#[test]
#[ignore]
fn t2_counts_containment_on_the_pilot_corpus() {
    let mut tally = T2Tally::default();
    let mut bad = Vec::new();
    for name in PILOT_NAMES.iter().chain(SIZE2_CELLS.iter()) {
        bad.extend(t2_on(&fx(name), &mut tally));
    }
    note!("t2 corpus: {tally:?}");
    assert!(
        bad.is_empty(),
        "conformance: T2: {:#?}",
        &bad[..bad.len().min(20)]
    );
    assert!(
        tally.less + tally.greater > 0 && tally.incomparable > 0,
        "conformance: T2 is vacuous on this corpus: {tally:?}"
    );
}

// =========================================================================
// Deliverable 2's oracle trace (reference only: today's `Summary`, no
// compact code)
// =========================================================================

/// One summary as a JSON line: side, completion index, the `Sig` `Debug`
/// rendering and its length, the word lengths per visible thread (sorted
/// names), and every `VisOrder` pair as `[[t, i], [t', j]]`.
fn dump_line(side: &str, idx: usize, s: &Summary, vis: &[String]) -> String {
    let mut names: Vec<&String> = vis.iter().collect();
    names.sort();
    let sig = format!("{:?}", s.sig);
    let words: Vec<serde_json::Value> = names
        .iter()
        .map(|t| serde_json::json!([t, s.sig.word(t).len()]))
        .collect();
    let pairs: Vec<serde_json::Value> = s
        .ord
        .iter()
        .map(|(a, b)| serde_json::json!([[a.thread, a.index], [b.thread, b.index]]))
        .collect();
    serde_json::json!({
        "side": side, "idx": idx, "sig": sig, "sig_len": sig.len(),
        "words": words, "ord": pairs,
    })
    .to_string()
}

/// The oracle trace for deliverable 2: for each size-2 cell, both families in
/// Must's `Ltr` completion order (the stateful engine's kept graphs: Spec
/// first, then Impl), each summarised by today's `Summary`, written as JSON
/// lines to `$COMPACT_DUMP_DIR/<cell with / → _>.jsonl`. The prediction
/// script replays frozen §3–§7 on them independently of `compact.rs`.
#[test]
#[ignore]
fn oracle_trace_dump() {
    let Ok(dir) = std::env::var("COMPACT_DUMP_DIR") else {
        return;
    };
    std::fs::create_dir_all(&dir).unwrap();
    for name in SIZE2_CELLS {
        let f = fx(name);
        let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
        let mut lines = Vec::new();
        for (side, gs) in [("spec", &o.kept_spec_graphs), ("impl", &o.kept_impl_graphs)] {
            for (i, g) in gs.iter().enumerate() {
                let w = wobs(g, &f.visible).unwrap();
                let s = Summary::of(CompleteExecution::try_finished(g).unwrap(), &w, &f.visible)
                    .unwrap();
                lines.push(dump_line(side, i, &s, &f.visible));
            }
        }
        let path = std::path::Path::new(&dir).join(format!("{}.jsonl", name.replace('/', "_")));
        std::fs::write(&path, lines.join("\n") + "\n").unwrap();
        note!(
            "dump {name}: spec {} impl {} → {}",
            o.kept_spec_graphs.len(),
            o.kept_impl_graphs.len(),
            path.display()
        );
    }
}

/// The ten cells of the slice (§5.3).
const SLICE_CELLS: [&str; 10] = [
    "apps/a1/correct/spec/n2r2",
    "apps/a1/correct/spec/n3r3",
    "apps/a2/pb/spec/k2q2",
    "apps/a2/pb/spec/k3q3",
    "apps/a3/fifo/spec/k2q2",
    "apps/a3/fifo/spec/k3q3",
    "apps/a4/hash/a4a/k2q2m2",
    "apps/a4/hash/a4a/k3q3m3",
    "2pc/leader/conf/n2",
    "2pc/leader/conf/n3",
];

/// Step 0 (frozen §6) for deliverable 2, one cell per invocation:
/// `STEP0_CELL` (one of [`SLICE_CELLS`]) and `STEP0_INDEX` (`current` or
/// `compact`). `stateful::run_with` at X1's stateful configuration (`Ltr`,
/// exhaustive, no precheck), `keep_graphs = false`; prints
/// `impl_distinct_summaries` with `impl_graphs`, `spec_graphs`,
/// `orders_held`, `signatures`, the reports and the wall.
#[test]
#[ignore]
fn step0_impl_distinct_summaries() {
    let (Ok(name), Ok(kind)) = (std::env::var("STEP0_CELL"), std::env::var("STEP0_INDEX")) else {
        return;
    };
    assert!(
        SLICE_CELLS.contains(&name.as_str()),
        "conformance: not a slice cell: {name}"
    );
    let index = match kind.as_str() {
        "current" => crate::conformance::config::IndexKind::Current,
        "compact" => crate::conformance::config::IndexKind::Compact,
        other => panic!("conformance: STEP0_INDEX {other}"),
    };
    let f = fx(&name);
    let gc = crate::conformance::eval::x1_config(
        GridEngine::Stateful,
        crate::conformance::selector::Selector::Ltr,
    )
    .index(index)
    .impl_distinct(true);
    let cc = gc.conf_config(&f);
    let t0 = std::time::Instant::now();
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
    let c = &o.counters;
    note!(
        "STEP0\t{name}\t{kind}\tlabel {}\timpl_distinct_summaries {:?}\timpl_graphs {}\tspec_graphs {}\torders_held {}\tsignatures {}\treports {}\twall_ms {}",
        gc.label(),
        c.impl_distinct_summaries,
        c.impl_graphs,
        c.spec_graphs,
        c.orders_held,
        c.signatures,
        o.reports.len(),
        t0.elapsed().as_millis()
    );
}

// =========================================================================
// §5.2's comparison: the engine's own counters on the five size-2 cells
// =========================================================================

/// The three slice configurations (frozen §8 rows 1–3).
fn slice_configs() -> [(&'static str, GridConfig); 3] {
    use crate::conformance::config::{Capacity, IndexKind};
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    [
        (
            "row1",
            x1_config(GridEngine::Stateful, Selector::Ltr)
                .index(IndexKind::Compact)
                .antichain(true)
                .probe_memo(true)
                .impl_distinct(true),
        ),
        (
            "row2",
            x1_config(GridEngine::CompleteFirst, Selector::Ltr)
                .witness_cache(Capacity::Unbounded)
                .quiet(true)
                .index(IndexKind::Compact)
                .antichain(true)
                .probe_memo(true)
                .impl_distinct(true),
        ),
        (
            "row3",
            x1_config(GridEngine::CompleteFirst, Selector::Ltr)
                .witness_cache(Capacity::Bounded(64))
                .quiet(true)
                .index(IndexKind::Compact)
                .antichain(false)
                .probe_memo(true)
                .impl_distinct(true),
        ),
    ]
}

fn stats_json(s: &crate::conformance::compact::CompactStats) -> serde_json::Value {
    serde_json::json!({
        "antichain_effective": s.antichain_effective, "entries": s.entries, "buckets": s.buckets,
        "bucket_max": s.bucket_max, "admitted": s.admitted, "duplicates": s.duplicates,
        "antichain_dropped_new": s.antichain_dropped_new,
        "antichain_dropped_old": s.antichain_dropped_old, "insert_tests": s.insert_tests,
        "containment_tests": s.containment_tests, "summary_bytes": s.summary_bytes,
        "sig_bytes_est": s.sig_bytes_est, "signatures": s.signatures,
        "signatures_seen": s.signatures_seen, "sig_tests": s.sig_tests,
        "sig_aliases": s.sig_aliases,
        "inverted_used": s.inverted_used, "inverted_words": s.inverted_words,
        "trie_nodes_visited": s.trie_nodes_visited,
        "coordinates_compared": s.coordinates_compared,
        "memo_on": s.memo_on, "memo_hits": s.memo_hits,
        "memo_entries": s.memo_entries, "memo_clears": s.memo_clears,
        "impl_distinct_summaries": s.impl_distinct_summaries,
    })
}

/// §5.2: the engine's counters for the three slice rows on the five size-2
/// cells, one JSON line per row (`ENGINE\t…`), compared by the tester's
/// script with the predictions of derived.md §5. Run alone.
#[test]
#[ignore]
fn engine_counters_on_the_size2_cells() {
    // Phase 2: `ENGINE_CELLS` (comma list of slice cells) and `ENGINE_ROWS`
    // (comma list of `row1`..`row3`) narrow the run; the five size-2 cells
    // and all three rows when unset.
    let cells: Vec<String> = std::env::var("ENGINE_CELLS")
        .map(|v| v.split(',').map(str::to_owned).collect())
        .unwrap_or_else(|_| SIZE2_CELLS.iter().map(|s| (*s).to_owned()).collect());
    let rows = std::env::var("ENGINE_ROWS").unwrap_or_else(|_| "row1,row2,row3".to_owned());
    // Items 4-5: `ENGINE_BUCKET` = `inverted:<t>` or `trie` puts that slot
    // structure on every row (the scan when unset).
    let bucket = match std::env::var("ENGINE_BUCKET").ok().as_deref() {
        None | Some("scan") => crate::conformance::config::BucketKind::Scan,
        Some("trie") => crate::conformance::config::BucketKind::Trie,
        Some(v) => crate::conformance::config::BucketKind::Inverted(
            v.strip_prefix("inverted:")
                .and_then(|t| t.parse().ok())
                .unwrap_or_else(|| panic!("conformance: ENGINE_BUCKET {v}")),
        ),
    };
    for name in &cells {
        assert!(
            SLICE_CELLS.contains(&name.as_str()),
            "conformance: not a slice cell: {name}"
        );
        let f = fx(name);
        for (row, gc) in slice_configs()
            .into_iter()
            .filter(|(r, _)| rows.split(',').any(|x| x == *r))
        {
            let gc = gc.bucket(bucket);
            let cc = gc.conf_config(&f);
            let j = if gc.engine == GridEngine::Stateful {
                let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
                let c = &o.counters;
                serde_json::json!({
                    "cell": name, "row": row, "label": gc.label(), "reports": o.reports.len(),
                    "spec_graphs": c.spec_graphs, "impl_graphs": c.impl_graphs,
                    "orders_held": c.orders_held, "signatures": c.signatures,
                    "lookups": c.lookups, "lookups_signature_miss": c.lookups_signature_miss,
                    "lookups_succeeded": c.lookups_succeeded,
                    "lookups_failed_after_tests": c.lookups_failed_after_tests,
                    "containment_tests": c.containment_tests,
                    "impl_distinct_summaries": c.impl_distinct_summaries,
                    "compact": c.compact.as_ref().map(stats_json),
                })
            } else {
                let o = crate::conformance::cfirst::run_with(
                    &cc,
                    &f.implementation,
                    &f.specification,
                    false,
                );
                let c = &o.counters;
                serde_json::json!({
                    "cell": name, "row": row, "label": gc.label(), "reports": o.reports.len(),
                    "impl_graphs": c.impl_graphs, "cache_probes": c.cache_probes,
                    "cache_hits": c.cache_hits, "cache_tests": c.cache_tests,
                    "sweeps": c.sweeps, "sweeps_successful": c.sweeps_successful,
                    "sweep_sizes": c.sweep_sizes, "sweep_graphs": c.sweep_graphs,
                    "sweep_graphs_max": c.sweep_graphs_max, "witnesses": c.witnesses,
                    "admissions": c.admissions, "evictions": c.evictions,
                    "readmissions": c.readmissions,
                    "compact": c.compact.as_ref().map(stats_json),
                })
            };
            note!("ENGINE\t{j}");
        }
    }
}

// =========================================================================
// T1 (§5.2; deliverable 3): Current vs Compact in one process
// =========================================================================

use crate::conformance::grid_oracle::canon_key;

/// A report: its canonical key and its normalised replay snapshot.
type ReportSeq = Vec<(String, String)>;

/// A snapshot as JSON text with `sorted_error_graph.labels` and
/// `error_state.graph.finished_threads` sorted and object keys in sorted
/// order (`serde_json` without `preserve_order`). `replay.rs`'s
/// `SortedGraph::labels` and `exec_graph.rs`'s `finished_threads` are
/// `HashSet`s and `task_id_map` a `HashMap`, all serialized in per-instance
/// hash order (the graph's other hash fields are not serialized): two
/// `Current` runs of one fixture differ byte-wise there (measured with
/// `T1_SELF`). Every other array keeps its order. `Unavailable` is kept
/// verbatim.
fn normalised(s: &crate::conformance::report::ReplaySnapshot) -> String {
    use crate::conformance::report::ReplaySnapshot;
    let ReplaySnapshot::Serialized(j) = s else {
        return format!("{s:?}");
    };
    let mut v: serde_json::Value =
        serde_json::from_str(j).expect("conformance: a snapshot is JSON");
    for path in [
        "/sorted_error_graph/labels",
        "/error_state/graph/finished_threads",
    ] {
        if let Some(serde_json::Value::Array(a)) = v.pointer_mut(path) {
            a.sort_by_key(|e| e.to_string());
        }
    }
    v.to_string()
}

fn report_seq(
    reports: &[(ExecutionGraph, crate::conformance::report::ReplaySnapshot)],
    vis: &[String],
) -> ReportSeq {
    reports
        .iter()
        .map(|(g, s)| (canon_key(g, vis), normalised(s)))
        .collect()
}

#[derive(Default, Debug)]
struct T1Tally {
    fixtures: usize,
    stateful_reports: usize,
    cfirst_reports: usize,
    sweeps: usize,
    bounded_evictions: usize,
    eviction_or_readmission_differences: usize,
    /// The antichain at engine level (`Compact` rows with it on).
    stateful_dropped_new: usize,
    stateful_dropped_old: usize,
    cfirst_dropped_new: usize,
    cfirst_dropped_old: usize,
}

/// Which component of two report sequences differs (for T1's message).
fn seq_diff(a: &ReportSeq, b: &ReportSeq) -> String {
    use std::collections::BTreeSet;
    if a.len() != b.len() {
        return format!("lengths {} vs {}", a.len(), b.len());
    }
    let keys = a.iter().map(|x| &x.0).eq(b.iter().map(|x| &x.0));
    let ka: BTreeSet<&String> = a.iter().map(|x| &x.0).collect();
    let kb: BTreeSet<&String> = b.iter().map(|x| &x.0).collect();
    let snaps = a.iter().map(|x| &x.1).eq(b.iter().map(|x| &x.1));
    let first = a.iter().zip(b).position(|(x, y)| x != y);
    let detail = first
        .map(|i| {
            let (x, y) = (&a[i].1, &b[i].1);
            let at = x
                .chars()
                .zip(y.chars())
                .position(|(p, q)| p != q)
                .unwrap_or(0);
            let w = |t: &str| {
                t.chars()
                    .skip(at.saturating_sub(200))
                    .take(400)
                    .collect::<String>()
            };
            format!(
                "first at {i}, char {at} of {}/{}: current ..{}.. || compact ..{}..",
                x.len(),
                y.len(),
                w(x),
                w(y)
            )
        })
        .unwrap_or_default();
    format!(
        "keys in order {keys}, key sets {}, snapshots {snaps}; {detail}",
        ka == kb
    )
}

/// T1 on one fixture; the failures. `SVerify-S` (X1's stateful
/// configuration) under `Current` and under `Compact` with the antichain on:
/// identical report sequences (canonical key and replay snapshot, in report
/// order). Complete-first (X1's, quiet) at `Unbounded` (`Compact`: antichain
/// on, memo on) and at `Bounded(64)` (`Compact`: antichain off, memo on):
/// identical report sequences, `sweeps`, `sweep_sizes`, `sweeps_successful`,
/// `sweeps_failing`, `cache_hits`, `admissions`. `evictions` and
/// `readmissions` are tallied, not required equal (the two caches identify a
/// witness differently: canonical graph against summary).
fn t1_on(f: &Fixture, tally: &mut T1Tally) -> Vec<String> {
    use crate::conformance::config::{Capacity, IndexKind};
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    let vis = &f.visible;
    let mut bad = Vec::new();
    tally.fixtures += 1;
    let st = |k: IndexKind| {
        let cc = x1_config(GridEngine::Stateful, Selector::Ltr)
            .index(k)
            .antichain(true)
            .probe_memo(true)
            .conf_config(f);
        stateful::run_with(&cc, &f.implementation, &f.specification, false)
    };
    let other = if std::env::var("T1_SELF").is_ok() {
        IndexKind::Current
    } else {
        IndexKind::Compact
    };
    // `T1_PARTS` (gate 4 M1): a comma list of `st`, `inf`, `64` selecting
    // `SVerify-S`, complete-first `Unbounded` and `Bounded(64)`; all three
    // when unset.
    let parts = std::env::var("T1_PARTS").unwrap_or_else(|_| "st,inf,64".to_owned());
    let want = |p: &str| parts.split(',').any(|x| x.trim() == p);
    if want("st") {
        let (a, b) = (st(IndexKind::Current), st(other));
        let (ra, rb) = (report_seq(&a.reports, vis), report_seq(&b.reports, vis));
        tally.stateful_reports += ra.len();
        if let Some(s) = b.counters.compact.as_ref() {
            tally.stateful_dropped_new += s.antichain_dropped_new;
            tally.stateful_dropped_old += s.antichain_dropped_old;
        }
        if ra != rb {
            bad.push(format!(
                "{}: SVerify-S reports differ: {}",
                f.name,
                seq_diff(&ra, &rb)
            ));
        }
        if (a.counters.spec_graphs, a.counters.impl_graphs)
            != (b.counters.spec_graphs, b.counters.impl_graphs)
        {
            bad.push(format!("{}: SVerify-S family sizes differ", f.name));
        }
    }
    for (cap, anti) in [(Capacity::Unbounded, true), (Capacity::Bounded(64), false)]
        .into_iter()
        .filter(|(c, _)| {
            want(if *c == Capacity::Unbounded {
                "inf"
            } else {
                "64"
            })
        })
    {
        let cf = |k: IndexKind| {
            let cc = x1_config(GridEngine::CompleteFirst, Selector::Ltr)
                .witness_cache(cap)
                .quiet(true)
                .index(k)
                .antichain(anti)
                .probe_memo(true)
                .conf_config(f);
            crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false)
        };
        let (a, b) = (cf(IndexKind::Current), cf(other));
        let (ra, rb) = (report_seq(&a.reports, vis), report_seq(&b.reports, vis));
        tally.cfirst_reports += ra.len();
        tally.sweeps += a.counters.sweeps;
        if let Some(s) = b.counters.compact.as_ref() {
            tally.cfirst_dropped_new += s.antichain_dropped_new;
            tally.cfirst_dropped_old += s.antichain_dropped_old;
            if s.antichain_dropped_new != 0 {
                bad.push(format!(
                    "{} {cap:?}: antichain_dropped_new {} (frozen §4.3: provably 0)",
                    f.name, s.antichain_dropped_new
                ));
            }
            let w = b.counters.witnesses;
            if w + b.counters.evictions + s.antichain_dropped_old != b.counters.admissions {
                bad.push(format!("{} {cap:?}: R2 identity: witnesses {w} + evictions {} + dropped_old {} != admissions {}", f.name, b.counters.evictions, s.antichain_dropped_old, b.counters.admissions));
            }
        }
        let (ca, cb) = (&a.counters, &b.counters);
        if ra != rb {
            bad.push(format!(
                "{} {cap:?}: reports differ: {}",
                f.name,
                seq_diff(&ra, &rb)
            ));
        }
        let pa = (
            ca.sweeps,
            &ca.sweep_sizes,
            ca.sweeps_successful,
            ca.sweeps_failing,
            ca.cache_hits,
            ca.admissions,
        );
        let pb = (
            cb.sweeps,
            &cb.sweep_sizes,
            cb.sweeps_successful,
            cb.sweeps_failing,
            cb.cache_hits,
            cb.admissions,
        );
        if pa != pb {
            bad.push(format!(
                "{} {cap:?}: sweeps/sizes/hits/admissions differ: {pa:?} vs {pb:?}",
                f.name
            ));
        }
        if cap != Capacity::Unbounded {
            tally.bounded_evictions += ca.evictions;
            if (ca.evictions, ca.readmissions) != (cb.evictions, cb.readmissions) {
                tally.eviction_or_readmission_differences += 1;
                note!(
                    "t1 {} {cap:?}: evictions/readmissions current {:?} compact {:?}",
                    f.name,
                    (ca.evictions, ca.readmissions),
                    (cb.evictions, cb.readmissions)
                );
            }
        }
    }
    bad
}

/// T1 on the five size-2 cells (light; in the suite).
#[test]
fn t1_current_equals_compact_on_the_size2_cells() {
    let mut tally = T1Tally::default();
    let mut bad = Vec::new();
    for name in SIZE2_CELLS {
        bad.extend(t1_on(&fx(name), &mut tally));
    }
    note!("t1 size-2 cells: {tally:?}");
    assert!(bad.is_empty(), "conformance: T1: {bad:#?}");
}

/// T1 on the 132 `PILOT` fixtures and the five size-2 cells (§5.2). The
/// corpus holds violating pairs, so report sets are exercised (the tally must
/// show reports). Run alone.
#[test]
#[ignore]
fn t1_current_equals_compact_on_the_pilot_corpus() {
    let mut tally = T1Tally::default();
    let mut bad = Vec::new();
    for name in PILOT_NAMES.iter().chain(SIZE2_CELLS.iter()) {
        bad.extend(t1_on(&fx(name), &mut tally));
    }
    note!("t1 corpus: {tally:?}");
    assert!(
        bad.is_empty(),
        "conformance: T1: {:#?}",
        &bad[..bad.len().min(20)]
    );
    assert!(
        tally.stateful_reports > 0 && tally.cfirst_reports > 0,
        "conformance: T1 is vacuous on reports: {tally:?}"
    );
}

/// T1 on one fixture named by `T1_FIXTURE` (one process per fixture, so the
/// corpus is driven fixture by fixture under a per-process timeout). Prints
/// `T1\t<name>\tok|FAIL\t<tally>\t<wall ms>` and fails on a difference.
#[test]
#[ignore]
fn t1_one_fixture() {
    let Ok(name) = std::env::var("T1_FIXTURE") else {
        return;
    };
    assert!(
        PILOT_NAMES.contains(&name.as_str())
            || SIZE2_CELLS.contains(&name.as_str())
            || SLICE_CELLS.contains(&name.as_str()),
        "conformance: {name} is not in the T1 corpus"
    );
    let mut tally = T1Tally::default();
    let t0 = std::time::Instant::now();
    let bad = t1_on(&fx(&name), &mut tally);
    note!(
        "T1\t{name}\t{}\t{tally:?}\t{}",
        if bad.is_empty() { "ok" } else { "FAIL" },
        t0.elapsed().as_millis()
    );
    assert!(bad.is_empty(), "conformance: T1 {name}: {bad:#?}");
}

// =========================================================================
// Deliverable 4: the mechanisms, forced
// =========================================================================

use crate::conformance::compact::{
    CompactCache, CompactIndex, CompactSummary, Covers, Inserted, Probe,
};
use crate::conformance::config::Capacity;

/// A real compact summary (its `Sig`, hash and rendering length are a real
/// graph's), from the first Spec graph of `name`.
fn real_summary(name: &str) -> CompactSummary {
    let f = fx(name);
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
    let g = &o.kept_spec_graphs[0];
    let w = wobs(g, &f.visible).unwrap();
    CompactSummary::of(CompleteExecution::try_finished(g).unwrap(), &w, &f.visible).unwrap()
}

/// The same signature with a synthetic order of `base`'s length.
fn syn(base: &CompactSummary, v: &[u8]) -> CompactSummary {
    assert_eq!(
        v.len(),
        base.ord.len(),
        "conformance: a synthetic order of the wrong length"
    );
    CompactSummary {
        ord: OrdCounts::U8(v.to_vec()),
        ..base.clone()
    }
}

/// `L` unit vectors and the constant vectors of `base`'s length.
fn unit(l: usize, i: usize) -> Vec<u8> {
    (0..l).map(|j| u8::from(j == i)).collect()
}

const MECH_CELL: &str = "apps/a2/pb/spec/k2q2";

/// m1 (frozen §4.1, antichain on): a dominated new order is dropped
/// (`DroppedNew`); an exact duplicate is refused **before** any antichain
/// action (`Duplicate`, not a drop); a new order below held ones removes them
/// all (`antichain_dropped_old`), keeping the others' relative order; the
/// query answers with the **first** held entry `≤` the order; the counters
/// (`insert_tests`, `containment_tests`, `entries`, `bucket_max`,
/// `summary_bytes`, `sig_bytes`, `buckets`) follow frozen §7.
#[test]
fn m1_the_antichain_in_the_index() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    assert!(
        l >= 3,
        "conformance: the cell's order is too short for the test ({l})"
    );
    let (zero, one, two) = (vec![0u8; l], vec![1u8; l], vec![2u8; l]);
    let mut ix = CompactIndex::new(true);
    assert_eq!(ix.insert(&syn(&base, &one)).1, Inserted::Stored(0));
    assert_eq!(
        ix.insert(&syn(&base, &two)).1,
        Inserted::DroppedNew,
        "conformance: one ≤ two drops two"
    );
    assert_eq!(
        ix.insert(&syn(&base, &one)).1,
        Inserted::Duplicate,
        "conformance: a duplicate is not a drop"
    );
    let s = ix.stats().clone();
    assert_eq!(
        (
            s.admitted,
            s.duplicates,
            s.antichain_dropped_new,
            s.antichain_dropped_old,
            s.insert_tests,
            s.entries
        ),
        (1, 1, 1, 0, 2, 1)
    );
    // Two incomparable orders, then one below both: both removed.
    let mut ix = CompactIndex::new(true);
    let (a, b) = (unit(l, 0), unit(l, 1));
    let c = {
        let mut v = vec![0u8; l];
        v[2] = 1;
        v
    };
    assert!(matches!(ix.insert(&syn(&base, &a)).1, Inserted::Stored(_)));
    assert!(matches!(ix.insert(&syn(&base, &b)).1, Inserted::Stored(_)));
    assert!(matches!(ix.insert(&syn(&base, &c)).1, Inserted::Stored(_)));
    assert_eq!(ix.stats().bucket_max, 3);
    assert!(matches!(
        ix.insert(&syn(&base, &zero)).1,
        Inserted::Stored(3)
    ));
    let s = ix.stats().clone();
    assert_eq!(
        (
            s.entries,
            s.antichain_dropped_old,
            s.admitted,
            s.bucket_max,
            s.buckets
        ),
        (1, 3, 4, 3, 1),
        "conformance: zero ≤ a, b, c removes all three; bucket_max is the maximum reached"
    );
    assert_eq!(
        s.summary_bytes, l,
        "conformance: one held entry of l u8 counts"
    );
    assert_eq!(
        (s.sig_bytes_est, s.signatures, s.signatures_seen),
        (base.sig_est, 1, 1),
        "conformance: one live slot"
    );
    assert_eq!(ix.covers(&syn(&base, &two)).1, Covers::Found(3));
    assert_eq!(ix.stats().containment_tests, 1);
    // Query order: antichain off, a then b held; a query above both is
    // answered by the first in insertion order.
    let mut ix = CompactIndex::new(false);
    ix.insert(&syn(&base, &a));
    ix.insert(&syn(&base, &b));
    assert_eq!(
        ix.covers(&syn(&base, &one)).1,
        Covers::Found(0),
        "conformance: the first held entry answers"
    );
    assert_eq!(ix.covers(&syn(&base, &unit(l, 1))).1, Covers::Found(1));
    assert_eq!(
        ix.stats().containment_tests,
        3,
        "conformance: 1 + 2 comparisons"
    );
    assert_eq!(ix.covers(&syn(&base, &zero)).1, Covers::NotFound);
    assert_eq!(ix.stats().containment_tests, 5);
}

/// m2 (antichain off): dominated orders are both stored; the duplicate scan
/// still counts one `insert_tests` per entry examined and stops at the equal
/// one.
#[test]
fn m2_the_index_without_the_antichain() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    let (one, two) = (vec![1u8; l], vec![2u8; l]);
    let mut ix = CompactIndex::new(false);
    assert!(matches!(
        ix.insert(&syn(&base, &one)).1,
        Inserted::Stored(_)
    ));
    assert!(matches!(
        ix.insert(&syn(&base, &two)).1,
        Inserted::Stored(_)
    ));
    assert_eq!(ix.insert(&syn(&base, &two)).1, Inserted::Duplicate);
    let s = ix.stats().clone();
    assert_eq!(
        (
            s.entries,
            s.admitted,
            s.duplicates,
            s.antichain_dropped_new,
            s.antichain_dropped_old,
            s.insert_tests,
            s.bucket_max
        ),
        (2, 2, 1, 0, 0, 3, 2),
        "conformance: inserts: 0 + 1 + 2 comparisons"
    );
    assert!(!s.antichain_effective);
}

/// m3 (frozen §4.3, §5, R1): `Bounded(2)` with the memo. Admissions m1, m2,
/// then m3 evicts m1 **first** (the memo cleared), inserts m3 and extends the
/// memo with g3 only; g1 then misses (m1 gone, the memo empty of it); the
/// re-admission of m1 evicts m2 (a second clear) and counts `readmissions`.
#[test]
fn m3_fifo_eviction_clears_the_memo_in_r1_order() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    let (m1, m2, m3) = (
        syn(&base, &unit(l, 0)),
        syn(&base, &unit(l, 1)),
        syn(&base, &unit(l, 2)),
    );
    // g_i = m_i (equal orders cover).
    let (g1, g2, g3) = (m1.clone(), m2.clone(), m3.clone());
    let mut c = CompactCache::new(Capacity::Bounded(2), true, true);
    assert_eq!(c.probe(&g1).0, Probe::Miss);
    assert!(c.admit(&m1, &g1));
    assert_eq!(c.probe(&g1).0, Probe::MemoHit);
    assert_eq!(c.probe(&g2).0, Probe::Miss);
    assert!(c.admit(&m2, &g2));
    assert_eq!((c.len(), c.memo_len(), c.evictions()), (2, 2, 0));
    assert_eq!(c.probe(&g3).0, Probe::Miss);
    assert!(c.admit(&m3, &g3));
    assert_eq!(
        (c.len(), c.memo_len(), c.evictions(), c.stats().memo_clears),
        (2, 1, 1, 1),
        "conformance: evict m1, clear, insert m3, memo = {{g3}}"
    );
    assert_eq!(c.probe(&g3).0, Probe::MemoHit);
    assert_eq!(
        c.probe(&g1).0,
        Probe::Miss,
        "conformance: m1 evicted and g1 forgotten by the memo"
    );
    assert_eq!(
        c.probe(&g2).0,
        Probe::Hit,
        "conformance: m2 still held: a bucket hit"
    );
    assert!(c.admit(&m1, &g1));
    let s = c.stats();
    assert_eq!(
        (
            c.admissions(),
            c.evictions(),
            c.readmissions(),
            s.memo_clears,
            c.len(),
            c.memo_len(),
            s.antichain_effective
        ),
        (4, 2, 1, 2, 2, 1, false),
        "conformance: m1 re-admitted after its eviction; m2 evicted; memo = {{g1}}"
    );
}

/// m4 (frozen §5): the memo is extended at a bucket hit and at an admission,
/// never at a miss; with the memo off nothing is memoised.
#[test]
fn m4_the_memo_is_extended_at_hits_and_admissions_only() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    let m = syn(&base, &unit(l, 0));
    let g1 = m.clone();
    let mut g2v = unit(l, 0);
    g2v[1] = 1;
    let g2 = syn(&base, &g2v); // m ≤ g2, g2 ≠ g1
    let gx = syn(&base, &unit(l, 1)); // not covered by m
    let mut c = CompactCache::new(Capacity::Unbounded, true, true);
    assert_eq!(c.probe(&gx).0, Probe::Miss);
    assert_eq!(c.memo_len(), 0, "conformance: a miss is not memoised");
    assert!(c.admit(&m, &g1));
    assert_eq!(
        c.memo_len(),
        1,
        "conformance: extended at the admission with the probed summary"
    );
    assert_eq!(c.probe(&g2).0, Probe::Hit);
    assert_eq!(c.memo_len(), 2, "conformance: extended at the bucket hit");
    assert_eq!(c.probe(&g2).0, Probe::MemoHit);
    assert_eq!(c.probe(&gx).0, Probe::Miss);
    let s = c.stats();
    assert_eq!((s.memo_hits, s.memo_entries, s.memo_on), (1, 2, true));
    let mut off = CompactCache::new(Capacity::Unbounded, true, false);
    assert!(off.admit(&m, &g1));
    assert_eq!(off.probe(&g2).0, Probe::Hit);
    assert_eq!(
        off.probe(&g2).0,
        Probe::Hit,
        "conformance: no memo: the bucket answers again"
    );
    let s = off.stats();
    assert_eq!((s.memo_hits, s.memo_entries, s.memo_on), (0, 0, false));
}

/// m5 (frozen §4.3): `Bounded(n)` forces the antichain off, in the cache and
/// in the engine's exported `antichain_effective`; `Unbounded` keeps the
/// requested value.
#[test]
fn m5_bounded_forces_the_antichain_off() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    assert!(!CompactCache::new(Capacity::Bounded(4), true, true)
        .index()
        .antichain());
    assert!(
        !CompactCache::new(Capacity::Bounded(4), true, true)
            .stats()
            .antichain_effective
    );
    assert!(CompactCache::new(Capacity::Unbounded, true, true)
        .index()
        .antichain());
    assert!(!CompactCache::new(Capacity::Unbounded, false, true)
        .index()
        .antichain());
    let f = fx(MECH_CELL);
    for (cap, want) in [(Capacity::Bounded(64), false), (Capacity::Unbounded, true)] {
        let cc = x1_config(GridEngine::CompleteFirst, Selector::Ltr)
            .witness_cache(cap)
            .quiet(true)
            .index(IndexKind::Compact)
            .antichain(true)
            .probe_memo(true)
            .conf_config(&f);
        let o =
            crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false);
        assert_eq!(
            o.counters.compact.as_ref().map(|s| s.antichain_effective),
            Some(want),
            "conformance: {cap:?} with anti=true"
        );
    }
}

/// m6 (`Zero`): the compact cache admits nothing and answers nothing; in the
/// engine, `Compact` at `Zero` equals `Current` at `Zero` (reports,
/// `sweeps`, `sweep_sizes`, `cache_hits` 0) on the lock at size 2 (28
/// completions, every one swept), and the memo stays empty.
#[test]
fn m6_zero_admits_nothing() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    let base = real_summary(MECH_CELL);
    let m = syn(&base, &vec![0u8; base.ord.len()]);
    let mut c = CompactCache::new(Capacity::Zero, true, true);
    assert!(!c.admit(&m, &m), "conformance: Zero admits nothing");
    assert_eq!((c.len(), c.memo_len()), (0, 0));
    assert_eq!(c.probe(&m).0, Probe::Miss);
    let f = fx("apps/a3/fifo/spec/k2q2");
    let run = |k: IndexKind| {
        let cc = x1_config(GridEngine::CompleteFirst, Selector::Ltr)
            .witness_cache(Capacity::Zero)
            .quiet(true)
            .index(k)
            .antichain(true)
            .probe_memo(true)
            .conf_config(&f);
        crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false)
    };
    let (a, b) = (run(IndexKind::Current), run(IndexKind::Compact));
    assert_eq!(
        report_seq(&a.reports, &f.visible),
        report_seq(&b.reports, &f.visible)
    );
    assert_eq!(
        (
            a.counters.sweeps,
            &a.counters.sweep_sizes,
            a.counters.cache_hits
        ),
        (
            b.counters.sweeps,
            &b.counters.sweep_sizes,
            b.counters.cache_hits
        )
    );
    assert_eq!(
        (
            b.counters.sweeps,
            b.counters.cache_hits,
            b.counters.witnesses
        ),
        (28, 0, 0)
    );
    let s = b.counters.compact.as_ref().unwrap();
    assert_eq!(
        (s.memo_entries, s.memo_hits, s.entries, s.admitted),
        (0, 0, 0, 0)
    );
}

/// m7 (frozen §3.2): the `u16` width. A program whose thread `a` sends 256
/// messages that thread `b` receives (one channel, one sender: one
/// execution): each visible word is 256 > 255 long, so the counts are
/// `U16`, `len = n · (T − 1) = 512`, `payload_bytes = 1024`; the counts are
/// those of the order (`a`'s k-th send is porf-before `b`'s k-th receive and
/// later ones), and the summary compares `Equal` with itself.
#[test]
fn m7_the_u16_width() {
    use crate::conformance::grid::prog;
    let p = prog(|| {
        let b = crate::thread::Builder::new()
            .name("b".to_owned())
            .spawn(|| {
                for _ in 0..256 {
                    let _: i32 = crate::recv_msg_block();
                }
            })
            .unwrap();
        let bid = b.thread().id();
        let _a = crate::thread::Builder::new()
            .name("a".to_owned())
            .spawn(move || {
                for i in 0..256 {
                    crate::send_msg(bid, i as i32);
                }
            })
            .unwrap();
    });
    let mut f = fx(MECH_CELL);
    f.name = "compact/u16".to_owned();
    f.implementation = p.clone();
    f.specification = p;
    f.visible = vec!["a".to_owned(), "b".to_owned()];
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
    assert_eq!(o.kept_impl_graphs.len(), 1, "conformance: one execution");
    let g = &o.kept_impl_graphs[0];
    let w = wobs(g, &f.visible).unwrap();
    let c = OrdCounts::of(g, &w, &f.visible);
    assert!(c.is_wide(), "conformance: 256 visible events need u16");
    assert_eq!((c.len(), c.payload_bytes()), (512, 1024));
    assert_eq!(OrdCounts::cmp(&c, &c), Some(Ordering::Equal));
    let OrdCounts::U16(v) = &c else {
        unreachable!()
    };
    // Thread order: a (events 0..256), then b. For a's events the other
    // thread is b: b's receives are never porf-before a's sends → 0. For b's
    // k-th receive: a's sends 0..=k are porf-before it → k + 1.
    assert!(
        v[..256].iter().all(|&x| x == 0),
        "conformance: a's counts against b"
    );
    assert!(
        v[256..]
            .iter()
            .enumerate()
            .all(|(k, &x)| x as usize == k + 1),
        "conformance: b's counts against a"
    );
    // The stateful engine's Compact row on this pair: the same width end to end.
    let ccc = GridConfig::new(GridEngine::Stateful)
        .index(crate::conformance::config::IndexKind::Compact)
        .conf_config(&f);
    let oc = stateful::run_with(&ccc, &f.implementation, &f.specification, false);
    let s = oc.counters.compact.as_ref().unwrap();
    assert_eq!((oc.reports.len(), s.entries, s.summary_bytes), (0, 1, 1024));
}

// =========================================================================
// Gate 4 round 01: B1 (collisions at the memo) and B2 (the u16 bound)
// =========================================================================

/// The panic message of `f`, or `None` when it returns.
fn panic_text<R>(f: impl FnOnce() -> R) -> Option<String> {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    match r {
        Ok(_) => None,
        Err(e) => Some(
            e.downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_default(),
        ),
    }
}

/// A summary with `base`'s bucket hash and counts but another fixture's
/// `Sig` (and its byte estimate): two signatures in one bucket with equal
/// counts, the case a hash- or shape-only identity would confuse.
fn forged(base: &CompactSummary) -> CompactSummary {
    let other = real_summary("2pc/leader/conf/n2");
    assert!(
        other.sig != base.sig,
        "conformance: the forging fixture has another signature"
    );
    CompactSummary {
        hash: base.hash,
        ord: base.ord.clone(),
        sig: other.sig,
        sig_est: other.sig_est,
    }
}

/// m8 (phase 2 D1; P2-frozen §1, §5, §7; replaces the slice's
/// collision-panic test): a summary with an equal bucket hash and equal
/// counts but an unequal `Sig` is a **signature miss**, never an answer and
/// never a panic — at a memo probe after an admission and after a bucket hit
/// (`(Miss, None)`), and at a bucket query (`(None, NoSig)`: no `≤` test and,
/// P1, no slot). Stored, it gets its own slot, and each summary then answers
/// only from its own slot; through the rendering hint (P3) each resolution of
/// an existing slot costs one `Sig` test and no alias arises.
#[test]
fn m8_a_forged_equal_hash_different_sig_is_a_signature_miss() {
    let base = real_summary(MECH_CELL);
    let bad = forged(&base);
    // The memo after an admission.
    let mut c = CompactCache::new(Capacity::Unbounded, true, true);
    assert_eq!(
        c.probe(&base),
        (Probe::Miss, None),
        "conformance: empty cache"
    );
    assert!(c.admit(&base, &base), "conformance: admitted");
    assert_eq!(
        c.probe(&base),
        (Probe::MemoHit, Some(0)),
        "conformance: control"
    );
    assert_eq!(
        c.probe(&bad),
        (Probe::Miss, None),
        "conformance: memo (admission), forged"
    );
    // The memo after a bucket hit (w ≤ q).
    let w = syn(&base, &vec![0u8; base.ord.len()]);
    let q = syn(&base, &vec![1u8; base.ord.len()]);
    let mut c = CompactCache::new(Capacity::Unbounded, true, true);
    assert_eq!(c.probe(&w).0, Probe::Miss);
    assert!(c.admit(&w, &w), "conformance: admitted");
    assert_eq!(
        c.probe(&q),
        (Probe::Hit, Some(0)),
        "conformance: a bucket hit"
    );
    assert_eq!(
        c.probe(&q),
        (Probe::MemoHit, Some(0)),
        "conformance: memoised"
    );
    let bad_q = CompactSummary {
        ord: q.ord.clone(),
        ..bad.clone()
    };
    assert_eq!(
        c.probe(&bad_q),
        (Probe::Miss, None),
        "conformance: memo (bucket hit), forged"
    );
    // The index.
    let mut ix = CompactIndex::new(true);
    assert_eq!(ix.insert(&base), (0, Inserted::Stored(0)));
    let t0 = ix.stats().containment_tests;
    assert_eq!(
        ix.covers(&bad),
        (None, Covers::NoSig),
        "conformance: a signature miss, no slot"
    );
    let s = ix.stats().clone();
    assert_eq!(s.containment_tests, t0, "conformance: no test on a miss");
    assert_eq!(
        (
            s.buckets,
            s.signatures,
            s.signatures_seen,
            s.sig_tests,
            s.sig_aliases
        ),
        (1, 1, 1, 1, 0),
        "conformance: one bucket, one slot; one Sig test; the query created nothing"
    );
    assert_eq!(
        ix.insert(&bad),
        (1, Inserted::Stored(1)),
        "conformance: its own slot, not a duplicate of base's counts"
    );
    assert_eq!(ix.covers(&base), (Some(0), Covers::Found(0)));
    assert_eq!(ix.covers(&bad), (Some(1), Covers::Found(1)));
    let s = ix.stats().clone();
    assert_eq!(
        (
            s.buckets,
            s.signatures,
            s.signatures_seen,
            s.entries,
            s.duplicates
        ),
        (1, 2, 2, 2, 0)
    );
    assert_eq!(
        s.sig_bytes_est,
        base.sig_est + bad.sig_est,
        "conformance: the two occupied slots"
    );
    // P2-derived §13: insert base 0; covers bad 1 (second pass, miss);
    // insert bad 1 (second pass, new slot); covers base 1 and covers bad 1
    // (each through its hint).
    assert_eq!(
        (s.sig_tests, s.sig_aliases),
        (4, 0),
        "conformance: Sig == comparisons"
    );
}

/// The single graph of: `a` sends `n` messages to `b`, which receives none
/// (no receive, so no revisit and one execution); `a` and `b` visible.
fn sends_graph(n: usize) -> (ExecutionGraph, Vec<String>) {
    use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
    use crate::conformance::stateful::{enumerate, EnumRun};
    let p: std::sync::Arc<dyn Fn() + Send + Sync> = std::sync::Arc::new(move || {
        let b = crate::thread::Builder::new()
            .name("b".to_owned())
            .spawn(|| {})
            .unwrap();
        let bid = b.thread().id();
        let _a = crate::thread::Builder::new()
            .name("a".to_owned())
            .spawn(move || {
                for i in 0..n {
                    crate::send_msg(bid, i as i32);
                }
            })
            .unwrap();
    });
    let got: std::rc::Rc<std::cell::RefCell<Vec<ExecutionGraph>>> = Default::default();
    let sink: CompletionSink = {
        let got = std::rc::Rc::clone(&got);
        Box::new(move |g: &ExecutionGraph, _| {
            got.borrow_mut().push(g.clone());
            SinkVerdict::Continue
        })
    };
    let vis = vec!["a".to_owned(), "b".to_owned()];
    enumerate(
        EnumRun {
            // Above the grid's `CONF_THREAD_THRESHOLD` (1 << 16), which stops
            // the search once a thread's next event index exceeds it
            // (`must.rs` `add_to_graph`): `a` needs Begin, n sends and End.
            config: crate::Config::builder()
                .with_seed(0)
                .with_thread_threshold(1 << 17)
                .build(),
            visible: vis.clone(),
            mode: ConfMode::Enumerate,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
        },
        &p,
    );
    let mut v = got.borrow_mut();
    assert_eq!(v.len(), 1, "conformance: one execution");
    (v.pop().unwrap(), vis)
}

/// m9 (gate 4 B2, frozen §3.2, §5.1 item 2): the `u16` bound. A visible
/// thread of exactly `u16::MAX` = 65 535 visible events is accepted (`U16`,
/// its counts against `b` all 0, no wrap); one of 65 536 is refused before
/// any count is accumulated, in every profile, naming the thread and the
/// count — through `OrdCounts::of` and through `CompactSummary::of`.
/// Under the grid's own `CONF_THREAD_THRESHOLD` = 65 536 such a thread
/// never completes (Begin + 65 536 sends + End needs index 65 537, and the
/// search stops there), so the refusal is reachable only through a
/// configuration with a higher threshold; this test raises it to 1 << 17.
#[test]
fn m9_the_u16_bound_refuses_65536_visible_events() {
    let max = u16::MAX as usize;
    let (g, vis) = sends_graph(max);
    let w = wobs(&g, &vis).unwrap();
    assert_eq!(w.of("a").len(), max, "conformance: a's visible word");
    let c = OrdCounts::of(&g, &w, &vis);
    assert!(c.is_wide(), "conformance: u16");
    assert_eq!(c.len(), max, "conformance: n · (T − 1)");
    let OrdCounts::U16(v) = &c else {
        unreachable!()
    };
    assert!(v.iter().all(|&x| x == 0), "conformance: a against b");
    let (g, vis) = sends_graph(max + 1);
    let w = wobs(&g, &vis).unwrap();
    assert_eq!(w.of("a").len(), max + 1, "conformance: a's visible word");
    let want = format!("the visible thread `a` has {} visible events", max + 1);
    for (site, got) in [
        ("OrdCounts::of", panic_text(|| OrdCounts::of(&g, &w, &vis))),
        (
            "CompactSummary::of",
            panic_text(|| {
                CompactSummary::of(CompleteExecution::try_finished(&g).unwrap(), &w, &vis)
            }),
        ),
    ] {
        let m = got.unwrap_or_else(|| panic!("conformance: {site}: 65 536 accepted"));
        assert!(
            m.contains(&want) && m.contains("65535"),
            "conformance: {site}: another panic: {m}"
        );
    }
}

/// The streaming oracle trace (phase 2, D4's size-3 lock reference; approved
/// 2026-10-19): `oracle_trace_dump`'s lines for one cell
/// (`$COMPACT_STREAM_CELL`), written as each completion arrives instead of
/// from kept graphs, so the lock's ~330 k implementation completions are
/// never held. The two enumerations are `stateful::run_with`'s (Spec with
/// `max_iterations` lifted, then Impl with the cell's configuration), so the
/// order is the in-memory dump's. A summary already written on its side is
/// written again as `{"side", "idx", "ref"}`, `ref` the index of its first
/// occurrence (the order stays exact; the file stays small).
#[test]
#[ignore]
fn oracle_trace_stream() {
    use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
    use crate::conformance::stateful::{enumerate, EnumRun};
    use std::io::Write;
    let (Ok(dir), Ok(name)) = (
        std::env::var("COMPACT_DUMP_DIR"),
        std::env::var("COMPACT_STREAM_CELL"),
    ) else {
        return;
    };
    std::fs::create_dir_all(&dir).expect("conformance: the dump directory");
    let f = fx(&name);
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
    let path = std::path::Path::new(&dir).join(format!("{}.jsonl", name.replace('/', "_")));
    let out = std::rc::Rc::new(std::cell::RefCell::new(std::io::BufWriter::new(
        std::fs::File::create(&path).expect("conformance: the dump file"),
    )));
    let mut counts = Vec::new();
    for side in ["spec", "impl"] {
        let seen: std::rc::Rc<
            std::cell::RefCell<(usize, std::collections::HashMap<String, usize>)>,
        > = Default::default();
        let sink: CompletionSink = {
            let (out, seen, vis) = (
                std::rc::Rc::clone(&out),
                std::rc::Rc::clone(&seen),
                f.visible.clone(),
            );
            Box::new(move |g: &ExecutionGraph, _| {
                let w = wobs(g, &vis).expect("conformance: wobs");
                let s = Summary::of(
                    CompleteExecution::try_finished(g).expect("conformance: complete"),
                    &w,
                    &vis,
                )
                .expect("conformance: a summary");
                let mut st = seen.borrow_mut();
                let i = st.0;
                st.0 += 1;
                let key = dump_line(side, 0, &s, &vis);
                let line = match st.1.get(&key) {
                    Some(&first) => {
                        serde_json::json!({"side": side, "idx": i, "ref": first}).to_string()
                    }
                    None => {
                        st.1.insert(key, i);
                        dump_line(side, i, &s, &vis)
                    }
                };
                writeln!(out.borrow_mut(), "{line}").expect("conformance: a dump line");
                SinkVerdict::Continue
            })
        };
        let mut config = cc.config.clone();
        if side == "spec" {
            config.max_iterations = None;
        }
        let program = if side == "spec" {
            &f.specification
        } else {
            &f.implementation
        };
        enumerate(
            EnumRun {
                config,
                visible: f.visible.clone(),
                mode: ConfMode::Enumerate,
                sink,
                cut: false,
                stop_at_first_report: false,
                gate_sink: None,
            },
            program,
        );
        let st = seen.borrow();
        counts.push((side, st.0, st.1.len()));
    }
    out.borrow_mut().flush().expect("conformance: flush");
    note!("stream {name}: {counts:?} → {}", path.display());
}

// =========================================================================
// Phase 2 items 1–3: the D1, D4, D6 and D7 mechanism fixtures
// (P2-derived.md §1, §2, §3, §6, §8, written before the code)
// =========================================================================

/// A test-local fixture around a program pair, `Bag` model, seed 0, the grid's
/// thread threshold.
fn local_fixture(
    name: &str,
    spec: crate::conformance::grid::Prog,
    imp: crate::conformance::grid::Prog,
    vis: &[&str],
) -> Fixture {
    let mut f = fx(MECH_CELL);
    f.name = name.to_owned();
    f.specification = spec;
    f.implementation = imp;
    f.visible = vis.iter().map(|s| (*s).to_owned()).collect();
    f.config = crate::conformance::grid::cfg(crate::ConsType::Bag);
    f
}

/// `P(v₁, …)` (P2-derived §1.1): visible `a` and `r`; `r` receives one `i32`
/// and forwards it to `a`; one invisible sender per value sends it to `r`.
/// One complete graph per value; all share the shape and the counts
/// `[2, 0, 0]`, and differ in `Sig` exactly when the values differ.
fn p_prog(vals: &'static [i32]) -> crate::conformance::grid::Prog {
    crate::conformance::grid::prog(move || {
        let a = crate::thread::Builder::new()
            .name("a".to_owned())
            .spawn(|| {
                let _: i32 = crate::recv_msg_block();
            })
            .unwrap();
        let aid = a.thread().id();
        let r = crate::thread::Builder::new()
            .name("r".to_owned())
            .spawn(move || {
                let x: i32 = crate::recv_msg_block();
                crate::send_msg(aid, x);
            })
            .unwrap();
        let rid = r.thread().id();
        for (k, v) in vals.iter().enumerate() {
            let v = *v;
            crate::thread::Builder::new()
                .name(format!("s{k}"))
                .spawn(move || crate::send_msg(rid, v))
                .unwrap();
        }
    })
}

/// The compact summaries of a program's complete graphs, in the stateful
/// engine's (Current, `keep_graphs`) completion order: `(spec, impl)`.
fn kept_summaries(f: &Fixture) -> (Vec<CompactSummary>, Vec<CompactSummary>) {
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(f);
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
    let sum = |gs: &[ExecutionGraph]| -> Vec<CompactSummary> {
        gs.iter()
            .map(|g| CompactSummary::at_completion(g, &f.visible, "test"))
            .collect()
    };
    (sum(&o.kept_spec_graphs), sum(&o.kept_impl_graphs))
}

fn sverify_pair(
    f: &Fixture,
) -> (
    crate::conformance::stateful::StatefulOutcome,
    crate::conformance::stateful::StatefulOutcome,
) {
    use crate::conformance::config::IndexKind;
    let run = |k: IndexKind| {
        let cc = GridConfig::new(GridEngine::Stateful)
            .index(k)
            .antichain(true)
            .impl_distinct(true)
            .conf_config(f);
        stateful::run_with(&cc, &f.implementation, &f.specification, false)
    };
    (run(IndexKind::Current), run(IndexKind::Compact))
}

/// m10 (P2-derived §1.2, §8; P2-frozen §4): `SVerify-S` on two signatures of
/// one shape. `P(1,2)` against itself: one bucket, two slots, each query
/// answered from its own slot. `P(1,2)` against `P(1,3)`: `G(3)` finds the
/// bucket, no slot of its signature: `NoSig`, no `≤` test, a report — equal
/// counts in the other slots do not answer it. Current agrees in the same
/// process (reports; `sig_key_buckets` = buckets; `signatures`).
#[test]
fn m10_d1_two_signatures_of_one_shape_in_sverify_s() {
    static V12: [i32; 2] = [1, 2];
    static V13: [i32; 2] = [1, 3];
    // D1-self.
    let f = local_fixture("compact/d1-self", p_prog(&V12), p_prog(&V12), &["a", "r"]);
    let (spec, imp) = kept_summaries(&f);
    assert_eq!(
        (spec.len(), imp.len()),
        (2, 2),
        "conformance: two graphs each"
    );
    assert!(
        spec[0].hash == spec[1].hash && spec[0].sig != spec[1].sig && spec[0].ord == spec[1].ord,
        "conformance: one shape, two signatures, equal counts"
    );
    assert_eq!(
        spec[0].ord,
        OrdCounts::U8(vec![2, 0, 0]),
        "conformance: P's counts"
    );
    let (cur, cmp) = sverify_pair(&f);
    let s = cmp.counters.compact.as_ref().unwrap();
    assert_eq!(
        (
            cmp.reports.len(),
            s.buckets,
            s.signatures,
            s.signatures_seen,
            s.entries,
            s.admitted,
            s.insert_tests,
            s.containment_tests,
            s.coordinates_compared,
            s.sig_tests,
            s.sig_bytes_est
        ),
        (0, 1, 2, 2, 2, 2, 0, 2, 6, 3, 256),
        "conformance: D1-self, SVerify-S compact (P2-frozen §7: hint)"
    );
    assert_eq!(cur.reports.len(), 0);
    assert_eq!(
        (cmp.counters.sig_key_buckets, cmp.counters.signatures),
        (cur.counters.sig_key_buckets, cur.counters.signatures),
        "conformance: the current index's two counts"
    );
    assert_eq!(
        (cur.counters.sig_key_buckets, cur.counters.signatures),
        (1, 2)
    );
    // D1-miss.
    let f = local_fixture("compact/d1-miss", p_prog(&V12), p_prog(&V13), &["a", "r"]);
    let (spec, imp) = kept_summaries(&f);
    let (cur, cmp) = sverify_pair(&f);
    let s = cmp.counters.compact.as_ref().unwrap();
    let g1_slot = spec
        .iter()
        .position(|m| imp.iter().any(|g| g.sig == m.sig))
        .unwrap();
    assert_eq!(
        (
            cmp.reports.len(),
            s.buckets,
            s.signatures,
            s.signatures_seen,
            s.entries,
            s.containment_tests,
            s.coordinates_compared,
            s.sig_tests,
            s.sig_bytes_est
        ),
        (1, 1, 2, 2, 2, 1, 3, 4, 256),
        "conformance: D1-miss, SVerify-S compact (G(1)'s slot at {g1_slot}; P1: no slot for Sig(3))"
    );
    let c = &cmp.counters;
    assert_eq!(
        (
            c.lookups,
            c.lookups_succeeded,
            c.lookups_signature_miss,
            c.lookups_failed_after_tests
        ),
        (2, 1, 1, 0)
    );
    let k = &cur.counters;
    assert_eq!(
        (
            cur.reports.len(),
            k.lookups_signature_miss,
            k.lookups_succeeded
        ),
        (1, 1, 1),
        "conformance: Current agrees"
    );
    assert_eq!(
        report_seq(&cur.reports, &f.visible),
        report_seq(&cmp.reports, &f.visible)
    );
    assert_eq!(
        (c.impl_distinct_summaries, k.impl_distinct_summaries),
        (Some(2), Some(2)),
        "conformance: exact distinct counts, the unstored signature included"
    );
}

fn cfirst_compact(f: &Fixture, cap: Capacity) -> crate::conformance::cfirst::CFirstOutcome {
    use crate::conformance::config::IndexKind;
    let cc = GridConfig::new(GridEngine::CompleteFirst)
        .witness_cache(cap)
        .quiet(true)
        .index(IndexKind::Compact)
        .antichain(true)
        .probe_memo(true)
        .impl_distinct(true)
        .conf_config(f);
    crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false)
}

fn cfirst_current(f: &Fixture, cap: Capacity) -> crate::conformance::cfirst::CFirstOutcome {
    let cc = GridConfig::new(GridEngine::CompleteFirst)
        .witness_cache(cap)
        .quiet(true)
        .conf_config(f);
    crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false)
}

/// m11 (P2-derived §1.3, §1.4.3, §8; P2-frozen §4–§5): complete-first on two
/// signatures of one shape. `P(1,2)` against `P(1,3)` at `w=inf`: a failing
/// sweep for `G(3)` (a report), whose signature still gets an id and an empty
/// slot; `sig_tests` 2 or 3 by the implementation order. `P(1,2)` against
/// itself: two slots, four `Sig` tests. `P₃(1,2,1)` at `Bounded(1)`: the
/// emptied slot keeps its id, so a re-admission counts — equal to the current
/// engine's — and the counters follow the implementation order's row.
/// The implementation order is read from the stateful engine's kept graphs
/// (the same `Ltr` enumeration of the same program).
#[test]
fn m11_d1_two_signatures_of_one_shape_in_complete_first() {
    static V12: [i32; 2] = [1, 2];
    static V13: [i32; 2] = [1, 3];
    static V121: [i32; 3] = [1, 2, 1];
    // D1-miss, w=inf.
    let f = local_fixture(
        "compact/d1-miss-cf",
        p_prog(&V12),
        p_prog(&V13),
        &["a", "r"],
    );
    let (spec, imp) = kept_summaries(&f);
    let g1_first = spec.iter().any(|m| m.sig == imp[0].sig);
    let o = cfirst_compact(&f, Capacity::Unbounded);
    let s = o.counters.compact.as_ref().unwrap();
    assert_eq!(
        (
            o.reports.len(),
            o.counters.sweeps,
            o.counters.admissions,
            s.signatures,
            s.signatures_seen,
            s.buckets,
            s.sig_tests,
            s.impl_distinct_summaries
        ),
        (1, 2, 1, 1, 1, 1, if g1_first { 1 } else { 0 }, Some(2)),
        "conformance: D1-miss complete-first (G(1) first: {g1_first})"
    );
    let cur = cfirst_current(&f, Capacity::Unbounded);
    assert_eq!(
        report_seq(&cur.reports, &f.visible),
        report_seq(&o.reports, &f.visible)
    );
    assert_eq!(
        (&cur.counters.sweep_sizes, cur.counters.sweeps),
        (&o.counters.sweep_sizes, o.counters.sweeps)
    );
    // D1-self, w=inf.
    let f = local_fixture(
        "compact/d1-self-cf",
        p_prog(&V12),
        p_prog(&V12),
        &["a", "r"],
    );
    let o = cfirst_compact(&f, Capacity::Unbounded);
    let s = o.counters.compact.as_ref().unwrap();
    assert_eq!(
        (
            o.reports.len(),
            o.counters.admissions,
            s.signatures,
            s.signatures_seen,
            s.buckets,
            s.sig_tests,
            s.memo_entries
        ),
        (0, 2, 2, 2, 1, 2, 2),
        "conformance: D1-self complete-first"
    );
    // P₃(1,2,1) at Bounded(1).
    let f = local_fixture("compact/d1-p3", p_prog(&V121), p_prog(&V121), &["a", "r"]);
    let (spec, imp) = kept_summaries(&f);
    assert_eq!((spec.len(), imp.len()), (3, 3));
    let one = &spec
        .iter()
        .find(|m| spec.iter().filter(|n| n.sig == m.sig).count() == 2)
        .unwrap()
        .sig;
    let order: Vec<u8> = imp
        .iter()
        .map(|g| if &g.sig == one { 1 } else { 2 })
        .collect();
    // (sweeps, admissions, evictions, memo_clears, readmissions, memo_hits, sig_tests)
    let want = match order.as_slice() {
        [1, 2, 1] => (3, 3, 2, 2, 1, 0, 4),
        [1, 1, 2] => (2, 2, 1, 1, 0, 1, 3),
        [2, 1, 1] => (2, 2, 1, 1, 0, 1, 3),
        other => panic!("conformance: an impossible order {other:?}"),
    };
    let o = cfirst_compact(&f, Capacity::Bounded(1));
    let (c, s) = (&o.counters, o.counters.compact.as_ref().unwrap());
    assert_eq!(
        (
            c.sweeps,
            c.admissions,
            c.evictions,
            s.memo_clears,
            c.readmissions,
            s.memo_hits,
            s.sig_tests
        ),
        want,
        "conformance: P3 at Bounded(1), order {order:?}"
    );
    assert_eq!(
        (
            s.signatures,
            s.signatures_seen,
            s.buckets,
            s.entries,
            o.reports.len()
        ),
        (1, 2, 1, 1, 0)
    );
    let cur = cfirst_current(&f, Capacity::Bounded(1));
    assert_eq!(
        (
            cur.counters.evictions,
            cur.counters.readmissions,
            &cur.counters.sweep_sizes
        ),
        (c.evictions, c.readmissions, &c.sweep_sizes),
        "conformance: the emptied slot keeps its id: readmissions equal the current engine's"
    );
}

/// m12 (P2-derived §2.2; P2-frozen §2): D4's exit. A held order whose first
/// coordinate exceeds the query's is rejected after one coordinate (the
/// slice's three-way scan read all `L`); a held order larger at 0 and
/// smaller at 1 after one (the slice: two); a held order `≤` the query reads
/// all `L` and answers. `containment_tests` counts the tests, and
/// `coordinates_compared` the coordinates.
#[test]
fn m12_d4_the_first_exceeding_coordinate_exits() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    let mut q = vec![1u8; l];
    q[0] = 0;
    let mut coords = 0;
    assert!(!syn(&base, &vec![1u8; l])
        .ord
        .le_counted(&syn(&base, &q).ord, &mut coords));
    assert_eq!(coords, 1, "conformance: exit at coordinate 0");
    let mut h = vec![0u8; l];
    h[0] = 1;
    let mut coords = 0;
    assert!(!syn(&base, &h)
        .ord
        .le_counted(&syn(&base, &q).ord, &mut coords));
    assert_eq!(coords, 1);
    let mut coords = 0;
    assert!(syn(&base, &vec![0u8; l])
        .ord
        .le_counted(&syn(&base, &q).ord, &mut coords));
    assert_eq!(coords, l, "conformance: a contained order reads all");
    // Through the index (antichain off; admission order h1, h0).
    let mut ix = CompactIndex::new(false);
    ix.insert(&syn(&base, &vec![1u8; l]));
    ix.insert(&syn(&base, &vec![0u8; l]));
    assert_eq!(ix.covers(&syn(&base, &q)), (Some(0), Covers::Found(1)));
    let s = ix.stats().clone();
    assert_eq!(
        (s.containment_tests, s.coordinates_compared),
        (2, 1 + l),
        "conformance: 1 coordinate for the exceeding entry, L for the answering one"
    );
    assert!(s.coordinates_compared <= s.containment_tests * l);
}

/// `Q` (P2-derived §3.1): one signature (`a: [Send 5]`, `b: [Recv 5]`), two
/// orders. `direct = false`: `a` sends to invisible `x`, which forwards a 5
/// to `b`, and invisible `y` sends a 5 to `b` (b reads y: `[0,0]`; b reads
/// x: `[0,1]`); under `Ltr` the `[0,0]` graph completes first (measured).
/// `direct = true`: `a` sends its 5 straight to `b` and `y`, spawned after
/// `a`, sends a 5 too (b reads a: `[0,1]`; b reads y: `[0,0]`); under `Ltr`
/// the `[0,1]` graph completes first (measured), so the second insertion
/// removes it.
fn q_prog(direct: bool) -> crate::conformance::grid::Prog {
    crate::conformance::grid::prog(move || {
        let b = crate::thread::Builder::new()
            .name("b".to_owned())
            .spawn(|| {
                let _: i32 = crate::recv_msg_block();
            })
            .unwrap();
        let bid = b.thread().id();
        let spawn_y = move || {
            crate::thread::Builder::new()
                .name("y".to_owned())
                .spawn(move || crate::send_msg(bid, 5i32))
                .unwrap();
        };
        if direct {
            crate::thread::Builder::new()
                .name("a".to_owned())
                .spawn(move || crate::send_msg(bid, 5i32))
                .unwrap();
            spawn_y();
        } else {
            spawn_y();
            let xid = crate::thread::Builder::new()
                .name("x".to_owned())
                .spawn(move || {
                    let _: i32 = crate::recv_msg_block();
                    crate::send_msg(bid, 5i32);
                })
                .unwrap()
                .thread()
                .id();
            crate::thread::Builder::new()
                .name("a".to_owned())
                .spawn(move || crate::send_msg(xid, 5i32))
                .unwrap();
        }
    })
}

/// m13 (P2-derived §3.1; P2-frozen §3 D7): `orders_held` under `Compact` is
/// the held orders, `admitted − antichain_dropped_old` = `entries`. On `Q`
/// the enumeration order decides between a removal (`[0,1]` first: the
/// second insertion removes it; the slice's `orders_held` would say 2) and a
/// dropped new order; both spawn orders are run and at least one must take
/// the removal, so the D7 case is exercised.
#[test]
fn m13_d7_orders_held_subtracts_antichain_removals() {
    let mut removal_seen = false;
    for direct in [true, false] {
        let f = local_fixture("compact/d7-q", q_prog(direct), q_prog(direct), &["a", "b"]);
        let (spec, _) = kept_summaries(&f);
        assert_eq!(spec.len(), 2, "conformance: two graphs");
        assert_eq!(spec[0].sig, spec[1].sig, "conformance: one signature");
        let big_first = spec[0].ord == OrdCounts::U8(vec![0, 1]);
        assert!(
            big_first || spec[0].ord == OrdCounts::U8(vec![0, 0]),
            "conformance: Q's counts {:?}",
            spec[0].ord
        );
        let (_, cmp) = sverify_pair(&f);
        let s = cmp.counters.compact.as_ref().unwrap();
        let want = if big_first { (2, 1, 0) } else { (1, 0, 1) };
        assert_eq!(
            (s.admitted, s.antichain_dropped_old, s.antichain_dropped_new),
            want,
            "conformance: Q, direct {direct}, [0,1] first {big_first}"
        );
        assert_eq!(
            (
                cmp.counters.orders_held,
                s.entries,
                cmp.reports.len(),
                s.containment_tests
            ),
            (1, 1, 0, 2)
        );
        assert_eq!(
            cmp.counters.orders_held,
            s.admitted - s.antichain_dropped_old
        );
        removal_seen |= big_first;
    }
    assert!(
        removal_seen,
        "conformance: neither spawn order put [0,1] first"
    );
}

/// m14 (P2-derived §3.2; P2-frozen §3 D6, §5): the `impl_distinct` knob.
/// Off (the default): no distinct set, the column blank (`None`) on both
/// engines and both index kinds, and the label unchanged. On:
/// `/distinct=on` closes the label and parses back; the stateful engine
/// counts under both kinds and complete-first under `Compact` only, each
/// equal to step 0 on the cell (A2 pb k2q2: 6).
#[test]
fn m14_d6_the_distinct_knob() {
    use crate::conformance::config::IndexKind;
    let f = fx(MECH_CELL);
    for k in [IndexKind::Current, IndexKind::Compact] {
        for on in [false, true] {
            let g = GridConfig::new(GridEngine::Stateful)
                .index(k)
                .impl_distinct(on);
            let label = g.label();
            assert_eq!(label.ends_with("/distinct=on"), on, "conformance: {label}");
            let back = crate::conformance::eval::parse_label(&label)
                .unwrap_or_else(|| panic!("conformance: {label} does not parse"));
            assert_eq!(back.label(), label, "conformance: the label round-trips");
            let o = stateful::run_with(
                &g.conf_config(&f),
                &f.implementation,
                &f.specification,
                false,
            );
            let want = on.then_some(6);
            assert_eq!(
                o.counters.impl_distinct_summaries, want,
                "conformance: stateful {k:?} {on}"
            );
            if let Some(s) = o.counters.compact.as_ref() {
                assert_eq!(s.impl_distinct_summaries, want, "conformance: stats {on}");
            }
            let c = GridConfig::new(GridEngine::CompleteFirst)
                .quiet(true)
                .index(k)
                .impl_distinct(on);
            let o = crate::conformance::cfirst::run_with(
                &c.conf_config(&f),
                &f.implementation,
                &f.specification,
                false,
            );
            let got = o
                .counters
                .compact
                .as_ref()
                .and_then(|s| s.impl_distinct_summaries);
            let want = (on && k == IndexKind::Compact).then_some(6);
            assert_eq!(got, want, "conformance: complete-first {k:?} {on}");
        }
    }
    assert!(
        !GridConfig::new(GridEngine::Stateful)
            .label()
            .contains("distinct"),
        "conformance: the default label is the slice's"
    );
}

/// m15 (P1, P2-frozen §7): a query never creates a bucket or a slot. On an
/// empty index two queries are both `(None, NoBucket)` (the first created
/// nothing, so the second is not `NoSig`); with `base` held, two queries of
/// another signature of the shape are both `(None, NoSig)` with
/// `signatures_seen` unchanged; in the cache a probe of an absent signature
/// is `(Miss, None)` and only the admission creates its slot.
#[test]
fn m15_p1_a_query_creates_no_bucket_and_no_slot() {
    let base = real_summary(MECH_CELL);
    let bad = forged(&base);
    let mut ix = CompactIndex::new(true);
    for _ in 0..2 {
        assert_eq!(ix.covers(&base), (None, Covers::NoBucket));
    }
    let s = ix.stats().clone();
    assert_eq!(
        (s.buckets, s.signatures, s.signatures_seen, s.sig_tests),
        (0, 0, 0, 0),
        "conformance: nothing created by two queries"
    );
    assert_eq!(ix.insert(&base), (0, Inserted::Stored(0)));
    for _ in 0..2 {
        assert_eq!(ix.covers(&bad), (None, Covers::NoSig));
    }
    let s = ix.stats().clone();
    assert_eq!(
        (
            s.buckets,
            s.signatures,
            s.signatures_seen,
            s.sig_tests,
            s.containment_tests
        ),
        (1, 1, 1, 2, 0),
        "conformance: one Sig test per query, no slot"
    );
    let mut c = CompactCache::new(Capacity::Unbounded, true, true);
    assert!(c.admit(&base, &base));
    assert_eq!(c.probe(&bad), (Probe::Miss, None));
    assert_eq!(
        c.stats().signatures_seen,
        1,
        "conformance: the probe created nothing"
    );
    assert!(
        c.admit(&bad, &bad),
        "conformance: the admission creates the slot"
    );
    assert_eq!(c.probe(&bad), (Probe::MemoHit, Some(1)));
    assert_eq!(c.stats().signatures_seen, 2);
}

/// A message type whose equality ignores a field its `Debug` prints: two
/// `Sig`-equal values with different renderings (`Val`'s equality is the
/// type's `PartialEq`, through `msg_equals`).
#[derive(Clone, Debug)]
struct Noisy {
    v: i32,
    noise: i32,
}

impl PartialEq for Noisy {
    fn eq(&self, other: &Self) -> bool {
        self.v == other.v
    }
}

/// `PN` (P2-derived §13.1): `P`'s shape with `Noisy` messages; the two
/// senders send `Noisy { v: 1, noise: 0 }` and `Noisy { v: 1, noise: 1 }`.
fn pn_prog() -> crate::conformance::grid::Prog {
    crate::conformance::grid::prog(|| {
        let a = crate::thread::Builder::new()
            .name("a".to_owned())
            .spawn(|| {
                let _: Noisy = crate::recv_msg_block();
            })
            .unwrap();
        let aid = a.thread().id();
        let r = crate::thread::Builder::new()
            .name("r".to_owned())
            .spawn(move || {
                let x: Noisy = crate::recv_msg_block();
                crate::send_msg(aid, x);
            })
            .unwrap();
        let rid = r.thread().id();
        for noise in 0..2 {
            crate::thread::Builder::new()
                .name(format!("s{noise}"))
                .spawn(move || crate::send_msg(rid, Noisy { v: 1, noise }))
                .unwrap();
        }
    })
}

/// m16 (P3, P2-frozen §7): an alias. `PN`'s two graphs have equal `Sig` and
/// different renderings; the second insertion's rendering has no hint, the
/// second pass finds slot 0 by `Sig ==` (an alias, appended to its hint
/// list), and the insertion is a duplicate; each query then costs one test
/// through its hint. Current agrees (one signature, no report).
#[test]
fn m16_p3_an_alias_is_found_by_the_second_pass() {
    let f = local_fixture("compact/p3-alias", pn_prog(), pn_prog(), &["a", "r"]);
    let (spec, _) = kept_summaries(&f);
    assert_eq!(spec.len(), 2, "conformance: two graphs");
    assert!(
        spec[0].sig == spec[1].sig && format!("{:?}", spec[0].sig) != format!("{:?}", spec[1].sig),
        "conformance: equal signatures, different renderings"
    );
    let (cur, cmp) = sverify_pair(&f);
    let s = cmp.counters.compact.as_ref().unwrap();
    assert_eq!(
        (
            cmp.reports.len(),
            s.sig_tests,
            s.sig_aliases,
            s.signatures,
            s.signatures_seen,
            s.entries,
            s.duplicates,
            s.buckets
        ),
        (0, 3, 1, 1, 1, 1, 1, 1),
        "conformance: one alias, found once, then hinted"
    );
    assert_eq!(
        (cur.reports.len(), cur.counters.signatures),
        (0, 1),
        "conformance: Current agrees"
    );
}

/// m17 (P7, P2-frozen §7): `/distinct=on` prints only where the knob has
/// effect — Stateful under both kinds, CompleteFirst under Compact — and
/// every printed label parses back to itself.
#[test]
fn m17_p7_the_distinct_suffix_only_where_it_acts() {
    use crate::conformance::config::IndexKind;
    for e in [
        GridEngine::Stateful,
        GridEngine::CompleteFirst,
        GridEngine::Enumerator,
    ] {
        for k in [IndexKind::Current, IndexKind::Compact] {
            for on in [false, true] {
                let g = GridConfig::new(e).index(k).impl_distinct(on);
                let label = g.label();
                let acts = on
                    && (e == GridEngine::Stateful
                        || (e == GridEngine::CompleteFirst && k == IndexKind::Compact));
                assert_eq!(
                    label.ends_with("/distinct=on"),
                    acts,
                    "conformance: {e:?} {k:?} {on}: {label}"
                );
                let back = crate::conformance::eval::parse_label(&label)
                    .unwrap_or_else(|| panic!("conformance: {label} does not parse"));
                assert_eq!(back.label(), label, "conformance: {label} round-trips");
            }
        }
    }
}

// =========================================================================
// Phase 2 items 4, 5, 7: the inverted index, the trie, the knobs
// (P2-derived §11, §15; P2-frozen §6, §6.1), written before their code
// =========================================================================

use crate::conformance::config::BucketKind;

fn kinds() -> [BucketKind; 5] {
    [
        BucketKind::Scan,
        BucketKind::Inverted(0),
        BucketKind::Inverted(3),
        BucketKind::Inverted(BucketKind::INVERTED_DEFAULT_THRESHOLD),
        BucketKind::Trie,
    ]
}

/// T2's extension (PHASE2 §2; P2-derived §11.1): for each fixture, the
/// spec summaries inserted into one index per slot structure (scan,
/// `inverted:0`, `inverted:3`, `inverted:256`, trie), with the antichain on
/// and off; every insertion's `(SigId, Inserted)` and every implementation
/// query's `(Option<SigId>, Covers)` — the answering `seq` included — must be
/// the scan's. Returns the number of queries compared.
fn t2x_on(name: &str) -> usize {
    let f = fx(name);
    let (spec, imp) = kept_summaries(&f);
    let mut queries = 0;
    for anti in [true, false] {
        let mut ix: Vec<CompactIndex> = kinds()
            .iter()
            .map(|k| CompactIndex::with_bucket(anti, *k))
            .collect();
        for m in &spec {
            let r: Vec<_> = ix.iter_mut().map(|x| x.insert(m)).collect();
            assert!(
                r.iter().all(|x| *x == r[0]),
                "conformance: {name} anti {anti}: insertions differ {r:?}"
            );
        }
        let mut reached = 0;
        for g in &imp {
            let r: Vec<_> = ix.iter_mut().map(|x| x.covers(g)).collect();
            assert!(
                r.iter().all(|x| *x == r[0]),
                "conformance: {name} anti {anti}: answers differ {r:?}"
            );
            if matches!(r[0].1, Covers::Found(_) | Covers::NotFound) {
                reached += 1;
            }
            queries += 1;
        }
        // P2-frozen §6.1: at threshold 0 every query reaching a slot that
        // holds orders goes through its index; `inverted:256` uses at most
        // as many.
        assert_eq!(
            ix[1].stats().inverted_used,
            Some(reached),
            "conformance: {name} anti {anti}: inverted_used at threshold 0"
        );
        assert!(ix[3].stats().inverted_used.unwrap_or(0) <= reached);
        assert_eq!(
            ix[0].stats().inverted_used,
            None,
            "conformance: scan has no inverted counter"
        );
        assert!(ix[4].stats().trie_nodes_visited.is_some());
    }
    queries
}

#[test]
fn t2x_the_structures_answer_as_the_scan_on_the_size2_cells() {
    let n: usize = SIZE2_CELLS.iter().map(|c| t2x_on(c)).sum();
    note!("t2x size-2: {n} queries");
    assert!(n > 0);
}

#[test]
#[ignore]
fn t2x_the_structures_answer_as_the_scan_on_the_pilot_corpus() {
    let n: usize = PILOT_NAMES.iter().map(|c| t2x_on(c)).sum();
    note!("t2x pilot: {n} queries");
}

/// m18 (P2-derived §11.2): the threshold crossing at `inverted:3` — scan
/// below three orders, the index from the third on, kept after the antichain
/// empties the slot down to one order — and the trie on the same steps.
#[test]
fn m18_the_inverted_threshold_crossing_and_the_trie() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    assert!(l >= 3);
    let u = |i: usize| syn(&base, &unit(l, i));
    let zero = syn(&base, &vec![0u8; l]);
    let st = |ix: &CompactIndex| {
        let s = ix.stats();
        (
            s.containment_tests,
            s.coordinates_compared,
            s.inverted_used,
            s.inverted_words,
        )
    };
    let mut ix = CompactIndex::with_bucket(true, BucketKind::Inverted(3));
    ix.insert(&u(0));
    ix.insert(&u(1));
    assert_eq!(
        ix.covers(&u(1)),
        (Some(0), Covers::Found(1)),
        "conformance: step 2"
    );
    assert_eq!(
        st(&ix),
        (2, 1 + l, Some(0), Some(0)),
        "conformance: below the threshold, the scan"
    );
    ix.insert(&u(2));
    assert_eq!(
        ix.covers(&u(2)),
        (Some(0), Covers::Found(2)),
        "conformance: step 4"
    );
    assert_eq!(
        st(&ix),
        (2, 1 + l, Some(1), Some(3)),
        "conformance: the index, 2 + 1 words"
    );
    assert_eq!(ix.insert(&zero), (0, Inserted::Stored(3)));
    assert_eq!(ix.stats().antichain_dropped_old, 3);
    assert_eq!(
        ix.covers(&u(0)),
        (Some(0), Covers::Found(3)),
        "conformance: step 6"
    );
    assert_eq!(
        st(&ix),
        (2, 1 + l, Some(2), Some(6)),
        "conformance: the index kept at one order"
    );
    // The trie on the same steps.
    let mut tr = CompactIndex::with_bucket(true, BucketKind::Trie);
    tr.insert(&u(0));
    tr.insert(&u(1));
    assert_eq!(tr.covers(&u(1)), (Some(0), Covers::Found(1)));
    assert_eq!(tr.stats().trie_nodes_visited, Some(l + 1));
    tr.insert(&u(2));
    assert_eq!(tr.covers(&u(2)), (Some(0), Covers::Found(2)));
    assert_eq!(tr.stats().trie_nodes_visited, Some(2 * (l + 1)));
    tr.insert(&zero);
    assert_eq!(tr.covers(&u(0)), (Some(0), Covers::Found(3)));
    let s = tr.stats();
    assert_eq!(
        (
            s.trie_nodes_visited,
            s.containment_tests,
            s.coordinates_compared
        ),
        (Some(3 * (l + 1)), 0, 0),
        "conformance: no ≤ test through the trie"
    );
}

/// m19 (P2-derived §15.2 R1): antichain removal reaches each structure. u₀,
/// u₁, then 0…0 removing both; the query u₁ is answered by 0…0 (seq 2) —
/// inverted: rule {0}, 1 + 1 words; trie: L + 1 nodes (a stale branch or
/// `min_seq` would enter u₁'s dead path or answer seq 1).
#[test]
fn m19_antichain_removal_reaches_the_structures() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    let u = |i: usize| syn(&base, &unit(l, i));
    let zero = syn(&base, &vec![0u8; l]);
    for k in [BucketKind::Scan, BucketKind::Inverted(0), BucketKind::Trie] {
        let mut ix = CompactIndex::with_bucket(true, k);
        ix.insert(&u(0));
        ix.insert(&u(1));
        assert_eq!(ix.insert(&zero), (0, Inserted::Stored(2)));
        assert_eq!(ix.stats().antichain_dropped_old, 2);
        assert_eq!(
            ix.covers(&u(1)),
            (Some(0), Covers::Found(2)),
            "conformance: {k:?}"
        );
        let s = ix.stats();
        let got = (
            s.containment_tests,
            s.inverted_used,
            s.inverted_words,
            s.trie_nodes_visited,
        );
        let want = match k {
            BucketKind::Scan => (1, None, None, None),
            BucketKind::Inverted(_) => (0, Some(1), Some(2), None),
            BucketKind::Trie => (0, None, None, Some(l + 1)),
        };
        assert_eq!(got, want, "conformance: {k:?}");
    }
}

/// m20 (P2-derived §15.2 R2): FIFO eviction and re-admission at
/// `Bounded(2)` with each structure. After u₀ is evicted, the probe u₀
/// misses (inverted 2 + 1 words; trie 3 nodes); re-admitting u₀ evicts u₁
/// and stores u₀ at seq 3 (a new position; `readmissions` 1); the probe
/// u₀ + u₁ is answered by seq 3 (inverted 1 + 1 words; trie L + 3 nodes).
#[test]
fn m20_fifo_eviction_and_readmission_reach_the_structures() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    let u = |i: usize| syn(&base, &unit(l, i));
    let mut q = vec![0u8; l];
    q[0] = 1;
    q[1] = 1;
    let q = syn(&base, &q);
    for k in [BucketKind::Scan, BucketKind::Inverted(0), BucketKind::Trie] {
        let mut c = CompactCache::with_bucket(Capacity::Bounded(2), false, true, k);
        for i in 0..3 {
            assert!(c.admit(&u(i), &u(i)), "conformance: {k:?} admit u{i}");
        }
        assert_eq!(c.evictions(), 1);
        let s0 = c.stats();
        assert_eq!(
            c.probe(&u(0)),
            (Probe::Miss, Some(0)),
            "conformance: {k:?} u0 evicted"
        );
        let s1 = c.stats();
        let d = |a: Option<usize>, b: Option<usize>| b.map(|b| b - a.unwrap_or(0));
        let got = (
            s1.containment_tests - s0.containment_tests,
            d(s0.inverted_words, s1.inverted_words),
            d(s0.trie_nodes_visited, s1.trie_nodes_visited),
        );
        let want = match k {
            BucketKind::Scan => (2, None, None),
            BucketKind::Inverted(_) => (0, Some(3), None),
            BucketKind::Trie => (0, None, Some(3)),
        };
        assert_eq!(got, want, "conformance: {k:?} the miss");
        assert!(c.admit(&u(0), &u(0)), "conformance: {k:?} re-admission");
        assert_eq!((c.evictions(), c.readmissions()), (2, 1));
        let s2 = c.stats();
        assert_eq!(
            c.probe(&q),
            (Probe::Hit, Some(0)),
            "conformance: {k:?} the hit"
        );
        let s3 = c.stats();
        let got = (
            s3.containment_tests - s2.containment_tests,
            d(s2.inverted_words, s3.inverted_words),
            d(s2.trie_nodes_visited, s3.trie_nodes_visited),
        );
        let want = match k {
            BucketKind::Scan => (2, None, None),
            BucketKind::Inverted(_) => (0, Some(2), None),
            BucketKind::Trie => (0, None, Some(l + 3)),
        };
        assert_eq!(got, want, "conformance: {k:?} the hit");
    }
}

/// m21 (P2-derived §15.3, §15.4; P2-frozen §6 item 7): the bucket field in
/// the label — under Compact only, never for the scan, before `/distinct=on`
/// — round-trips through `parse_label`; and `COMPACT2` is 24 + 14 rows as
/// PHASE2 §6 says, every row rep 0, timed, default tier, knob off.
#[test]
fn m21_the_bucket_label_and_the_compact2_spec() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::{
        compact2_ablation_configs, compact2_spec, compact_configs, parse_label, RunKind,
    };
    for e in [GridEngine::Stateful, GridEngine::CompleteFirst] {
        for k in [IndexKind::Current, IndexKind::Compact] {
            for b in [
                BucketKind::Scan,
                BucketKind::Inverted(0),
                BucketKind::Inverted(256),
                BucketKind::Trie,
            ] {
                for on in [false, true] {
                    let g = GridConfig::new(e).index(k).bucket(b).impl_distinct(on);
                    let label = g.label();
                    let field = match (k, b) {
                        (IndexKind::Compact, BucketKind::Inverted(t)) => {
                            Some(format!("/bucket=inverted:{t}"))
                        }
                        (IndexKind::Compact, BucketKind::Trie) => Some("/bucket=trie".to_owned()),
                        _ => None,
                    };
                    match &field {
                        Some(f) => {
                            let at = label
                                .find(f.as_str())
                                .unwrap_or_else(|| panic!("conformance: {label}"));
                            if let Some(d) = label.find("/distinct=on") {
                                assert!(at < d, "conformance: bucket before distinct: {label}");
                            }
                        }
                        None => assert!(!label.contains("bucket="), "conformance: {label}"),
                    }
                    let back = parse_label(&label)
                        .unwrap_or_else(|| panic!("conformance: {label} does not parse"));
                    assert_eq!(back.label(), label, "conformance: round trip");
                }
            }
        }
    }
    let spec = compact2_spec();
    assert_eq!(spec.name, "COMPACT2");
    assert_eq!(spec.rows.len(), 38, "conformance: 6 × 4 + 2 × 7");
    let size: Vec<&str> = vec![
        "apps/a1/correct/spec/n4r4",
        "apps/a2/pb/spec/k4q4",
        "apps/a3/fifo/spec/k4q4",
        "apps/a4/hash/a4a/k4q4m4",
        "2pc/leader/conf/n4",
        "2pc/leader/conf/n5",
    ];
    let configs = compact_configs();
    let ablations = compact2_ablation_configs();
    for (i, r) in spec.rows.iter().enumerate() {
        assert!(
            r.rep == 0 && r.run_kind == RunKind::Timed && r.tier.name == "default",
            "conformance: row {i}"
        );
        assert!(
            !r.config.label().contains("distinct=on"),
            "conformance: D6 off on row {i}"
        );
        if i < 24 {
            assert_eq!(r.fixture, size[i / 4], "conformance: block 1 row {i}");
            assert_eq!(r.config.label(), configs[i % 4].label());
        } else {
            let j = i - 24;
            let cell = ["apps/a3/fifo/spec/k3q3", "apps/a4/hash/a4a/k3q3m3"][j / 7];
            assert_eq!(r.fixture, cell, "conformance: block 2 row {i}");
            assert_eq!(r.config.label(), ablations[j % 7].label());
        }
    }
    let labels: Vec<String> = ablations.iter().map(|g| g.label()).collect();
    let n = |s: &str| labels.iter().filter(|l| l.contains(s)).count();
    assert_eq!(
        (
            n("bucket=inverted:0"),
            n("bucket=trie"),
            n("anti=false"),
            n("pmemo=false")
        ),
        (2, 2, 2, 1),
        "conformance: the seven ablations: {labels:#?}"
    );
}

// =========================================================================
// Final audit of 55ef467, A1: several covering orders for one query
// (P2-derived §18, derived before this test)
// =========================================================================

/// §18.1's 73 orders, in admission order, as length-L count vectors on
/// `MECH_CELL`'s signature: c₀ (seq 0); 69 fillers (x₃ ≥ 1, coordinate sum
/// 10, x₃ ascending then (x₀, x₁, x₂) lexicographic, skipping (5, 4, 0, 1));
/// c₁ (70); c₂ (71); m = c₀ − e₁ (72).
fn a1_orders(l: usize) -> Vec<Vec<u8>> {
    let v = |xs: [u8; 4]| {
        let mut o = vec![0u8; l];
        o[..4].copy_from_slice(&xs);
        o
    };
    let mut out = vec![v([5, 5, 0, 0])];
    'fill: for x3 in 1..=10u8 {
        for x0 in 0..=10u8 {
            for x1 in 0..=10u8 {
                let Some(x2) = 10u8.checked_sub(x3 + x0 + x1) else {
                    continue;
                };
                if [x0, x1, x2, x3] == [5, 4, 0, 1] {
                    continue;
                }
                out.push(v([x0, x1, x2, x3]));
                if out.len() == 70 {
                    break 'fill;
                }
            }
        }
    }
    out.push(v([4, 1, 5, 0]));
    out.push(v([0, 5, 5, 0]));
    out.push(v([5, 4, 0, 0]));
    out
}

/// m22 (A1; P2-derived §18): one query q = (5, 5, 5, 0) with several
/// pairwise-incomparable covers (c₀ seq 0, c₁ seq 70, c₂ seq 71, m seq 72),
/// a slot of 73 positions (two bitset words), and a removal of the earliest
/// cover — by the antichain (m < c₀) with the antichain on, by FIFO eviction
/// at `Bounded(72)` with it off. Scan, `inverted:0`, `inverted:40` (crossed
/// between Q0 and Q1) and trie must all return the **earliest live** cover:
/// Q0 (30 orders) `Found(0)`; Q1 (72 orders) `Found(0)` though the
/// value-ascending first cover is c₂ (71); Q2 (after the removal)
/// `Found(70)` though c₂ (71) is still met first and c₀'s stale position 0 is
/// in word 0. With the antichain on, `inverted:0`'s words are 4, 9, 10.
#[test]
fn m22_a1_the_earliest_of_several_covers_after_removals() {
    let base = real_summary(MECH_CELL);
    let l = base.ord.len();
    assert!(l >= 4, "conformance: the cell's order is too short ({l})");
    let orders = a1_orders(l);
    assert_eq!(orders.len(), 73);
    let s = |o: &Vec<u8>| syn(&base, o);
    let mut qv = vec![0u8; l];
    qv[..3].copy_from_slice(&[5, 5, 5]);
    let q = s(&qv);
    // The covers, independent of any structure: exactly seq 0, 70, 71, 72.
    let covers: Vec<usize> = (0..73)
        .filter(|&i| orders[i].iter().zip(&qv).all(|(a, b)| a <= b))
        .collect();
    assert_eq!(covers, vec![0, 70, 71, 72], "conformance: §18.1 fact 3");
    let kinds = [
        BucketKind::Scan,
        BucketKind::Inverted(0),
        BucketKind::Inverted(40),
        BucketKind::Trie,
    ];
    // Antichain on: the index, the removal by dominance.
    for k in kinds {
        let mut ix = CompactIndex::with_bucket(true, k);
        let words = |ix: &CompactIndex| ix.stats().inverted_words.unwrap_or(0);
        for o in &orders[..30] {
            assert!(matches!(ix.insert(&s(o)).1, Inserted::Stored(_)));
        }
        let w0 = words(&ix);
        assert_eq!(
            ix.covers(&q),
            (Some(0), Covers::Found(0)),
            "conformance: {k:?} Q0"
        );
        let w1 = words(&ix);
        for o in &orders[30..72] {
            assert!(
                matches!(ix.insert(&s(o)).1, Inserted::Stored(_)),
                "conformance: {k:?}"
            );
        }
        assert_eq!(
            ix.covers(&q),
            (Some(0), Covers::Found(0)),
            "conformance: {k:?} Q1"
        );
        let w2 = words(&ix);
        assert_eq!(ix.insert(&s(&orders[72])), (0, Inserted::Stored(72)));
        assert_eq!(
            ix.stats().antichain_dropped_old,
            1,
            "conformance: {k:?}: m removes c₀ alone"
        );
        assert_eq!(
            ix.covers(&q),
            (Some(0), Covers::Found(70)),
            "conformance: {k:?} Q2"
        );
        let w3 = words(&ix);
        let got = (w1 - w0, w2 - w1, w3 - w2);
        match k {
            BucketKind::Inverted(0) => assert_eq!(got, (4, 9, 10), "conformance: §18.3 words"),
            BucketKind::Inverted(40) => assert_eq!(got, (0, 9, 10), "conformance: §18.3 words"),
            _ => assert_eq!(got, (0, 0, 0)),
        }
    }
    // Antichain off: the cache at Bounded(72), memo off, FIFO eviction.
    for k in kinds {
        let mut c = CompactCache::with_bucket(Capacity::Bounded(72), false, false, k);
        for o in &orders[..30] {
            assert!(c.admit(&s(o), &s(o)));
        }
        assert_eq!(
            c.index().clone().covers(&q),
            (Some(0), Covers::Found(0)),
            "conformance: {k:?} off Q0"
        );
        for o in &orders[30..72] {
            assert!(c.admit(&s(o), &s(o)));
        }
        assert_eq!(c.evictions(), 0);
        assert_eq!(
            c.index().clone().covers(&q),
            (Some(0), Covers::Found(0)),
            "conformance: {k:?} off Q1"
        );
        assert!(c.admit(&s(&orders[72]), &s(&orders[72])));
        assert_eq!(
            c.evictions(),
            1,
            "conformance: {k:?}: m's admission evicts c₀"
        );
        assert_eq!(
            c.index().clone().covers(&q),
            (Some(0), Covers::Found(70)),
            "conformance: {k:?} off Q2"
        );
        assert_eq!(
            c.probe(&q),
            (Probe::Hit, Some(0)),
            "conformance: {k:?} off probe"
        );
        assert!(
            !c.index().antichain(),
            "conformance: Bounded forces the antichain off"
        );
    }
}

// =========================================================================
// SVERIFY-P I1-9 (criteria rev 1.3): every execution reaches the completion
// gate — measured on the stateful engine (both sides) and complete-first
// against a plain `verify` of the same program
// =========================================================================

/// A fixture by name: the catalogue, or a `P4-MIXED` registry entry.
fn any_fixture(name: &str) -> Fixture {
    crate::conformance::grid::mixed_fixtures()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| fx(name))
}

/// Plain Must on one program with the fixture's configuration and the one
/// field conformance forces (`keep_going_after_error`, as the `Explore` arm):
/// `execs + block`.
fn plain_total(f: &Fixture, p: &crate::conformance::grid::Prog) -> usize {
    let mut cfg = f.config.clone();
    cfg.keep_going_after_error = true;
    let p = p.clone();
    let s = crate::verify(cfg, move || p());
    s.execs + s.block
}

/// I1-9: on A3 fifo k2q2, A4 hash k2q2m2 (every completion blocked),
/// `mixed/branch` and a violating pilot fixture (a3 never-grant k2q2), the
/// stateful engine's completion counts (`spec_graphs`; `impl_graphs` and its
/// ctx-side `executions`) and complete-first's outer `executions` equal plain
/// Must's `execs + block` on the same program. Neither engine prunes here
/// (`Enumerate` never does; complete-first's cut is off), so the exploration is
/// plain Must's and every ending reaches `Gate::Completion`. The gated engine
/// prunes and does not expose Must's `Stats`; it is covered by the shared-path
/// inference (rev 1.3).
#[test]
fn i1_9_every_execution_reaches_the_completion_gate() {
    let mut bad = Vec::new();
    for name in [
        "apps/a3/fifo/spec/k2q2",
        "apps/a4/hash/a4a/k2q2m2",
        "mixed/branch",
        "apps/a3/never-grant/spec/k2q2",
    ] {
        let f = any_fixture(name);
        let spec_total = plain_total(&f, &f.specification);
        let impl_total = plain_total(&f, &f.implementation);
        let st = stateful::run_with(
            &GridConfig::new(GridEngine::Stateful).conf_config(&f),
            &f.implementation,
            &f.specification,
            false,
        );
        let got = (st.counters.spec_graphs, st.counters.impl_graphs, st.executions);
        if got != (spec_total, impl_total, impl_total) {
            bad.push(format!(
                "{name} stateful: {got:?} vs plain ({spec_total}, {impl_total})"
            ));
        }
        let cf = crate::conformance::cfirst::run_with(
            &GridConfig::new(GridEngine::CompleteFirst).conf_config(&f),
            &f.implementation,
            &f.specification,
            false,
        );
        if (cf.executions, cf.counters.impl_graphs) != (impl_total, impl_total) {
            bad.push(format!(
                "{name} complete-first: ({}, {}) vs plain {impl_total}",
                cf.executions, cf.counters.impl_graphs
            ));
        }
        note!("i1-9 {name}: spec {spec_total} impl {impl_total}");
    }
    assert!(bad.is_empty(), "conformance: I1-9: {bad:#?}");
}

/// SVERIFY-P I1-7, the "after" side of SVerify-S's uncovered multiset (the
/// "before" side: `oracle_trace_stream` replayed by the coverage rule, the
/// tester's scratch `svp/before/`). `I1_FIXTURE` names one fixture; SVerify-S
/// at X1 (`Ltr`, every report) runs it; each reported graph's summary is
/// printed as `UNC\t<Sig Debug>\t<OrdCounts, comma-separated>` (the before
/// side's line format), followed by `UNCN\t<reports>`.
#[test]
#[ignore]
fn i1_sverify_s_uncovered_multiset() {
    let Ok(name) = std::env::var("I1_FIXTURE") else {
        return;
    };
    let f = any_fixture(&name);
    let cc = crate::conformance::eval::x1_config(
        GridEngine::Stateful,
        crate::conformance::selector::Selector::Ltr,
    )
    .conf_config(&f);
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
    for (g, _) in &o.reports {
        let w = wobs(g, &f.visible).expect("conformance: wobs");
        let s = Summary::of(CompleteExecution::try_finished(g).unwrap(), &w, &f.visible)
            .expect("conformance: a summary");
        let counts = match OrdCounts::of(g, &w, &f.visible) {
            OrdCounts::U8(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
            OrdCounts::U16(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
        };
        note!("UNC\t{:?}\t{}", s.sig, counts.join(","));
    }
    note!("UNCN\t{}", o.reports.len());
}

// =========================================================================
// SVERIFY-P I2 (tester, gate 3; criteria/SVERIFY-P-I2.md rev 1.3): the set
// index against `CompactIndex::with_bucket(false, Scan)`
// =========================================================================

use crate::conformance::compact::{SetIndex, SetStats};

/// The reference's counters as `SetStats` (`slot_max` is `bucket_max`;
/// `insert_tests` has no counterpart, I2-7).
fn ref_stats(ix: &CompactIndex) -> SetStats {
    let c = ix.stats();
    SetStats {
        entries: c.entries,
        buckets: c.buckets,
        slot_max: c.bucket_max,
        signatures: c.signatures,
        signatures_seen: c.signatures_seen,
        sig_tests: c.sig_tests,
        sig_aliases: c.sig_aliases,
        admitted: c.admitted,
        duplicates: c.duplicates,
        containment_tests: c.containment_tests,
        coordinates_compared: c.coordinates_compared,
        summary_bytes: c.summary_bytes,
        sig_bytes_est: c.sig_bytes_est,
    }
}

/// The reference's held orders as (sig_id, seq, counts), sorted.
fn ref_held(ix: &CompactIndex) -> Vec<(u32, u64, OrdCounts)> {
    let mut v: Vec<_> = ix
        .buckets()
        .flat_map(|(_, b)| {
            b.slots
                .iter()
                .flat_map(|sl| sl.orders.iter().map(move |e| (sl.sig_id, e.seq, e.ord.clone())))
        })
        .collect();
    v.sort_by_key(|x| (x.0, x.1));
    v
}

fn set_held(ix: &SetIndex) -> Vec<(u32, u64, OrdCounts)> {
    let mut v: Vec<_> = ix
        .entries()
        .map(|(id, _, e)| (id, e.seq, e.ord.clone()))
        .collect();
    v.sort_by_key(|x| (x.0, x.1));
    v
}

/// I2-3 on one explicit sequence: per insertion the same `(SigId, Inserted)`,
/// insertion-only counters 0 (I2-8), per query (through `&self`) the same
/// `(Option<SigId>, Covers)` including the seq, at the end the same held
/// multiset of (sig_id, seq, counts) with equal representatives, and the same
/// counters. Returns the mismatches.
fn i2_compare(spec: &[CompactSummary], imp: &[CompactSummary]) -> Vec<String> {
    let mut bad = Vec::new();
    let (mut set, mut rf) = (SetIndex::new(), CompactIndex::with_bucket(false, BucketKind::Scan));
    for (i, s) in spec.iter().enumerate() {
        let (a, b) = (set.insert(s), rf.insert(s));
        if a != b {
            bad.push(format!("insertion {i}: set {a:?} reference {b:?}"));
        }
    }
    let st = set.stats();
    if (st.containment_tests, st.coordinates_compared) != (0, 0) {
        bad.push(format!("I2-8: an insertion-only sequence counted {st:?}"));
    }
    let shared: &SetIndex = &set;
    for (i, g) in imp.iter().chain(spec.iter()).enumerate() {
        let (a, b) = (shared.covers(g), rf.covers(g));
        if a != b {
            bad.push(format!("query {i}: set {a:?} reference {b:?}"));
        }
    }
    if set_held(&set) != ref_held(&rf) {
        bad.push("held multisets differ".to_owned());
    }
    let reps: std::collections::BTreeMap<u32, &Sig> = rf
        .buckets()
        .flat_map(|(_, b)| {
            b.slots
                .iter()
                .filter(|s| !s.orders.is_empty())
                .map(|s| (s.sig_id, &s.sig))
        })
        .collect();
    for (id, sig, _) in set.entries() {
        if reps.get(&id).is_none_or(|r| *r != sig) {
            bad.push(format!("the representative of sig_id {id} differs"));
        }
    }
    if set.stats() != ref_stats(&rf) {
        bad.push(format!("stats: set {:?} reference {:?}", set.stats(), ref_stats(&rf)));
    }
    bad
}

/// s1 (I2-3): `SetIndex` is `Send` (I3 moves per-task sets into the merge).
#[test]
fn s1_the_set_index_is_send() {
    fn assert_send<T: Send>() {}
    assert_send::<SetIndex>();
}

/// s2 (I2-3, I2-8): equality with the reference on the five size-2 cells
/// (specification inserted in completion order; implementation and
/// specification summaries queried).
#[test]
fn s2_the_set_index_equals_the_reference_on_the_size2_cells() {
    let mut bad = Vec::new();
    for name in SIZE2_CELLS {
        let (spec, imp) = kept_summaries(&fx(name));
        bad.extend(i2_compare(&spec, &imp).into_iter().map(|m| format!("{name}: {m}")));
    }
    assert!(bad.is_empty(), "conformance: I2-3: {bad:#?}");
}

/// s2 on the pilot corpus (I2-10's in-process part), one process.
#[test]
#[ignore]
fn s2_the_set_index_equals_the_reference_on_the_pilot_corpus() {
    let mut bad = Vec::new();
    for name in PILOT_NAMES {
        let (spec, imp) = kept_summaries(&fx(name));
        bad.extend(i2_compare(&spec, &imp).into_iter().map(|m| format!("{name}: {m}")));
    }
    note!("s2 pilot: {} fixtures", PILOT_NAMES.len());
    assert!(bad.is_empty(), "conformance: I2-3 on the pilot: {bad:#?}");
}

/// A seeded permutation (Fisher–Yates with a 64-bit LCG).
fn shuffled<T: Clone>(v: &[T], mut seed: u64) -> Vec<T> {
    let mut out = v.to_vec();
    for i in (1..out.len()).rev() {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        out.swap(i, (seed >> 33) as usize % (i + 1));
    }
    out
}

/// s3 (I2-4, rev 1.3): order dependence with a `Noisy` alias pair. The
/// insertions are A3 fifo k2q2's specification summaries plus `PN`'s two
/// (equal `Sig` and counts, different renderings), in one order, its reverse
/// and a seeded shuffle; each inserted in full, then the same queries (A3's
/// implementation summaries, `PN`'s, a forged `NoSig` and a `NoBucket`).
/// Equal across orders: the held identities (by `Sig ==` and counts), the
/// occupancy counters, `sig_aliases` (1), the outcome-class counts and each
/// query's `Covers` discriminant. Between the order and its reverse, the
/// `Noisy` pair's `Stored`/`Duplicate` assignment and the stored
/// representative's rendering swap. The order-dependent quantities are
/// printed.
#[test]
fn s3_order_dependence_with_a_noisy_alias_pair() {
    let (a3_spec, a3_imp) = kept_summaries(&fx("apps/a3/fifo/spec/k2q2"));
    let pn = local_fixture("compact/i2-noisy", pn_prog(), pn_prog(), &["a", "r"]);
    let (pn_spec, pn_imp) = kept_summaries(&pn);
    assert_eq!(pn_spec.len(), 2);
    let render = |s: &CompactSummary| format!("{:?}", s.sig);
    assert!(pn_spec[0].sig == pn_spec[1].sig && render(&pn_spec[0]) != render(&pn_spec[1]));
    let mut seq: Vec<CompactSummary> = vec![pn_spec[0].clone()];
    seq.extend(a3_spec.iter().cloned());
    seq.push(pn_spec[1].clone());
    let mut queries: Vec<CompactSummary> = a3_imp.clone();
    queries.extend(pn_imp.iter().cloned());
    queries.push(forged(&a3_spec[0]));
    queries.push(real_summary("2pc/leader/conf/n2"));
    let orders = [
        ("sequence", seq.clone()),
        ("reverse", seq.iter().rev().cloned().collect()),
        ("shuffle", shuffled(&seq, 17)),
    ];
    let run = |ins: &[CompactSummary]| {
        let mut ix = SetIndex::new();
        let outcomes: Vec<Inserted> = ins.iter().map(|s| ix.insert(s).1).collect();
        let answers: Vec<Covers> = queries.iter().map(|q| ix.covers(q).1).collect();
        (ix, outcomes, answers)
    };
    let disc = |c: &Covers| match c {
        Covers::Found(_) => "Found",
        Covers::NotFound => "NotFound",
        Covers::NoSig => "NoSig",
        Covers::NoBucket => "NoBucket",
    };
    let mut first: Option<(SetStats, Vec<&str>, (usize, usize))> = None;
    let mut bad = Vec::new();
    let mut pn_roles = Vec::new();
    for (what, ins) in &orders {
        let (ix, outcomes, answers) = run(ins);
        let s = ix.stats();
        let classes = (
            outcomes.iter().filter(|o| matches!(o, Inserted::Stored(_))).count(),
            outcomes.iter().filter(|o| matches!(o, Inserted::Duplicate)).count(),
        );
        let d: Vec<&str> = answers.iter().map(disc).collect();
        let inv = SetStats {
            sig_tests: 0,
            containment_tests: 0,
            coordinates_compared: 0,
            ..s
        };
        // Held identities: every held (Sig, counts) of this order is held in
        // the first order's index, by `Sig ==` and counts (checked below via
        // the invariant counters and the per-identity check).
        if let Some((s0, d0, c0)) = &first {
            if inv != *s0 || &d != d0 || classes != *c0 {
                bad.push(format!(
                    "{what}: invariant {inv:?} {classes:?} vs {s0:?} {c0:?}; \
                     discriminants equal {}",
                    &d == d0
                ));
            }
        } else {
            first = Some((inv, d.clone(), classes));
        }
        if s.sig_aliases != 1 {
            bad.push(format!("{what}: sig_aliases {}", s.sig_aliases));
        }
        // The held identities, by `Sig ==` and counts, against the sequence order.
        let held: Vec<(Sig, OrdCounts)> =
            ix.entries().map(|(_, g, e)| (g.clone(), e.ord.clone())).collect();
        for q in &seq {
            if !held.iter().any(|(g, o)| *g == q.sig && *o == q.ord) {
                bad.push(format!("{what}: an inserted identity is not held"));
            }
        }
        // The Noisy pair: which occurrence stored, and the representative.
        let pos0 = ins.iter().position(|x| render(x) == render(&pn_spec[0])).unwrap();
        let pos1 = ins.iter().position(|x| render(x) == render(&pn_spec[1])).unwrap();
        let rep = ix
            .entries()
            .find(|(_, g, _)| **g == pn_spec[0].sig)
            .map(|(_, g, _)| format!("{g:?}"))
            .unwrap();
        pn_roles.push((
            what.to_string(),
            outcomes[pos0],
            outcomes[pos1],
            rep == render(&pn_spec[0]),
        ));
        let seqs: Vec<(u32, u64)> = ix.entries().map(|(id, _, e)| (id, e.seq)).collect();
        note!(
            "s3 {what}: sig_tests {} containment {} coords {} found-seqs {:?} entries[..4] {:?}",
            s.sig_tests,
            s.containment_tests,
            s.coordinates_compared,
            answers
                .iter()
                .filter_map(|c| if let Covers::Found(q) = c { Some(*q) } else { None })
                .take(6)
                .collect::<Vec<_>>(),
            &seqs[..seqs.len().min(4)]
        );
    }
    // Sequence: pn0 first stores, pn1 duplicates, representative pn0's
    // rendering; reverse: the roles and the rendering swap.
    let (s, r) = (&pn_roles[0], &pn_roles[1]);
    if !(matches!(s.1, Inserted::Stored(_)) && s.2 == Inserted::Duplicate && s.3) {
        bad.push(format!("sequence roles {s:?}"));
    }
    if !(r.1 == Inserted::Duplicate && matches!(r.2, Inserted::Stored(_)) && !r.3) {
        bad.push(format!("reverse roles {r:?}"));
    }
    assert!(bad.is_empty(), "conformance: I2-4: {bad:#?}");
}

/// s4 (I2-5): the `Noisy` pair (equal by `PartialEq`, different `Debug`) is one
/// entry and one `Duplicate` through the alias path (`sig_aliases` 1), the
/// query finds it, and every counter equals the reference's.
#[test]
fn s4_equality_is_never_by_rendering() {
    let pn = local_fixture("compact/i2-noisy", pn_prog(), pn_prog(), &["a", "r"]);
    let (spec, imp) = kept_summaries(&pn);
    let bad = i2_compare(&spec, &imp);
    assert!(bad.is_empty(), "conformance: I2-5 against the reference: {bad:#?}");
    let mut ix = SetIndex::new();
    assert_eq!(ix.insert(&spec[0]), (0, Inserted::Stored(0)));
    assert_eq!(ix.insert(&spec[1]), (0, Inserted::Duplicate));
    for q in &spec {
        assert_eq!(ix.covers(q), (Some(0), Covers::Found(0)));
    }
    let s = ix.stats();
    assert_eq!((s.entries, s.duplicates, s.sig_aliases, s.signatures), (1, 1, 1, 1));
}

/// s5 (I2-6): `entries()` yields buckets in ascending `SigHash`, slots in
/// creation order (ids ascending within a bucket), orders in admission order
/// (seqs ascending within a slot); two identical insertion histories give
/// identical iterations.
#[test]
fn s5_the_iteration_order_is_deterministic() {
    let mut ins = Vec::new();
    for name in ["apps/a1/correct/spec/n2r2", "apps/a4/hash/a4a/k2q2m2", "2pc/leader/conf/n2"] {
        ins.extend(kept_summaries(&fx(name)).0);
    }
    let pn = local_fixture("compact/i2-noisy", pn_prog(), pn_prog(), &["a", "r"]);
    ins.extend(kept_summaries(&pn).0);
    let build = || {
        let mut ix = SetIndex::new();
        let mut hash_of = std::collections::HashMap::new();
        for s in &ins {
            let (id, _) = ix.insert(s);
            hash_of.entry(id).or_insert(s.hash);
        }
        (ix, hash_of)
    };
    let (a, hash_of) = build();
    let (b, _) = build();
    let ia: Vec<(u32, u64)> = a.entries().map(|(id, _, e)| (id, e.seq)).collect();
    let ib: Vec<(u32, u64)> = b.entries().map(|(id, _, e)| (id, e.seq)).collect();
    assert_eq!(ia, ib, "conformance: deterministic for one history");
    assert_eq!(ia.len(), a.len());
    for w in ia.windows(2) {
        let (h0, h1) = (hash_of[&w[0].0], hash_of[&w[1].0]);
        assert!(h0 <= h1, "conformance: buckets in ascending SigHash");
        if h0 == h1 {
            assert!(w[0].0 <= w[1].0, "conformance: slots in creation order");
            if w[0].0 == w[1].0 {
                assert!(w[0].1 < w[1].1, "conformance: orders in admission order");
            }
        }
    }
    assert!(hash_of.values().collect::<std::collections::BTreeSet<_>>().len() >= 3);
}

/// s6 (I2-1, I2-5, I2-8, I2-9): source checks on the appended set index:
/// `insert` reaches no `cmp`/`le`; no explicit `Debug` formatting other than
/// through `render_hash`; both ids checked; every panic message prefixed.
#[test]
fn s6_the_set_index_source() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/compact.rs");
    let text = std::fs::read_to_string(path).expect("conformance: compact.rs");
    let start = text.find("// `SVERIFY-P` I2: the set index").expect("conformance: the I2 block");
    let block = &text[start..];
    let ins_from = block.find("pub(crate) fn insert(").unwrap();
    let ins_to = block.find("/// The read-only query (I2-3)").unwrap();
    let insert = &block[ins_from..ins_to];
    for bad in [".cmp(", "le_counted", ".le("] {
        assert!(!insert.contains(bad), "conformance: I2-8: `insert` contains {bad}");
    }
    // No printing macro is listed: `compact.rs` is not test-only, so s5's
    // `c1_no_user_facing_emission_outside_the_rendering_module` scans it,
    // and spelling one out here would trip that scan on this file.
    for bad in ["{:?}", "{sig:?}", "format!(", "write!("] {
        assert!(!block.contains(bad), "conformance: I2-5/s5: the I2 block contains {bad}");
    }
    assert_eq!(block.matches(".checked_add(1)").count(), 2, "conformance: seq and SigId checked");
    for line in block.lines().filter(|l| l.contains(".expect(\"") || l.contains("panic!(\"")) {
        assert!(
            line.contains("\"conformance: "),
            "conformance: a message without the prefix: {line}"
        );
    }
}

/// s7 (I2-10, in-process): one cell (`I2_CELL`) through `oracle_trace_stream`'s
/// two enumerations; the completion sinks build each `CompactSummary` and feed
/// both types — the specification inserted, then the implementation queried —
/// comparing every outcome; at the end the counters. Prints `S7` with the
/// entries and duplicates. The k-th `Stored` insertion must carry seq k, so the
/// seqs are 0 .. entries - 1 in completion order (I2-10).
#[test]
#[ignore]
fn s7_the_set_index_on_one_cell_in_process() {
    use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
    use crate::conformance::stateful::{enumerate, EnumRun};
    let Ok(name) = std::env::var("I2_CELL") else {
        return;
    };
    let f = any_fixture(&name);
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
    type Pair = (SetIndex, CompactIndex, Vec<String>, usize, u64);
    let st: std::rc::Rc<std::cell::RefCell<Pair>> = std::rc::Rc::new(std::cell::RefCell::new((
        SetIndex::new(),
        CompactIndex::with_bucket(false, BucketKind::Scan),
        Vec::new(),
        0,
        0,
    )));
    for side in ["spec", "impl"] {
        let sink: CompletionSink = {
            let (st, vis) = (std::rc::Rc::clone(&st), f.visible.clone());
            Box::new(move |g: &ExecutionGraph, _| {
                let s = CompactSummary::at_completion(g, &vis, side);
                let mut p = st.borrow_mut();
                let (set, rf, bad, n, stored) = &mut *p;
                *n += 1;
                if side == "spec" {
                    let (a, b) = (set.insert(&s), rf.insert(&s));
                    if a != b && bad.len() < 20 {
                        bad.push(format!("insertion {n}: {a:?} vs {b:?}"));
                    }
                    if let Inserted::Stored(q) = a.1 {
                        if q != *stored && bad.len() < 20 {
                            bad.push(format!("insertion {n}: seq {q}, expected {stored}"));
                        }
                        *stored += 1;
                    }
                } else {
                    let (a, b) = (set.covers(&s), rf.covers(&s));
                    if a != b && bad.len() < 20 {
                        bad.push(format!("query {n}: {a:?} vs {b:?}"));
                    }
                }
                SinkVerdict::Continue
            })
        };
        let mut config = cc.config.clone();
        if side == "spec" {
            config.max_iterations = None;
        }
        let program = if side == "spec" { &f.specification } else { &f.implementation };
        enumerate(
            EnumRun {
                config,
                visible: f.visible.clone(),
                mode: ConfMode::Enumerate,
                sink,
                cut: false,
                stop_at_first_report: false,
                gate_sink: None,
            },
            program,
        );
    }
    let p = st.borrow();
    let (set, rf, bad, n, stored) = &*p;
    let (s, r) = (set.stats(), ref_stats(rf));
    note!(
        "S7\t{name}\tentries {}\tduplicates {}\tcompletions {n}\tsig_tests {}\tsig_aliases {}\t\
         containment {}\tcoords {}\tref_insert_tests {}\tstats_equal {}\tmismatches {}",
        s.entries,
        s.duplicates,
        s.sig_tests,
        s.sig_aliases,
        s.containment_tests,
        s.coordinates_compared,
        rf.stats().insert_tests,
        s == r,
        bad.len()
    );
    assert!(bad.is_empty(), "conformance: I2-10 {name}: {bad:#?}");
    assert_eq!(s, r, "conformance: I2-10 {name}: counters");
    assert_eq!(*stored, s.entries as u64, "conformance: I2-10 {name}: seq 0 .. entries");
    assert!(set_held(set) == ref_held(rf), "conformance: I2-10 {name}: held multisets");
}

/// s8 (I2-11, information): the specification summaries of one cell
/// (`I2_TIME_CELL`) collected first, then inserted into each type; the walls.
#[test]
#[ignore]
fn s8_insertion_walls() {
    use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
    use crate::conformance::stateful::{enumerate, EnumRun};
    let Ok(name) = std::env::var("I2_TIME_CELL") else {
        return;
    };
    let f = any_fixture(&name);
    let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
    let got: std::rc::Rc<std::cell::RefCell<Vec<CompactSummary>>> = Default::default();
    let sink: CompletionSink = {
        let (got, vis) = (std::rc::Rc::clone(&got), f.visible.clone());
        Box::new(move |g: &ExecutionGraph, _| {
            got.borrow_mut().push(CompactSummary::at_completion(g, &vis, "spec"));
            SinkVerdict::Continue
        })
    };
    let mut config = cc.config.clone();
    config.max_iterations = None;
    enumerate(
        EnumRun {
            config,
            visible: f.visible.clone(),
            mode: ConfMode::Enumerate,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
        },
        &f.specification,
    );
    let summaries = got.borrow();
    let t0 = std::time::Instant::now();
    let mut set = SetIndex::new();
    for s in summaries.iter() {
        set.insert(s);
    }
    let set_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let t1 = std::time::Instant::now();
    let mut rf = CompactIndex::with_bucket(false, BucketKind::Scan);
    for s in summaries.iter() {
        rf.insert(s);
    }
    let ref_ms = t1.elapsed().as_secs_f64() * 1000.0;
    note!(
        "S8\t{name}\tsummaries {}\tset_ms {set_ms:.1}\tref_ms {ref_ms:.1}\t\
         ref_insert_tests {}\tentries {}",
        summaries.len(),
        rf.stats().insert_tests,
        set.len()
    );
}
