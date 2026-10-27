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
    let counts = OrdCounts::of(g, &w, vis);
    let summary = Summary::of(exec, w, vis).expect("conformance: a summary");
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
                let s = Summary::of(CompleteExecution::try_finished(g).unwrap(), w, &f.visible)
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
        // `MIN-ENGINES` E6: the count is the counter (the list keeps the first).
        c.reports,
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
                    // `MIN-ENGINES` E6: the count is the counter.
                    "cell": name, "row": row, "label": gc.label(), "reports": c.reports,
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
                    // `MIN-ENGINES` E6: the count is the counter.
                    "cell": name, "row": row, "label": gc.label(), "reports": c.reports,
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
        // `MIN-ENGINES` E6: T1 compares the report sequences: every report kept.
        stateful::run_with(&e6_all(cc), &f.implementation, &f.specification, false)
    };
    // `MIN-ENGINES` E7b (the tester, gate 3): `T1_OTHER=set` compares `Current`
    // with the set index (the stateless engine's newly admitted cache).
    let other = if std::env::var("T1_SELF").is_ok() {
        IndexKind::Current
    } else if std::env::var("T1_OTHER").is_ok_and(|v| v == "set") {
        IndexKind::Set
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
            // `MIN-ENGINES` E6: every report kept (the sequences are compared).
            let cc = e6_all(cc);
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
    CompactSummary::of(CompleteExecution::try_finished(g).unwrap(), w, &f.visible).unwrap()
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
        // `MIN-ENGINES` E6: every report kept (the sequences are compared).
        let cc = e6_all(cc);
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
/// only from its own slot. `MIN-ENGINES` E4: the rendering hint (P3) is gone;
/// each resolution scans the bucket's slots in creation order, one `Sig` test
/// per slot up to the hit, and no alias arises.
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
    // `MIN-ENGINES` E4 (the tester's re-pin at gate 3; 4 through the P3 hint
    // before): no hint, the creation-order scan — insert base 0; covers bad 1
    // (slot 0, miss); insert bad 1 (slot 0, miss; new slot 1); covers base 1
    // (slot 0); covers bad 2 (slot 0, then slot 1) = 5; no alias.
    assert_eq!(
        (s.sig_tests, s.sig_aliases),
        (5, 0),
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
            paper_events: false,
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
                CompactSummary::of(CompleteExecution::try_finished(&g).unwrap(), w.clone(), &vis)
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
                    w,
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
                paper_events: false,
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
        // `MIN-ENGINES` E6: every report kept (the lists are compared).
        stateful::run_with(&e6_all(cc), &f.implementation, &f.specification, false)
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
        // `MIN-ENGINES` E4 (the tester's re-pin at gate 3): `sig_tests` 3 → 4,
        // no hint — the second insertion scans slot 0 (1), the query of slot
        // 0's graph costs 1 and of slot 1's 2 (the hint answered it at 1).
        (0, 1, 2, 2, 2, 2, 0, 2, 6, 4, 256),
        "conformance: D1-self, SVerify-S compact (E4: no hint, the plain scan)"
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
        // `MIN-ENGINES` E4 (the tester's re-pin at gate 3): `sig_tests` 4 →
        // 4 + G(1)'s slot, no hint — the second insertion 1, G(1)'s query its
        // slot + 1 (the hint answered it at 1), G(3)'s query both slots (2).
        (1, 1, 2, 2, 2, 1, 3, 4 + g1_slot, 256),
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
    // `MIN-ENGINES` E6: every report kept (m11 compares the sequences).
    let cc = e6_all(cc);
    crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false)
}

fn cfirst_current(f: &Fixture, cap: Capacity) -> crate::conformance::cfirst::CFirstOutcome {
    let cc = GridConfig::new(GridEngine::CompleteFirst)
        .witness_cache(cap)
        .quiet(true)
        .conf_config(f);
    // `MIN-ENGINES` E6: as `cfirst_compact`.
    let cc = e6_all(cc);
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
/// engines and every index kind, and the label unchanged. On:
/// `/distinct=on` closes the label and parses back; the stateful engine
/// counts under every kind and complete-first under `Compact` and `Set`,
/// each equal to step 0 on the cell (A2 pb k2q2: 6). `MIN-ENGINES` E7b gate
/// 4 round 01 M1 (the tester's re-pin): the domain takes `Set`, which
/// complete-first now reads.
#[test]
fn m14_d6_the_distinct_knob() {
    use crate::conformance::config::IndexKind;
    let f = fx(MECH_CELL);
    for k in [IndexKind::Current, IndexKind::Compact, IndexKind::Set] {
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
            let want = (on && k != IndexKind::Current).then_some(6);
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

/// m16 (P3, P2-frozen §7): what was an alias. `PN`'s two graphs have equal
/// `Sig` and different renderings. `MIN-ENGINES` E4 (the tester's re-pin at
/// gate 3): the rendering hint is gone, so there is no second pass and no
/// alias — the second insertion finds slot 0 by `Sig ==` in the plain scan
/// (one test) and is a duplicate, and each query costs one test (slot 0):
/// `sig_tests` 3 as before, `sig_aliases` 1 → 0. Current agrees (one
/// signature, no report).
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
        (0, 3, 0, 1, 1, 1, 1, 1),
        "conformance: no alias (E4: no hint), one test per resolution"
    );
    assert_eq!(
        (cur.reports.len(), cur.counters.signatures),
        (0, 1),
        "conformance: Current agrees"
    );
}

/// m17 (P7, P2-frozen §7): `/distinct=on` prints only where the knob has
/// effect — Stateful under every kind, CompleteFirst under Compact and Set —
/// and every printed label parses back to itself. `MIN-ENGINES` E7b gate 4
/// round 01 M1 (the tester's re-pin): the domain takes `Set`; the enumerator
/// with `index=set` is no key (s15), so there only the suffix is checked.
#[test]
fn m17_p7_the_distinct_suffix_only_where_it_acts() {
    use crate::conformance::config::IndexKind;
    for e in [
        GridEngine::Stateful,
        GridEngine::CompleteFirst,
        GridEngine::Enumerator,
    ] {
        for k in [IndexKind::Current, IndexKind::Compact, IndexKind::Set] {
            for on in [false, true] {
                let g = GridConfig::new(e).index(k).impl_distinct(on);
                let label = g.label();
                let acts = on
                    && (e == GridEngine::Stateful
                        || (e == GridEngine::CompleteFirst && k != IndexKind::Current));
                assert_eq!(
                    label.ends_with("/distinct=on"),
                    acts,
                    "conformance: {e:?} {k:?} {on}: {label}"
                );
                if e == GridEngine::Enumerator && k == IndexKind::Set {
                    assert_eq!(
                        crate::conformance::eval::parse_label(&label),
                        None,
                        "conformance: {label} is no key"
                    );
                    continue;
                }
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
/// `MIN-ENGINES` E7b gate 4 round 01 M1 (the tester's re-pin): `Set` too.
#[test]
fn m21_the_bucket_label_and_the_compact2_spec() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::{
        compact2_ablation_configs, compact2_spec, compact_configs, parse_label, RunKind,
    };
    for e in [GridEngine::Stateful, GridEngine::CompleteFirst] {
        for k in [IndexKind::Current, IndexKind::Compact, IndexKind::Set] {
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
    // `MIN-ENGINES` E6: the multiset is of every report.
    let o = stateful::run_with(&e6_all(cc), &f.implementation, &f.specification, false);
    for (g, _) in &o.reports {
        let w = wobs(g, &f.visible).expect("conformance: wobs");
        let counts = match OrdCounts::of(g, &w, &f.visible) {
            OrdCounts::U8(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
            OrdCounts::U16(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
        };
        let s = Summary::of(CompleteExecution::try_finished(g).unwrap(), w, &f.visible)
            .expect("conformance: a summary");
        note!("UNC\t{:?}\t{}", s.sig, counts.join(","));
    }
    note!("UNCN\t{}", o.reports.len());
}

/// MIN-ENGINES E1 rev 1.3 (the record's nested-spawn fixtures): the existing
/// corpus programs, reached through test-only `pub(super)` —
/// `stateful_tests::nested4` (the corpus pair `nested4/self`: `p1` spawns `x`,
/// `p2` spawns `y`; visible `p1`, `p2`) and `selector_tests`' adversarial pairs
/// on `Bag` (`nested_race`: `p1` spawns `x`, `p2` spawns `y`, which may spawn
/// `z` behind a toss; `deep_chain`: `a` → `b` → `c`; visible `r`) — named
/// `e1:…`, on `Bag` as their corpora run them.
/// The record's fixture by name: the four `e1:` nested pairs, else the
/// catalogue's.
fn e1_fixture(name: &str) -> Fixture {
    match name {
        "e1:nested4/self" => {
            let p = crate::conformance::stateful_tests::nested4;
            local_fixture(name, p(), p(), &["p1", "p2"])
        }
        "e1:race/bag" | "e1:race-bad/bag" => {
            let race = crate::conformance::selector_tests::nested_race;
            local_fixture(name, race(false), race(name == "e1:race-bad/bag"), &["r"])
        }
        "e1:chain/bag" => {
            let deep = crate::conformance::selector_tests::deep_chain;
            let chain = || crate::conformance::grid::prog(deep);
            local_fixture(name, chain(), chain(), &["r"])
        }
        _ => any_fixture(name),
    }
}

/// MIN-ENGINES E1, the before/after record (the tester; derived §E1). One
/// fixture per process: `E1_FIXTURE`; `E1_SELECTOR` `Ltr` (default),
/// `Reverse` or `FewestEvents`; `E1_PARTS` (default `stateful,stateless,enum`).
/// - `stateful`: SVerify-S at X1 (`x1_config`), each report's summary printed
///   as `UNC\t<Sig Debug>\t<counts>` (the I1 record's format), then `E1S`;
/// - `stateless`: complete-first at X1, the same per report as `UNCS`, then
///   `E1C`;
/// - `enum`: both programs enumerated (`stateful::enumerate`, the stateful
///   engine's mode), one `E1E` line per side: completions, distinct, a digest
///   of the multiset (sorted lines `mult\tsig\tcounts`) and of the completion
///   order (the sequence of `sig\tcounts`), the longest origination vector,
///   and whether a visible value's rendering names a `ThreadId`; then, per
///   side, an `E4C` line (`MIN-ENGINES` E4-6 (c), outside the record's `E1`
///   lines): completions sharing a rendering are compared by `Sig ==`, and
///   equal signatures must have equal `Sig::hash128` (asserted).
/// `MIN-ENGINES` E7a: the engine parts above pin the before-state ([`e7_before`]:
/// the index they ran, the memo on, the sweep record on, every report kept);
/// the stateless part prints the E7 record of its `Current` run, and two more
/// parts print theirs: `e7c` (`Compact`, the sweep record on, the memo at its
/// new default, off) and `e7d` (`Compact` at E7a's defaults, through the grid,
/// with an `E7R` line of its row's knob columns) — all outside the `E1` filter.
/// `MIN-ENGINES` E7b: and `e7s`, the stateless engine at its new default
/// (`Set`), the sweep record on, its E7 record outside the filter.
/// `MIN-ENGINES` E9 (E9-5 (ii)): `e9s` (the stateful engine at x1's
/// configuration under `Current` and under its default `Set`) and `e9c` (the
/// stateless engine at x1's), one `E9` line per run outside the filter: the
/// report count, whether both first-report fields are `Some`, and whether the
/// bounds hold (`W` within the run's own wall, `H` between the run's
/// `VmHWM` before and after) — never a value.
/// `MIN-ENGINES` E6: every engine part above keeps every report (`all_reports`
/// on, today's lists); two more parts run the default (off): `e6s` (stateful
/// under `Set`) and `e6c` (stateless), each an `E6T`/`E6C` line outside the
/// `E1` filter — the verdict, the count, the kept length and the first kept
/// entry's `UNC` text, compared offline with `E1T`/`UNCSET` and `E1C`/`UNCS`.
/// Digests are std's `DefaultHasher` (fixed keys): comparable across runs of
/// one toolchain, not across toolchains.
#[test]
#[ignore]
fn e1_record() {
    use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
    use crate::conformance::selector::Selector;
    use crate::conformance::stateful::{enumerate, EnumRun};
    use std::hash::{Hash, Hasher};
    let Ok(name) = std::env::var("E1_FIXTURE") else {
        return;
    };
    let sel = match std::env::var("E1_SELECTOR").as_deref() {
        Ok("Reverse") => Selector::Reverse,
        Ok("FewestEvents") => Selector::FewestEvents,
        _ => Selector::Ltr,
    };
    let parts = std::env::var("E1_PARTS").unwrap_or_else(|_| "stateful,stateless,enum".to_owned());
    let f = e1_fixture(&name);
    let line_of = |g: &ExecutionGraph| -> String {
        let w = wobs(g, &f.visible).expect("conformance: wobs");
        let counts = match OrdCounts::of(g, &w, &f.visible) {
            OrdCounts::U8(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
            OrdCounts::U16(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
        };
        let s = Summary::of(CompleteExecution::try_finished(g).unwrap(), w, &f.visible)
            .expect("conformance: a summary");
        format!("{:?}\t{}", s.sig, counts.join(","))
    };
    let digest = |lines: &[String]| -> String {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        for l in lines {
            l.hash(&mut h);
        }
        format!("{:016x}", h.finish())
    };
    if parts.contains("stateful") {
        let cc = crate::conformance::eval::x1_config(GridEngine::Stateful, sel).conf_config(&f);
        // `MIN-ENGINES` E6/E7a: the before-state, every report kept.
        let cc = e7_before(cc, crate::conformance::config::IndexKind::Current);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
        for (g, _) in &o.reports {
            note!("UNC\t{}", line_of(g));
        }
        let c = &o.counters;
        note!(
            "E1S\t{name}\t{sel:?}\treports {}\tspec_graphs {}\timpl_graphs {}\torders_held {}\t\
             lookups {}/{}/{}\tspec_errors {}",
            o.reports.len(),
            c.spec_graphs,
            c.impl_graphs,
            c.orders_held,
            c.lookups_succeeded,
            c.lookups_failed_after_tests,
            c.lookups_signature_miss,
            o.spec_errors.len()
        );
    }
    if parts.contains("stateless") {
        let cc =
            crate::conformance::eval::x1_config(GridEngine::CompleteFirst, sel).conf_config(&f);
        let cc = e7_before(cc, crate::conformance::config::IndexKind::Current);
        let o =
            crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false);
        for (g, _) in &o.reports {
            note!("UNCS\t{}", line_of(g));
        }
        let c = &o.counters;
        let sizes: Vec<String> = c.sweep_sizes.iter().map(|n| n.to_string()).collect();
        note!(
            "E1C\t{name}\t{sel:?}\treports {}\texecutions {}\tspec_errors {}\tsweeps {}\t\
             sweep_sizes {} sum {} digest {}\tcache_hits {}\tadmissions {}\tevictions {}\t\
             witnesses {}",
            o.reports.len(),
            o.executions,
            o.spec_errors.len(),
            c.sweeps,
            sizes.len(),
            c.sweep_sizes.iter().sum::<usize>(),
            digest(&sizes),
            c.cache_hits,
            c.admissions,
            c.evictions,
            c.witnesses
        );
        note!("E7\t{name}\t{sel:?}\tcurrent\t{}", e7_record(&o, &line_of));
    }
    // Rev 1.1 E1-4 (the record's missing fields), three further parts:
    // `stateful_set` — SVerify-S at X1 on `Set`: verdict, `UNCSET` lines,
    //   graphs per side (the order digests are the `enum` part's: the same
    //   mode and configuration explore identically);
    // `stateless_keep` — the stateless engine at X1 with `keep_graphs`: the
    //   outer completion order's digest, the sweep count, and per sweep its
    //   size and order digest (`SW` lines) — run on the light fixtures only;
    // `plain` — plain Must per side (the fixture's `Config` with
    //   `keep_going_after_error`): `execs` and `block`.
    if parts.contains("stateful_set") {
        let cc = crate::conformance::eval::x1_config(GridEngine::Stateful, sel)
            .index(crate::conformance::config::IndexKind::Set)
            .conf_config(&f);
        let cc = e7_before(cc, crate::conformance::config::IndexKind::Set);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
        for (g, _) in &o.reports {
            note!("UNCSET\t{}", line_of(g));
        }
        let c = &o.counters;
        note!(
            "E1T\t{name}\t{sel:?}\tverdict {}\treports {}\tspec_graphs {}\timpl_graphs {}",
            if o.reports.is_empty() { "conforms" } else { "reported" },
            o.reports.len(),
            c.spec_graphs,
            c.impl_graphs
        );
    }
    if parts.contains("stateless_keep") {
        let cc =
            crate::conformance::eval::x1_config(GridEngine::CompleteFirst, sel).conf_config(&f);
        let cc = e7_before(cc, crate::conformance::config::IndexKind::Current);
        let o =
            crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, true);
        let outer: Vec<String> = o.kept_impl_graphs.iter().map(|g| line_of(g)).collect();
        let mut sweeps: Vec<String> = Vec::new();
        for (i, sw) in o.kept_spec_graphs.iter().enumerate() {
            let lines: Vec<String> = sw.iter().map(|g| line_of(g)).collect();
            let size = o.counters.sweep_sizes.get(i).copied().unwrap_or(usize::MAX);
            let d = digest(&lines);
            note!("SW\t{i}\tkept {}\tsize {size}\torder {d}", lines.len());
            sweeps.push(format!("{}\t{size}\t{d}", lines.len()));
        }
        note!(
            "E1K\t{name}\t{sel:?}\tverdict {}\treports {}\texecutions {}\touter {}\t\
             outer_order {}\tsweeps {}\tkept_sweeps {}\tsweep_digest {}",
            if o.reports.is_empty() { "conforms" } else { "reported" },
            o.reports.len(),
            o.executions,
            outer.len(),
            digest(&outer),
            o.counters.sweeps,
            o.kept_spec_graphs.len(),
            digest(&sweeps)
        );
        note!(
            "E1KC\t{name}\t{sel:?}\tcache_hits {}\tadmissions {}\tevictions {}\twitnesses {}",
            o.counters.cache_hits,
            o.counters.admissions,
            o.counters.evictions,
            o.counters.witnesses
        );
    }
    if parts.contains("e6s") {
        let cc = crate::conformance::eval::x1_config(GridEngine::Stateful, sel)
            .index(crate::conformance::config::IndexKind::Set)
            .conf_config(&f);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
        note!(
            "E6T\t{name}\t{sel:?}\tverdict {}\tcount {}\tkept {}\tfirst {}",
            if o.reports.is_empty() { "conforms" } else { "reported" },
            o.counters.reports,
            o.reports.len(),
            o.reports.first().map_or_else(|| "-".to_owned(), |(g, _)| line_of(g))
        );
    }
    if parts.contains("e6c") {
        let cc =
            crate::conformance::eval::x1_config(GridEngine::CompleteFirst, sel).conf_config(&f);
        let o =
            crate::conformance::cfirst::run_with(&cc, &f.implementation, &f.specification, false);
        note!(
            "E6C\t{name}\t{sel:?}\tverdict {}\tcount {}\tkept {}\tfirst {}",
            if o.reports.is_empty() { "conforms" } else { "reported" },
            o.counters.reports,
            o.reports.len(),
            o.reports.first().map_or_else(|| "-".to_owned(), |(g, _)| line_of(g))
        );
    }
    if parts.contains("e7c") || parts.contains("e7d") {
        use crate::conformance::grid::{row_of, GridEnd, GridRaw};
        let compact = crate::conformance::eval::x1_config(GridEngine::CompleteFirst, sel)
            .index(crate::conformance::config::IndexKind::Compact);
        for (part, record) in [("e7c", true), ("e7d", false)] {
            if !parts.contains(part) {
                continue;
            }
            // `e7c`: the sweep record on; `e7d`: E7a's defaults. Both keep every
            // report (E6's knob) so the uncovered multiset is comparable.
            let mut g = compact.clone();
            g.sweep_record = record;
            g.all_reports = true;
            // The runner's own path with `keep_graphs` off (`run_grid` keeps
            // every graph: gigabytes on the heavy fixtures, gate 3's probe).
            let r = match crate::conformance::eval::run_row_in_process(&f, &g, false) {
                GridEnd::Ok(r) => r,
                other => panic!("conformance: {name} {part}: {other:?}"),
            };
            let row = row_of(&r);
            let GridRaw::CompleteFirst(o) = &r.raw else {
                panic!("conformance: {name} {part}: not a complete-first outcome")
            };
            note!("E7\t{name}\t{sel:?}\t{part}\t{}", e7_record(o, &line_of));
            let col = |k: &str| {
                row.iter()
                    .find(|(c, _)| *c == k)
                    .map_or_else(|| "-".to_owned(), |(_, v)| v.clone())
            };
            note!(
                "E7R\t{name}\t{sel:?}\t{part}\tsweep_sizes {}\tsweep_ends {}\tmemo_on {}\t\
                 memo_hits {}\tmemo_entries {}\tmemo_clears {}",
                col("sweep_sizes"),
                col("sweep_ends"),
                col("memo_on"),
                col("memo_hits"),
                col("memo_entries"),
                col("memo_clears")
            );
        }
    }
    // `MIN-ENGINES` E7b (the tester, gate 3): `e7s` — the stateless engine at
    // its new default (`Set`), the sweep record on and every report kept; its
    // E7 record is compared with the `Current` part's, field for field.
    if parts.contains("e7s") {
        use crate::conformance::grid::{GridEnd, GridRaw};
        let mut g = crate::conformance::eval::x1_config(GridEngine::CompleteFirst, sel);
        assert_eq!(g.index, crate::conformance::config::IndexKind::Set, "conformance: the default");
        g.sweep_record = true;
        g.all_reports = true;
        let r = match crate::conformance::eval::run_row_in_process(&f, &g, false) {
            GridEnd::Ok(r) => r,
            other => panic!("conformance: {name} e7s: {other:?}"),
        };
        let GridRaw::CompleteFirst(o) = &r.raw else {
            panic!("conformance: {name} e7s: not a complete-first outcome")
        };
        note!("E7\t{name}\t{sel:?}\te7s\t{}", e7_record(o, &line_of));
    }
    // `MIN-ENGINES` E9 (the tester, gate 3; E9-5 (ii)): the first-report
    // columns' presence and bounds, never a value.
    for (part, engine) in [("e9s", GridEngine::Stateful), ("e9c", GridEngine::CompleteFirst)] {
        use crate::conformance::config::IndexKind;
        use crate::conformance::grid::{GridEnd, GridRaw};
        if !parts.contains(part) {
            continue;
        }
        let kinds: &[IndexKind] = if engine == GridEngine::Stateful {
            &[IndexKind::Current, IndexKind::Set]
        } else {
            &[IndexKind::Set]
        };
        for &k in kinds {
            let g = crate::conformance::eval::x1_config(engine, sel).index(k);
            let r = match crate::conformance::eval::run_row_in_process(&f, &g, false) {
                GridEnd::Ok(r) => r,
                other => panic!("conformance: {name} {part}: {other:?}"),
            };
            let (n, wall, kb, end) = match &r.raw {
                GridRaw::Stateful(o) => {
                    let c = &o.counters;
                    let fr = (c.wall_ms_at_first_report, c.vmhwm_kb_at_first_report);
                    (c.reports, fr.0, fr.1, c.impl_wall_time_ms)
                }
                GridRaw::CompleteFirst(o) => {
                    let c = &o.counters;
                    let fr = (c.wall_ms_at_first_report, c.vmhwm_kb_at_first_report);
                    (c.reports, fr.0, fr.1, c.outer_wall_time_ms)
                }
                _ => panic!("conformance: {name} {part}: an unexpected outcome"),
            };
            let first = match (wall, kb) {
                (Some(_), Some(_)) => "some",
                (None, None) => "none",
                _ => "mixed",
            };
            let bounds = match (wall, kb, r.vm_hwm_kb) {
                (Some(w), Some(h), (Some(b), Some(a))) => w <= end && b <= h && h <= a,
                (None, None, _) => true,
                _ => false,
            };
            note!(
                "E9\t{name}\t{sel:?}\t{part}\t{k:?}\treports {n}\tfirst {first}\tbounds {}",
                if bounds { "ok" } else { "BAD" }
            );
        }
    }
    if parts.contains("plain") {
        let sides = [("specification", &f.specification), ("implementation", &f.implementation)];
        for (side, program) in sides {
            let mut cfg = f.config.clone();
            cfg.keep_going_after_error = true;
            let p = program.clone();
            let s = crate::verify(cfg, move || p());
            note!("E1P\t{name}\t{side}\texecs {}\tblock {}", s.execs, s.block);
        }
    }
    if parts.contains("enum") {
        let cc = crate::conformance::eval::x1_config(GridEngine::Stateful, sel).conf_config(&f);
        let sides = [("specification", &f.specification), ("implementation", &f.implementation)];
        for (side, program) in sides {
            type Acc = (Vec<String>, usize, bool);
            let acc: std::rc::Rc<std::cell::RefCell<Acc>> = Default::default();
            // `MIN-ENGINES` E4-6 (c): per rendering, its signatures and their
            // hashes; equal-`Sig` pairs compared; pairs whose hashes differ.
            type E4c = (std::collections::HashMap<String, Vec<(Sig, u128)>>, usize, usize);
            let e4c: std::rc::Rc<std::cell::RefCell<E4c>> = Default::default();
            let sink: CompletionSink = {
                let (acc, vis) = (std::rc::Rc::clone(&acc), f.visible.clone());
                let e4c = std::rc::Rc::clone(&e4c);
                Box::new(move |g: &ExecutionGraph, _| {
                    let w = wobs(g, &vis).expect("conformance: wobs");
                    let counts = match OrdCounts::of(g, &w, &vis) {
                        OrdCounts::U8(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
                        OrdCounts::U16(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
                    };
                    let s = Summary::of(CompleteExecution::try_finished(g).unwrap(), w, &vis)
                        .expect("conformance: a summary");
                    let r = format!("{:?}", s.sig);
                    let mut a = acc.borrow_mut();
                    a.0.push(format!("{r}\t{}", counts.join(",")));
                    let depth = g
                        .thread_ids()
                        .into_iter()
                        .map(|t| g.get_thread_tclab(t).origination_vec().len())
                        .max()
                        .unwrap_or(0);
                    a.1 = a.1.max(depth);
                    if !a.2 {
                        // `MIN-ENGINES` E4: the row's observations moved into the
                        // signature's word, read there.
                        a.2 = vis.iter().any(|n| {
                            s.sig.word(n).iter().any(|o| format!("{o:?}").contains("ThreadId"))
                        });
                    }
                    let h = s.sig.hash128();
                    let mut e = e4c.borrow_mut();
                    let (groups, compared, differ) = &mut *e;
                    let group = groups.entry(r).or_default();
                    match group.iter().find(|(g, _)| *g == s.sig) {
                        Some((_, h0)) => {
                            *compared += 1;
                            *differ += usize::from(*h0 != h);
                        }
                        None => group.push((s.sig, h)),
                    }
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
                    paper_events: false,
                },
                program,
            );
            let (order, depth, tid) = std::mem::take(&mut *acc.borrow_mut());
            let mut counts: std::collections::BTreeMap<&String, usize> = Default::default();
            for l in &order {
                *counts.entry(l).or_default() += 1;
            }
            let ms: Vec<String> = counts.iter().map(|(l, m)| format!("{m}\t{l}")).collect();
            note!(
                "E1E\t{name}\t{sel:?}\t{side}\tcompletions {}\tdistinct {}\tms {}\torder {}\t\
                 depth {depth}\tthreadid {tid}",
                order.len(),
                ms.len(),
                digest(&ms),
                digest(&order)
            );
            let (groups, compared, differ) = std::mem::take(&mut *e4c.borrow_mut());
            let sigs: usize = groups.values().map(Vec::len).sum();
            note!(
                "E4C\t{name}\t{sel:?}\t{side}\trenderings {}\tsignatures {sigs}\t\
                 equal_sig_pairs {compared}\thash_differs {differ}",
                groups.len()
            );
            assert_eq!(
                differ, 0,
                "conformance: E4-6 (c): equal signatures with different hash128 ({side})"
            );
        }
    }
}

// =========================================================================
// SVERIFY-P I2 (tester, gate 3; criteria/SVERIFY-P-I2.md rev 1.3): the set
// index against `CompactIndex::with_bucket(false, Scan)`
// =========================================================================

use crate::conformance::compact::{SetIndex, SetStats};

/// The reference's counters as `SetStats` (`slot_max` is `bucket_max`;
/// `insert_tests` has no counterpart, I2-7; `exact_hits` 0, the reference
/// has no probe, I2b-6).
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
        exact_hits: 0,
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
        .map(|(id, _, seq, ord)| (id, seq, ord.clone()))
        .collect();
    v.sort_by_key(|x| (x.0, x.1));
    v
}

/// The exact-hit oracle (I2b-3; derived §I2b item 3): the reference's own
/// held list as `sig_id → (counts → seq)`, read from `CompactIndex`'s slots,
/// so that a hit is decided without the set's map.
type Oracle = std::collections::HashMap<u32, std::collections::HashMap<OrdCounts, u64>>;

fn exact_oracle(rf: &CompactIndex) -> Oracle {
    let mut m: Oracle = std::collections::HashMap::new();
    for (id, seq, ord) in ref_held(rf) {
        m.entry(id).or_default().insert(ord, seq);
    }
    m
}

/// One comparison's totals: the queries, the exact hits, the hits whose
/// reference witness is an earlier order (`seq_r < seq_s`), and the
/// reference's containment tests and coordinates on the hit queries.
#[derive(Clone, Copy, Debug, Default)]
struct I2bTally {
    queries: usize,
    hits: usize,
    witness_differs: usize,
    hit_ref_tests: usize,
    hit_ref_coords: usize,
}

/// One query through both indexes (I2b-3), from per-query snapshots of both
/// records: the `Option<SigId>` and the class equal, `sig_tests` and
/// `sig_aliases` moving equally. On an exact hit (the oracle) the set answers
/// the held order's own seq with `seq_r ≤ seq_s`, its two scan counters do
/// not move, `exact_hits` gains one, and the reference tests at least once;
/// otherwise the answers (seq included) and the deltas are equal and
/// `exact_hits` does not move. At most twenty mismatches are kept.
fn i2b_query(
    set: &SetIndex,
    rf: &mut CompactIndex,
    oracle: &Oracle,
    q: &CompactSummary,
    t: &mut I2bTally,
    bad: &mut Vec<String>,
) {
    let (s0, r0) = (set.stats(), rf.stats().clone());
    let (a, b) = (set.covers(q), rf.covers(q));
    let (s1, r1) = (set.stats(), rf.stats().clone());
    let n = t.queries;
    t.queries += 1;
    let mut push = |m: String| {
        if bad.len() < 20 {
            bad.push(m);
        }
    };
    let ds = (
        s1.containment_tests - s0.containment_tests,
        s1.coordinates_compared - s0.coordinates_compared,
        s1.exact_hits - s0.exact_hits,
    );
    let dr = (
        r1.containment_tests - r0.containment_tests,
        r1.coordinates_compared - r0.coordinates_compared,
    );
    if (s1.sig_tests - s0.sig_tests, s1.sig_aliases - s0.sig_aliases)
        != (r1.sig_tests - r0.sig_tests, r1.sig_aliases - r0.sig_aliases)
    {
        push(format!("query {n}: sig_tests or sig_aliases moved differently"));
    }
    if a.0 != b.0 || std::mem::discriminant(&a.1) != std::mem::discriminant(&b.1) {
        push(format!("query {n}: set {a:?} reference {b:?}"));
        return;
    }
    let exact = b.0.and_then(|id| oracle.get(&id)).and_then(|m| m.get(&q.ord)).copied();
    match exact {
        Some(seq_s) => {
            t.hits += 1;
            t.hit_ref_tests += dr.0;
            t.hit_ref_coords += dr.1;
            let seq_r = match b.1 {
                Covers::Found(r) => r,
                _ => u64::MAX,
            };
            if seq_r < seq_s {
                t.witness_differs += 1;
            }
            if a.1 != Covers::Found(seq_s) || ds != (0, 0, 1) || dr.0 == 0 || seq_r > seq_s {
                push(format!(
                    "query {n}, exact hit {seq_s}: set {a:?} {ds:?} reference {b:?} {dr:?}"
                ));
            }
        }
        None => {
            if a != b || ds != (dr.0, dr.1, 0) {
                push(format!("query {n}: set {a:?} {ds:?} reference {b:?} {dr:?}"));
            }
        }
    }
}

/// The end of one comparison (I2b-3, I2b-6): `exact_hits` is the oracle's
/// count; the two identities hold (the set's scan counters plus the
/// reference's work on the hit queries are the reference's), that work being
/// at least one test per hit; every other `SetStats` field is the
/// reference's; the held multisets are equal; `as_compact_stats` is the
/// reference's record with `insert_tests` 0 and the set's two scan counters.
fn i2b_end(set: &SetIndex, rf: &CompactIndex, t: &I2bTally, bad: &mut Vec<String>) {
    let (s, r) = (set.stats(), ref_stats(rf));
    if s.exact_hits != t.hits {
        bad.push(format!("exact_hits {} against the oracle's {}", s.exact_hits, t.hits));
    }
    if s.containment_tests + t.hit_ref_tests != r.containment_tests
        || s.coordinates_compared + t.hit_ref_coords != r.coordinates_compared
        || t.hit_ref_tests < t.hits
    {
        bad.push(format!("the identities: set {s:?} reference {r:?} {t:?}"));
    }
    let rest = SetStats {
        containment_tests: r.containment_tests,
        coordinates_compared: r.coordinates_compared,
        exact_hits: 0,
        ..s
    };
    if rest != r {
        bad.push(format!("the other fields: set {s:?} reference {r:?}"));
    }
    let mut want = rf.stats().clone();
    want.insert_tests = 0;
    want.containment_tests = s.containment_tests;
    want.coordinates_compared = s.coordinates_compared;
    if s.as_compact_stats() != want {
        bad.push(format!("as_compact_stats {:?} against {want:?}", s.as_compact_stats()));
    }
    if set_held(set) != ref_held(rf) {
        bad.push("held multisets differ".to_owned());
    }
}

/// I2b-3 on one explicit sequence: per insertion the same `(SigId,
/// Inserted)`; the scan counters and `exact_hits` 0 after the insertions
/// (I2-8); every query through `&self` by [`i2b_query`]; the representatives
/// equal; [`i2b_end`]. Returns the mismatches and the totals.
fn i2_compare(spec: &[CompactSummary], imp: &[CompactSummary]) -> (Vec<String>, I2bTally) {
    let mut bad = Vec::new();
    let (mut set, mut rf) = (SetIndex::new(), CompactIndex::with_bucket(false, BucketKind::Scan));
    for (i, s) in spec.iter().enumerate() {
        let (a, b) = (set.insert(s), rf.insert(s));
        if a != b {
            bad.push(format!("insertion {i}: set {a:?} reference {b:?}"));
        }
    }
    let st = set.stats();
    if (st.containment_tests, st.coordinates_compared, st.exact_hits) != (0, 0, 0) {
        bad.push(format!("I2-8: an insertion-only sequence counted {st:?}"));
    }
    let oracle = exact_oracle(&rf);
    let mut t = I2bTally::default();
    let shared: &SetIndex = &set;
    for g in imp.iter().chain(spec.iter()) {
        i2b_query(shared, &mut rf, &oracle, g, &mut t, &mut bad);
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
    for (id, sig, _, _) in set.entries() {
        if reps.get(&id).is_none_or(|r| *r != sig) {
            bad.push(format!("the representative of sig_id {id} differs"));
        }
    }
    i2b_end(&set, &rf, &t, &mut bad);
    (bad, t)
}

/// s1 (I2-3): `SetIndex` is `Send` (I3 moves per-task sets into the merge).
#[test]
fn s1_the_set_index_is_send() {
    fn assert_send<T: Send>() {}
    assert_send::<SetIndex>();
}

/// s2 (I2-3, I2-8; I2b-3): the set against the reference on the five size-2
/// cells (specification inserted in completion order; implementation and
/// specification summaries queried, the latter all exact hits).
#[test]
fn s2_the_set_index_equals_the_reference_on_the_size2_cells() {
    let mut bad = Vec::new();
    for name in SIZE2_CELLS {
        let (spec, imp) = kept_summaries(&fx(name));
        let (b, t) = i2_compare(&spec, &imp);
        note!("s2 {name}: {t:?}");
        bad.extend(b.into_iter().map(|m| format!("{name}: {m}")));
    }
    assert!(bad.is_empty(), "conformance: I2b-3: {bad:#?}");
}

/// s2 on the pilot corpus (I2-10's in-process part), one process.
#[test]
#[ignore]
fn s2_the_set_index_equals_the_reference_on_the_pilot_corpus() {
    let mut bad = Vec::new();
    let mut all = I2bTally::default();
    for name in PILOT_NAMES {
        let (spec, imp) = kept_summaries(&fx(name));
        let (b, t) = i2_compare(&spec, &imp);
        all.queries += t.queries;
        all.hits += t.hits;
        all.witness_differs += t.witness_differs;
        all.hit_ref_tests += t.hit_ref_tests;
        all.hit_ref_coords += t.hit_ref_coords;
        bad.extend(b.into_iter().map(|m| format!("{name}: {m}")));
    }
    note!("s2 pilot: {} fixtures {all:?}", PILOT_NAMES.len());
    assert!(bad.is_empty(), "conformance: I2b-3 on the pilot: {bad:#?}");
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
/// occupancy counters, `sig_aliases` (0 since `MIN-ENGINES` E4, which removed
/// the rendering hint; 1 before), the outcome-class counts and each
/// query's `Covers` discriminant. Between the order and its reverse, the
/// `Noisy` pair's `Stored`/`Duplicate` assignment and the stored
/// representative's rendering swap. The order-dependent quantities are
/// printed. I2b-4: `exact_hits` is in the invariant record (equal across the
/// three orders) and is not 0.
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
        // `MIN-ENGINES` E4 (the tester's re-pin at gate 3): no hint, no alias
        // (1 under `print_vals` before).
        if s.sig_aliases != 0 {
            bad.push(format!("{what}: sig_aliases {}", s.sig_aliases));
        }
        if s.exact_hits == 0 {
            bad.push(format!("{what}: no exact hit"));
        }
        // The held identities, by `Sig ==` and counts, against the sequence order.
        let held: Vec<(Sig, OrdCounts)> =
            ix.entries().map(|(_, g, _, o)| (g.clone(), o.clone())).collect();
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
            .find(|(_, g, _, _)| **g == pn_spec[0].sig)
            .map(|(_, g, _, _)| format!("{g:?}"))
            .unwrap();
        pn_roles.push((
            what.to_string(),
            outcomes[pos0],
            outcomes[pos1],
            rep == render(&pn_spec[0]),
        ));
        let seqs: Vec<(u32, u64)> = ix.entries().map(|(id, _, seq, _)| (id, seq)).collect();
        note!(
            "s3 {what}: exact_hits {} sig_tests {} containment {} coords {} found-seqs {:?} \
             entries[..4] {:?}",
            s.exact_hits,
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
/// entry and one `Duplicate` — by the plain scan since `MIN-ENGINES` E4
/// (`sig_aliases` 0; through the alias path before, 1) — the query finds it,
/// and every counter equals the reference's.
#[test]
fn s4_equality_is_never_by_rendering() {
    let pn = local_fixture("compact/i2-noisy", pn_prog(), pn_prog(), &["a", "r"]);
    let (spec, imp) = kept_summaries(&pn);
    let (bad, _) = i2_compare(&spec, &imp);
    assert!(bad.is_empty(), "conformance: I2-5 against the reference: {bad:#?}");
    let mut ix = SetIndex::new();
    assert_eq!(ix.insert(&spec[0]), (0, Inserted::Stored(0)));
    assert_eq!(ix.insert(&spec[1]), (0, Inserted::Duplicate));
    for q in &spec {
        assert_eq!(ix.covers(q), (Some(0), Covers::Found(0)));
    }
    let s = ix.stats();
    // `MIN-ENGINES` E4 (the tester's re-pin at gate 3): `sig_aliases` 1 → 0.
    assert_eq!((s.entries, s.duplicates, s.sig_aliases, s.signatures), (1, 1, 0, 1));
    // I2b-3: both queries are exact hits, answered by the probe alone.
    assert_eq!((s.exact_hits, s.containment_tests, s.coordinates_compared), (2, 0, 0));
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
    // I2b-5: the item type, `(SigId, &Sig, u64, &OrdCounts)`.
    let first: Option<(u32, &Sig, u64, &OrdCounts)> = a.entries().next();
    assert!(first.is_some());
    let ia: Vec<(u32, u64)> = a.entries().map(|(id, _, seq, _)| (id, seq)).collect();
    let ib: Vec<(u32, u64)> = b.entries().map(|(id, _, seq, _)| (id, seq)).collect();
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

/// s6 (I2-1, I2-5, I2-8, I2-9; I2b-1–3): source checks on the set index's
/// code (comment lines dropped): one `IndexMap<OrdCounts, u64>` per slot and
/// no second copy (no `HashSet<OrdCounts>`, no `Vec<Entry>`, no `held:`);
/// nothing ever removed from a map (the scan and `entries()` rely on its
/// insertion order); `insert` decides by `contains_key`, stores one clone and
/// reaches no `cmp`/`le`; `covers` probes before the scan and advances
/// `exact_hits` at one site; no explicit `Debug` formatting other than
/// through `render_hash`; both ids checked; every panic message prefixed.
#[test]
fn s6_the_set_index_source() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance/compact.rs");
    let text = std::fs::read_to_string(path).expect("conformance: compact.rs");
    let start = text.find("// `SVERIFY-P` I2: the set index").expect("conformance: the I2 block");
    let block = &text[start..];
    let code: Vec<&str> = block.lines().filter(|l| !l.trim_start().starts_with("//")).collect();
    let code = code.join("\n");
    assert!(
        code.contains("    orders: indexmap::IndexMap<OrdCounts, u64>,"),
        "conformance: I2b-1: one map per slot"
    );
    // `MIN-ENGINES` E7b (the tester's re-pin at gate 3): `remove(` is gone from
    // the list — the stateless cache's eviction removes through
    // `SetIndex::remove`, by `shift_remove`, which keeps the scan's order.
    for gone in ["HashSet<OrdCounts>", "Vec<Entry>", "held:"] {
        assert!(!code.contains(gone), "conformance: I2b-1: the set index's code has {gone}");
    }
    assert!(
        code.contains(".shift_remove_index(") && !code.contains("swap_remove"),
        "conformance: E7b-1: the order kept"
    );
    let at = |s: &str| code.find(s).unwrap_or_else(|| panic!("conformance: no {s}"));
    let insert = &code[at("pub(crate) fn insert(")..at("pub(crate) fn covers(")];
    for bad in [".cmp(", "le_counted", ".le("] {
        assert!(!insert.contains(bad), "conformance: I2-8: `insert` contains {bad}");
    }
    assert!(
        insert.contains("slot.orders.contains_key(&s.ord)")
            && insert.contains("slot.orders.insert(s.ord.clone(), seq)"),
        "conformance: I2b-2: the duplicate check and the one stored copy"
    );
    let covers = &code[at("pub(crate) fn covers(")..at("pub(crate) fn entries(")];
    let probe = covers.find("slot.orders.get(&s.ord)").expect("conformance: I2b-3: the probe");
    let scan = covers.find("le_counted").expect("conformance: I2b-3: the scan");
    assert!(probe < scan, "conformance: I2b-3: the probe precedes the scan");
    assert_eq!(code.matches("self.exact_hits.set(").count(), 1, "conformance: I2b-3: one site");
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

/// s7 (I2-10, I2b-3, in-process): one cell (`I2_CELL`) through
/// `oracle_trace_stream`'s two enumerations; the completion sinks build each
/// `CompactSummary` and feed both types. The specification is inserted
/// (identical outcomes; the k-th `Stored` insertion carries seq k, so the
/// seqs are 0 .. entries - 1 in completion order), then the implementation
/// queried, each query by [`i2b_query`] against the oracle built once the
/// specification is in; at the end [`i2b_end`]. Prints `S7`.
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
    struct Run {
        set: SetIndex,
        rf: CompactIndex,
        bad: Vec<String>,
        n: usize,
        stored: u64,
        oracle: Option<Oracle>,
        t: I2bTally,
    }
    let st = std::rc::Rc::new(std::cell::RefCell::new(Run {
        set: SetIndex::new(),
        rf: CompactIndex::with_bucket(false, BucketKind::Scan),
        bad: Vec::new(),
        n: 0,
        stored: 0,
        oracle: None,
        t: I2bTally::default(),
    }));
    for side in ["spec", "impl"] {
        let sink: CompletionSink = {
            let (st, vis) = (std::rc::Rc::clone(&st), f.visible.clone());
            Box::new(move |g: &ExecutionGraph, _| {
                let s = CompactSummary::at_completion(g, &vis, side);
                let mut p = st.borrow_mut();
                let Run {
                    set,
                    rf,
                    bad,
                    n,
                    stored,
                    oracle,
                    t,
                } = &mut *p;
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
                    let o = oracle.get_or_insert_with(|| exact_oracle(rf));
                    i2b_query(set, rf, o, &s, t, bad);
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
                paper_events: false,
            },
            program,
        );
    }
    let p = st.borrow();
    let mut bad = p.bad.clone();
    i2b_end(&p.set, &p.rf, &p.t, &mut bad);
    let (s, r) = (p.set.stats(), ref_stats(&p.rf));
    note!(
        "S7\t{name}\tentries {}\tduplicates {}\tcompletions {}\tqueries {}\texact_hits {}\t\
         witness_differs {}\tsig_tests {}\tsig_aliases {}\tcontainment {} ref {}\t\
         coords {} ref {}\tref_insert_tests {}\tmismatches {}",
        s.entries,
        s.duplicates,
        p.n,
        p.t.queries,
        s.exact_hits,
        p.t.witness_differs,
        s.sig_tests,
        s.sig_aliases,
        s.containment_tests,
        r.containment_tests,
        s.coordinates_compared,
        r.coordinates_compared,
        p.rf.stats().insert_tests,
        bad.len()
    );
    assert!(bad.is_empty(), "conformance: I2-10/I2b-3 {name}: {bad:#?}");
    assert_eq!(p.stored, s.entries as u64, "conformance: I2-10 {name}: seq 0 .. entries");
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
            paper_events: false,
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

// =========================================================================
// SVERIFY-P I2b (tester, gate 3; criteria/SVERIFY-P-I2B.md rev 1.3, derived
// §I2b items 1–11): the fast path's witness, the layout, the knob, the
// refusals, the key, the measurement
// =========================================================================

/// s9 (I2b-3, I2b-10, the behavioural difference from I2): one slot holding
/// `A` (all zeros) and then `B` (coordinate 0 raised), so `A ≤ B`. The query
/// `B` is an exact hit: the set answers `B`'s seq (1) by the probe, the
/// reference `A`'s (0) by its first `≤`; the class is equal; the set's scan
/// counters do not move, the reference tests once. The query `A`: both
/// answer 0, the set by the probe. `C ≥ A`, held nowhere: both scan, one
/// test each, both answer 0. Indexes holding `B` alone: `D` (coordinate 1
/// raised) is incomparable — `NotFound` after one test each — and `E`
/// (coordinate 0 at 2) answers `B`'s seq by the scan. On the I2 code the
/// query `B` answers 0 and tests once.
#[test]
fn s9_an_exact_hit_reports_its_own_seq() {
    let base = real_summary("apps/a3/fifo/spec/k2q2");
    let l = base.ord.len();
    assert!(l >= 2, "conformance: s9 needs two coordinates");
    let at = |v: &[(usize, u8)]| {
        let mut x = vec![0u8; l];
        for &(i, c) in v {
            x[i] = c;
        }
        syn(&base, &x)
    };
    let (a, b, c) = (at(&[]), at(&[(0, 1)]), at(&[(0, 1), (1, 1)]));
    let (mut set, mut rf) = (SetIndex::new(), CompactIndex::with_bucket(false, BucketKind::Scan));
    for s in [&a, &b] {
        assert_eq!(set.insert(s), rf.insert(s));
    }
    let snap = |set: &SetIndex, rf: &CompactIndex| {
        let (s, r) = (set.stats(), rf.stats().clone());
        (s.containment_tests, s.exact_hits, r.containment_tests)
    };
    let mut prev = snap(&set, &rf);
    let mut step = |set: &SetIndex, rf: &mut CompactIndex, q: &CompactSummary| {
        let ans = (set.covers(q), rf.covers(q));
        let now = snap(set, rf);
        let d = (now.0 - prev.0, now.1 - prev.1, now.2 - prev.2);
        prev = now;
        (ans, d)
    };
    let found = |q: u64| (Some(0), Covers::Found(q));
    assert_eq!(step(&set, &mut rf, &b), ((found(1), found(0)), (0, 1, 1)), "conformance: B");
    assert_eq!(step(&set, &mut rf, &a), ((found(0), found(0)), (0, 1, 1)), "conformance: A");
    assert_eq!(step(&set, &mut rf, &c), ((found(0), found(0)), (1, 0, 1)), "conformance: C");
    assert_eq!(
        set.stats().containment_tests + 2,
        rf.stats().containment_tests,
        "conformance: I2b-3: the identity, the reference's two tests on the hits"
    );
    let (mut set2, mut rf2) = (SetIndex::new(), CompactIndex::with_bucket(false, BucketKind::Scan));
    assert_eq!(set2.insert(&b), rf2.insert(&b));
    let (d, e) = (at(&[(1, 1)]), at(&[(0, 2)]));
    let nf = (Some(0), Covers::NotFound);
    assert_eq!((set2.covers(&d), rf2.covers(&d)), (nf, nf), "conformance: D");
    assert_eq!((set2.covers(&e), rf2.covers(&e)), (found(0), found(0)), "conformance: E");
    let s2 = set2.stats();
    assert_eq!((s2.containment_tests, s2.exact_hits), (2, 0));
    assert_eq!(rf2.stats().containment_tests, 2);
}

/// s10 (I2b-8 (a)): the inline sizes the byte model rests on, on this
/// target: `OrdCounts` 32 B, and the `IndexMap` bucket's fields (hash, key,
/// value) 48 B.
#[test]
fn s10_the_inline_sizes_of_the_byte_model() {
    assert_eq!(std::mem::size_of::<OrdCounts>(), 32, "conformance: I2b-8: OrdCounts");
    assert_eq!(
        std::mem::size_of::<(usize, OrdCounts, u64)>(),
        48,
        "conformance: I2b-8: the bucket's fields"
    );
}

/// One stateful run through the grid driver (`run_grid` → `call` →
/// `stateful::run_with`, the knob's path), with its row.
fn knob_run(
    f: &Fixture,
    g: &GridConfig,
) -> (stateful::StatefulOutcome, crate::conformance::grid::Row) {
    use crate::conformance::grid::{row_of, run_grid, GridEnd, GridRaw};
    // `MIN-ENGINES` E6: the uncovered sequences are compared: every report kept.
    let mut g = g.clone();
    g.all_reports = true;
    match run_grid(f, &g, None) {
        GridEnd::Ok(r) => {
            let row = row_of(&r);
            match r.raw {
                GridRaw::Stateful(o) => (o, row),
                other => panic!("conformance: {}: not a stateful outcome: {other:?}", f.name),
            }
        }
        other => panic!("conformance: {}: {other:?}", f.name),
    }
}

/// The implementation summaries of the reported graphs, in report order: the
/// uncovered sequence.
fn uncovered(f: &Fixture, o: &stateful::StatefulOutcome) -> Vec<(Sig, OrdCounts)> {
    o.reports
        .iter()
        .map(|(g, _)| {
            let s = CompactSummary::at_completion(g, &f.visible, "implementation");
            (s.sig, s.ord)
        })
        .collect()
}

/// I2b-7's engine-level equality on one fixture: Set, Compact with the
/// antichain off, Compact at its defaults and Current. Equal across the
/// four: the class counters, the reports and the uncovered sequence, the
/// graph counts, `executions`, the ends. `orders_held`: Set = Compact
/// (antichain off) = Current ≥ Compact (defaults). Set's `counters.compact`
/// is Compact-antichain-off's but `insert_tests` (0) and the two scan
/// counters (smaller by at least `exact_hits`); `counters.containment_tests`
/// is the set's; `set_index` only under Set, `compact_index` never under it;
/// the `index_kind` column; each label round-trips. Returns the mismatches
/// and a one-line summary.
fn i2b_knob(f: &Fixture, distinct: bool) -> (Vec<String>, String) {
    use crate::conformance::config::IndexKind;
    let base = GridConfig::new(GridEngine::Stateful).impl_distinct(distinct);
    let configs = [
        ("set", base.clone().index(IndexKind::Set), "set"),
        ("compact-anti-off", base.clone().index(IndexKind::Compact).antichain(false), "compact"),
        ("compact-default", base.clone().index(IndexKind::Compact), "compact"),
        // `MIN-ENGINES` E7b (the tester's re-pin at gate 3): `Current` named —
        // the default is `Set` now.
        ("current", base.clone().index(IndexKind::Current), "current"),
    ];
    let mut bad = Vec::new();
    let mut runs = Vec::new();
    for (w, g, kind) in &configs {
        let (o, row) = knob_run(f, g);
        let col = row.iter().find(|(c, _)| *c == "index_kind").map(|(_, v)| v.as_str());
        if col != Some(*kind) {
            bad.push(format!("{w}: index_kind {col:?}"));
        }
        if crate::conformance::eval::parse_label(&g.label()).as_ref() != Some(g) {
            bad.push(format!("{w}: the label {} does not round-trip", g.label()));
        }
        runs.push((*w, o));
    }
    let view = |o: &stateful::StatefulOutcome| {
        let c = &o.counters;
        format!(
            "{:?}",
            (
                (c.spec_graphs, c.impl_graphs, c.lookups, c.lookups_signature_miss),
                (c.lookups_containment_tested, c.lookups_succeeded, c.lookups_failed_after_tests),
                (c.reports, c.signatures, c.sig_key_buckets, c.impl_distinct_summaries),
                (c.invisible_ops_of_visible_threads, o.executions, o.reports.len()),
                (o.spec_errors.len(), &o.impl_end, &o.spec_end),
            )
        )
    };
    let (v0, u0) = (view(&runs[0].1), uncovered(f, &runs[0].1));
    for (w, o) in &runs[1..] {
        if view(o) != v0 {
            bad.push(format!("{w}: {} against set {v0}", view(o)));
        }
        if uncovered(f, o) != u0 {
            bad.push(format!("{w}: the uncovered sequence differs"));
        }
    }
    let held: Vec<usize> = runs.iter().map(|(_, o)| o.counters.orders_held).collect();
    if !(held[0] == held[1] && held[0] == held[3] && held[0] >= held[2]) {
        bad.push(format!("orders_held {held:?}"));
    }
    let (so, ro) = (&runs[0].1, &runs[1].1);
    let eh = so
        .set_index
        .as_ref()
        .expect("conformance: set_index under Set")
        .stats()
        .exact_hits;
    match (so.counters.compact.clone(), ro.counters.compact.clone()) {
        (Some(sc), Some(rc)) => {
            let mut want = rc.clone();
            want.insert_tests = 0;
            want.containment_tests = sc.containment_tests;
            want.coordinates_compared = sc.coordinates_compared;
            if sc != want {
                bad.push(format!("counters.compact: set {sc:?} against {rc:?}"));
            }
            if sc.containment_tests + eh > rc.containment_tests
                || sc.coordinates_compared > rc.coordinates_compared
                || eh > so.counters.lookups_succeeded
                || so.counters.containment_tests != sc.containment_tests
            {
                bad.push(format!("scan counters: set {sc:?} exact_hits {eh} against {rc:?}"));
            }
        }
        other => bad.push(format!("counters.compact {other:?}")),
    }
    if so.compact_index.is_some() || runs[1..].iter().any(|(_, o)| o.set_index.is_some()) {
        bad.push("set_index only under Set, compact_index never under it".to_owned());
    }
    let line = format!(
        "{}: exact_hits {eh} orders_held {held:?} containment set {} compact {}",
        f.name, so.counters.containment_tests, ro.counters.containment_tests
    );
    (bad, line)
}

/// s11 (I2b-7): the knob's engine-level equality on the five size-2 cells,
/// and on A4 k2q2m2 with `impl_distinct` on.
#[test]
fn s11_the_set_knob_at_the_engine() {
    let mut bad = Vec::new();
    let cells = SIZE2_CELLS.iter().map(|n| (*n, false));
    for (name, distinct) in cells.chain([("apps/a4/hash/a4a/k2q2m2", true)]) {
        let (b, line) = i2b_knob(&fx(name), distinct);
        note!("s11 {line} distinct {distinct}");
        bad.extend(b.into_iter().map(|m| format!("{name}: {m}")));
    }
    assert!(bad.is_empty(), "conformance: I2b-7: {bad:#?}");
}

/// s11 on the pilot corpus, one process.
#[test]
#[ignore]
fn s11_the_set_knob_at_the_engine_on_the_pilot_corpus() {
    let mut bad = Vec::new();
    for name in PILOT_NAMES {
        let (b, _) = i2b_knob(&fx(name), false);
        bad.extend(b.into_iter().map(|m| format!("{name}: {m}")));
    }
    note!("s11 pilot: {} fixtures, {} mismatches", PILOT_NAMES.len(), bad.len());
    assert!(bad.is_empty(), "conformance: I2b-7 on the pilot: {bad:#?}");
}

/// s12 (I2b-7, "not read" at the engine): under `Set`, `antichain`,
/// `probe_memo` and `bucket` change nothing — one label, and the same
/// counters (the wall times aside), set counters, reports and executions.
#[test]
fn s12_the_set_knob_reads_no_compact_knob() {
    use crate::conformance::config::IndexKind;
    let f = fx("apps/a3/fifo/spec/k2q2");
    let set = GridConfig::new(GridEngine::Stateful).index(IndexKind::Set);
    let variants = [
        set.clone(),
        set.clone().antichain(false),
        set.clone().probe_memo(false),
        set.clone().bucket(BucketKind::Trie),
        set.clone()
            .antichain(false)
            .probe_memo(false)
            .bucket(BucketKind::Inverted(2)),
    ];
    let view = |o: &stateful::StatefulOutcome| {
        let mut c = o.counters.clone();
        c.spec_wall_time_ms = 0;
        c.impl_wall_time_ms = 0;
        (
            format!("{c:?}"),
            o.set_index.as_ref().map(|s| s.stats()),
            uncovered(&f, o),
            o.executions,
        )
    };
    let want = view(&knob_run(&f, &variants[0]).0);
    for g in &variants[1..] {
        assert_eq!(g.label(), variants[0].label(), "conformance: one key");
        assert!(view(&knob_run(&f, g).0) == want, "conformance: I2b-7: {g:?} changes the run");
    }
}

/// s13 (I2b-7, "not read" in the source): the set's construction in
/// `stateful.rs` is one statement, `SetIndex::new()`, which takes no
/// argument; the file reads `cc.antichain` and `cc.bucket` once each, at the
/// `Compact` construction, and `cc.probe_memo` nowhere.
#[test]
fn s13_the_set_construction_reads_no_knob() {
    let read = |p: &str| {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(p);
        std::fs::read_to_string(path).expect("conformance: a source")
    };
    let st = read("src/conformance/stateful.rs");
    let at = st.find("    if cc.index == IndexKind::Set {\n").expect("conformance: the Set arm");
    let end = at + st[at..].find("\n    }\n").expect("conformance: its end");
    let body = &st[at..end];
    assert_eq!(body.lines().count(), 2, "conformance: one statement: {body}");
    assert!(
        body.contains("state.borrow_mut().set = Some(SetIndex::new());"),
        "conformance: the Set construction: {body}"
    );
    for knob in ["antichain", "probe_memo", "bucket"] {
        assert!(!body.contains(knob), "conformance: the Set construction reads {knob}");
    }
    assert_eq!((st.matches("cc.antichain").count(), st.matches("cc.bucket").count()), (1, 1));
    assert!(st.contains("compact = Some(CompactIndex::with_bucket(cc.antichain, cc.bucket));"));
    assert!(!st.contains("cc.probe_memo"), "conformance: probe_memo is complete-first's");
    let cp = read("src/conformance/compact.rs");
    let block = &cp[cp.find("// `SVERIFY-P` I2: the set index").expect("conformance: I2")..];
    assert!(block.contains("    pub(crate) fn new() -> Self {\n"), "conformance: no argument");
}

/// s14 (I2b-7's two refusal sites; `MIN-ENGINES` E7b-5 (c), the tester's
/// re-pin at gate 3): E7b admits the stateless engine with `Set` — the public
/// `verify` runs both programs and returns its verdict, the grid's
/// `conf_config` builds the configuration, `run_grid` ends `Ok` with the set
/// cache present — and refuses `Set` with `completion_cover(Flat)` (the
/// owner's ruling F1): the public `verify` returns `KnobConflict { knob:
/// "index(Set)", conflicts_with: "completion_cover(Flat): use index(Current)" }`
/// and runs neither program; the grid's `conf_config` panics with its message,
/// which names `index(Current)`. The gated and enumerator engines read no
/// index: under `Set` they run as under `Compact`.
#[test]
fn s14_complete_first_with_set_is_admitted_and_flat_set_refused() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::grid::{run_grid, GridEnd, GridRaw};
    use crate::conformance::{CompletionCover, ConfBuilder, ConfError, Engine};
    use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};
    let f = fx("apps/a3/fifo/spec/k2q2");
    let verify = |flat: bool| {
        let calls = std::sync::Arc::new(AtomicUsize::new(0));
        let (ci, cs) = (std::sync::Arc::clone(&calls), std::sync::Arc::clone(&calls));
        let (imp, spec) = (f.implementation.clone(), f.specification.clone());
        let mut b = ConfBuilder::new()
            .config(f.config.clone())
            .visible_threads(f.visible.clone())
            .engine(Engine::CompleteFirst);
        if flat {
            b = b.completion_cover(CompletionCover::Flat);
        }
        let cc = b.index(IndexKind::Set).build().expect("conformance: the builder takes it");
        let r = crate::conformance::verify(
            cc,
            move || {
                ci.fetch_add(1, SeqCst);
                imp()
            },
            move || {
                cs.fetch_add(1, SeqCst);
                spec()
            },
        );
        (r, calls.load(SeqCst))
    };
    let (r, calls) = verify(false);
    assert!(
        matches!(r, Ok(ref v) if v.outcome().cfirst_counters().is_some()) && calls > 0,
        "conformance: CompleteFirst × Set at the public site: {r:?}, {calls} calls"
    );
    let (r, calls) = verify(true);
    assert!(
        matches!(
            r,
            Err(ConfError::KnobConflict {
                knob: "index(Set)",
                conflicts_with: "completion_cover(Flat): use index(Current)"
            })
        ) && calls == 0,
        "conformance: Flat × Set at the public site: {r:?}, {calls} calls"
    );
    let g = GridConfig::new(GridEngine::CompleteFirst).index(IndexKind::Set);
    let cc = g.conf_config(&f);
    assert_eq!(cc.index, IndexKind::Set, "conformance: the grid site builds it");
    match run_grid(&f, &g, None) {
        GridEnd::Ok(r) => match r.raw {
            GridRaw::CompleteFirst(o) => assert!(
                o.set_cache.is_some() && o.compact_cache.is_none(),
                "conformance: the set cache"
            ),
            other => panic!("conformance: {other:?}"),
        },
        other => panic!("conformance: run_grid: {other:?}"),
    }
    let msg = "conformance: index(Set) with completion_cover(Flat) is not a configuration; set \
               index(Current) (MIN-ENGINES E7b)";
    let flat = GridConfig::new(GridEngine::CompleteFirst)
        .precheck(true)
        .cover(CompletionCover::Flat)
        .index(IndexKind::Set);
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let p = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| flat.conf_config(&f)));
    std::panic::set_hook(prev);
    let got = match p {
        Ok(_) => panic!("conformance: the grid site did not refuse Flat × Set"),
        Err(p) => p
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| p.downcast_ref::<String>().cloned()),
    };
    assert_eq!(got.as_deref(), Some(msg), "conformance: the grid site's message");
    for e in [GridEngine::Gated, GridEngine::Enumerator] {
        let run = |k: IndexKind| match run_grid(&f, &GridConfig::new(e).index(k), None) {
            GridEnd::Ok(r) => match r.raw {
                GridRaw::Gated(o) => format!(
                    "{:?}",
                    (o.reports.len(), o.executions, o.max_paper_events, o.aborted, o.impl_end)
                ),
                GridRaw::Enumerator(o) => format!(
                    "{:?}",
                    (o.reports.len(), o.diagnostics.len(), o.end, o.skipped_gates, o.spec_error)
                ),
                other => panic!("conformance: {other:?}"),
            },
            other => panic!("conformance: {other:?}"),
        };
        assert_eq!(run(IndexKind::Set), run(IndexKind::Compact), "conformance: {e:?}");
    }
}

/// s15 (I2b-7, the parser): the Set key is the fourteen-field
/// `…/index=set`; it parses back to `GridConfig::new(Stateful).index(Set)`
/// field by field, the unprinted knobs at `GridConfig::new`'s values (a Set
/// configuration with other knob values has the same key and parses to the
/// defaults), and with `distinct=on`; it is refused on every engine but the
/// stateful one, with a bucket suffix, and in the sixteen-field form.
/// `MIN-ENGINES` E7b (the tester's re-pin at gate 3): and the stateless
/// engine's — its default key, parsing back to `GridConfig::new` — but never
/// with `cover=Flat` (F1).
#[test]
fn s15_the_set_key() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::parse_label;
    let set = GridConfig::new(GridEngine::Stateful).index(IndexKind::Set);
    let key = set.label();
    assert_eq!(key.split('/').count(), 14, "conformance: {key}");
    assert!(key.ends_with("/index=set"), "conformance: {key}");
    assert_eq!(parse_label(&key), Some(set.clone()));
    let other = set.clone().antichain(false).probe_memo(false).bucket(BucketKind::Trie);
    assert_eq!(other.label(), key, "conformance: the unread knobs are not printed");
    assert_eq!(parse_label(&other.label()), Some(set.clone()));
    let d = set.clone().impl_distinct(true);
    assert_eq!(parse_label(&d.label()), Some(d.clone()));
    let cf = GridConfig::new(GridEngine::CompleteFirst);
    assert_eq!(parse_label(&cf.label()), Some(cf.clone()), "conformance: CompleteFirst, Set");
    let flat = cf.clone().precheck(true).cover(crate::conformance::CompletionCover::Flat);
    let flat_set = flat.clone().index(IndexKind::Set).label();
    assert!(
        flat_set.ends_with("cover=Flat/w=inf/quiet=false/index=set"),
        "conformance: {flat_set}"
    );
    assert_eq!(parse_label(&flat_set), None, "conformance: Flat with index=set");
    assert_eq!(parse_label(&flat.label()), Some(flat.clone()), "conformance: Flat, Current");
    for e in [
        GridEngine::Gated,
        GridEngine::Enumerator,
        GridEngine::Verify,
        GridEngine::Explore,
    ] {
        let k = GridConfig::new(e).index(IndexKind::Set).label();
        assert!(k.ends_with("/index=set"), "conformance: {k}");
        assert_eq!(parse_label(&k), None, "conformance: {e:?} with index=set");
    }
    for bad in [
        format!("{key}/bucket=trie"),
        format!("{key}/bucket=inverted:2"),
        key.replace("/index=set", "/index=set/anti=false/pmemo=false"),
        key.replace("/index=set", "/index=set/anti=true/pmemo=true"),
        key.replace("/index=set", "/index=compact"),
    ] {
        assert_eq!(parse_label(&bad), None, "conformance: {bad}");
    }
}

extern "C" {
    /// glibc: return the free memory of every arena to the kernel.
    fn malloc_trim(pad: usize) -> i32;
}

/// `VmSize` and `VmRSS` of this process (`/proc/self/status`) and the exact
/// `Rss` (`/proc/self/smaps_rollup`, a walk of the page tables), KiB. `VmRSS`
/// is read from the kernel's per-CPU counters, which fold in batches of
/// pages, so a small delta of it is approximate; the walk is not.
fn vm_kib() -> (i64, i64, i64) {
    let read = |p: &str| std::fs::read_to_string(p).expect("conformance: /proc/self");
    let field = |s: &str, k: &str| {
        s.lines()
            .find_map(|l| l.strip_prefix(k))
            .and_then(|v| v.trim().trim_end_matches("kB").trim().parse::<i64>().ok())
            .unwrap_or_else(|| panic!("conformance: no {k}"))
    };
    let (s, r) = (read("/proc/self/status"), read("/proc/self/smaps_rollup"));
    (field(&s, "VmSize:"), field(&s, "VmRSS:"), field(&r, "Rss:"))
}

/// The specification summaries of one cell, collected in-process (as s8).
fn spec_summaries_in_process(name: &str) -> Vec<CompactSummary> {
    use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
    use crate::conformance::stateful::{enumerate, EnumRun};
    let f = any_fixture(name);
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
            paper_events: false,
        },
        &f.specification,
    );
    let v = got.borrow().clone();
    v
}

/// s16 (I2b-8 (b), information, single runs): `I2B_MEM_CELL`'s
/// specification summaries collected first, then inserted into one index
/// (`I2B_MEM_KIND`: `set`, or `ref` for `CompactIndex::with_bucket(false,
/// Scan)`), with `malloc_trim(0)` before each reading; prints `S16` with the
/// `VmSize` and `VmRSS` deltas and both per held order.
#[test]
#[ignore]
fn s16_bytes_per_entry() {
    let (Ok(name), Ok(kind)) = (std::env::var("I2B_MEM_CELL"), std::env::var("I2B_MEM_KIND")) else {
        return;
    };
    let summaries = spec_summaries_in_process(&name);
    // SAFETY: glibc's `malloc_trim` only releases free memory of the
    // allocator's own arenas; no live allocation is touched.
    let trim = || {
        unsafe { malloc_trim(0) };
    };
    trim();
    let (v0, r0, x0) = vm_kib();
    let (entries, signatures, (v1, r1, x1)) = match kind.as_str() {
        "set" => {
            let mut ix = SetIndex::new();
            for s in &summaries {
                ix.insert(s);
            }
            trim();
            let m = vm_kib();
            let st = std::hint::black_box(&ix).stats();
            (st.entries, st.signatures, m)
        }
        "ref" => {
            let mut ix = CompactIndex::with_bucket(false, BucketKind::Scan);
            for s in &summaries {
                ix.insert(s);
            }
            trim();
            let m = vm_kib();
            let st = std::hint::black_box(&ix).stats().clone();
            (st.entries, st.signatures, m)
        }
        other => panic!("conformance: I2B_MEM_KIND {other}"),
    };
    let per = |d: i64| d as f64 * 1024.0 / entries as f64;
    note!(
        "S16\t{name}\t{kind}\tsummaries {}\tentries {entries}\tsignatures {signatures}\t\
         vmsize_delta_kib {}\tvmrss_delta_kib {}\trss_exact_delta_kib {}\t\
         B_per_entry_vmsize {:.1}\tB_per_entry_vmrss {:.1}\tB_per_entry_rss_exact {:.1}",
        summaries.len(),
        v1 - v0,
        r1 - r0,
        x1 - x0,
        per(v1 - v0),
        per(r1 - r0),
        per(x1 - x0)
    );
}

// =========================================================================
// MIN-ENGINES E1 (tester, gate 3; criteria/MIN-ENGINES-E1.md rev 1.4,
// derived §E1 items 9–16): the plain-scheduled modes, the second scheduler,
// names only, the key
// =========================================================================

/// One complete graph's summary line (`Sig` Debug, tab, the order counts),
/// as the before/after record prints it (`e1_record`'s `line_of`).
fn e1_line(g: &ExecutionGraph, visible: &[String]) -> String {
    let w = wobs(g, visible).expect("conformance: wobs");
    let counts = match OrdCounts::of(g, &w, visible) {
        OrdCounts::U8(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
        OrdCounts::U16(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>(),
    };
    let s = Summary::of(CompleteExecution::try_finished(g).unwrap(), w, visible)
        .expect("conformance: a summary");
    format!("{:?}\t{}", s.sig, counts.join(","))
}

/// One program's summary lines in the stateful engine's `Enumerate` run's
/// completion order (`stateful::enumerate`) under `config`, unbounded.
fn e1_enumerate(
    config: &crate::Config,
    visible: &[String],
    p: &crate::conformance::grid::Prog,
) -> Vec<String> {
    use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
    use crate::conformance::stateful::{enumerate, EnumRun};
    let acc: std::rc::Rc<std::cell::RefCell<Vec<String>>> = Default::default();
    let sink: CompletionSink = {
        let (acc, vis) = (std::rc::Rc::clone(&acc), visible.to_vec());
        Box::new(move |g: &ExecutionGraph, _| {
            acc.borrow_mut().push(e1_line(g, &vis));
            SinkVerdict::Continue
        })
    };
    let mut config = config.clone();
    config.max_iterations = None;
    enumerate(
        EnumRun {
            config,
            visible: visible.to_vec(),
            mode: ConfMode::Enumerate,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        p,
    );
    let out = std::mem::take(&mut *acc.borrow_mut());
    out
}

/// MIN-ENGINES E1-1 (derived §E1 item 12): the counting test, on the lead's
/// test-only counter (`must::selector_picks_for_test`, bumped on the selector
/// branch at both scheduling sites). On A3 fifo k2q2 and the nested pair
/// `e1:race/bag`, under each selector: no pick over a stateful run (both
/// sides, `Enumerate`) or a complete-first outer run (`CFirstOuter`), each of
/// which explores; and picks over an enumerator run, the oracle's `Collect`
/// run, a gated run and complete-first with its precheck (`Precheck`) on the
/// same fixture — the counter is live and those modes keep the selector.
/// **The counter is thread-local and a sweep runs on its own scoped thread**
/// (`cfirst::sweep_with`), so it sees no `CFirstSweep` (or `GatedSweep`) pick:
/// the sweeps' not-reading is pinned by behaviour instead —
/// `cfirst_tests::c12_the_selector_no_longer_reaches_the_outer_run_or_the_sweeps`
/// (every swept graph's stamps equal under the three selectors) and the
/// after-run's per-sweep order digests.
#[test]
fn e1_the_selector_branch_is_never_taken_by_the_plain_modes() {
    use crate::conformance::eval::x1_config;
    use crate::conformance::search::SearchOpts;
    use crate::conformance::selector::{InnerOrder, Selector};
    use crate::must::{reset_selector_picks_for_test as reset, selector_picks_for_test as picks};
    let mut bad = Vec::new();
    for name in ["apps/a3/fifo/spec/k2q2", "e1:race/bag"] {
        let f = e1_fixture(name);
        for sel in [Selector::Ltr, Selector::Reverse, Selector::FewestEvents] {
            reset();
            let cc = x1_config(GridEngine::Stateful, sel).conf_config(&f);
            let st = stateful::run_with(&cc, &f.implementation, &f.specification, false);
            let (n, c) = (picks(), &st.counters);
            if n != 0 || c.spec_graphs == 0 || c.impl_graphs == 0 {
                bad.push(format!(
                    "{name} {sel:?} stateful: {n} picks, graphs {} / {}",
                    c.spec_graphs, c.impl_graphs
                ));
            }
            reset();
            let cc = x1_config(GridEngine::CompleteFirst, sel).conf_config(&f);
            let cf = crate::conformance::cfirst::run_with(
                &cc,
                &f.implementation,
                &f.specification,
                false,
            );
            let n = picks();
            if n != 0 || cf.executions == 0 || cf.counters.sweeps == 0 {
                bad.push(format!(
                    "{name} {sel:?} complete-first: {n} picks, {} executions, {} sweeps",
                    cf.executions, cf.counters.sweeps
                ));
            }
        }
        let mut live = Vec::new();
        reset();
        let mut ec = f.config.clone();
        ec.selector = Selector::Ltr;
        let _ = crate::conformance::verify_conformance_with_opts(
            ec,
            f.implementation.clone(),
            f.specification.clone(),
            f.visible.clone(),
            usize::MAX,
            false,
            SearchOpts {
                inner_order: InnerOrder::Recorded,
                memo: true,
                instrument: false,
            },
        );
        live.push(("enumerator", picks()));
        reset();
        let mut config = x1_config(GridEngine::Stateful, Selector::Ltr).conf_config(&f).config;
        config.max_iterations = None;
        let gs = crate::conformance::selector_tests::graphs_of(
            config,
            &f.visible,
            f.implementation.clone(),
        );
        live.push(("collect", if gs.is_empty() { 0 } else { picks() }));
        reset();
        let cc = x1_config(GridEngine::Gated, Selector::Ltr).conf_config(&f);
        let _ =
            crate::conformance::gated::run_with(&cc, &f.implementation, &f.specification, false);
        live.push(("gated", picks()));
        reset();
        let cc = x1_config(GridEngine::CompleteFirst, Selector::Ltr).precheck(true).conf_config(&f);
        let _ = crate::conformance::cfirst::run(
            cc,
            f.implementation.clone(),
            f.specification.clone(),
        );
        live.push(("precheck", picks()));
        note!("e1 counting {name}: {live:?}");
        for (what, n) in live {
            if n == 0 {
                bad.push(format!("{name} {what}: no pick (the counter is not live)"));
            }
        }
    }
    assert!(bad.is_empty(), "conformance: E1-1: {bad:#?}");
}

/// MIN-ENGINES E1-1 (derived §E1 item 12, the source half): `uses_selector` is
/// the predicate over `ConfMode::plain_scheduling`, which names `Enumerate`,
/// `CFirstOuter` and `CFirstSweep` and no other mode; the scheduling step's
/// plain branch is the `SchedulePolicy` match with the LTR arm
/// `runnable.iter().find(..)` — no candidate vector, no origination vector —
/// and `unblock_ready`'s plain return is `blocked.first()`.
#[test]
fn e1_the_plain_path_builds_no_candidate_vector() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let must = std::fs::read_to_string(root.join("must.rs")).expect("conformance: must.rs");
    let ctx = std::fs::read_to_string(root.join("conformance/ctx.rs"))
        .expect("conformance: ctx.rs");
    assert!(
        must.contains(
            "self.probe.is_some() || self.conf.as_ref().is_some_and(|c| \
             !c.mode().plain_scheduling())"
        ),
        "conformance: the predicate"
    );
    let at = ctx
        .find("pub(crate) fn plain_scheduling(self) -> bool {")
        .expect("conformance: plain_scheduling");
    let body = &ctx[at..at + ctx[at..].find("\n    }\n").expect("conformance: its end")];
    assert_eq!(body.matches("ConfMode::").count(), 3, "conformance: {body}");
    for m in ["ConfMode::Enumerate", "ConfMode::CFirstOuter", "ConfMode::CFirstSweep"] {
        assert!(body.contains(m), "conformance: {m} in {body}");
    }
    let start = must
        .find("let next = if self.uses_selector() {")
        .expect("conformance: the scheduling step");
    let rest = &must[start..];
    let els = rest
        .find("        } else {\n            match self.config.schedule_policy {")
        .expect("conformance: the plain branch");
    let end = rest.find("        if next.is_some() {").expect("conformance: its end");
    let plain = &rest[els..end];
    for no in ["collect", "Vec", "origination_vec", "selector"] {
        assert!(!plain.contains(no), "conformance: `{no}` on the plain path: {plain}");
    }
    assert!(
        plain.contains(
            "SchedulePolicy::LTR => runnable\n                    .iter()\n                    \
             .find(|(t, i)| self.is_thread_runnable(t, i))"
        ),
        "conformance: the LTR arm: {plain}"
    );
    assert!(rest[..els].contains("self.config.selector.pick("));
    assert!(
        must.contains(
            "            return self.config.selector.pick(&self.current.graph, &candidates);\n\
             \x20       }\n        blocked.first().map(|(t, _)| t.to_owned())"
        ),
        "conformance: unblock_ready's plain return"
    );
}

/// MIN-ENGINES E1-4 (ii) (derived §E1 item 11): a second scheduler. The
/// oracle's `Collect` run (`selector_tests::graphs_of`; that mode keeps the
/// selector) under `Reverse`, against the stateful engine's `Enumerate` run
/// (plain Must) of the same program, both sides, on the four nested pairs and
/// the five size-2 cells: equal multisets of summary lines on every side, and
/// a differing completion order on A3 fifo k2q2's implementation (where
/// `Reverse` moved the order before E1), so the check is not vacuous. One
/// `E1X` line per side records whether the order differs; a nested pair whose
/// order does not differ is the digest's limit, not a failure.
#[test]
fn e1_collect_under_reverse_against_plain() {
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    let mut bad = Vec::new();
    let mut differ = Vec::new();
    for name in [
        "e1:nested4/self",
        "e1:race/bag",
        "e1:race-bad/bag",
        "e1:chain/bag",
        "apps/a1/correct/spec/n2r2",
        "apps/a2/pb/spec/k2q2",
        "apps/a3/fifo/spec/k2q2",
        "apps/a4/hash/a4a/k2q2m2",
        "2pc/leader/conf/n2",
    ] {
        let f = e1_fixture(name);
        let mut config = x1_config(GridEngine::Stateful, Selector::Reverse).conf_config(&f).config;
        config.max_iterations = None;
        let sides = [("specification", &f.specification), ("implementation", &f.implementation)];
        for (side, p) in sides {
            let gs = crate::conformance::selector_tests::graphs_of(
                config.clone(),
                &f.visible,
                p.clone(),
            );
            let collect: Vec<String> = gs.iter().map(|g| e1_line(g, &f.visible)).collect();
            let plain = e1_enumerate(&config, &f.visible, p);
            let (mut a, mut b) = (collect.clone(), plain.clone());
            a.sort();
            b.sort();
            if a != b || a.is_empty() {
                bad.push(format!(
                    "{name} {side}: multisets differ ({} / {})",
                    a.len(),
                    b.len()
                ));
            }
            let order = if collect == plain { "same" } else { "differs" };
            note!("E1X\t{name}\t{side}\tcompletions {}\torder {order}", plain.len());
            if collect != plain {
                differ.push(format!("{name} {side}"));
            }
        }
    }
    note!("e1 second scheduler: orders differ on {differ:?}");
    assert!(bad.is_empty(), "conformance: E1-4 (ii): {bad:#?}");
    assert!(
        differ.contains(&"apps/a3/fifo/spec/k2q2 implementation".to_owned()),
        "conformance: E1-4 (ii) vacuous: {differ:?}"
    );
}

/// Whether two lists of compact summaries are equal as multisets: `Sig ==`
/// (`msg_equals`), then `OrdCounts ==` (compared only under equal signatures).
fn e1_same_multiset(
    a: &[crate::conformance::compact::CompactSummary],
    b: &[crate::conformance::compact::CompactSummary],
) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut left: Vec<&crate::conformance::compact::CompactSummary> = b.iter().collect();
    for x in a {
        match left.iter().position(|y| y.sig == x.sig && y.ord == x.ord) {
            Some(i) => {
                left.swap_remove(i);
            }
            None => return false,
        }
    }
    true
}

/// MIN-ENGINES E1-3 (derived §E1 item 13): names only, on the compact summary.
/// `P₁`: `main` spawns an invisible receiver `q`, an invisible `w`, then the
/// visible `v`; `P₀`: `q`, then `v`; `v` sends 1 and 2 to `q` (`Bag`). The two
/// programs' multisets of `CompactSummary` (the stateful engine's kept graphs)
/// are equal and the engine reports nothing, while `v`'s `ThreadId` differs
/// between them (`resolve_visible`; the pairing is by name). The limit (E1-3's
/// caveat), pinned: when `v` sends its own `ThreadId`, the multisets differ
/// and the engine reports — a value carrying a thread id is the program's
/// content.
#[test]
fn e1_names_only_on_the_compact_summary() {
    use crate::conformance::compact::CompactSummary;
    fn prog(extra: bool, own_id: bool) -> crate::conformance::grid::Prog {
        crate::conformance::grid::prog(move || {
            let q = crate::thread::Builder::new()
                .name("q".to_owned())
                .spawn(move || {
                    for _ in 0..2 {
                        if own_id {
                            let _: crate::thread::ThreadId = crate::recv_msg_block();
                        } else {
                            let _: i32 = crate::recv_msg_block();
                        }
                    }
                })
                .unwrap();
            let qid = q.thread().id();
            if extra {
                crate::thread::Builder::new()
                    .name("w".to_owned())
                    .spawn(|| {})
                    .unwrap();
            }
            crate::thread::Builder::new()
                .name("v".to_owned())
                .spawn(move || {
                    if own_id {
                        let me = crate::thread::current().id();
                        crate::send_msg(qid, me);
                        crate::send_msg(qid, me);
                    } else {
                        crate::send_msg(qid, 1i32);
                        crate::send_msg(qid, 2i32);
                    }
                })
                .unwrap();
        })
    }
    type Side = (Vec<CompactSummary>, Vec<String>);
    let run = |own_id: bool| -> (Side, Side, usize) {
        let f = local_fixture("e1:names", prog(true, own_id), prog(false, own_id), &["v"]);
        let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
        let side = |gs: &[ExecutionGraph]| -> Side {
            let s = gs
                .iter()
                .map(|g| CompactSummary::at_completion(g, &f.visible, "test"))
                .collect();
            let mut ids: Vec<String> = gs
                .iter()
                .map(|g| {
                    let t = crate::conformance::obs::resolve_visible(g, "v");
                    format!("{:?}", t.expect("conformance: v resolves").expect("conformance: v"))
                })
                .collect();
            ids.sort();
            ids.dedup();
            (s, ids)
        };
        (side(&o.kept_spec_graphs), side(&o.kept_impl_graphs), o.reports.len())
    };
    let ((s, sid), (i, iid), reports) = run(false);
    note!("e1 names: spec {} graphs, v {sid:?}; impl {} graphs, v {iid:?}", s.len(), i.len());
    assert!(!s.is_empty() && !i.is_empty(), "conformance: E1-3: no graphs");
    assert!(e1_same_multiset(&s, &i), "conformance: E1-3: the multisets differ");
    assert_eq!(reports, 0, "conformance: E1-3: the engine reports");
    assert!(
        sid.len() == 1 && iid.len() == 1 && sid != iid,
        "conformance: E1-3 vacuous: v is {sid:?} in P₁ and {iid:?} in P₀"
    );
    let ((s, _), (i, _), reports) = run(true);
    assert!(
        !e1_same_multiset(&s, &i) && reports > 0,
        "conformance: E1-3's limit: a ThreadId-valued message compared equal ({reports} reports)"
    );
}

/// MIN-ENGINES E1-2 (derived §E1 item 14 (a)–(c); rev 1.4's rule): the key.
/// (a) `Plain` exactly on `plain_key()` configurations (the stateful engine;
/// complete-first without the precheck), under each selector: the three give
/// one key, which parses to `Ltr` with no legacy selector and reprints itself;
/// complete-first with the precheck names its selector (three keys, each
/// round-tripping exactly); `Plain` on the enumerator, the gated engine or a
/// precheck row is no key. (b)–(c) Every key of the four stores
/// (`campaign-1`, `apptab-1`, `cfirst-1`, `compact-2`) parses and reprints byte
/// for byte; a stored stateful or precheck-free complete-first key naming a
/// selector is a legacy identity (`legacy_selector: Some(s)`); each of the
/// three spellings is stored on both engines; one stored key of each is
/// refused by `run_row_in_process` with its spelling and the fix in the
/// payload and no program run (a counting fixture, which runs under the
/// `Plain` key).
#[test]
fn e1_the_key_plain_and_legacy() {
    use crate::conformance::eval::{parse_key, parse_label, read_rows, run_row_in_process};
    use crate::conformance::eval::x1_config;
    use crate::conformance::grid::GridEnd;
    use crate::conformance::selector::Selector;
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};
    let sels = [Selector::Ltr, Selector::Reverse, Selector::FewestEvents];
    let mut bad = Vec::new();
    for engine in [GridEngine::Stateful, GridEngine::CompleteFirst] {
        for (pre, stop) in [(false, false), (false, true), (true, false), (true, true)] {
            let of = |s: Selector| GridConfig::new(engine).selector(s).precheck(pre).stop(stop);
            let plain = engine == GridEngine::Stateful || !pre;
            let labels: BTreeSet<String> = sels.iter().map(|s| of(*s).label()).collect();
            let want_n = if plain { 1 } else { 3 };
            if labels.len() != want_n {
                bad.push(format!("(a) {engine:?} pre={pre}: {labels:?}"));
            }
            for s in sels {
                let (c, l) = (of(s), of(s).label());
                let want = if plain { "Plain".to_owned() } else { format!("{s:?}") };
                if l.split('/').nth(1) != Some(want.as_str()) || c.plain_key() != plain {
                    bad.push(format!("(a) {l}: field, plain_key {}", c.plain_key()));
                }
                let sel = if plain { Selector::Ltr } else { s };
                match parse_label(&l) {
                    Some(p)
                        if p.label() == l && p.legacy_selector.is_none() && p.selector == sel => {}
                    other => bad.push(format!("(a) {l}: {other:?}")),
                }
            }
        }
    }
    for l in [
        GridConfig::new(GridEngine::Enumerator).label(),
        GridConfig::new(GridEngine::Gated).label(),
        GridConfig::new(GridEngine::CompleteFirst).precheck(true).label(),
    ] {
        let p = l.replacen("/Ltr/", "/Plain/", 1);
        if parse_label(&p).is_some() {
            bad.push(format!("(a) `Plain` parsed on {p}"));
        }
    }
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../plan/traceForge/log/eval");
    let mut seen: BTreeMap<(String, String), String> = BTreeMap::new();
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for store in ["campaign-1", "apptab-1", "cfirst-1", "compact-2"] {
        let rows = read_rows(&dir.join(store).join("rows.csv"))
            .unwrap_or_else(|e| panic!("conformance: {store}: {}", e.text()));
        if rows.is_empty() {
            bad.push(format!("(c) {store}: no rows"));
        }
        for r in &rows {
            let k = &r["key"];
            let field = k.split('|').nth(1).unwrap_or("");
            let Some((_, c, ..)) = parse_key(k) else {
                bad.push(format!("(c) {store}: {k} does not parse"));
                continue;
            };
            if c.label() != field {
                bad.push(format!("(c) {store}: {k} reprints {}", c.label()));
                continue;
            }
            let name = field.split('/').nth(1).unwrap_or("").to_owned();
            let plain_engine = c.engine == GridEngine::Stateful
                || (c.engine == GridEngine::CompleteFirst && !c.precheck);
            let class = match c.legacy_selector {
                Some(s) if plain_engine && format!("{s:?}") == name => {
                    seen.entry((format!("{:?}", c.engine), name)).or_insert_with(|| k.clone());
                    "legacy"
                }
                None if !plain_engine => "selector",
                _ => {
                    bad.push(format!("(b) {store}: {k}: legacy {:?}", c.legacy_selector));
                    "?"
                }
            };
            *counts.entry(format!("{store} {class}")).or_default() += 1;
        }
    }
    note!("e1 keys: {counts:?}");
    for e in ["Stateful", "CompleteFirst"] {
        for s in sels {
            if !seen.contains_key(&(e.to_owned(), format!("{s:?}"))) {
                bad.push(format!("(b) no stored {e} key under {s:?}"));
            }
        }
    }
    static E1_CALLS: AtomicUsize = AtomicUsize::new(0);
    let counting = || {
        crate::conformance::grid::prog(|| {
            E1_CALLS.fetch_add(1, SeqCst);
            let _ = crate::thread::Builder::new()
                .name("r".to_owned())
                .spawn(|| {})
                .unwrap();
        })
    };
    let fx = local_fixture("e1:counting", counting(), counting(), &["r"]);
    for ((e, s), k) in &seen {
        let (_, c, ..) = parse_key(k).expect("conformance: a stored key");
        let before = E1_CALLS.load(SeqCst);
        match run_row_in_process(&fx, &c, false) {
            GridEnd::Panicked { payload, .. }
                if payload.starts_with("refused: ")
                    && payload.contains(&format!("`{s}`"))
                    && payload.contains("`Plain` key") => {}
            other => bad.push(format!("(b) {e} {s}: {k}: {other:?}")),
        }
        if E1_CALLS.load(SeqCst) != before {
            bad.push(format!("(b) {e} {s}: a program ran"));
        }
    }
    let before = E1_CALLS.load(SeqCst);
    let end = run_row_in_process(&fx, &x1_config(GridEngine::Stateful, Selector::Ltr), false);
    if E1_CALLS.load(SeqCst) == before || matches!(end, GridEnd::Panicked { .. }) {
        bad.push(format!("(b) the counting fixture did not run under `Plain`: {end:?}"));
    }
    assert!(bad.is_empty(), "conformance: E1-2: {bad:#?}");
}

/// MIN-ENGINES E1-2 (derived §E1 item 14 (b)), through the child: `EVAL_ROW`
/// naming a legacy key (the stateful engine under `Reverse`; complete-first
/// under `FewestEvents`) is refused by `eval_row` with its `conformance: `
/// diagnostic before any engine — the child fails and prints no sentinel
/// record; the same row under its `Plain` key prints one.
#[test]
fn e1_eval_row_refuses_a_legacy_key() {
    use crate::conformance::eval::{parse_label, row_json, RowSpec, RunKind, Tier};
    let row = |c: GridConfig| RowSpec {
        fixture: "ex:naive/k2/enc1".to_owned(),
        config: c,
        rep: 0,
        tier: Tier::default_tier(),
        run_kind: RunKind::Timed,
        family: "ex:naive".to_owned(),
        knobs: "k=2,enc=1".to_owned(),
        k: [Some(2), Some(1), None, None],
        variant: "violating".to_owned(),
        twin_key: String::new(),
        series: None,
    };
    let child = |json: String| -> (bool, String) {
        let out = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--ignored", "--exact", "conformance::eval::eval_row"])
            .args(["--nocapture", "--test-threads=1"])
            .env("EVAL_ROW", json)
            .env_remove("EVAL_RUN_DIR")
            .env_remove("EVAL_EXPORT")
            .output()
            .expect("conformance: the child");
        let text = String::from_utf8_lossy(&out.stdout).into_owned()
            + &String::from_utf8_lossy(&out.stderr);
        (out.status.success(), text)
    };
    let mut bad = Vec::new();
    let cases = [(GridEngine::Stateful, "Reverse"), (GridEngine::CompleteFirst, "FewestEvents")];
    for (engine, s) in cases {
        let plain = GridConfig::new(engine).label();
        let legacy = plain.replacen("/Plain/", &format!("/{s}/"), 1);
        let c = parse_label(&legacy).expect("conformance: a legacy label parses");
        if c.legacy_selector.is_none() || c.label() != legacy {
            bad.push(format!("{legacy}: not a legacy identity"));
            continue;
        }
        let (ok, text) = child(row_json(&row(c)));
        if ok
            || !text.contains("conformance: EVAL_ROW names a legacy key")
            || !text.contains(&format!("`{s}`"))
            || text.contains("EVALROW\t")
        {
            bad.push(format!("{legacy}: ok {ok}: {text}"));
        }
        let (ok, text) = child(row_json(&row(GridConfig::new(engine))));
        if !ok || !text.contains("EVALROW\t") {
            bad.push(format!("{plain}: ok {ok}: {text}"));
        }
    }
    assert!(bad.is_empty(), "conformance: E1-2: {bad:#?}");
}

/// MIN-ENGINES E1-2 with rev 1.4's spec rule (the lead's F1 fix: one row per
/// point where the key is `Plain`, `selectors_for`): no built-in spec, and no
/// contract spec, lists a key twice. Derived from the spec builders before
/// running: as landed at 14:42 `x0_spec` kept its own three-selector loop, so
/// X0 listed its stateful and complete-first keys three times each (12 rows,
/// 8 keys) and this test failed on X0 alone (the tester's F1b, 15:01); the
/// lead's fix (17:58) builds X0 by `selectors_for` as well: 8 rows, 8 keys.
#[test]
fn e1_no_spec_lists_a_key_twice() {
    use crate::conformance::eval::{builtin_specs, contract_specs, profile_name};
    let mut bad = Vec::new();
    for s in builtin_specs().into_iter().chain(contract_specs()) {
        let keys: std::collections::BTreeSet<String> =
            s.rows.iter().map(|r| r.key(profile_name())).collect();
        if keys.len() != s.rows.len() {
            bad.push(format!("{}: {} rows, {} keys", s.name, s.rows.len(), keys.len()));
        }
    }
    assert!(bad.is_empty(), "conformance: duplicate keys: {bad:?}");
}

/// MIN-ENGINES E1-2, the lead's F2 fix (the tester's finding at gate 3): a
/// row's `selector` column is the key's second field (`selector_field`) —
/// `Plain` on a `Plain`-key row under every selector, a legacy key's own
/// spelling, and the selector's name where a run reads it (complete-first with
/// the precheck, the gated engine, the enumerator) — on `row_of_end`'s settings
/// columns.
#[test]
fn e1_the_selector_column_is_the_keys_field() {
    use crate::conformance::eval::{parse_label, x1_config};
    use crate::conformance::grid::{row_of_end, GridEnd};
    use crate::conformance::selector::Selector;
    let col = |c: &GridConfig| -> String {
        let end = GridEnd::Panicked {
            fixture: "e1:column".to_owned(),
            config: c.clone(),
            payload: String::new(),
        };
        let row = row_of_end(&end);
        row.into_iter().find(|(k, _)| *k == "selector").map(|(_, v)| v).unwrap_or_default()
    };
    let mut bad = Vec::new();
    for s in [Selector::Ltr, Selector::Reverse, Selector::FewestEvents] {
        let name = format!("{s:?}");
        let cases = [
            (x1_config(GridEngine::Stateful, s), "Plain"),
            (x1_config(GridEngine::CompleteFirst, s), "Plain"),
            (x1_config(GridEngine::CompleteFirst, s).precheck(true), name.as_str()),
            (x1_config(GridEngine::Gated, s), name.as_str()),
            (x1_config(GridEngine::Enumerator, s), name.as_str()),
        ];
        for (c, want) in cases {
            let (got, l) = (col(&c), c.label());
            if got != want || l.split('/').nth(1) != Some(got.as_str()) {
                bad.push(format!("{l}: column {got:?}, want {want}"));
            }
        }
        let plain = GridConfig::new(GridEngine::Stateful).label();
        let legacy = plain.replacen("/Plain/", &format!("/{name}/"), 1);
        let c = parse_label(&legacy).expect("conformance: a legacy label parses");
        if col(&c) != name {
            bad.push(format!("{legacy}: column {:?}", col(&c)));
        }
    }
    assert!(bad.is_empty(), "conformance: F2: {bad:#?}");
}

// =========================================================================
// MIN-ENGINES E2 (tester, gate 3; criteria/MIN-ENGINES-E2.md; derived §E2):
// the growing gates return at entry in the plain-scheduled modes
// =========================================================================

/// One Must exploring `p` with a gate-disabled context in `mode` (a completion
/// sink counting calls in the enumerating modes), on the test thread: the
/// context's counters, its F49/F42 tallies, plain Must's split, the sink's
/// calls, and the test-only take and clone counts over the run.
fn e2_entry_counts(
    f: &Fixture,
    p: &crate::conformance::grid::Prog,
    mode: crate::conformance::ctx::ConfMode,
) -> (crate::conformance::report::ConfCounters, usize, usize, usize, usize, usize, usize) {
    use crate::conformance::ctx::{ConfCtx, SinkVerdict};
    use crate::must::{carry_clones_for_test, gate_takes_for_test, reset_gate_counts_for_test};
    let mut config = crate::conformance::eval::x1_config(
        GridEngine::Stateful,
        crate::conformance::selector::Selector::Ltr,
    )
    .conf_config(f)
    .config;
    config.max_iterations = None;
    let calls = std::rc::Rc::new(std::cell::Cell::new(0usize));
    let mut ctx = ConfCtx::gate_disabled(config.clone(), f.visible.clone(), mode);
    if mode.enumerates() {
        let c = std::rc::Rc::clone(&calls);
        ctx.set_sink(Box::new(move |_, _| {
            c.set(c.get() + 1);
            SinkVerdict::Continue
        }));
    }
    let must = std::rc::Rc::new(std::cell::RefCell::new(crate::must::Must::new(config, false)));
    must.borrow_mut().enable_conformance(ctx);
    reset_gate_counts_for_test();
    {
        let _guard = crate::conformance::testing::CurrentMustGuard;
        let q = p.clone();
        crate::explore(&must, &std::sync::Arc::new(move || q()));
    }
    let (takes, clones) = (gate_takes_for_test(), carry_clones_for_test());
    let m = must.borrow();
    let s = m.stats();
    let ctx = m.conf_ctx().expect("conformance: the context went missing");
    (
        ctx.counters().clone(),
        ctx.skipped_gates(),
        ctx.inert_gates(),
        s.execs + s.block,
        calls.get(),
        takes,
        clones,
    )
}

/// MIN-ENGINES E2 (derived §E2 items 4–5 (a), (c), (d)): in `Enumerate`,
/// `CFirstOuter` and `CFirstSweep` no growing gate enters the context —
/// `gate_invocations` = `executions` = plain Must's `execs + block` = the
/// completion sink's calls; `gate_skipped_disabled` = the completions too (the
/// completion gate itself ends at the gate-disabled return, `ctx.rs` 1556 — the
/// tester's correction of derived §E2 item 4, which had it 0); the other skip
/// counters, `skipped_gates` and `inert_gates` 0; the gate takes equal to the
/// completions and no carry clone — on A3 fifo k2q2's implementation
/// (replays, backward revisits) and `e1:race/bag`; under `Collect` and
/// `Precheck` on the same programs the growing gates still enter
/// (`gate_invocations` > `executions`, `gate_skipped_disabled` > 0, takes >
/// completions; on A3 fifo k2q2 the carry is cloned at its backward revisits),
/// and a `GatedOuter` run (`gated::run_with`, its outer run on the test thread)
/// clones the carry — the counts are live. The completion gate still takes once
/// per execution in every mode (the verdict's reading: takes = executions).
#[test]
fn e2_no_growing_gate_enters_the_context_in_the_plain_modes() {
    use crate::conformance::ctx::ConfMode;
    let mut bad = Vec::new();
    for name in ["apps/a3/fifo/spec/k2q2", "e1:race/bag"] {
        let f = e1_fixture(name);
        for mode in [ConfMode::Enumerate, ConfMode::CFirstOuter, ConfMode::CFirstSweep] {
            let (c, skipped, inert, total, calls, takes, clones) =
                e2_entry_counts(&f, &f.implementation, mode);
            let zero = c.gate_skipped_inert
                + c.gate_skipped_replay
                + c.gate_skipped_pruned
                + c.gate_skipped_aborted
                + skipped
                + inert;
            if c.gate_invocations != c.executions
                || c.executions != total
                || calls != total
                || c.gate_skipped_disabled != total
                || zero != 0
                || takes != total
                || clones != 0
            {
                bad.push(format!(
                    "{name} {mode:?}: invocations {} executions {} total {total} calls {calls} \
                     skips {zero} takes {takes} clones {clones}",
                    c.gate_invocations, c.executions
                ));
            }
        }
        for mode in [ConfMode::Collect, ConfMode::Precheck] {
            let (c, _, _, total, _, takes, clones) = e2_entry_counts(&f, &f.implementation, mode);
            let entered = c.gate_invocations > c.executions && c.gate_skipped_disabled > 0;
            note!("e2 {name} {mode:?}: takes {takes} completions {total} clones {clones}");
            let cloned = clones > 0 || name != "apps/a3/fifo/spec/k2q2";
            if !entered || takes <= total || !cloned {
                bad.push(format!(
                    "{name} {mode:?}: invocations {} executions {} disabled {} takes {takes} \
                     clones {clones}",
                    c.gate_invocations, c.executions, c.gate_skipped_disabled
                ));
            }
        }
    }
    {
        use crate::must::{carry_clones_for_test, reset_gate_counts_for_test};
        let f = e1_fixture("apps/a3/fifo/spec/k2q2");
        let cc = crate::conformance::eval::x1_config(
            GridEngine::Gated,
            crate::conformance::selector::Selector::Ltr,
        )
        .conf_config(&f);
        reset_gate_counts_for_test();
        let (imp, spec) = (&f.implementation, &f.specification);
        let _ = crate::conformance::gated::run_with(&cc, imp, spec, false);
        if carry_clones_for_test() == 0 {
            bad.push("GatedOuter: no carry clone (the counter is not live)".to_owned());
        }
    }
    assert!(bad.is_empty(), "conformance: E2: {bad:#?}");
}

/// MIN-ENGINES E2 (derived §E2 item 5 (b)): the source order. In
/// `conf_gate_at` the plain-mode return names `gate != Completion` and precedes
/// `self.conf.take()`; in `conf_revisit_gate` it precedes the label match, the
/// `take()` and the `outgoing_carry` clone; both read E1's `plain_scheduling`.
#[test]
fn e2_the_returns_precede_the_take_and_the_clone() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let must = std::fs::read_to_string(root.join("must.rs")).expect("conformance: must.rs");
    let body = |head: &str| -> &str {
        let at = must.find(head).unwrap_or_else(|| panic!("conformance: {head}"));
        let rest = &must[at..];
        &rest[..rest.find("\n    }\n").expect("conformance: the function's end")]
    };
    let g = body("fn conf_gate_at(");
    let (ret, take) = (g.find("plain_scheduling()"), g.find("self.conf.take()"));
    assert!(
        matches!((ret, take), (Some(r), Some(t)) if r < t) && g.contains("Completion"),
        "conformance: conf_gate_at: {g}"
    );
    let r = body("fn conf_revisit_gate(");
    let ret = r.find("plain_scheduling()");
    for later in ["match self.current.graph.label(pos)", "self.conf.take()", "conf_carry"] {
        let l = r.find(later);
        assert!(
            matches!((ret, l), (Some(a), Some(b)) if a < b),
            "conformance: conf_revisit_gate: `{later}` before the return: {r}"
        );
    }
}

// =========================================================================
// MIN-ENGINES E4 (the tester, gate 3; criteria/MIN-ENGINES-E4.md rev 1.4,
// E4-6 (a)–(d); derived §E4 items 1–5): the summary borrows the thread names,
// clones each value once, keys on the shape in one pass, and has no hint
// =========================================================================

/// A source check's window: the text of `src` from `head` to the first `end`
/// after it.
fn e4_window<'a>(src: &'a str, head: &str, end: &str) -> &'a str {
    let at = src.find(head).unwrap_or_else(|| panic!("conformance: no `{head}`"));
    let rest = &src[at..];
    &rest[..rest.find(end).unwrap_or_else(|| panic!("conformance: no end of `{head}`"))]
}

/// E4-6 (a), a source check (the gate-1 reading: no counter in
/// `exec_graph.rs`). The summary path's name resolution borrows the thread's
/// creation label: `get_thread_tclab`, which returns a cloned `TCreate`, is
/// named nowhere in `obs.rs` and not in `ctx.rs`'s spawn-order guard;
/// `resolve`, `is_visible` and `check_annotation_at` read `thread_name`, the
/// guard reads `thread_create_pos`, and both getters borrow
/// (`self.get_thr(&tid).tclab`). Fails before E4, where all four sites called
/// `get_thread_tclab`.
#[test]
fn e4_a_the_summary_path_borrows_the_thread_names() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let read = |p: &str| {
        std::fs::read_to_string(root.join(p)).unwrap_or_else(|_| panic!("conformance: {p}"))
    };
    let (obs, ctx, eg) = (
        read("conformance/obs.rs"),
        read("conformance/ctx.rs"),
        read("exec_graph.rs"),
    );
    let mut bad = Vec::new();
    if obs.contains("get_thread_tclab") {
        bad.push("obs.rs names `get_thread_tclab`".to_owned());
    }
    for head in [
        "fn resolve(",
        "pub(crate) fn is_visible(",
        "pub(crate) fn check_annotation_at(",
    ] {
        if !e4_window(&obs, head, "\n}\n").contains(".thread_name(") {
            bad.push(format!("obs.rs `{head}` does not read `thread_name`"));
        }
    }
    let guard = e4_window(&ctx, "pub(crate) fn check_spawn_order(", "\n}\n");
    if guard.contains("get_thread_tclab") || !guard.contains(".thread_create_pos(") {
        bad.push(format!("ctx.rs `check_spawn_order`: {guard}"));
    }
    for (head, borrow) in [
        (
            "pub(crate) fn thread_name(&self, tid: ThreadId) -> Option<&str> {",
            "self.get_thr(&tid).tclab.name().as_deref()",
        ),
        (
            "pub(crate) fn thread_create_pos(&self, tid: ThreadId) -> Event {",
            "self.get_thr(&tid).tclab.pos()",
        ),
    ] {
        let body = e4_window(&eg, head, "\n    }\n");
        if !body.contains(borrow) || body.contains("get_thread_tclab") {
            bad.push(format!("exec_graph.rs: {body}"));
        }
    }
    assert!(bad.is_empty(), "conformance: E4-6 (a): {bad:#?}");
}

/// E4-6 (b): one value clone per observation, read with the test-only
/// `OBS_CLONES` (`obs.rs`). `observe` constructs an `Obs` from the graph's
/// value, which is not a clone of an `Obs`, so the counter reads the second
/// clones only; a move is not a clone (the gate-1 reading). Over the size-2
/// cells' complete graphs (both sides, in the stateful engine's kept order),
/// the counter reads 0 around each summary path:
/// - `CompactSummary::at_completion`, the one function both engines'
///   completion sinks (`stateful.rs`'s specification and implementation
///   sinks, `cfirst.rs`'s implementation sink) and the complete-first sweep
///   call;
/// - `stateful::summarise` (the `Current` sinks);
/// - `FlatWitness::of`, on a probe of the specification graph, which offers
///   nothing;
/// - `WitnessCache::admit_from_sweep`, the `Current` witness admission.
/// Before E4 each read `O`, the graph's observations (summed over its rows):
/// `Sig::of` cloned every observation out of the borrowed `Wobs`. Around the
/// test-side `Families::new` (the grid oracle) the counter reads
/// `O_spec + O_impl`, before E4 and after: its shared helper `summary_of`
/// clones each family graph's `Wobs`. This is criteria E4-2's one `2·O` path
/// and not an engine path; it is said here, and it is pinned. `O > 0`, a
/// probe that completes, and the `Families` reading make the zeros
/// non-vacuous: the counter is this thread's, and every call runs here.
#[test]
fn e4_b_one_value_clone_per_observation_on_every_summary_path() {
    use crate::conformance::grid_oracle::Families;
    use crate::conformance::obs::{obs_clones_for_test, reset_obs_clones_for_test};
    use crate::conformance::prober::probe_from;
    use crate::conformance::witness::{FlatWitness, WitnessCache};
    fn around(f: impl FnOnce()) -> usize {
        reset_obs_clones_for_test();
        f();
        obs_clones_for_test()
    }
    let mut bad = Vec::new();
    let (mut graphs, mut observations, mut probes) = (0usize, 0usize, 0usize);
    for name in SIZE2_CELLS {
        let f = fx(name);
        let vis = &f.visible;
        let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
        let (spec, imp) = (&o.kept_spec_graphs, &o.kept_impl_graphs);
        let o_of = |gs: &[ExecutionGraph]| -> usize {
            gs.iter()
                .map(|g| {
                    let w = wobs(g, vis).expect("conformance: wobs");
                    w.names().map(|n| w.of(n).len()).sum::<usize>()
                })
                .sum()
        };
        let (o_spec, o_imp) = (o_of(spec), o_of(imp));
        graphs += spec.len() + imp.len();
        observations += o_spec + o_imp;
        let compact = around(|| {
            for g in spec.iter().chain(imp) {
                let _ = CompactSummary::at_completion(g, vis, "test");
            }
        });
        let current = around(|| {
            for g in spec.iter().chain(imp) {
                let _ = stateful::summarise(g, vis, "test");
            }
        });
        let mut flat = 0;
        for g in spec {
            let p = f.specification.clone();
            let probed = probe_from(cc.config.clone(), g.clone(), move || p());
            if probed.complete().is_none() {
                continue;
            }
            probes += 1;
            flat += around(|| {
                let w = FlatWitness::of(&probed, vis).expect("conformance: a flat witness");
                assert!(w.is_some(), "conformance: a complete probe's witness");
            });
        }
        let mut wc = WitnessCache::new(vis.clone());
        let mut admitted = 0usize;
        let admit = around(|| {
            for g in spec {
                let exec = CompleteExecution::assume_finished_at_gate(g);
                let new = wc.admit_from_sweep(exec).expect("conformance: an admission");
                admitted += usize::from(new);
            }
        });
        let families = around(|| {
            let _ = Families::new(spec, imp, 0, vis);
        });
        note!(
            "e4 (b) {name}: graphs {}+{} O {o_spec}+{o_imp}; at_completion {compact} \
             summarise {current} flat {flat} admit {admit} ({admitted} admitted) \
             families {families}",
            spec.len(),
            imp.len()
        );
        if (compact, current, flat, admit) != (0, 0, 0, 0) {
            bad.push(format!(
                "{name}: at_completion {compact} summarise {current} flat {flat} admit {admit}"
            ));
        }
        if families != o_spec + o_imp {
            bad.push(format!("{name}: families {families}, O {o_spec}+{o_imp}"));
        }
    }
    note!("e4 (b): {graphs} graphs, {observations} observations, {probes} complete probes");
    assert!(
        graphs > 0 && observations > 0 && probes > 0,
        "conformance: E4-6 (b) is not vacuous"
    );
    assert!(bad.is_empty(), "conformance: E4-6 (b): {bad:#?}");
}

/// `a` sends one value to `b`, which receives nothing: an `i64` if `wide`,
/// else an `i32` (E4-6 (c)'s pair of concrete types).
fn e4_one_send(wide: bool) -> crate::conformance::grid::Prog {
    crate::conformance::grid::prog(move || {
        let b = crate::thread::Builder::new()
            .name("b".to_owned())
            .spawn(|| {})
            .unwrap();
        let bid = b.thread().id();
        crate::thread::Builder::new()
            .name("a".to_owned())
            .spawn(move || {
                if wide {
                    crate::send_msg(bid, 1i64);
                } else {
                    crate::send_msg(bid, 1i32);
                }
            })
            .unwrap();
    })
}

/// E4-6 (c): the bucket key is a function of the shape.
/// (1) Equal `Sig` ⟹ equal `Sig::hash128`, and each compact summary's key is
/// its signature's `hash128`. This is checked over every pair of the size-2
/// cells' summaries (both sides) and `PN`'s, whose pair has equal `Sig` and
/// different renderings — the pair a rendering-keyed hash would split. It is
/// green before E4 and after, by design: the hash reads only kind, ⊥, the
/// concrete message type and status, and `msg_equals` downcasts to one type.
/// (Since gate 4's M1 the type is read as its `TypeId`, what `msg_equals`
/// downcasts on; before, as the public `type_name` string — the regression is
/// `e4_m1_a_reassigned_type_name_keeps_the_bucket`.) The record's summaries
/// are checked in `e1_record`'s `E4C` line.
/// (2) A differing status, word length or concrete type ⟹ a differing hash
/// (with overwhelming probability): `b`'s status flipped through
/// `Sig::from_rows`; `a` sending one value against two; one `i32` against one
/// `i64`.
#[test]
fn e4_c_the_bucket_key_is_a_function_of_the_shape() {
    use crate::conformance::morphism::{statuses, Status};
    let mut bad = Vec::new();
    let (mut pairs, mut equal, mut split) = (0usize, 0usize, 0usize);
    let mut fixtures: Vec<Fixture> = SIZE2_CELLS.iter().map(|n| fx(n)).collect();
    fixtures.push(local_fixture("compact/e4-noisy", pn_prog(), pn_prog(), &["a", "r"]));
    for f in &fixtures {
        let (spec, imp) = kept_summaries(f);
        let all: Vec<&CompactSummary> = spec.iter().chain(&imp).collect();
        let shown: Vec<String> = all.iter().map(|s| format!("{:?}", s.sig)).collect();
        for (i, a) in all.iter().enumerate() {
            if a.hash != a.sig.hash128() {
                bad.push(format!("{}: summary {i}'s key is not its hash128", f.name));
            }
            for (j, b) in all.iter().enumerate().skip(i + 1) {
                pairs += 1;
                if a.sig == b.sig {
                    equal += 1;
                    split += usize::from(shown[i] != shown[j]);
                    if a.hash != b.hash {
                        bad.push(format!("{}: summaries {i}, {j}: equal Sig, two hashes", f.name));
                    }
                }
            }
        }
    }
    note!("e4 (c): {pairs} pairs, {equal} with equal Sig, {split} of those rendered apart");
    assert!(equal > 0 && split > 0, "conformance: E4-6 (c) (1) is not vacuous");
    // (2) Word length: one send against two.
    let sig_of = |g: &ExecutionGraph, vis: &[String]| -> Sig {
        let w = wobs(g, vis).expect("conformance: wobs");
        Sig::of(CompleteExecution::try_finished(g).unwrap(), w, vis)
            .expect("conformance: a signature")
    };
    let (g1, vis) = sends_graph(1);
    let (g2, _) = sends_graph(2);
    let (one, two) = (sig_of(&g1, &vis), sig_of(&g2, &vis));
    assert_eq!((one.word("a").len(), two.word("a").len()), (1, 2));
    if one.hash128() == two.hash128() {
        bad.push("word length: one hash".to_owned());
    }
    // Status: `b`'s flipped, the rows the same.
    let exec = CompleteExecution::try_finished(&g1).unwrap();
    let w = wobs(&g1, &vis).expect("conformance: wobs");
    let st = statuses(exec, &w, &vis).expect("conformance: statuses");
    let mut flipped = st.clone();
    let b = flipped.get_mut("b").expect("conformance: `b`'s status");
    *b = if *b == Status::Done { Status::Blocked } else { Status::Done };
    let same = Sig::from_rows(st, w.clone(), &vis);
    let other = Sig::from_rows(flipped, w, &vis);
    assert!(same == one && other != one, "conformance: the status pair");
    if same.hash128() == other.hash128() {
        bad.push("status: one hash".to_owned());
    }
    // The concrete type: an `i32` against an `i64`, one send each.
    let one_send = |wide: bool| -> CompactSummary {
        let p = e4_one_send(wide);
        let f = local_fixture("compact/e4-type", p.clone(), p, &["a", "b"]);
        let (spec, _) = kept_summaries(&f);
        assert_eq!(spec.len(), 1, "conformance: one execution");
        spec.into_iter().next().unwrap()
    };
    let (narrow, wide) = (one_send(false), one_send(true));
    assert!(
        narrow.sig != wide.sig
            && narrow.sig.word("a").len() == 1
            && wide.sig.word("a").len() == 1
            && narrow.sig.status("a") == wide.sig.status("a")
            && narrow.sig.status("b") == wide.sig.status("b"),
        "conformance: the `i32`/`i64` pair differs in the concrete type only"
    );
    if narrow.hash == wide.hash {
        bad.push("concrete type: one hash".to_owned());
    }
    assert!(bad.is_empty(), "conformance: E4-6 (c): {bad:#?}");
}

/// A summary in `base`'s bucket and with `base`'s counts, carrying `other`'s
/// real signature (`forged`'s construction, another source).
fn e4_into_bucket(base: &CompactSummary, other: &str) -> CompactSummary {
    let o = real_summary(other);
    CompactSummary {
        hash: base.hash,
        ord: base.ord.clone(),
        sig: o.sig,
        sig_est: o.sig_est,
    }
}

/// E4-6 (d): no rendering hint. A source check: `render_hash` has one body,
/// `None`, and `compact.rs` names `print_vals` only in comments, so there is
/// no feature-gated variant and the hint maps stay empty under both feature
/// sets. Then a built three-slot bucket — one shape hash with three
/// signatures: `MECH_CELL`'s, and forged with 2pc n2's and A3 fifo k2q2's —
/// in `CompactIndex` and in `SetIndex`:
/// - inserting the slot-k signature costs k `Sig` tests;
/// - a query of slot k's signature costs k + 1, on every repeat (the hint
///   answered a repeat at 1);
/// - a signature with no slot (A1 correct n2r2's) costs 3 and is `NoSig`;
/// - `PN`'s pair (equal `Sig`, different renderings) is one slot, and its
///   second insertion is a duplicate at one test;
/// - `sig_aliases` stays 0.
/// Fails before E4 under `print_vals` (the default features): the repeated
/// queries, and `PN`'s alias.
#[test]
fn e4_d_no_rendering_hint() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let src = std::fs::read_to_string(root.join("conformance/compact.rs"))
        .expect("conformance: compact.rs");
    let code: Vec<&str> = src.lines().filter(|l| !l.trim_start().starts_with("//")).collect();
    let code = code.join("\n");
    assert!(!code.contains("print_vals"), "conformance: a `print_vals` gate in compact.rs");
    assert_eq!(code.matches("fn render_hash(").count(), 1, "conformance: one `render_hash`");
    let body = e4_window(&code, "fn render_hash(", "\n}");
    assert_eq!(
        body[body.find('{').expect("conformance: a body") + 1..].trim(),
        "None",
        "conformance: `render_hash`'s body"
    );
    let base = real_summary(MECH_CELL);
    let slots = [
        base.clone(),
        e4_into_bucket(&base, "2pc/leader/conf/n2"),
        e4_into_bucket(&base, "apps/a3/fifo/spec/k2q2"),
    ];
    let stranger = e4_into_bucket(&base, "apps/a1/correct/spec/n2r2");
    let sigs = [&slots[0].sig, &slots[1].sig, &slots[2].sig, &stranger.sig];
    for (i, a) in sigs.iter().enumerate() {
        for b in &sigs[i + 1..] {
            assert!(a != b, "conformance: four signatures");
        }
    }
    let pn = local_fixture("compact/e4-noisy", pn_prog(), pn_prog(), &["a", "r"]);
    let (pn_spec, _) = kept_summaries(&pn);
    assert!(pn_spec.len() == 2 && pn_spec[0].sig == pn_spec[1].sig);
    let mut bad = Vec::new();
    // The compact index.
    let mut ix = CompactIndex::new(true);
    for (k, s) in slots.iter().enumerate() {
        let t = ix.stats().sig_tests;
        let (id, ins) = ix.insert(s);
        let cost = ix.stats().sig_tests - t;
        if id as usize != k || !matches!(ins, Inserted::Stored(_)) || cost != k {
            bad.push(format!("compact insert {k}: ({id}, {ins:?}) at {cost} tests"));
        }
    }
    for round in 0..2 {
        for k in [2, 0, 1] {
            let t = ix.stats().sig_tests;
            let got = ix.covers(&slots[k]);
            let cost = ix.stats().sig_tests - t;
            if got.0 != Some(k as u32) || !matches!(got.1, Covers::Found(_)) || cost != k + 1 {
                bad.push(format!("compact query {round}/{k}: {got:?} at {cost} tests"));
            }
        }
    }
    let t = ix.stats().sig_tests;
    let got = ix.covers(&stranger);
    let cost = ix.stats().sig_tests - t;
    if got != (None, Covers::NoSig) || cost != 3 {
        bad.push(format!("compact stranger: {got:?} at {cost} tests"));
    }
    if ix.stats().sig_aliases != 0 {
        bad.push(format!("compact sig_aliases {}", ix.stats().sig_aliases));
    }
    let mut ix = CompactIndex::new(true);
    ix.insert(&pn_spec[0]);
    let t = ix.stats().sig_tests;
    let got = ix.insert(&pn_spec[1]);
    let cost = ix.stats().sig_tests - t;
    if got != (0, Inserted::Duplicate) || cost != 1 || ix.stats().sig_aliases != 0 {
        bad.push(format!("compact PN: {got:?} at {cost} tests, {:?}", ix.stats().sig_aliases));
    }
    // The set index.
    let mut set = SetIndex::new();
    for (k, s) in slots.iter().enumerate() {
        let t = set.stats().sig_tests;
        let (id, ins) = set.insert(s);
        let cost = set.stats().sig_tests - t;
        if id as usize != k || !matches!(ins, Inserted::Stored(_)) || cost != k {
            bad.push(format!("set insert {k}: ({id}, {ins:?}) at {cost} tests"));
        }
    }
    for round in 0..2 {
        for k in [2, 0, 1] {
            let t = set.stats().sig_tests;
            let got = set.covers(&slots[k]);
            let cost = set.stats().sig_tests - t;
            if got.0 != Some(k as u32) || !matches!(got.1, Covers::Found(_)) || cost != k + 1 {
                bad.push(format!("set query {round}/{k}: {got:?} at {cost} tests"));
            }
        }
    }
    let t = set.stats().sig_tests;
    let got = set.covers(&stranger);
    let cost = set.stats().sig_tests - t;
    if got != (None, Covers::NoSig) || cost != 3 {
        bad.push(format!("set stranger: {got:?} at {cost} tests"));
    }
    if set.stats().sig_aliases != 0 {
        bad.push(format!("set sig_aliases {}", set.stats().sig_aliases));
    }
    let mut set = SetIndex::new();
    set.insert(&pn_spec[0]);
    let t = set.stats().sig_tests;
    let got = set.insert(&pn_spec[1]);
    let cost = set.stats().sig_tests - t;
    if got != (0, Inserted::Duplicate) || cost != 1 || set.stats().sig_aliases != 0 {
        bad.push(format!("set PN: {got:?} at {cost} tests, {:?}", set.stats().sig_aliases));
    }
    assert!(bad.is_empty(), "conformance: E4-6 (d): {bad:#?}");
}

/// E4 gate 4 round 01 M1 (Codex), the regression. `Val::type_name` is a public
/// `String` that takes no part in equality (`msg_equals` downcasts to the
/// concrete type; `Obs::eq` ignores the name), so the bucket key must not read
/// it. A graph and its copy whose one send has its value's `type_name`
/// reassigned give equal observations and equal signatures with different
/// public type names, and must give:
/// - equal `hash128` (and equal compact keys);
/// - one slot in `SigBuckets` (`entry` twice, `get` of either: one key bucket);
/// - one slot in the compact bucket's `Sig ==` resolution, in `CompactIndex`
///   and in `SetIndex`: the copy's insertion a `Duplicate` of the original's
///   slot, each one's query `Found` there, `sig_aliases` 0.
/// Fails on the type-name-hashing body (`sig.rs` 65a044c5, kept below as a
/// reference over the same byte stream): it gives the pair two keys, so every
/// index above put the copy in a bucket of its own (`SigKey` had the same
/// defect: `COMPACT-INDEX-P2-CODE` reopened).
#[test]
fn e4_m1_a_reassigned_type_name_keeps_the_bucket() {
    use crate::conformance::morphism::Status;
    use crate::conformance::obs::Obs;
    use crate::conformance::sig::SigBuckets;
    let (g, vis) = sends_graph(1);
    let e = wobs(&g, &vis).expect("conformance: wobs").of("a")[0].0;
    let mut forged = g.clone();
    let val = &mut forged.send_label_mut(e).expect("conformance: `a`'s send").val;
    let original = val.clone();
    val.type_name = format!("forged::{}", val.type_name);
    assert!(
        *val == original && val.type_name != original.type_name,
        "conformance: equal values, different public type names"
    );
    let summary = |g: &ExecutionGraph| -> CompactSummary {
        let exec = CompleteExecution::try_finished(g).expect("conformance: complete");
        CompactSummary::of(exec, wobs(g, &vis).expect("conformance: wobs"), &vis)
            .expect("conformance: a summary")
    };
    let (s, t) = (summary(&g), summary(&forged));
    let names = |s: &CompactSummary| -> Vec<String> {
        s.sig.word("a").iter().filter_map(|o| o.type_name().map(str::to_owned)).collect()
    };
    assert!(
        s.sig.word("a") == t.sig.word("a") && s.sig == t.sig && names(&s) != names(&t),
        "conformance: equal observations and signatures, different type names"
    );
    // The pre-fix body: per name (sorted) its length and bytes, the word's
    // length, per observation a kind tag and the `type_name` string's length
    // and bytes; per status name its length, bytes and tag.
    let by_type_name = |sig: &Sig| -> u128 {
        use std::hash::Hasher as _;
        let mut a = std::collections::hash_map::DefaultHasher::new();
        let mut b = std::collections::hash_map::DefaultHasher::new();
        a.write_u64(0x5f3759df);
        b.write_u64(0x9e3779b97f4a7c15);
        let mut put = |bytes: &[u8]| {
            a.write(bytes);
            b.write(bytes);
        };
        let mut names: Vec<&String> = vis.iter().collect();
        names.sort();
        names.dedup();
        for n in &names {
            let word = sig.word(n);
            put(&(n.len() as u64).to_le_bytes());
            put(n.as_bytes());
            put(&(word.len() as u64).to_le_bytes());
            for o in word {
                let (tag, ty) = match o {
                    Obs::Send(v) => (0u8, v.type_name.as_str()),
                    Obs::Recv(Some(v)) => (1, v.type_name.as_str()),
                    Obs::Recv(None) => (2, ""),
                };
                put(&[tag]);
                put(&(ty.len() as u64).to_le_bytes());
                put(ty.as_bytes());
            }
        }
        for n in &names {
            put(&(n.len() as u64).to_le_bytes());
            put(n.as_bytes());
            put(&[match sig.status(n).expect("conformance: a status") {
                Status::Errored => 0,
                Status::Done => 1,
                Status::Blocked => 2,
            }]);
        }
        ((a.finish() as u128) << 64) | b.finish() as u128
    };
    assert_ne!(
        by_type_name(&s.sig),
        by_type_name(&t.sig),
        "conformance: the type-name-hashing body splits the pair"
    );
    let mut bad = Vec::new();
    if s.sig.hash128() != t.sig.hash128() || s.hash != t.hash {
        bad.push("hash128 differs: the key reads the public type name".to_owned());
    }
    // `SigBuckets`: `entry` with each, `get` with each.
    let mut sb: SigBuckets<usize> = SigBuckets::new();
    *sb.entry(s.sig.clone(), || 0) += 1;
    *sb.entry(t.sig.clone(), || 0) += 1;
    let got = (sb.len(), sb.key_buckets(), sb.get(&s.sig).copied(), sb.get(&t.sig).copied());
    if got != (1, 1, Some(2), Some(2)) {
        bad.push(format!("SigBuckets (len, key_buckets, get s, get t): {got:?}"));
    }
    // The compact index, either insertion first.
    for (what, a, b) in [("compact s, t", &s, &t), ("compact t, s", &t, &s)] {
        let mut ix = CompactIndex::new(true);
        let first = ix.insert(a);
        let second = ix.insert(b);
        let (qa, qb) = (ix.covers(a), ix.covers(b));
        let st = ix.stats();
        let got = (st.buckets, st.signatures, st.signatures_seen, st.sig_aliases);
        if second != (first.0, Inserted::Duplicate)
            || qa != (Some(first.0), Covers::Found(0))
            || qb != (Some(first.0), Covers::Found(0))
            || got != (1, 1, 1, 0)
        {
            bad.push(format!("{what}: {first:?} {second:?} {qa:?} {qb:?} {got:?}"));
        }
    }
    // The set index, either insertion first.
    for (what, a, b) in [("set s, t", &s, &t), ("set t, s", &t, &s)] {
        let mut ix = SetIndex::new();
        let first = ix.insert(a);
        let second = ix.insert(b);
        let (qa, qb) = (ix.covers(a), ix.covers(b));
        let st = ix.stats();
        let got = (st.buckets, st.signatures, st.signatures_seen, st.sig_aliases);
        if second != (first.0, Inserted::Duplicate)
            || qa != (Some(first.0), Covers::Found(0))
            || qb != (Some(first.0), Covers::Found(0))
            || got != (1, 1, 1, 0)
        {
            bad.push(format!("{what}: {first:?} {second:?} {qa:?} {qb:?} {got:?}"));
        }
    }
    assert!(bad.is_empty(), "conformance: gate-4 M1: {bad:#?}");
}

// =========================================================================
// MIN-ENGINES E6 (the tester, gate 3; criteria/MIN-ENGINES-E6.md rev 1.1,
// E6-6 (a)–(e); derived §E6): every report counted; the first report's graph,
// snapshot and dump kept; the rest behind `all_reports` (off)
// =========================================================================

/// `cc` with every report kept (`all_reports` on): the list's tests (E6-6 (e)).
/// `MIN-ENGINES` E7a (the tester, gate 3): and the sweep record on — its users
/// (T1, m6, m11's complete-first pair, the record's parts) compare the sweep
/// sizes too, which the default would leave empty on both sides.
fn e6_all(mut cc: crate::conformance::ConfConfig) -> crate::conformance::ConfConfig {
    cc.all_reports = true;
    cc.sweep_record = true;
    cc
}

/// E6-6 (b)'s violating fixtures (the record's `N`: 2, 4, 5, 24) and one
/// conforming fixture (`N` = 0).
const E6_FIXTURES: [&str; 5] = [
    "apps/a1/correct/spec/n2r1",
    "apps/a2/silent-put/spec/k2q1",
    "apps/a3/double-grant/spec/k2q1",
    "apps/a1/eager/spec/n2r1",
    "e1:race-bad/bag",
];

/// E6-6 (a), a source check of the three sites (`stateful.rs` one,
/// `cfirst.rs` two): each increments the counter, and only then tests
/// `all_reports || st.reports.is_empty()`; the snapshot and the graph clone
/// are inside that test; no other `replay_snapshot(g, must_state` in the two
/// files. Fails before E6 (no retention test).
#[test]
fn e6_a_the_sites_count_then_keep_the_first() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut bad = Vec::new();
    for (file, sites) in [("conformance/stateful.rs", 1), ("conformance/cfirst.rs", 2)] {
        let src = std::fs::read_to_string(root.join(file)).expect("conformance: a source file");
        let at: Vec<usize> =
            src.match_indices("st.counters.reports += 1;").map(|(i, _)| i).collect();
        if at.len() != sites {
            bad.push(format!("{file}: {} counter sites", at.len()));
        }
        for i in at {
            // `MIN-ENGINES` E9 (the tester's re-pin at gate 3): the first-report
            // reader's call now sits between the counter and the retention
            // test (E9-2), so the window is 1400 bytes (was 900).
            let w = &src[i..(i + 1400).min(src.len())];
            let (knob, empty) = (w.find("all_reports"), w.find("st.reports.is_empty()"));
            let snap = w.find("replay_snapshot(g, must_state");
            let push = w.find("st.reports.push(");
            let ok = matches!(
                (knob, empty, snap, push),
                (Some(k), Some(e), Some(s), Some(p)) if k < s && e < s && s < p
            );
            if !ok {
                bad.push(format!("{file} at {i}: {knob:?} {empty:?} {snap:?} {push:?}"));
            }
        }
        let snaps = src.matches("replay_snapshot(g, must_state").count();
        if snaps != sites {
            bad.push(format!("{file}: {snaps} snapshot calls"));
        }
    }
    assert!(bad.is_empty(), "conformance: E6-6 (a): {bad:#?}");
}

/// The first entries of two report lists, compared: graph text and the
/// snapshot through [`normalised`] (two runs' snapshots differ in
/// per-instance hash-map order, as T1 measured).
fn e6_first(
    what: &str,
    on: &[(ExecutionGraph, crate::conformance::report::ReplaySnapshot)],
    off: &[(ExecutionGraph, crate::conformance::report::ReplaySnapshot)],
    bad: &mut Vec<String>,
) {
    if let (Some(a), Some(b)) = (on.first(), off.first()) {
        if a.0.to_string() != b.0.to_string() {
            bad.push(format!("{what}: the first graph differs"));
        }
        if normalised(&a.1) != normalised(&b.1) {
            bad.push(format!("{what}: the first snapshot differs"));
        }
    }
}

/// One grid column of `row`.
fn e6_col(row: &crate::conformance::grid::Row, k: &str) -> String {
    row.iter()
        .find(|(c, _)| *c == k)
        .map(|(_, v)| v.clone())
        .unwrap_or_else(|| panic!("conformance: no `{k}` column"))
}

/// E6-6 (b): the knob off against on, on [`E6_FIXTURES`] × stateful under
/// `Current`/`Compact`/`Set` and complete-first under `Current`/`Compact` ×
/// stop-at-first off/on, through the grid (`run_grid`, the row too). With N
/// the knob-on list's length: both counters N; the off list min(N, 1); the
/// first graph and snapshot equal; the verdict and the end equal; the grid's
/// `reports` and `counter_reports` columns equal (`reports` from the counter);
/// complete-first's first-report columns present iff N ≥ 1 on both, and
/// `paper_events_at_first_report(grid)` equal. Complete-first × `Set` is
/// built (`MIN-ENGINES` E7b admits it; refused before). Then the public route, both
/// engines under `Current`: `report_count` N on both; `reports()` N on, min(N,
/// 1) off; the first `ConfReport`'s dump, tag, gate, events and (normalised)
/// snapshot equal. Fails before E6: the off list is N long.
#[test]
fn e6_b_the_knob_off_against_on() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::x1_config;
    use crate::conformance::grid::{row_of, run_grid, GridEnd, GridRaw};
    use crate::conformance::selector::Selector;
    let mut bad = Vec::new();
    let (mut runs, mut many) = (0usize, 0usize);
    for name in E6_FIXTURES {
        let f = e1_fixture(name);
        let mut cfgs = Vec::new();
        for k in [IndexKind::Current, IndexKind::Compact, IndexKind::Set] {
            for stop in [false, true] {
                cfgs.push(x1_config(GridEngine::Stateful, Selector::Ltr).index(k).stop(stop));
            }
        }
        for k in [IndexKind::Current, IndexKind::Compact] {
            for stop in [false, true] {
                let g = x1_config(GridEngine::CompleteFirst, Selector::Ltr).quiet(true);
                cfgs.push(g.index(k).stop(stop));
            }
        }
        for g in cfgs {
            let run = |on: bool| {
                let mut g = g.clone();
                g.all_reports = on;
                match run_grid(&f, &g, None) {
                    GridEnd::Ok(r) => r,
                    other => panic!("conformance: {name}: {other:?}"),
                }
            };
            let (on, off) = (run(true), run(false));
            let what = format!("{name} {}", g.label());
            runs += 1;
            let n = match (&on.raw, &off.raw) {
                (GridRaw::Stateful(a), GridRaw::Stateful(b)) => {
                    let n = a.reports.len();
                    let got = (a.counters.reports, b.counters.reports, b.reports.len());
                    if got != (n, n, n.min(1)) || a.impl_end != b.impl_end {
                        bad.push(format!("{what}: (on, off, kept) {got:?}, N {n}"));
                    }
                    e6_first(&what, &a.reports, &b.reports, &mut bad);
                    n
                }
                (GridRaw::CompleteFirst(a), GridRaw::CompleteFirst(b)) => {
                    let n = a.reports.len();
                    let got = (a.counters.reports, b.counters.reports, b.reports.len());
                    if got != (n, n, n.min(1))
                        || a.impl_end != b.impl_end
                        || a.cut_reports.len() != b.cut_reports.len()
                    {
                        bad.push(format!("{what}: (on, off, kept) {got:?}, N {n}"));
                    }
                    let first = |c: &crate::conformance::CFirstCounters| {
                        let w = c.wall_ms_at_first_report.is_some();
                        (w, c.vmhwm_kb_at_first_report.is_some())
                    };
                    let (fa, fb) = (first(&a.counters), first(&b.counters));
                    if fa.0 != (n >= 1) || fa != fb {
                        bad.push(format!("{what}: the first-report columns {fa:?} {fb:?}"));
                    }
                    e6_first(&what, &a.reports, &b.reports, &mut bad);
                    n
                }
                _ => panic!("conformance: {what}: an unexpected outcome"),
            };
            many += usize::from(n >= 2);
            let (ra, rb) = (row_of(&on), row_of(&off));
            for col in ["reports", "counter_reports"] {
                if e6_col(&ra, col) != e6_col(&rb, col) || e6_col(&ra, col) != n.to_string() {
                    bad.push(format!("{what}: column `{col}`"));
                }
            }
            if g.engine == GridEngine::CompleteFirst {
                let col = "paper_events_at_first_report(grid)";
                if e6_col(&ra, col) != e6_col(&rb, col) {
                    bad.push(format!("{what}: column `{col}`"));
                }
            }
        }
        // `MIN-ENGINES` E7b (the tester's re-pin at gate 3): complete-first ×
        // `Set` is admitted (refused since I2b; E7b-5 (c) is s14).
        let set = x1_config(GridEngine::CompleteFirst, Selector::Ltr).index(IndexKind::Set);
        if set.conf_config(&f).index != IndexKind::Set {
            bad.push(format!("{name}: complete-first × Set not built"));
        }
        // The public route.
        for engine in [GridEngine::Stateful, GridEngine::CompleteFirst] {
            let public = |on: bool| {
                let mut cc = x1_config(engine, Selector::Ltr).quiet(true).conf_config(&f);
                cc.all_reports = on;
                crate::conformance::run(cc, f.implementation.clone(), f.specification.clone())
                    .unwrap_or_else(|e| panic!("conformance: {name}: {e:?}"))
            };
            let (a, b) = (public(true), public(false));
            let (a, b) = (a.outcome(), b.outcome());
            let n = a.reports().len();
            let what = format!("{name} {engine:?} public");
            let got = (a.report_count(), b.report_count(), b.reports().len());
            if got != (n, n, n.min(1)) {
                bad.push(format!("{what}: (on, off, kept) {got:?}, N {n}"));
            }
            if let (Some(x), Some(y)) = (a.reports().first(), b.reports().first()) {
                if (x.graph_dump(), x.tag(), x.gate(), x.events())
                    != (y.graph_dump(), y.tag(), y.gate(), y.events())
                    || normalised(x.replay_snapshot()) != normalised(y.replay_snapshot())
                {
                    bad.push(format!("{what}: the first report differs"));
                }
            }
        }
    }
    note!("e6 (b): {runs} configurations, {many} with N ≥ 2");
    assert!(many > 0, "conformance: E6-6 (b) is not vacuous");
    assert!(bad.is_empty(), "conformance: E6-6 (b): {bad:#?}");
}

/// E6-6 (c): the test-only snapshot counter (`report.rs`), on this thread
/// (the engines' completion sinks run here; `run_grid` would not). On A1
/// eager n2r1 (N = 5) and A1 correct n2r1 (N = 0), stateful and
/// complete-first: min(N, 1) snapshots with the knob off, N with it on.
/// Fails before E6: off took N.
#[test]
fn e6_c_later_snapshots_are_not_computed() {
    use crate::conformance::eval::x1_config;
    use crate::conformance::report::{replay_snapshots_for_test, reset_replay_snapshots_for_test};
    use crate::conformance::selector::Selector;
    let mut bad = Vec::new();
    let mut seen = Vec::new();
    for name in ["apps/a1/eager/spec/n2r1", "apps/a1/correct/spec/n2r1"] {
        let f = e1_fixture(name);
        for engine in [GridEngine::Stateful, GridEngine::CompleteFirst] {
            for on in [false, true] {
                let mut cc = x1_config(engine, Selector::Ltr).quiet(true).conf_config(&f);
                cc.all_reports = on;
                let (imp, spec) = (&f.implementation, &f.specification);
                reset_replay_snapshots_for_test();
                let n = if engine == GridEngine::Stateful {
                    stateful::run_with(&cc, imp, spec, false).counters.reports
                } else {
                    crate::conformance::cfirst::run_with(&cc, imp, spec, false).counters.reports
                };
                let s = replay_snapshots_for_test();
                seen.push((name, engine, on, n, s));
                if s != if on { n } else { n.min(1) } {
                    bad.push(format!("{name} {engine:?} on={on}: N {n}, {s} snapshots"));
                }
            }
        }
    }
    note!("e6 (c): {seen:?}");
    assert!(
        seen.iter().any(|&(_, _, on, n, s)| on && n >= 2 && s == n),
        "conformance: E6-6 (c) is not vacuous"
    );
    assert!(bad.is_empty(), "conformance: E6-6 (c): {bad:#?}");
}

/// E6-6 (d)'s cut fixture: visible `a` and `r`; `r` receives one `i32` from one
/// of the invisible senders and forwards it to `a`. The implementation's
/// senders send 1, 2 and 3 and `a` asserts the value is not 3; the
/// specification's one sender sends 7 and `a` asserts nothing. Complete-first
/// with the cut on: two uncovered completions (1, 2) and one cut report (3's
/// visible failure); with the cut off three uncovered completions.
fn e6_cut_prog(spec: bool) -> crate::conformance::grid::Prog {
    crate::conformance::grid::prog(move || {
        let a = crate::thread::Builder::new()
            .name("a".to_owned())
            .spawn(move || {
                let y: i32 = crate::recv_msg_block();
                if !spec {
                    crate::assert(y != 3);
                }
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
        let vals: Vec<i32> = if spec { vec![7] } else { vec![1, 2, 3] };
        for (k, v) in vals.into_iter().enumerate() {
            crate::thread::Builder::new()
                .name(format!("s{k}"))
                .spawn(move || crate::send_msg(rid, v))
                .unwrap();
        }
    })
}

/// E6-6 (d): the rendering counts what it does not list (rev 1.1; Codex's
/// readings: N completion reports, C cut reports; knob off: the header N + C,
/// kept min(N, 1) + C, the elision N − 1 when N ≥ 1, `not_a_certificate`'s
/// count N + C; knob on: N + C kept, no elision; the "exactly" sentence of N
/// alone, complete-first's only when the outer run completed and no cut fired,
/// the stateful one under its completed enumerations). Pinned:
/// - A1 eager n2r1 (N = 5), stateful and complete-first (cut off): off, the
///   header "5 candidate violation(s)", "The list holds 1 of them; 4 further
///   candidate violation(s) counted, not kept (ConfBuilder::all_reports).",
///   "There are exactly 5 " and the engine's tail; on, the same header and
///   sentence and no elision line;
/// - [`e6_cut_prog`] under complete-first with the cut on (N = 2, C = 1): off,
///   the header 3, kept 2 (one completion report, the cut report), "The list
///   holds 2 of them; 1 further …", `not_a_certificate` `Reported { count: 3 }`,
///   the cut line and no "exactly" sentence; on, kept 3 and no elision; with the
///   cut off (N = 3, C = 0): the header 3, kept 1 off, "There are exactly 3 ".
/// Fails before E6: the header counted the list and the sentence was "The list
/// is exactly the set".
#[test]
fn e6_d_the_rendering_counts_what_it_does_not_list() {
    use crate::conformance::eval::x1_config;
    use crate::conformance::report::{
        CFIRST_CUT_PREFIXES, CFIRST_EXACTLY_THE_SET, STATEFUL_EXACTLY_THE_SET,
    };
    use crate::conformance::selector::Selector;
    use crate::conformance::{ConfBuilder, ConfVerdict, Engine, NotACertificate};
    let elision = |kept: usize, more: usize| {
        format!(
            "The list holds {kept} of them; {more} further candidate violation(s) counted, \
             not kept (ConfBuilder::all_reports)."
        )
    };
    let mut bad = Vec::new();
    // A1 eager n2r1, N = 5, both engines, the cut off.
    let f = e1_fixture("apps/a1/eager/spec/n2r1");
    for (engine, tail) in [
        (GridEngine::Stateful, STATEFUL_EXACTLY_THE_SET),
        (GridEngine::CompleteFirst, CFIRST_EXACTLY_THE_SET),
    ] {
        for on in [false, true] {
            let mut cc = x1_config(engine, Selector::Ltr).quiet(true).conf_config(&f);
            cc.all_reports = on;
            let v = crate::conformance::run(cc, f.implementation.clone(), f.specification.clone())
                .unwrap_or_else(|e| panic!("conformance: {e:?}"));
            let s = v.to_string();
            let o = v.outcome();
            let what = format!("eager {engine:?} on={on}");
            let kept = if on { 5 } else { 1 };
            if !matches!(v, ConfVerdict::Reported(_))
                || (o.report_count(), o.reports().len()) != (5, kept)
                || !s.contains("conformance: 5 candidate violation(s).")
                || s.contains(&elision(1, 4)) == on
                || s.contains("The list holds") == on
                || !s.contains(&format!("There are exactly 5 {tail}"))
                || s.contains("The list is exactly")
            {
                bad.push(format!("{what}: {s}"));
            }
        }
    }
    // The cut fixture, complete-first.
    let f = local_fixture("compact/e6-cut", e6_cut_prog(true), e6_cut_prog(false), &["a", "r"]);
    for (cut, on) in [(true, false), (true, true), (false, false), (false, true)] {
        let cc = ConfBuilder::new()
            .config(f.config.clone())
            .visible_threads(f.visible.clone())
            .engine(Engine::CompleteFirst)
            .early_error_cut(cut)
            .all_reports(on)
            .build()
            .expect("conformance: in scope");
        let v = crate::conformance::run(cc, f.implementation.clone(), f.specification.clone())
            .unwrap_or_else(|e| panic!("conformance: {e:?}"));
        let s = v.to_string();
        let o = v.outcome();
        let c = o.cfirst_counters().expect("conformance: complete-first counters");
        let what = format!("cut={cut} on={on}");
        let (n, k) = (c.reports, c.cut_reports);
        let want_nk = if cut { (2, 1) } else { (3, 0) };
        let kept = if on { n + k } else { n.min(1) + k };
        let reported = o
            .not_a_certificate()
            .into_iter()
            .any(|x| matches!(x, NotACertificate::Reported { count } if count == n + k));
        let exactly = format!("There are exactly {n} {CFIRST_EXACTLY_THE_SET}");
        if (n, k) != want_nk
            || (o.report_count(), o.reports().len()) != (n + k, kept)
            || !reported
            || !s.contains(&format!("conformance: {} candidate violation(s).", n + k))
            || s.contains(&elision(kept, n + k - kept)) == on
            || s.contains("The list holds") == on
            || s.contains(&exactly) == cut
            || s.contains(CFIRST_CUT_PREFIXES) != cut
        {
            bad.push(format!("{what}: N {n} C {k} kept {}: {s}", o.reports().len()));
        }
    }
    assert!(bad.is_empty(), "conformance: E6-6 (d): {bad:#?}");
}

// =========================================================================
// MIN-ENGINES E7a (the tester, gate 3; criteria/MIN-ENGINES-E7A.md rev 1.3,
// E7a-6 (a)–(f); derived §E7): the compact summary end to end on the
// stateless engine, the probe memo off by default, the sweep record behind a
// knob
// =========================================================================

/// The before-state of the record's engine parts (E7a-5 (i)): `index`, the
/// memo on, the sweep record on, every report kept (E6).
fn e7_before(
    cc: crate::conformance::ConfConfig,
    index: crate::conformance::config::IndexKind,
) -> crate::conformance::ConfConfig {
    let mut cc = e6_all(cc);
    cc.index = index;
    cc.probe_memo = true;
    cc.sweep_record = true;
    cc
}

/// The E7 record of a stateless outcome (rev 1.3): the verdict class, the md5
/// of the sorted uncovered lines, the fifteen counters, the `sweep_ends` text
/// from the scalars and `sweep_sizes` entry by entry.
fn e7_record(
    o: &crate::conformance::cfirst::CFirstOutcome,
    line_of: &dyn Fn(&ExecutionGraph) -> String,
) -> String {
    let c = &o.counters;
    let mut unc: Vec<String> = o.reports.iter().map(|(g, _)| line_of(g)).collect();
    unc.sort();
    let unc = crate::conformance::campaign_tests::md5_hex(unc.join("\n").as_bytes());
    let verdict = if c.reports + c.cut_reports > 0 { "reported" } else { "conforms" };
    format!(
        "verdict {verdict}\tunc {unc}\timpl_graphs {}\tcache_probes {}\tcache_hits {}\t\
         sweeps {}\tsweeps_successful {}\tsweeps_failing {}\tsweeps_aborted {}\t\
         sweep_graphs {}\tsweep_graphs_max {}\tadmissions {}\tevictions {}\treadmissions {}\t\
         reports {}\tcut_reports {}\timpl_end {:?}\t\
         sweep_ends witness={} exhausted={} aborted={} budgeted=0\tsweep_sizes {:?}",
        c.impl_graphs,
        c.cache_probes,
        c.cache_hits,
        c.sweeps,
        c.sweeps_successful,
        c.sweeps_failing,
        c.sweeps_aborted,
        c.sweep_graphs,
        c.sweep_graphs_max,
        c.admissions,
        c.evictions,
        c.readmissions,
        c.reports,
        c.cut_reports,
        o.impl_end,
        c.sweeps_successful,
        c.sweeps_failing,
        c.sweeps_aborted,
        c.sweep_sizes
    )
}

/// The compact sweep relation, as `cfirst::covers_compact` states it (that
/// function is private to the engine; E7a-6 (c) pins its text to this one).
fn e7_covers(spec: &CompactSummary, query: &CompactSummary) -> bool {
    spec.hash == query.hash && spec.sig == query.sig && spec.ord.le(&query.ord)
}

/// E7a-6 (a): no pair-set summary on the compact path. The test-only counter
/// of `Summary::of` calls (`sig.rs`, this thread: the outer sink's) reads 0
/// over a stateless `Compact` run on each size-2 cell — runs with misses and
/// witnesses — and more than 0 under `Current` (the control: today's path
/// summarises every completion). Fails before E7a: a `Compact` miss built the
/// pair-set summary of the query (`lazy`) on this thread.
#[test]
fn e7a_a_no_pair_set_summary_on_the_compact_path() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    use crate::conformance::sig::{reset_summaries_built_for_test, summaries_built_for_test};
    let mut bad = Vec::new();
    let (mut misses, mut witnesses) = (0usize, 0usize);
    for name in SIZE2_CELLS {
        let f = fx(name);
        for index in [IndexKind::Compact, IndexKind::Current] {
            let g = x1_config(GridEngine::CompleteFirst, Selector::Ltr).index(index).quiet(true);
            let cc = g.conf_config(&f);
            reset_summaries_built_for_test();
            let o = crate::conformance::cfirst::run_with(
                &cc,
                &f.implementation,
                &f.specification,
                false,
            );
            let n = summaries_built_for_test();
            note!(
                "e7a (a) {name} {index:?}: summaries {n} sweeps {} successful {}",
                o.counters.sweeps,
                o.counters.sweeps_successful
            );
            if index == IndexKind::Compact {
                misses += o.counters.sweeps;
                witnesses += o.counters.sweeps_successful;
                if n != 0 {
                    bad.push(format!("{name} Compact: {n} pair-set summaries"));
                }
            } else if n == 0 {
                bad.push(format!("{name} Current: no summary counted (the control)"));
            }
        }
    }
    assert!(misses > 0 && witnesses > 0, "conformance: E7a-6 (a) is not vacuous");
    assert!(bad.is_empty(), "conformance: E7a-6 (a): {bad:#?}");
}

/// E7a-6 (b): no witness clone. A compact sweep (`SweepTest::Compact`) of
/// `MECH_CELL`'s specification for each of its implementation summaries
/// returns the witness's compact summary (`witness_summary`), no graph
/// (`witness` `None`), and the query moved back (`query`); the witness's
/// summary satisfies the compact relation against the query. A query of
/// another fixture's signature finds none (both `None`). And the source: the
/// sweep sink's compact arm keeps `Some(spec)`, the summary, and clones no
/// graph. Fails before E7a (no compact arm; the witness was `m.clone()`).
#[test]
fn e7a_b_the_witness_is_not_cloned() {
    use crate::conformance::cfirst::{sweep_with, SweepTest};
    use crate::conformance::ctx::ConfMode;
    let f = fx(MECH_CELL);
    let cc = GridConfig::new(GridEngine::CompleteFirst).conf_config(&f);
    let (_, imp) = kept_summaries(&f);
    let stranger = real_summary("2pc/leader/conf/n2");
    let mut bad = Vec::new();
    let mut found = 0usize;
    for q in imp.iter().chain(std::iter::once(&stranger)) {
        let swept = sweep_with(
            &cc.config,
            &f.visible,
            &f.specification,
            SweepTest::Compact(q.clone()),
            None,
            false,
            ConfMode::CFirstSweep,
            true,
        );
        let back = swept.query.as_ref().is_some_and(|b| b.sig == q.sig && b.ord == q.ord);
        match (&swept.witness, &swept.witness_summary) {
            (None, Some(w)) => {
                found += 1;
                if !e7_covers(w, q) || !back {
                    bad.push("a witness summary that does not cover its query".to_owned());
                }
            }
            (None, None) => {
                if !back {
                    bad.push("the query was not returned".to_owned());
                }
            }
            (Some(_), _) => bad.push("a witness graph on the compact arm".to_owned()),
        }
    }
    assert!(found > 0, "conformance: E7a-6 (b) is not vacuous");
    let last = sweep_with(
        &cc.config,
        &f.visible,
        &f.specification,
        SweepTest::Compact(stranger),
        None,
        false,
        ConfMode::CFirstSweep,
        true,
    );
    if last.witness_summary.is_some() || last.witness.is_some() {
        bad.push("a stranger's query found a witness".to_owned());
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let src = std::fs::read_to_string(root.join("conformance/cfirst.rs"))
        .expect("conformance: cfirst.rs");
    let head = "if let Some(cs) = query.borrow().as_ref() {";
    let arm = e4_window(&src, head, "return SinkVerdict::Continue;");
    if !arm.contains("*found_summary.borrow_mut() = Some(spec);") || arm.contains(".clone()") {
        bad.push(format!("the compact arm: {arm}"));
    }
    assert!(bad.is_empty(), "conformance: E7a-6 (b): {bad:#?}");
}

/// E7a-6 (c): the compact test's equality, in process. On each size-2 cell,
/// for every pair (a specification graph `m`, an implementation graph `g`) of
/// the stateful engine's kept families, `covers_compact(cs(m), cs(g))` equals
/// `covered(summary(g), summary(m))` on the pair-set summaries. Green by
/// design (COMPACT-INDEX phase 2's T2: equal signatures align positions,
/// `po ⊆ porf` makes each predecessor set a prefix, equal prefix lengths give
/// equal transported-order membership); the function is E7a's — its text in
/// `cfirst.rs` is pinned to [`e7_covers`]'s. The pilot's share is T2, s2 and s7.
#[test]
fn e7a_c_the_compact_test_equals_covered() {
    use crate::conformance::sig::covered;
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let src = std::fs::read_to_string(root.join("conformance/cfirst.rs"))
        .expect("conformance: cfirst.rs");
    assert!(
        src.contains(
            "fn covers_compact(spec: &CompactSummary, query: &CompactSummary) -> bool {\n    \
             spec.hash == query.hash && spec.sig == query.sig && spec.ord.le(&query.ord)\n}"
        ),
        "conformance: `covers_compact`'s text"
    );
    let mut bad = Vec::new();
    let (mut pairs, mut hits) = (0usize, 0usize);
    for name in SIZE2_CELLS {
        let f = fx(name);
        let cc = GridConfig::new(GridEngine::Stateful).conf_config(&f);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, true);
        let both = |g: &ExecutionGraph| {
            (
                CompactSummary::at_completion(g, &f.visible, "test"),
                stateful::summarise(g, &f.visible, "test"),
            )
        };
        let spec: Vec<_> = o.kept_spec_graphs.iter().map(both).collect();
        let imp: Vec<_> = o.kept_impl_graphs.iter().map(both).collect();
        for (mc, ms) in &spec {
            for (gc, gs) in &imp {
                pairs += 1;
                let (a, b) = (e7_covers(mc, gc), covered(gs, ms));
                hits += usize::from(b);
                if a != b {
                    bad.push(format!("{name}: compact {a}, pair-set {b}"));
                }
            }
        }
    }
    note!("e7a (c): {pairs} pairs, {hits} covered");
    assert!(hits > 0 && hits < pairs, "conformance: E7a-6 (c) is not vacuous");
    assert!(bad.is_empty(), "conformance: E7a-6 (c): {bad:#?}");
}

/// E7a-6 (d): the probe memo off by default. `ConfBuilder::new()`'s built
/// configuration and `GridConfig::new` have `probe_memo` false; a default
/// `Compact` key prints `pmemo=false` and round-trips through `parse_label`; a
/// `pmemo=true` key still parses with the memo on; a stateless `Compact` run at
/// the defaults reports `memo_on` false, and with `probe_memo(true)` true
/// (the memo-subject tests set it at their own configuration). Fails before
/// E7a (the default was on).
#[test]
fn e7a_d_the_probe_memo_is_off_by_default() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::parse_label;
    let cc = crate::conformance::ConfBuilder::new().build().expect("conformance: in scope");
    let g = GridConfig::new(GridEngine::CompleteFirst).index(IndexKind::Compact);
    assert!(!cc.probe_memo && !g.probe_memo, "conformance: the memo's default");
    let key = g.label();
    assert!(key.ends_with("/pmemo=false"), "conformance: {key}");
    assert_eq!(parse_label(&key), Some(g.clone()), "conformance: the key round-trips");
    let on = g.clone().probe_memo(true);
    assert!(on.label().ends_with("/pmemo=true"));
    assert_eq!(parse_label(&on.label()), Some(on.clone()));
    let f = fx(MECH_CELL);
    for (gc, want) in [(g, false), (on, true)] {
        let cc = gc.quiet(true).conf_config(&f);
        let (imp, spec) = (&f.implementation, &f.specification);
        let o = crate::conformance::cfirst::run_with(&cc, imp, spec, false);
        let s = o.counters.compact.as_ref().expect("conformance: the compact stats");
        assert_eq!(s.memo_on, want, "conformance: memo_on");
        if !want {
            assert_eq!((s.memo_hits, s.memo_entries, s.memo_clears), (0, 0, 0));
        }
    }
}

/// E7a-6 (e): the sweep record. On A3 fifo k2q2 (sweeps on every miss), the
/// stateless engine under `Current` and `Compact`, through the grid: the knob
/// off (the default) leaves `sweep_sizes` and `sweep_ends` empty and the
/// `sweep_sizes` column blank; on, `sweep_sizes` has one entry per sweep
/// summing to `sweep_graphs` and `sweep_ends` one per sweep; the `sweep_ends`
/// column's text and every scalar counter are equal across the knob. Fails
/// before E7a (the vectors grew whatever the knob).
#[test]
fn e7a_e_the_sweep_record_behind_its_knob() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::grid::{row_of, run_grid, GridEnd, GridRaw};
    let f = fx("apps/a3/fifo/spec/k2q2");
    let mut bad = Vec::new();
    for index in [IndexKind::Current, IndexKind::Compact] {
        let run = |record: bool| {
            let mut g = GridConfig::new(GridEngine::CompleteFirst).index(index).quiet(true);
            g.sweep_record = record;
            match run_grid(&f, &g, None) {
                GridEnd::Ok(r) => r,
                other => panic!("conformance: {other:?}"),
            }
        };
        let (on, off) = (run(true), run(false));
        let (ra, rb) = (row_of(&on), row_of(&off));
        let (GridRaw::CompleteFirst(a), GridRaw::CompleteFirst(b)) = (&on.raw, &off.raw) else {
            panic!("conformance: complete-first outcomes")
        };
        let (ca, cb) = (&a.counters, &b.counters);
        let what = format!("{index:?}");
        if ca.sweeps == 0
            || ca.sweep_sizes.len() != ca.sweeps
            || ca.sweep_sizes.iter().sum::<usize>() != ca.sweep_graphs
            || a.sweep_ends.len() != ca.sweeps
        {
            bad.push(format!("{what} on: {} sizes, {} ends, {} sweeps", ca.sweep_sizes.len(),
                a.sweep_ends.len(), ca.sweeps));
        }
        if !cb.sweep_sizes.is_empty() || !b.sweep_ends.is_empty() {
            bad.push(format!("{what} off: vectors kept"));
        }
        let scalars = |c: &crate::conformance::CFirstCounters| {
            (c.sweeps, c.sweeps_successful, c.sweeps_failing, c.sweeps_aborted, c.sweep_graphs,
             c.sweep_graphs_max, c.cache_hits, c.admissions, c.reports)
        };
        if scalars(ca) != scalars(cb) {
            bad.push(format!("{what}: the scalars differ"));
        }
        if e6_col(&rb, "sweep_sizes") != "" || e6_col(&ra, "sweep_sizes").is_empty() {
            bad.push(format!("{what}: the sweep_sizes column"));
        }
        if e6_col(&ra, "sweep_ends") != e6_col(&rb, "sweep_ends") {
            bad.push(format!("{what}: the sweep_ends column"));
        }
    }
    assert!(bad.is_empty(), "conformance: E7a-6 (e): {bad:#?}");
}

// =========================================================================
// MIN-ENGINES E7b (the tester, gate 3; criteria/MIN-ENGINES-E7B.md rev 1.1,
// E7b-5 (a)–(e); derived §E7 (c)): `Set` for the stateless cache, the
// default of both engines, the keys
// =========================================================================

/// The five occupancy fields E7b-5 (a) compares at every step.
fn e7b_occ(s: &crate::conformance::compact::CompactStats) -> [usize; 5] {
    [s.entries, s.buckets, s.signatures, s.summary_bytes, s.sig_bytes_est]
}

/// E7b-5 (a): `SetCache` against `CompactCache` (antichain off, memo off) on
/// the same admissions and probes. One `SigHash` bucket with two unequal
/// signatures (`MECH_CELL`'s and a forged one), synthetic orders of its
/// length:
/// - under `Bounded(1)` every admission evicts the one held order, so the
///   bucket empties and fills again at each step, slots are refilled after
///   being emptied, and the first order comes back (a re-admission);
/// - under `Bounded(2)` and `Unbounded`, a longer run; under `Zero` nothing.
/// At every step: `admit`'s answer, `len`, the three tallies and `entries`,
/// `buckets`, `signatures`, `summary_bytes`, `sig_bytes_est` equal; then each
/// probe's `Hit`/`Miss` equal. The historical fields by their definitions:
/// `admitted` = admissions, `signatures_seen` = 2, `bucket_max` ≤ the
/// capacity. Fails before E7b (no `SetCache`).
#[test]
fn e7b_a_the_set_cache_against_the_compact_cache() {
    use crate::conformance::compact::{Probe, SetCache};
    let base = real_summary(MECH_CELL);
    let other = e4_into_bucket(&base, "2pc/leader/conf/n2");
    assert!(base.hash == other.hash && base.sig != other.sig, "conformance: one bucket, two sigs");
    let l = base.ord.len();
    assert!(l >= 3, "conformance: room for three unit orders");
    let ords: Vec<Vec<u8>> = (0..3).map(|i| unit(l, i)).collect();
    let mk = |s: &CompactSummary, v: &[u8]| syn(s, v);
    // The admission sequence: (signature, order index), the first order again
    // at the end (a re-admission under `Bounded(n)`).
    let seq: Vec<CompactSummary> = vec![
        mk(&base, &ords[0]),
        mk(&other, &ords[0]),
        mk(&base, &ords[1]),
        mk(&other, &ords[1]),
        mk(&base, &ords[2]),
        mk(&base, &ords[0]),
    ];
    let ones = vec![1u8; l];
    let queries = [mk(&base, &ones), mk(&other, &ones), mk(&base, &ords[1]), mk(&other, &ords[2])];
    let mut bad = Vec::new();
    for cap in [Capacity::Bounded(1), Capacity::Bounded(2), Capacity::Unbounded, Capacity::Zero] {
        let mut set = SetCache::new(cap);
        let mut cmp = CompactCache::new(cap, false, false);
        let mut readmitted = 0usize;
        for (i, w) in seq.iter().enumerate() {
            let what = format!("{cap:?} step {i}");
            let (a, b) = (set.admit(w, w), cmp.admit(w, w));
            let (ss, cs) = (set.stats(), cmp.stats());
            let tallies = |x: (usize, usize, usize, usize)| x;
            let (ts, tc) = (
                tallies((set.len(), set.admissions(), set.evictions(), set.readmissions())),
                tallies((cmp.len(), cmp.admissions(), cmp.evictions(), cmp.readmissions())),
            );
            if a != b || ts != tc || e7b_occ(&ss) != e7b_occ(&cs) {
                bad.push(format!("{what}: admit {a}/{b} tallies {ts:?}/{tc:?} occupancy {:?}/{:?}",
                    e7b_occ(&ss), e7b_occ(&cs)));
            }
            readmitted = ts.3;
            for (j, q) in queries.iter().enumerate() {
                let (ps, pc) = (set.probe(q).0, cmp.probe(q).0);
                let hit = |p: Probe| matches!(p, Probe::Hit | Probe::MemoHit);
                if hit(ps) != hit(pc) || matches!(ps, Probe::MemoHit) {
                    bad.push(format!("{what} query {j}: {ps:?} / {pc:?}"));
                }
            }
            if ss.admitted != set.admissions()
                || ss.signatures_seen > 2
                || matches!(cap, Capacity::Bounded(n) if ss.bucket_max > n)
            {
                bad.push(format!("{what}: historical {} {} {}", ss.admitted, ss.signatures_seen,
                    ss.bucket_max));
            }
        }
        match cap {
            Capacity::Bounded(1) => {
                if readmitted == 0 || set.evictions() != seq.len() - 1 {
                    bad.push(format!("{cap:?}: {readmitted} re-admissions, {} evictions",
                        set.evictions()));
                }
            }
            Capacity::Zero => {
                if set.len() != 0 || set.admissions() != 0 {
                    bad.push("Zero admitted".to_owned());
                }
            }
            _ => {}
        }
    }
    assert!(bad.is_empty(), "conformance: E7b-5 (a): {bad:#?}");
}

/// E7b-5 (b) and (d): the per-engine defaults and the keys.
/// `ConfBuilder::new()` builds `index` `Set`; `GridConfig::new(engine)` is
/// `Set` for the stateful and stateless engines and `Current` for the
/// enumerator and the gated engine; each default key round-trips through
/// `parse_label`; the two engines' default keys are the fourteen-field
/// `…/w=inf/quiet=false/index=set`, the others' the eleven-field form; and
/// the old eleven- and thirteen-field keys of the two engines still parse,
/// as `Current`, and round-trip. Fails before E7b (the default was
/// `Current`).
#[test]
fn e7b_b_the_defaults_and_the_keys() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::parse_label;
    let cc = crate::conformance::ConfBuilder::new().build().expect("conformance: in scope");
    assert_eq!(cc.index, IndexKind::Set, "conformance: the builder's default");
    let mut bad = Vec::new();
    for (e, want) in [
        (GridEngine::Stateful, IndexKind::Set),
        (GridEngine::CompleteFirst, IndexKind::Set),
        (GridEngine::Enumerator, IndexKind::Current),
        (GridEngine::Gated, IndexKind::Current),
    ] {
        let g = GridConfig::new(e);
        let key = g.label();
        let fields = key.split('/').count();
        let want_fields = if want == IndexKind::Set { 14 } else { 11 };
        if g.index != want || parse_label(&key) != Some(g.clone()) || fields != want_fields {
            bad.push(format!("{e:?}: {:?} {key} ({fields} fields)", g.index));
        }
        if want == IndexKind::Set && !key.ends_with("/w=inf/quiet=false/index=set") {
            bad.push(format!("{e:?}: {key}"));
        }
        if want == IndexKind::Set {
            // E7b-5 (d): the old keys — eleven fields, and thirteen.
            for old in [
                g.clone().index(IndexKind::Current),
                g.clone().index(IndexKind::Current).quiet(true),
            ] {
                let k = old.label();
                match parse_label(&k) {
                    Some(p) if p.index == IndexKind::Current && p.label() == k => {}
                    other => bad.push(format!("{e:?}: old key {k}: {other:?}")),
                }
            }
        }
    }
    assert!(bad.is_empty(), "conformance: E7b-5 (b)/(d): {bad:#?}");
}

/// E7b gate 4 round 01 M1 (Codex's required test; the tester's derivation):
/// under `Set` the complete-first engine counts its step-0 distinct
/// summaries (`impl_distinct`), so the knob is effective there and the key
/// carries it. With `g(on) = GridConfig::new(CompleteFirst).impl_distinct(on)`
/// (index `Set`, the default): the two labels differ; the on label is the
/// off label followed by `/distinct=on`; each parses back to its own
/// configuration and re-labels to itself. On `MECH_CELL` the cache
/// statistics read `None` with the knob off and, with it on, the number of
/// distinct `(Sig, OrdCounts)` among the implementation's complete graphs
/// (computed here from the stateful engine's kept graphs: 6, m14's figure).
/// Fails before the fix: the on label equals the off label and parses back
/// with the knob off.
#[test]
fn e7b_g4_m1_the_distinct_knob_under_set_is_in_the_key() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::parse_label;
    let f = fx(MECH_CELL);
    let (_, imp) = kept_summaries(&f);
    let mut distinct: Vec<&CompactSummary> = Vec::new();
    for s in &imp {
        if !distinct.iter().any(|d| d.sig == s.sig && d.ord == s.ord) {
            distinct.push(s);
        }
    }
    assert_eq!(distinct.len(), 6, "conformance: the step-0 count on the cell");
    let g = |on: bool| GridConfig::new(GridEngine::CompleteFirst).impl_distinct(on);
    let (off, on) = (g(false), g(true));
    assert_eq!((off.index, on.index), (IndexKind::Set, IndexKind::Set));
    let (lo, ln) = (off.label(), on.label());
    assert_ne!(lo, ln, "conformance: two configurations, two keys");
    assert!(!lo.contains("distinct"), "conformance: {lo}");
    assert_eq!(ln, format!("{lo}/distinct=on"), "conformance: the suffix");
    for (c, l) in [(&off, &lo), (&on, &ln)] {
        let back = parse_label(l).unwrap_or_else(|| panic!("conformance: {l} does not parse"));
        assert_eq!(&back, c, "conformance: {l} parses back to its configuration");
        assert_eq!(&back.label(), l, "conformance: {l} round-trips");
    }
    for (c, want) in [(&off, None), (&on, Some(distinct.len()))] {
        let o = crate::conformance::cfirst::run_with(
            &c.conf_config(&f),
            &f.implementation,
            &f.specification,
            false,
        );
        assert!(
            o.set_cache.is_some() && o.compact_cache.is_none(),
            "conformance: the set cache"
        );
        let got = o.counters.compact.as_ref().map(|s| s.impl_distinct_summaries);
        assert_eq!(got, Some(want), "conformance: the cache statistics, knob {}", c.impl_distinct);
    }
}

// =========================================================================
// MIN-ENGINES E9 (the tester, gate 3; criteria/MIN-ENGINES-E9.md rev 1.0,
// E9-6 (a)–(e); derived §E9 item 4): the stateful engine's first-report
// wall and `VmHWM`, in the stateless engine's two columns
// =========================================================================

/// E9-6's fixtures besides [`E6_FIXTURES`]: `cfcfg` c04's four
/// (`ex:naive/k2/enc1`, two reports; `apps/a1/eager/spec/n2r2`, 55; two
/// conforming pairs).
const E9_C04: [&str; 4] = [
    "ex:naive/k2/enc1",
    "apps/a1/eager/spec/n2r2",
    "apps/a1/correct/spec/n2r2",
    "synth/share/m2c1",
];

/// E9-6 (a): the stateful columns follow the report count. On [`E6_FIXTURES`]
/// and [`E9_C04`], the stateful engine through `run_grid` at x1's
/// configuration under `Current`, `Compact` and `Set`, `stop` off and on,
/// `all_reports` off and on: `wall_ms_at_first_report` and
/// `vmhwm_kb_at_first_report` are `Some` iff `counters.reports ≥ 1`; then
/// `W ≤ impl_wall_time_ms` (both floors of elapsed times from the one
/// `impl_started`, read in that order) and `vm_hwm_kb_before ≤ H ≤
/// vm_hwm_kb_after` (the grid run's own reads; `VmHWM` never decreases); the
/// row's two cells are the values' text, blank for `None`; the report count
/// and the presence are equal across `all_reports`. Fails before E9 (no
/// fields; the row has no such cells).
#[test]
fn e9_a_the_stateful_columns_follow_the_reports() {
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::x1_config;
    use crate::conformance::grid::{row_of, run_grid, GridEnd, GridRaw};
    use crate::conformance::selector::Selector;
    let mut bad = Vec::new();
    let (mut violating, mut conforming) = (0usize, 0usize);
    for name in E6_FIXTURES.iter().chain(E9_C04.iter()) {
        let f = e1_fixture(name);
        for k in [IndexKind::Current, IndexKind::Compact, IndexKind::Set] {
            for stop in [false, true] {
                let mut seen = Vec::new();
                for all in [false, true] {
                    let mut g = x1_config(GridEngine::Stateful, Selector::Ltr).index(k).stop(stop);
                    g.all_reports = all;
                    let what = format!("{name} {k:?} stop={stop} all={all}");
                    let r = match run_grid(&f, &g, None) {
                        GridEnd::Ok(r) => r,
                        other => panic!("conformance: {what}: {other:?}"),
                    };
                    let GridRaw::Stateful(o) = &r.raw else {
                        panic!("conformance: {what}: not a stateful outcome")
                    };
                    let c = &o.counters;
                    let n = c.reports;
                    let (w, h) = (c.wall_ms_at_first_report, c.vmhwm_kb_at_first_report);
                    if w.is_some() != (n >= 1) || h.is_some() != (n >= 1) {
                        bad.push(format!("{what}: reports {n}, {w:?} {h:?}"));
                    }
                    if let (Some(w), Some(h)) = (w, h) {
                        let (before, after) = r.vm_hwm_kb;
                        let ok = w <= c.impl_wall_time_ms
                            && before.is_some_and(|b| b <= h)
                            && after.is_some_and(|a| h <= a);
                        if !ok {
                            bad.push(format!(
                                "{what}: {w} ms of {} ms; {before:?} <= {h} <= {after:?}",
                                c.impl_wall_time_ms
                            ));
                        }
                    }
                    let row = row_of(&r);
                    let cells = (
                        e6_col(&row, "wall_ms_at_first_report"),
                        e6_col(&row, "vmhwm_kb_at_first_report"),
                    );
                    let want = (
                        w.map(|v| v.to_string()).unwrap_or_default(),
                        h.map(|v| v.to_string()).unwrap_or_default(),
                    );
                    if cells != want {
                        bad.push(format!("{what}: cells {cells:?}, want {want:?}"));
                    }
                    if n >= 1 {
                        violating += 1;
                    } else {
                        conforming += 1;
                    }
                    seen.push((n, w.is_some(), h.is_some()));
                }
                if seen[0] != seen[1] {
                    bad.push(format!("{name} {k:?} stop={stop}: across all_reports {seen:?}"));
                }
            }
        }
    }
    note!("e9_a: {violating} runs with a report, {conforming} without");
    assert!(violating > 0 && conforming > 0, "conformance: E9-6 (a) is vacuous");
    assert!(bad.is_empty(), "conformance: E9-6 (a): {bad:#?}");
}

/// E9-6 (b)'s child, run by [`e9_b_the_origin_is_the_implementation_run`]
/// (`E9_CASE=origin`): `a27`'s violating pair (two completions, two reports)
/// whose specification sleeps 400 ms at its first invocation and whose
/// implementation, from its second invocation on, sleeps 400 ms and touches a
/// 300 MiB allocation; the stateful engine at x1's configuration under `Set`
/// (first) and `Current`. Writes one `CASE\t` line: per run
/// `kind,reports,spec_calls,impl_calls,spec_ms,impl_ms,first_ms,first_kb,
/// before_kb,after_kb`, `;`-separated.
#[test]
#[ignore]
fn e9_child() {
    use crate::conformance::config::IndexKind;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    if std::env::var("E9_CASE").as_deref() != Ok("origin") {
        return;
    }
    let base = e1_fixture("a27");
    let mut out = Vec::new();
    for k in [IndexKind::Set, IndexKind::Current] {
        let spec_calls = Arc::new(AtomicUsize::new(0));
        let impl_calls = Arc::new(AtomicUsize::new(0));
        let mut f = base.clone();
        let (spec, sc) = (base.specification.clone(), spec_calls.clone());
        f.specification = Arc::new(move || {
            if sc.fetch_add(1, Ordering::SeqCst) == 0 {
                std::thread::sleep(std::time::Duration::from_millis(400));
            }
            spec()
        });
        let (imp, ic) = (base.implementation.clone(), impl_calls.clone());
        f.implementation = Arc::new(move || {
            if ic.fetch_add(1, Ordering::SeqCst) >= 1 {
                std::thread::sleep(std::time::Duration::from_millis(400));
                let v = vec![1u8; 300 << 20];
                std::hint::black_box(&v);
            }
            imp()
        });
        let cc = crate::conformance::eval::x1_config(
            GridEngine::Stateful,
            crate::conformance::selector::Selector::Ltr,
        )
        .index(k)
        .conf_config(&f);
        let before = crate::conformance::grid::vm_hwm_kb().unwrap_or(0);
        let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
        let after = crate::conformance::grid::vm_hwm_kb().unwrap_or(0);
        let c = &o.counters;
        let text = |v: Option<String>| v.unwrap_or_default();
        out.push(format!(
            "{k:?},{},{},{},{},{},{},{},{before},{after}",
            c.reports,
            spec_calls.load(Ordering::SeqCst),
            impl_calls.load(Ordering::SeqCst),
            c.spec_wall_time_ms,
            c.impl_wall_time_ms,
            text(c.wall_ms_at_first_report.map(|v| v.to_string())),
            text(c.vmhwm_kb_at_first_report.map(|v| v.to_string())),
        ));
    }
    use std::io::Write as _;
    writeln!(std::io::stdout().lock(), "CASE\t{}", out.join(";")).unwrap();
}

/// E9-6 (b): the origin and the first report's values, in a child process
/// (its `VmHWM` is its own), from [`e9_child`]'s line. Per run: two reports;
/// `spec_wall_time_ms ≥ 400 > W` (the clock starts after the index run, whose
/// first specification invocation slept 400 ms); `W < 400 ≤
/// impl_wall_time_ms` (the value is the first report's, read before the
/// second completion's sleep and never overwritten); in the child's first run
/// `H` is below the pre-run mark + 100 MiB while `VmHWM` after the run is at
/// least 250 MiB above it (the read is at the first report, before the late
/// allocation). Fails before E9 (no fields). Run alone.
#[test]
#[ignore]
fn e9_b_the_origin_is_the_implementation_run() {
    let o = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--ignored",
            "--exact",
            "conformance::compact_tests::e9_child",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("E9_CASE", "origin")
        .output()
        .unwrap();
    let got = String::from_utf8_lossy(&o.stdout)
        .lines()
        .find_map(|l| l.find("CASE\t").map(|k| l[k + 5..].to_owned()))
        .unwrap_or_else(|| {
            panic!(
                "conformance: E9-6 (b): no case line: {}",
                String::from_utf8_lossy(&o.stderr)
            )
        });
    note!("e9_b: {got}");
    let mut bad = Vec::new();
    for (i, part) in got.split(';').enumerate() {
        let f: Vec<&str> = part.split(',').collect();
        if f.len() != 10 {
            bad.push(format!("unparsed: {part}"));
            continue;
        }
        let num = |j: usize| f[j].parse::<u64>().unwrap_or(u64::MAX);
        let (reports, spec_calls, impl_calls) = (num(1), num(2), num(3));
        let (spec_ms, impl_ms, first_ms) = (num(4), num(5), num(6));
        let (first_kb, before, after) = (num(7), num(8), num(9));
        if reports != 2 || spec_calls < 1 || impl_calls < 2 {
            bad.push(format!("{}: reports {reports}, calls {spec_calls}/{impl_calls}", f[0]));
        }
        if !(spec_ms >= 400 && first_ms < 400 && impl_ms >= 400) {
            bad.push(format!(
                "{}: spec {spec_ms} ms, first {first_ms} ms, impl {impl_ms} ms",
                f[0]
            ));
        }
        if i == 0 && !(first_kb < before + 100 * 1024 && after >= before + 250 * 1024) {
            bad.push(format!(
                "{}: first-report VmHWM {first_kb} kB, before {before}, after {after}",
                f[0]
            ));
        }
    }
    assert!(bad.is_empty(), "conformance: E9-6 (b): {bad:#?}");
}

/// E9-6 (c): exactly `min(1, N)` first-report reads per run, for both
/// engines, by the lead's test-only hook (`cfirst::first_report_reads_for_test`,
/// a thread-local count of `note_first_report`'s first-report branch): on
/// [`E6_FIXTURES`] and [`E9_C04`], the stateful engine (`stateful::run_with`,
/// on this thread) and the stateless engine (`cfirst::run_with`, quiet) at
/// x1's configuration under `Current`, `Compact` and `Set`, `stop` off and on,
/// `all_reports` off and on. And the source: at each of the three report sites
/// (`stateful.rs` one, `cfirst.rs` two) the statement after
/// `st.counters.reports += 1;` (comments aside) is `let c = &mut
/// st.counters;`, then the reader's call, before the first report's snapshot;
/// `note_first_report(` occurs there and, in `cfirst.rs`, at its definition,
/// nowhere else; `stateful.rs` keeps its three `Instant::now()` and three
/// `.elapsed()` (`run`, the index run, the implementation run: no new clock)
/// and names no `vm_hwm`. Fails before E9 (no hook; the stateful count is 0 at
/// `N ≥ 1`); the stateless half passes before and after (E9-6 (e)).
#[test]
fn e9_c_one_read_per_run() {
    use crate::conformance::cfirst::{
        first_report_reads_for_test, reset_first_report_reads_for_test,
    };
    use crate::conformance::config::IndexKind;
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    let mut bad = Vec::new();
    let (mut runs, mut reads) = (0usize, 0usize);
    for name in E6_FIXTURES.iter().chain(E9_C04.iter()) {
        let f = e1_fixture(name);
        for engine in [GridEngine::Stateful, GridEngine::CompleteFirst] {
            for k in [IndexKind::Current, IndexKind::Compact, IndexKind::Set] {
                for stop in [false, true] {
                    for all in [false, true] {
                        let mut g = x1_config(engine, Selector::Ltr).index(k).stop(stop);
                        if engine == GridEngine::CompleteFirst {
                            g = g.quiet(true);
                        }
                        g.all_reports = all;
                        let cc = g.conf_config(&f);
                        reset_first_report_reads_for_test();
                        let n = if engine == GridEngine::Stateful {
                            stateful::run_with(&cc, &f.implementation, &f.specification, false)
                                .counters
                                .reports
                        } else {
                            crate::conformance::cfirst::run_with(
                                &cc,
                                &f.implementation,
                                &f.specification,
                                false,
                            )
                            .counters
                            .reports
                        };
                        let got = first_report_reads_for_test();
                        if got != n.min(1) {
                            bad.push(format!(
                                "{name} {engine:?} {k:?} stop={stop} all={all}: {got} reads, N {n}"
                            ));
                        }
                        runs += 1;
                        reads += got;
                    }
                }
            }
        }
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance");
    for (file, sites, calls) in [("stateful.rs", 1, 1), ("cfirst.rs", 2, 3)] {
        let src = std::fs::read_to_string(root.join(file)).expect("conformance: a source file");
        let at: Vec<usize> =
            src.match_indices("st.counters.reports += 1;").map(|(i, _)| i).collect();
        if at.len() != sites {
            bad.push(format!("{file}: {} report sites", at.len()));
        }
        for i in at {
            let w = &src[i + "st.counters.reports += 1;".len()..];
            let call = w.find("note_first_report(");
            let snap = w.find("replay_snapshot(g, must_state");
            match (call, snap) {
                (Some(c), Some(s)) if c < s => {
                    let between: Vec<&str> = w[..c]
                        .lines()
                        .map(str::trim)
                        .filter(|l| !l.is_empty() && !l.starts_with("//"))
                        .collect();
                    if between != ["let c = &mut st.counters;"] {
                        bad.push(format!("{file} at {i}: before the call {between:?}"));
                    }
                }
                other => bad.push(format!("{file} at {i}: call/snapshot {other:?}")),
            }
        }
        let n = src.matches("note_first_report(").count();
        if n != calls {
            bad.push(format!("{file}: {n} `note_first_report(`"));
        }
    }
    let st = std::fs::read_to_string(root.join("stateful.rs")).expect("conformance: stateful.rs");
    let clocks = (st.matches("Instant::now()").count(), st.matches(".elapsed()").count());
    if clocks != (3, 3) || st.contains("vm_hwm") {
        bad.push(format!("stateful.rs: clocks {clocks:?}, vm_hwm {}", st.contains("vm_hwm")));
    }
    note!("e9_c: {runs} runs, {reads} reads");
    assert!(reads > 0 && reads < runs, "conformance: E9-6 (c) is vacuous");
    assert!(bad.is_empty(), "conformance: E9-6 (c): {bad:#?}");
}

/// E9-6 (d): the public route, `conformance::run` with `Engine::Stateful` at
/// x1's configuration (`Set`): on `ex:naive/k2/enc1` (two reports) and
/// `apps/a1/correct/spec/n2r2` (none), `stateful_counters()` carries both
/// fields `Some` iff `report_count() ≥ 1`, with `W ≤ impl_wall_time_ms`; the
/// engine-independent `ConfCounters` names no first-report wall or memory
/// field (its `Debug` text). Fails before E9 (no fields).
#[test]
fn e9_d_the_public_route() {
    use crate::conformance::eval::x1_config;
    use crate::conformance::selector::Selector;
    let mut bad = Vec::new();
    for (name, violating) in [("ex:naive/k2/enc1", true), ("apps/a1/correct/spec/n2r2", false)] {
        let f = e1_fixture(name);
        let cc = x1_config(GridEngine::Stateful, Selector::Ltr).conf_config(&f);
        let v = crate::conformance::run(cc, f.implementation.clone(), f.specification.clone())
            .unwrap_or_else(|e| panic!("conformance: {name}: {e:?}"));
        let out = v.outcome();
        let sc = out
            .stateful_counters()
            .unwrap_or_else(|| panic!("conformance: {name}: no stateful counters"));
        let n = out.report_count();
        let (w, h) = (sc.wall_ms_at_first_report, sc.vmhwm_kb_at_first_report);
        if (n >= 1) != violating || w.is_some() != violating || h.is_some() != violating {
            bad.push(format!("{name}: report_count {n}, {w:?} {h:?}"));
        }
        if w.is_some_and(|w| w > sc.impl_wall_time_ms) {
            bad.push(format!("{name}: {w:?} ms of {} ms", sc.impl_wall_time_ms));
        }
        let pc = format!("{:?}", out.counters());
        if pc.contains("wall_ms_at_first_report") || pc.contains("vmhwm_kb_at_first_report") {
            bad.push(format!("{name}: ConfCounters names a first-report column: {pc}"));
        }
    }
    assert!(bad.is_empty(), "conformance: E9-6 (d): {bad:#?}");
}
