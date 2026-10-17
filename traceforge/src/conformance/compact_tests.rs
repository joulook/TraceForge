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
    .index(index);
    let cc = gc.conf_config(&f);
    let t0 = std::time::Instant::now();
    let o = stateful::run_with(&cc, &f.implementation, &f.specification, false);
    let c = &o.counters;
    note!(
        "STEP0\t{name}\t{kind}\tlabel {}\timpl_distinct_summaries {}\timpl_graphs {}\tspec_graphs {}\torders_held {}\tsignatures {}\treports {}\twall_ms {}",
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
                .probe_memo(true),
        ),
        (
            "row2",
            x1_config(GridEngine::CompleteFirst, Selector::Ltr)
                .witness_cache(Capacity::Unbounded)
                .quiet(true)
                .index(IndexKind::Compact)
                .antichain(true)
                .probe_memo(true),
        ),
        (
            "row3",
            x1_config(GridEngine::CompleteFirst, Selector::Ltr)
                .witness_cache(Capacity::Bounded(64))
                .quiet(true)
                .index(IndexKind::Compact)
                .antichain(false)
                .probe_memo(true),
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
        "sig_bytes": s.sig_bytes, "memo_on": s.memo_on, "memo_hits": s.memo_hits,
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
    for name in SIZE2_CELLS {
        let f = fx(name);
        for (row, gc) in slice_configs() {
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
    assert_eq!(ix.insert(&syn(&base, &one)), Inserted::Stored(0));
    assert_eq!(
        ix.insert(&syn(&base, &two)),
        Inserted::DroppedNew,
        "conformance: one ≤ two drops two"
    );
    assert_eq!(
        ix.insert(&syn(&base, &one)),
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
    assert!(matches!(ix.insert(&syn(&base, &a)), Inserted::Stored(_)));
    assert!(matches!(ix.insert(&syn(&base, &b)), Inserted::Stored(_)));
    assert!(matches!(ix.insert(&syn(&base, &c)), Inserted::Stored(_)));
    assert_eq!(ix.stats().bucket_max, 3);
    assert!(matches!(ix.insert(&syn(&base, &zero)), Inserted::Stored(3)));
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
    assert_eq!(s.sig_bytes, base.sig_len, "conformance: one live bucket");
    assert_eq!(ix.covers(&syn(&base, &two)), Covers::Found(3));
    assert_eq!(ix.stats().containment_tests, 1);
    // Query order: antichain off, a then b held; a query above both is
    // answered by the first in insertion order.
    let mut ix = CompactIndex::new(false);
    ix.insert(&syn(&base, &a));
    ix.insert(&syn(&base, &b));
    assert_eq!(
        ix.covers(&syn(&base, &one)),
        Covers::Found(0),
        "conformance: the first held entry answers"
    );
    assert_eq!(ix.covers(&syn(&base, &unit(l, 1))), Covers::Found(1));
    assert_eq!(
        ix.stats().containment_tests,
        3,
        "conformance: 1 + 2 comparisons"
    );
    assert_eq!(ix.covers(&syn(&base, &zero)), Covers::NotFound);
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
    assert!(matches!(ix.insert(&syn(&base, &one)), Inserted::Stored(_)));
    assert!(matches!(ix.insert(&syn(&base, &two)), Inserted::Stored(_)));
    assert_eq!(ix.insert(&syn(&base, &two)), Inserted::Duplicate);
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
    assert_eq!(c.probe(&g1), Probe::Miss);
    assert!(c.admit(&m1, &g1));
    assert_eq!(c.probe(&g1), Probe::MemoHit);
    assert_eq!(c.probe(&g2), Probe::Miss);
    assert!(c.admit(&m2, &g2));
    assert_eq!((c.len(), c.memo_len(), c.evictions()), (2, 2, 0));
    assert_eq!(c.probe(&g3), Probe::Miss);
    assert!(c.admit(&m3, &g3));
    assert_eq!(
        (c.len(), c.memo_len(), c.evictions(), c.stats().memo_clears),
        (2, 1, 1, 1),
        "conformance: evict m1, clear, insert m3, memo = {{g3}}"
    );
    assert_eq!(c.probe(&g3), Probe::MemoHit);
    assert_eq!(
        c.probe(&g1),
        Probe::Miss,
        "conformance: m1 evicted and g1 forgotten by the memo"
    );
    assert_eq!(
        c.probe(&g2),
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
    assert_eq!(c.probe(&gx), Probe::Miss);
    assert_eq!(c.memo_len(), 0, "conformance: a miss is not memoised");
    assert!(c.admit(&m, &g1));
    assert_eq!(
        c.memo_len(),
        1,
        "conformance: extended at the admission with the probed summary"
    );
    assert_eq!(c.probe(&g2), Probe::Hit);
    assert_eq!(c.memo_len(), 2, "conformance: extended at the bucket hit");
    assert_eq!(c.probe(&g2), Probe::MemoHit);
    assert_eq!(c.probe(&gx), Probe::Miss);
    let s = c.stats();
    assert_eq!((s.memo_hits, s.memo_entries, s.memo_on), (1, 2, true));
    let mut off = CompactCache::new(Capacity::Unbounded, true, false);
    assert!(off.admit(&m, &g1));
    assert_eq!(off.probe(&g2), Probe::Hit);
    assert_eq!(
        off.probe(&g2),
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
    assert_eq!(c.probe(&m), Probe::Miss);
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

/// A summary with `base`'s hash and order but another fixture's `Sig`: a
/// forged 128-bit collision with equal counts (gate 4 B1).
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
        sig_len: other.sig_len,
    }
}

/// m8 (gate 4 B1, frozen §3.3 C2, §5 C3): a forged collision (equal hash,
/// equal counts, unequal `Sig`) panics and never answers: at a memo entry
/// made by an admission, at one made by a bucket hit, at an insertion and at
/// a query; with the memo off it reaches the query's check.
#[test]
fn m8_a_forged_collision_panics_at_the_memo_the_insert_and_the_query() {
    let base = real_summary(MECH_CELL);
    let bad = forged(&base);
    let want = |site: &str, got: Option<String>| {
        let m = got.unwrap_or_else(|| panic!("conformance: {site}: returned, no panic"));
        assert!(
            m.contains("128-bit signature hash collision"),
            "conformance: {site}: another panic: {m}"
        );
        m
    };
    // A memo entry made by an admission.
    let mut c = CompactCache::new(Capacity::Unbounded, true, true);
    assert!(c.admit(&base, &base), "conformance: admitted");
    assert_eq!(c.probe(&base), Probe::MemoHit, "conformance: control");
    let m = want("memo (admission)", panic_text(|| c.probe(&bad)));
    assert!(
        m.contains("at a memo hit"),
        "conformance: the memo site: {m}"
    );
    // A memo entry made by a bucket hit (the witness is not the probe).
    let w = syn(&base, &vec![0u8; base.ord.len()]);
    let q = syn(&base, &vec![1u8; base.ord.len()]);
    let mut c = CompactCache::new(Capacity::Unbounded, true, true);
    assert!(c.admit(&w, &w), "conformance: admitted");
    assert_eq!(c.probe(&q), Probe::Hit, "conformance: a bucket hit");
    let bad_q = CompactSummary {
        ord: q.ord.clone(),
        ..bad.clone()
    };
    let m = want("memo (bucket hit)", panic_text(|| c.probe(&bad_q)));
    assert!(
        m.contains("at a memo hit"),
        "conformance: the memo site: {m}"
    );
    // The memo off: the query's check.
    let mut c = CompactCache::new(Capacity::Unbounded, true, false);
    assert!(c.admit(&base, &base), "conformance: admitted");
    let m = want("probe (memo off)", panic_text(|| c.probe(&bad)));
    assert!(m.contains("at a query"), "conformance: the query site: {m}");
    // The index directly: insertion and query.
    let mut ix = CompactIndex::new(true);
    assert_eq!(ix.insert(&base), Inserted::Stored(0));
    let m = want("insert", panic_text(|| ix.insert(&bad)));
    assert!(
        m.contains("at an insertion"),
        "conformance: the insertion site: {m}"
    );
    let mut ix = CompactIndex::new(false);
    assert_eq!(ix.insert(&base), Inserted::Stored(0));
    assert_eq!(ix.covers(&base), Covers::Found(0), "conformance: control");
    let m = want("covers", panic_text(|| ix.covers(&bad)));
    assert!(m.contains("at a query"), "conformance: the query site: {m}");
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
