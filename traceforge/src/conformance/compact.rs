//! `COMPACT-INDEX` §5 (the Monday slice; frozen semantics in
//! `plan/traceForge/log/dev/COMPACT-INDEX.frozen.md`): the compact summary,
//! the bucket index, and the complete-first cache built on it.
//!
//! **The compact summary** (§5.1 item 2; frozen §3). A complete graph's
//! [`Sig`] is kept with its values; its visible order is kept as counts:
//! for each visible event `e` and each *other* visible thread `t'`,
//! `c_e[t'] = |{ j : (t', j) is porf-before e }|`, computed at completion by
//! `graph.in_porf(a, e)` over the visible events `a` of `t'` (the direction of
//! `morphism::vo`). Because `po ⊆ porf`, the events of `t'` before `e` form a
//! prefix of `t'`'s chain, so the count determines the set, and for equal
//! signatures `ord(M) ⊆ ord(G) ⟺ c^M ≤ c^G` pointwise (T2). Same-thread
//! pairs are po on both sides of any equal-`Sig` comparison and are not
//! stored. Layout: `n · (T − 1)` counts, event-major (threads in sorted
//! declared-name order, the `BTreeMap` order of `Sig`), `u8` unless some
//! thread has more than 255 visible events, then `u16` throughout.
//!
//! **The bucket key** is a 128-bit hash of the `Debug` rendering of the
//! signature, used **only** to find the bucket; equality inside a bucket is
//! `Sig ==` (`msg_equals`). A bucket whose signature differs from a query's or
//! an insertion's is a 128-bit collision and a panic (frozen C2): no verdict
//! is ever answered from another signature's bucket. Precondition, the spec's
//! own: the `Debug` rendering of a message value is a function of its
//! `PartialEq` class (true of derived impls on plain data).
//!
//! **The bucket index** (§5.1 item 3; frozen §4). `HashMap<SigHash, Bucket>`,
//! `Bucket { sig, orders: Vec<_> }`; a query scans the bucket in insertion
//! order and the first entry `q ≤ g` answers. The antichain knob (default on):
//! an insertion dominated by a held entry (`held ≤ new`) is dropped; held
//! entries dominated by the new one (`new ≤ held`) are removed. Sound for the
//! yes/no probe: if `c^{M₁} ≤ c^{M₂} ≤ c^G` then `M₁` covers `G`. Exact
//! duplicates are refused before any antichain action. No inverted index in
//! the slice; `bucket_max` is exported instead.
//!
//! **The complete-first cache** (§5.1 item 4(b); frozen §4.3, §5): the index
//! with the capacity rules (`Zero` admits nothing; `Bounded(n)` FIFO over the
//! global admission order, the antichain **off**; `Unbounded`), and the probe
//! memo — the implementation summaries whose probe hit, consulted before the
//! bucket query, extended at a bucket hit and at an admission, cleared on
//! every eviction. Only hits are memoised: a miss may become a hit after a
//! sweep admits a witness. The memo holds the exact `(SigHash, OrdCounts)`
//! (frozen C3), never a hash of the counts.
//!
//! Everything here is a pure function of graphs and their `Wobs` rows, as
//! `sig.rs` is; nothing consults engine stamps or insertion order beyond the
//! bucket vectors' own.

use std::cmp::Ordering;
use std::collections::hash_map::{DefaultHasher, Entry as MapEntry};
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

use crate::conformance::config::Capacity;
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{wobs, Wobs};
use crate::conformance::sig::Sig;
use crate::exec_graph::ExecutionGraph;

/// The bucket key: a 128-bit hash of the signature's rendering (frozen §3.3).
pub(crate) type SigHash = u128;

/// Two seeded 64-bit `DefaultHasher` values of `text` (the construction of
/// `witness.rs::fingerprint_of`).
fn hash128(text: &str) -> u128 {
    let mut a = DefaultHasher::new();
    0x5f3759dfu64.hash(&mut a);
    text.hash(&mut a);
    let mut b = DefaultHasher::new();
    0x9e3779b97f4a7c15u64.hash(&mut b);
    text.hash(&mut b);
    ((a.finish() as u128) << 64) | b.finish() as u128
}

/// The visible order of a complete graph as counts (frozen §3.2).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum OrdCounts {
    U8(Vec<u8>),
    U16(Vec<u16>),
}

/// `a ≤ b` with some coordinate strictly less is `Less`; `a ≥ b` with some
/// strictly greater is `Greater`; equal is `Equal`; both directions strict
/// somewhere is `None` (incomparable). Exits at the first coordinate that
/// settles `None`.
fn cmp_counts<T: Ord>(a: &[T], b: &[T]) -> Option<Ordering> {
    assert_eq!(
        a.len(),
        b.len(),
        "conformance: OrdCounts of different signatures compared"
    );
    let mut less = false;
    let mut greater = false;
    for (x, y) in a.iter().zip(b) {
        match x.cmp(y) {
            Ordering::Less => less = true,
            Ordering::Greater => greater = true,
            Ordering::Equal => {}
        }
        if less && greater {
            return None;
        }
    }
    Some(match (less, greater) {
        (false, false) => Ordering::Equal,
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
        (true, true) => unreachable!("conformance: settled above"),
    })
}

impl OrdCounts {
    /// The counts of a complete graph from its `Wobs` rows: the declared
    /// names in sorted order, each row's events in program order; for event
    /// `e` of thread `t` and each other thread `t'` in that order, the number
    /// of `t'`'s visible events `a` with `graph.in_porf(a, e)`.
    pub(crate) fn of(graph: &ExecutionGraph, wobs: &Wobs, visible: &[String]) -> Self {
        let mut names: Vec<&str> = visible.iter().map(String::as_str).collect();
        names.sort_unstable();
        names.dedup();
        let rows: Vec<&[(crate::event::Event, crate::conformance::obs::Obs)]> =
            names.iter().map(|n| wobs.of(n)).collect();
        // Gate 4 B2: a count is bounded by its thread's visible length, so a
        // thread beyond `u16::MAX` visible events is refused here, in every
        // profile, before any count could wrap.
        for (name, row) in names.iter().zip(&rows) {
            assert!(
                row.len() <= u16::MAX as usize,
                "conformance: the visible thread `{name}` has {} visible events; the compact \
                 summary's counts are u16 (COMPACT-INDEX §5.1 item 2), at most {}",
                row.len(),
                u16::MAX
            );
        }
        let wide = rows.iter().any(|r| r.len() > 255);
        let t = rows.len();
        let mut counts: Vec<u16> =
            Vec::with_capacity(rows.iter().map(|r| r.len()).sum::<usize>() * t.saturating_sub(1));
        for (ti, row) in rows.iter().enumerate() {
            for (e, _) in row.iter() {
                for (tj, other) in rows.iter().enumerate() {
                    if tj == ti {
                        continue;
                    }
                    let mut c: u16 = 0;
                    for (a, _) in other.iter() {
                        if graph.in_porf(*a, *e) {
                            c += 1;
                        }
                    }
                    // The prefix property (po ⊆ porf): the members are exactly
                    // the first `c` events of the other thread's row.
                    debug_assert!(
                        other
                            .iter()
                            .enumerate()
                            .all(|(j, (a, _))| graph.in_porf(*a, *e) == (j < c as usize)),
                        "conformance: the events of a visible thread porf-before an event \
                         are not a prefix of its chain"
                    );
                    counts.push(c);
                }
            }
        }
        if wide {
            OrdCounts::U16(counts)
        } else {
            OrdCounts::U8(counts.into_iter().map(|c| c as u8).collect())
        }
    }

    /// Pointwise comparison; `None` is incomparable. Both operands must come
    /// from one signature (same length and width); anything else is a panic.
    pub(crate) fn cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (OrdCounts::U8(a), OrdCounts::U8(b)) => cmp_counts(a, b),
            (OrdCounts::U16(a), OrdCounts::U16(b)) => cmp_counts(a, b),
            _ => panic!("conformance: OrdCounts of different widths compared"),
        }
    }

    /// `self ≤ other` pointwise.
    pub(crate) fn le(&self, other: &Self) -> bool {
        matches!(self.cmp(other), Some(Ordering::Equal | Ordering::Less))
    }

    /// The payload bytes, headers excluded: `n · (T − 1)` times the width.
    pub(crate) fn payload_bytes(&self) -> usize {
        match self {
            OrdCounts::U8(v) => v.len(),
            OrdCounts::U16(v) => v.len() * 2,
        }
    }

    /// The number of counts (`n · (T − 1)`).
    pub(crate) fn len(&self) -> usize {
        match self {
            OrdCounts::U8(v) => v.len(),
            OrdCounts::U16(v) => v.len(),
        }
    }

    pub(crate) fn is_wide(&self) -> bool {
        matches!(self, OrdCounts::U16(_))
    }
}

/// What the index reads of a complete graph: the signature with its values,
/// its bucket hash, the rendering's length (for `sig_bytes`), and the counts.
#[derive(Clone, Debug)]
pub(crate) struct CompactSummary {
    pub(crate) hash: SigHash,
    pub(crate) sig: Sig,
    pub(crate) sig_len: usize,
    pub(crate) ord: OrdCounts,
}

impl CompactSummary {
    /// From a complete graph and its rows. `Err` is a §8 input error
    /// (`Sig::of`): a declared visible name never spawned.
    pub(crate) fn of(
        exec: CompleteExecution<'_>,
        wobs: &Wobs,
        visible: &[String],
    ) -> Result<Self, crate::conformance::obs::ObsError> {
        let sig = Sig::of(exec, wobs, visible)?;
        let text = format!("{sig:?}");
        let ord = OrdCounts::of(exec.graph(), wobs, visible);
        Ok(Self {
            hash: hash128(&text),
            sig,
            sig_len: text.len(),
            ord,
        })
    }

    /// One program's compact summary at a completion, or a panic naming the
    /// program on a §8 violation — the twin of `stateful::summarise`.
    pub(crate) fn at_completion(graph: &ExecutionGraph, visible: &[String], program: &str) -> Self {
        let exec = CompleteExecution::assume_finished_at_gate(graph);
        let w = wobs(graph, visible).unwrap_or_else(|e| {
            panic!("conformance: the {program} program is not a valid input: {e}")
        });
        Self::of(exec, &w, visible).unwrap_or_else(|e| {
            panic!("conformance: the {program} program is not a valid input: {e}")
        })
    }

    /// The memo and deduplication identity.
    pub(crate) fn key(&self) -> (SigHash, OrdCounts) {
        (self.hash, self.ord.clone())
    }
}

/// One held order with its run-wide admission number.
#[derive(Clone, Debug)]
pub(crate) struct Entry {
    pub(crate) seq: u64,
    pub(crate) ord: OrdCounts,
}

/// One signature's bucket: the values once, the orders as counts.
#[derive(Clone, Debug)]
pub(crate) struct Bucket {
    pub(crate) sig: Sig,
    sig_len: usize,
    pub(crate) orders: Vec<Entry>,
}

/// The index's own counters (frozen §7); the engines add theirs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompactStats {
    /// The antichain flag the index ran with (forced off under `Bounded(n)`).
    pub antichain_effective: bool,
    /// Held entries at the end.
    pub entries: usize,
    /// Live buckets at the end.
    pub buckets: usize,
    /// The largest bucket size reached at any time.
    pub bucket_max: usize,
    /// Insertions that stored an entry.
    pub admitted: usize,
    /// Insertions refused as exact duplicates.
    pub duplicates: usize,
    pub antichain_dropped_new: usize,
    pub antichain_dropped_old: usize,
    /// `cmp` calls started by insertions (the duplicate scan included).
    pub insert_tests: usize,
    /// `cmp` calls started by queries.
    pub containment_tests: usize,
    /// Σ payload bytes of the held entries at the end.
    pub summary_bytes: usize,
    /// Σ rendering length of the live buckets' signatures.
    pub sig_bytes: usize,
    /// Complete-first only (zero on the stateful engine).
    pub memo_on: bool,
    pub memo_hits: usize,
    pub memo_entries: usize,
    pub memo_clears: usize,
    /// Distinct implementation summaries over the run, by `(SigHash,
    /// OrdCounts)` (step 0's counter under the compact identity).
    pub impl_distinct_summaries: usize,
}

/// The outcome of an insertion (frozen §4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Inserted {
    Stored(u64),
    Duplicate,
    DroppedNew,
}

/// The outcome of a query (frozen §4.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Covers {
    /// No bucket for the signature.
    NoBucket,
    /// The bucket exists; the answering entry's `seq`.
    Found(u64),
    /// The bucket exists; no held entry is `≤` the query.
    NotFound,
}

/// The bucket index (§5.1 item 3).
#[derive(Clone, Debug)]
pub(crate) struct CompactIndex {
    buckets: HashMap<SigHash, Bucket>,
    antichain: bool,
    next_seq: u64,
    stats: CompactStats,
}

impl CompactIndex {
    pub(crate) fn new(antichain: bool) -> Self {
        Self {
            buckets: HashMap::new(),
            antichain,
            next_seq: 0,
            stats: CompactStats {
                antichain_effective: antichain,
                ..CompactStats::default()
            },
        }
    }

    pub(crate) fn antichain(&self) -> bool {
        self.antichain
    }

    pub(crate) fn stats(&self) -> &CompactStats {
        &self.stats
    }

    pub(crate) fn stats_mut(&mut self) -> &mut CompactStats {
        &mut self.stats
    }

    /// Held entries.
    pub(crate) fn len(&self) -> usize {
        self.stats.entries
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.stats.entries == 0
    }

    pub(crate) fn bucket(&self, hash: SigHash) -> Option<&Bucket> {
        self.buckets.get(&hash)
    }

    pub(crate) fn buckets(&self) -> impl Iterator<Item = (&SigHash, &Bucket)> {
        self.buckets.iter()
    }

    /// Frozen §4.1. Panics on a 128-bit collision (C2).
    pub(crate) fn insert(&mut self, s: &CompactSummary) -> Inserted {
        let antichain = self.antichain;
        let stats = &mut self.stats;
        let bucket = match self.buckets.entry(s.hash) {
            MapEntry::Occupied(e) => {
                let b = e.into_mut();
                assert!(
                    b.sig == s.sig,
                    "conformance: 128-bit signature hash collision at an insertion"
                );
                b
            }
            MapEntry::Vacant(e) => {
                stats.buckets += 1;
                stats.sig_bytes += s.sig_len;
                e.insert(Bucket {
                    sig: s.sig.clone(),
                    sig_len: s.sig_len,
                    orders: Vec::new(),
                })
            }
        };
        let mut dominated: Vec<usize> = Vec::new();
        for (i, held) in bucket.orders.iter().enumerate() {
            stats.insert_tests += 1;
            match held.ord.cmp(&s.ord) {
                Some(Ordering::Equal) => {
                    stats.duplicates += 1;
                    return Inserted::Duplicate;
                }
                Some(Ordering::Less) if antichain => {
                    stats.antichain_dropped_new += 1;
                    return Inserted::DroppedNew;
                }
                Some(Ordering::Greater) if antichain => dominated.push(i),
                _ => {}
            }
        }
        if !dominated.is_empty() {
            let mut i = 0;
            let mut removed_bytes = 0;
            bucket.orders.retain(|e| {
                let keep = !dominated.contains(&i);
                if !keep {
                    removed_bytes += e.ord.payload_bytes();
                }
                i += 1;
                keep
            });
            stats.antichain_dropped_old += dominated.len();
            stats.entries -= dominated.len();
            stats.summary_bytes -= removed_bytes;
        }
        let seq = self.next_seq;
        self.next_seq += 1;
        bucket.orders.push(Entry {
            seq,
            ord: s.ord.clone(),
        });
        stats.admitted += 1;
        stats.entries += 1;
        stats.summary_bytes += s.ord.payload_bytes();
        stats.bucket_max = stats.bucket_max.max(bucket.orders.len());
        Inserted::Stored(seq)
    }

    /// Frozen §4.2: the first held entry `≤` the query answers.
    pub(crate) fn covers(&mut self, s: &CompactSummary) -> Covers {
        let Some(bucket) = self.buckets.get(&s.hash) else {
            return Covers::NoBucket;
        };
        assert!(
            bucket.sig == s.sig,
            "conformance: 128-bit signature hash collision at a query"
        );
        for held in &bucket.orders {
            self.stats.containment_tests += 1;
            if held.ord.le(&s.ord) {
                return Covers::Found(held.seq);
            }
        }
        Covers::NotFound
    }

    /// Remove one entry by its bucket and admission number (eviction); the
    /// bucket is dropped when it empties.
    pub(crate) fn remove(&mut self, hash: SigHash, seq: u64) -> Option<OrdCounts> {
        let bucket = self.buckets.get_mut(&hash)?;
        let i = bucket.orders.iter().position(|e| e.seq == seq)?;
        let removed = bucket.orders.remove(i);
        self.stats.entries -= 1;
        self.stats.summary_bytes -= removed.ord.payload_bytes();
        if bucket.orders.is_empty() {
            self.stats.sig_bytes -= bucket.sig_len;
            self.stats.buckets -= 1;
            self.buckets.remove(&hash);
        }
        Some(removed.ord)
    }
}

/// The outcome of a cache probe.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Probe {
    /// Answered by the memo; no bucket query.
    MemoHit,
    /// Answered by the bucket query (the summary joins the memo).
    Hit,
    Miss,
}

/// The complete-first cache on the bucket index (§5.1 item 4(b)).
#[derive(Clone, Debug)]
pub(crate) struct CompactCache {
    index: CompactIndex,
    capacity: Capacity,
    /// `Bounded(n)` only: the global admission order.
    fifo: VecDeque<(SigHash, u64)>,
    /// `Bounded(n)` only: every summary evicted so far (re-admission detection).
    evicted: HashSet<(SigHash, OrdCounts)>,
    /// `Some` when the knob is on.
    memo: Option<HashSet<(SigHash, OrdCounts)>>,
    admissions: usize,
    evictions: usize,
    readmissions: usize,
    memo_hits: usize,
    memo_clears: usize,
}

impl CompactCache {
    /// The antichain runs only when requested **and** the capacity is not
    /// `Bounded(n)` (frozen §4.3).
    pub(crate) fn new(capacity: Capacity, antichain: bool, probe_memo: bool) -> Self {
        let effective = antichain && !matches!(capacity, Capacity::Bounded(_));
        Self {
            index: CompactIndex::new(effective),
            capacity,
            fifo: VecDeque::new(),
            evicted: HashSet::new(),
            memo: probe_memo.then(HashSet::new),
            admissions: 0,
            evictions: 0,
            readmissions: 0,
            memo_hits: 0,
            memo_clears: 0,
        }
    }

    pub(crate) fn capacity(&self) -> Capacity {
        self.capacity
    }

    pub(crate) fn index(&self) -> &CompactIndex {
        &self.index
    }

    pub(crate) fn len(&self) -> usize {
        self.index.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.index.is_empty()
    }

    pub(crate) fn admissions(&self) -> usize {
        self.admissions
    }

    pub(crate) fn evictions(&self) -> usize {
        self.evictions
    }

    pub(crate) fn readmissions(&self) -> usize {
        self.readmissions
    }

    pub(crate) fn memo_len(&self) -> usize {
        self.memo.as_ref().map_or(0, HashSet::len)
    }

    /// The index's counters with the cache's memo fields filled in.
    pub(crate) fn stats(&self) -> CompactStats {
        let mut s = self.index.stats().clone();
        s.memo_on = self.memo.is_some();
        s.memo_hits = self.memo_hits;
        s.memo_entries = self.memo_len();
        s.memo_clears = self.memo_clears;
        s
    }

    pub(crate) fn stats_mut(&mut self) -> &mut CompactStats {
        self.index.stats_mut()
    }

    /// Frozen §5 then §4.2: the memo first, then the bucket query; a bucket
    /// hit extends the memo.
    pub(crate) fn probe(&mut self, s: &CompactSummary) -> Probe {
        if let Some(memo) = self.memo.as_ref() {
            if memo.contains(&s.key()) {
                // Gate 4 B1: the memo's identity is the hash, so a memo hit
                // is answered only after the bucket of that hash — which
                // every memo entry has, since the memo is extended at a hit
                // or an admission and cleared on every eviction — carries
                // the query's signature (frozen C2: a collision panics, it
                // never answers).
                let bucket = self
                    .index
                    .bucket(s.hash)
                    .expect("conformance: a memoised summary has no bucket");
                assert!(
                    bucket.sig == s.sig,
                    "conformance: 128-bit signature hash collision at a memo hit"
                );
                self.memo_hits += 1;
                return Probe::MemoHit;
            }
        }
        match self.index.covers(s) {
            Covers::Found(_) => {
                if let Some(memo) = self.memo.as_mut() {
                    memo.insert(s.key());
                }
                Probe::Hit
            }
            Covers::NoBucket | Covers::NotFound => Probe::Miss,
        }
    }

    /// Admit a sweep's witness `witness`, found for the implementation
    /// summary `probed`. `false` when nothing was stored: under `Zero`
    /// (nothing is ever admitted), or because the index already holds an
    /// equal or dominating entry — which the caller treats as today's "the
    /// probe should have hit" assertion. Under `Bounded(n)` the oldest entry
    /// is evicted first when the cache is full, and every eviction clears the
    /// memo; the admission then extends the memo with `probed`.
    pub(crate) fn admit(&mut self, witness: &CompactSummary, probed: &CompactSummary) -> bool {
        if matches!(self.capacity, Capacity::Zero | Capacity::Bounded(0)) {
            return false;
        }
        if let Capacity::Bounded(n) = self.capacity {
            while self.index.len() >= n {
                let Some((hash, seq)) = self.fifo.pop_front() else {
                    break;
                };
                if let Some(ord) = self.index.remove(hash, seq) {
                    self.evicted.insert((hash, ord));
                    self.evictions += 1;
                    if let Some(memo) = self.memo.as_mut() {
                        memo.clear();
                        self.memo_clears += 1;
                    }
                }
            }
        }
        let seq = match self.index.insert(witness) {
            Inserted::Stored(seq) => seq,
            Inserted::Duplicate | Inserted::DroppedNew => return false,
        };
        self.admissions += 1;
        if matches!(self.capacity, Capacity::Bounded(_)) {
            if self.evicted.contains(&witness.key()) {
                self.readmissions += 1;
            }
            self.fifo.push_back((witness.hash, seq));
        }
        if let Some(memo) = self.memo.as_mut() {
            memo.insert(probed.key());
        }
        true
    }
}
