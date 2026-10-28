//! `COMPACT-INDEX` (the Monday slice, §5; phase 2, `COMPACT-INDEX-PHASE2.md`
//! §1 items 1–3; frozen semantics in `plan/traceForge/log/dev/
//! COMPACT-INDEX.frozen.md` and `COMPACT-INDEX-P2.frozen.md`): the compact
//! summary, the bucket index, and the complete-first cache built on it.
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
//! thread has more than 255 visible events, then `u16` throughout; a thread
//! beyond `u16::MAX` visible events is refused (gate 4 B2).
//!
//! **The bucket key** (phase 2 D1, P2-frozen §1) is a 128-bit hash of the
//! signature's **shape** (`Sig::hash128`, `sig.rs`: per thread the observation
//! shapes and the status, walked once into two seeded hashers — `MIN-ENGINES`
//! E4; before it a projection of the shape through a derived `Hash`) — never of
//! a rendering.
//! `sig(a) == sig(b)` implies `key(a) == key(b)`, so equal signatures always
//! meet in one bucket; unequal signatures of one shape share it, each in its
//! own **slot**, resolved by `Sig ==` (`msg_equals`) at every insertion and
//! every query. A query whose signature matches no slot holding an order is a
//! signature miss, never an answer. A 128-bit collision between two shapes
//! only puts them in one bucket, where `Sig ==` still separates them.
//!
//! **The rendering hint** (P3, P2-frozen §7) — gone since `MIN-ENGINES` E4.
//! Each bucket mapped a 64-bit hash of a signature's `Debug` rendering to slot
//! indices (under the `print_vals` feature only); resolution tried the hinted
//! slots first and then the others, all by `Sig ==`, so the hint ordered
//! candidates and decided nothing, and a slot found only by the second pass
//! was an alias, counted. Now `render_hash` is `None` under both feature
//! sets, the hint maps stay empty, resolution is the plain creation-order
//! scan, `sig_aliases` is 0 and `sig_tests` counts to the hit's position + 1.
//!
//! **Signature ids** (P1, P2; P2-frozen §7). Only an insertion creates a slot,
//! with a run-wide `sig_id` (allocation checked); a query never creates one.
//! Slots are never removed (an emptied slot keeps its signature and its id),
//! so the memo and the eviction history key on the exact `(sig_id,
//! OrdCounts)`.
//!
//! **The query** (§5.1 item 3; frozen §4.2; phase 2 D4) scans the slot's
//! orders in admission order; the first held order `q ≤ g` answers. `≤` reads
//! coordinates left to right and stops at the first one where the held count
//! exceeds the query's (`coordinates_compared` counts the reads).
//!
//! **The slot structures** (phase 2 items 4, 5, 7; P2-frozen §6, §6.1), the
//! [`BucketKind`] knob: the scan above; the **inverted index** (built once the
//! slot first holds `max(t, 1)` orders, kept from then on: per coordinate `i`
//! and value `v` the bitset `Ex[i][v]` of positions whose count at `i`
//! exceeds `v`, a `live` bitset, positions in admission order never reused;
//! a query's answer is the lowest live position outside `⋃_i Ex[i][q_i]`);
//! the **multiset trie** (a trie over the coordinates in order, each node
//! holding the smallest live `seq` below it; a query descends only into
//! children whose value is `≤` the query's and whose smallest `seq` beats the
//! best found). All three answer with the live order `≤` the query that has
//! the smallest admission number, which is the scan's answer; the duplicate
//! check and the antichain stay the scan's `cmp` over the slot's vector.
//!
//! **The antichain** (knob, default on): an insertion dominated by a held
//! order of its slot (`held ≤ new`) is dropped; held orders dominated by the
//! new one are removed. Sound for the yes/no probe: if `c^{M₁} ≤ c^{M₂} ≤ c^G`
//! then `M₁` covers `G`. Exact duplicates are refused before any antichain
//! action.
//!
//! **The complete-first cache** (§5.1 item 4(b); frozen §4.3, §5): the index
//! with the capacity rules (`Zero` admits nothing; `Bounded(n)` FIFO over the
//! global admission order, the antichain **off**; `Unbounded`), and the probe
//! memo — the implementation summaries whose probe hit, consulted after the
//! signature is resolved and before the order query, extended at a hit and at
//! an admission, cleared on every eviction. Only hits are memoised: a miss may
//! become a hit after a sweep admits a witness.
//!
//! Everything here is a pure function of graphs and their `Wobs` rows, as
//! `sig.rs` is; nothing consults engine stamps or insertion order beyond the
//! slots' own admission order.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use crate::conformance::config::{BucketKind, Capacity};
use crate::conformance::morphism::{statuses, CompleteExecution};
use crate::conformance::obs::{wobs, Wobs};
use crate::conformance::sig::Sig;
use crate::exec_graph::ExecutionGraph;

/// The bucket key: a 128-bit hash of the signature's shape (P2-frozen §1).
pub(crate) type SigHash = u128;

/// A signature's run-wide id (P2-frozen §1).
pub(crate) type SigId = u32;

/// The memo's and the eviction history's identity: the exact `(sig_id,
/// counts)` (P2-frozen §1, §7).
pub(crate) type MemoKey = (SigId, OrdCounts);

/// P3 (P2-frozen §7) had here, under `print_vals`, a 64-bit hash of the
/// signature's `Debug` rendering as a hint ordering the slot search.
/// `MIN-ENGINES` E4: no hint — `None` under both feature sets, so the hint
/// maps stay empty and the slot search is the plain creation-order scan
/// (`sig_aliases` is 0; `sig_tests` counts to the hit's position + 1).
fn render_hash(_sig: &Sig) -> Option<u64> {
    None
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
/// settles `None`. Used by the antichain at insertion.
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

/// Phase 2 D4: `a ≤ b` pointwise, `false` at the first coordinate where
/// `a` exceeds `b`; `coords` gains the number of coordinates read.
fn le_counts<T: Ord>(a: &[T], b: &[T], coords: &mut usize) -> bool {
    assert_eq!(
        a.len(),
        b.len(),
        "conformance: OrdCounts of different signatures compared"
    );
    for (x, y) in a.iter().zip(b) {
        *coords += 1;
        if x > y {
            return false;
        }
    }
    true
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

    /// `self ≤ other` pointwise, exiting at the first exceeding coordinate
    /// (D4); `coords` gains the coordinates read.
    pub(crate) fn le_counted(&self, other: &Self, coords: &mut usize) -> bool {
        match (self, other) {
            (OrdCounts::U8(a), OrdCounts::U8(b)) => le_counts(a, b, coords),
            (OrdCounts::U16(a), OrdCounts::U16(b)) => le_counts(a, b, coords),
            _ => panic!("conformance: OrdCounts of different widths compared"),
        }
    }

    /// `self ≤ other` pointwise (D4's exit; the read count discarded).
    pub(crate) fn le(&self, other: &Self) -> bool {
        let mut coords = 0;
        self.le_counted(other, &mut coords)
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

    /// The count at coordinate `i`.
    pub(crate) fn at(&self, i: usize) -> u16 {
        match self {
            OrdCounts::U8(v) => u16::from(v[i]),
            OrdCounts::U16(v) => v[i],
        }
    }
}

/// What the index reads of a complete graph: the signature with its values,
/// its shape's bucket hash, its estimated byte size (P2-frozen §1), and the
/// counts.
#[derive(Clone, Debug)]
pub(crate) struct CompactSummary {
    pub(crate) hash: SigHash,
    pub(crate) sig: Sig,
    /// `32 × Σ_t |w_t| + 16 × T` (P2-frozen §1).
    pub(crate) sig_est: usize,
    pub(crate) ord: OrdCounts,
}

impl CompactSummary {
    /// From a complete graph and its rows. `Err` is a §8 input error
    /// (`Sig::of`): a declared visible name never spawned.
    pub(crate) fn of(
        exec: CompleteExecution<'_>,
        wobs: Wobs,
        visible: &[String],
    ) -> Result<Self, crate::conformance::obs::ObsError> {
        // `MIN-ENGINES` E4: the statuses (the §8 refusal first, as before), the
        // count and the order borrow the rows; the signature then takes them
        // and is hashed in one pass.
        let statuses = statuses(exec, &wobs, visible)?;
        let mut names: Vec<&str> = visible.iter().map(String::as_str).collect();
        names.sort_unstable();
        names.dedup();
        let observations: usize = names.iter().map(|n| wobs.of(n).len()).sum();
        let ord = OrdCounts::of(exec.graph(), &wobs, visible);
        let sig_est = 32 * observations + 16 * names.len();
        let sig = Sig::from_rows(statuses, wobs, visible);
        Ok(Self {
            hash: sig.hash128(),
            sig,
            sig_est,
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
        Self::of(exec, w, visible).unwrap_or_else(|e| {
            panic!("conformance: the {program} program is not a valid input: {e}")
        })
    }
}

/// One held order with its run-wide admission number.
#[derive(Clone, Debug)]
pub(crate) struct Entry {
    pub(crate) seq: u64,
    pub(crate) ord: OrdCounts,
}

/// One signature's slot in its shape's bucket: the values once, the orders
/// as counts in admission order. Never removed (P2-frozen §1).
#[derive(Clone, Debug)]
pub(crate) struct SigSlot {
    pub(crate) sig_id: SigId,
    pub(crate) sig: Sig,
    sig_est: usize,
    pub(crate) orders: Vec<Entry>,
    /// Item 4: `Some` once built (`BucketKind::Inverted` only).
    inverted: Option<Inverted>,
    /// Item 5: `Some` from the first order (`BucketKind::Trie` only).
    trie: Option<Trie>,
}

impl SigSlot {
    /// Items 4, 5: index the slot's newest order; the inverted index is built
    /// over every held order when the slot first holds `max(t, 1)`.
    fn index_newest(&mut self, kind: BucketKind) {
        let e = self
            .orders
            .last()
            .expect("conformance: an order was just stored");
        match kind {
            BucketKind::Scan => {}
            BucketKind::Inverted(t) => match self.inverted.as_mut() {
                Some(inv) => inv.push(e.seq, &e.ord),
                None if self.orders.len() >= t.max(1) => {
                    let mut inv = Inverted::new(e.ord.len());
                    for held in &self.orders {
                        inv.push(held.seq, &held.ord);
                    }
                    self.inverted = Some(inv);
                }
                None => {}
            },
            BucketKind::Trie => self
                .trie
                .get_or_insert_with(|| Trie::new(e.ord.len()))
                .insert(e.seq, &e.ord),
        }
    }

    /// Items 4, 5: a removed order leaves the slot's structures.
    fn unindex(&mut self, e: &Entry) {
        if let Some(inv) = self.inverted.as_mut() {
            inv.remove(e.seq, &e.ord);
        }
        if let Some(trie) = self.trie.as_mut() {
            trie.remove(e.seq, &e.ord);
        }
    }
}

/// Item 4 (P2-frozen §6, §6.1): one slot's inverted index. Positions are
/// allocated in admission order from the build and never reused; every bitset
/// is dense, `⌈P/64⌉` words.
#[derive(Clone, Debug)]
struct Inverted {
    /// The `seq` of each position, ascending.
    seq_of: Vec<u64>,
    /// `⌈P/64⌉`.
    words: usize,
    live: Vec<u64>,
    /// `ex[i][v]`: the positions whose count at coordinate `i` exceeds `v`,
    /// for `v` below the largest count seen at `i`.
    ex: Vec<Vec<Vec<u64>>>,
}

impl Inverted {
    fn new(coords: usize) -> Self {
        Self {
            seq_of: Vec::new(),
            words: 0,
            live: Vec::new(),
            ex: vec![Vec::new(); coords],
        }
    }

    fn push(&mut self, seq: u64, ord: &OrdCounts) {
        let p = self.seq_of.len();
        self.seq_of.push(seq);
        if p / 64 + 1 > self.words {
            self.words = p / 64 + 1;
            self.live.resize(self.words, 0);
            for row in &mut self.ex {
                for bits in row.iter_mut() {
                    bits.resize(self.words, 0);
                }
            }
        }
        let (w, bit) = (p / 64, 1u64 << (p % 64));
        self.live[w] |= bit;
        for (i, row) in self.ex.iter_mut().enumerate() {
            let c = usize::from(ord.at(i));
            while row.len() < c {
                row.push(vec![0; self.words]);
            }
            for bits in &mut row[..c] {
                bits[w] |= bit;
            }
        }
    }

    fn remove(&mut self, seq: u64, ord: &OrdCounts) {
        let p = self
            .seq_of
            .binary_search(&seq)
            .expect("conformance: a held order has a position");
        let (w, bit) = (p / 64, 1u64 << (p % 64));
        self.live[w] &= !bit;
        for (i, row) in self.ex.iter_mut().enumerate() {
            for bits in &mut row[..usize::from(ord.at(i))] {
                bits[w] &= !bit;
            }
        }
    }

    /// The live order `≤ q` with the smallest `seq`: the union of the
    /// `Ex[i][q_i]` (every word of each), then the lowest set bit of `live ∧
    /// ¬excluded`, read word by word up to the first survivor. `words` counts
    /// the stored words read (P2-frozen §6.1).
    fn query(&self, q: &OrdCounts, words: &mut usize) -> Option<u64> {
        let mut excluded = vec![0u64; self.words];
        for (i, row) in self.ex.iter().enumerate() {
            if let Some(bits) = row.get(usize::from(q.at(i))) {
                for (x, b) in excluded.iter_mut().zip(bits) {
                    *x |= b;
                }
                *words += self.words;
            }
        }
        for (w, (live, x)) in self.live.iter().zip(&excluded).enumerate() {
            *words += 1;
            let survivors = live & !x;
            if survivors != 0 {
                return Some(self.seq_of[w * 64 + survivors.trailing_zeros() as usize]);
            }
        }
        None
    }
}

/// Item 5 (P2-frozen §6): one slot's multiset trie, an arena of nodes. A node
/// at depth `d < L` has children keyed by the count at coordinate `d`,
/// ascending; a node at depth `L` is one order's leaf. Every node holds the
/// smallest live `seq` below it (`u64::MAX` when none).
#[derive(Clone, Debug)]
struct Trie {
    depth: usize,
    nodes: Vec<TrieNode>,
    free: Vec<usize>,
}

#[derive(Clone, Debug)]
struct TrieNode {
    children: Vec<(u16, usize)>,
    min_seq: u64,
}

impl TrieNode {
    fn empty() -> Self {
        Self {
            children: Vec::new(),
            min_seq: u64::MAX,
        }
    }
}

impl Trie {
    fn new(depth: usize) -> Self {
        Self {
            depth,
            nodes: vec![TrieNode::empty()],
            free: Vec::new(),
        }
    }

    fn alloc(&mut self) -> usize {
        match self.free.pop() {
            Some(n) => {
                self.nodes[n] = TrieNode::empty();
                n
            }
            None => {
                self.nodes.push(TrieNode::empty());
                self.nodes.len() - 1
            }
        }
    }

    fn child(&self, node: usize, v: u16) -> Result<usize, usize> {
        self.nodes[node]
            .children
            .binary_search_by_key(&v, |&(k, _)| k)
    }

    /// Exact duplicates are refused before this (the scan's `cmp`), so every
    /// leaf holds one order.
    fn insert(&mut self, seq: u64, ord: &OrdCounts) {
        let mut cur = 0;
        self.nodes[0].min_seq = self.nodes[0].min_seq.min(seq);
        for d in 0..self.depth {
            let v = ord.at(d);
            cur = match self.child(cur, v) {
                Ok(j) => self.nodes[cur].children[j].1,
                Err(j) => {
                    let n = self.alloc();
                    self.nodes[cur].children.insert(j, (v, n));
                    n
                }
            };
            self.nodes[cur].min_seq = self.nodes[cur].min_seq.min(seq);
        }
    }

    /// Delete the order's leaf, prune the emptied nodes, recompute `min_seq`
    /// up the path.
    fn remove(&mut self, seq: u64, ord: &OrdCounts) {
        let mut path = Vec::with_capacity(self.depth + 1);
        let mut cur = 0;
        path.push(cur);
        for d in 0..self.depth {
            let j = self
                .child(cur, ord.at(d))
                .expect("conformance: a held order's path is in the trie");
            cur = self.nodes[cur].children[j].1;
            path.push(cur);
        }
        debug_assert_eq!(self.nodes[cur].min_seq, seq);
        if self.depth == 0 {
            self.nodes[0].min_seq = u64::MAX;
            return;
        }
        let mut dropped = true;
        for d in (0..self.depth).rev() {
            let node = path[d];
            if dropped {
                let j = self
                    .child(node, ord.at(d))
                    .expect("conformance: a held order's path is in the trie");
                self.nodes[node].children.remove(j);
                self.free.push(path[d + 1]);
            }
            dropped = d > 0 && self.nodes[node].children.is_empty();
            if !dropped {
                let m = self.nodes[node]
                    .children
                    .iter()
                    .map(|&(_, c)| self.nodes[c].min_seq)
                    .min()
                    .unwrap_or(u64::MAX);
                self.nodes[node].min_seq = m;
            }
        }
    }

    /// The live order `≤ q` with the smallest `seq`; `visited` counts the
    /// nodes entered, the root included.
    fn query(&self, q: &OrdCounts, visited: &mut usize) -> Option<u64> {
        let mut best = u64::MAX;
        self.descend(0, 0, q, &mut best, visited);
        (best != u64::MAX).then_some(best)
    }

    fn descend(&self, node: usize, d: usize, q: &OrdCounts, best: &mut u64, visited: &mut usize) {
        *visited += 1;
        if d == self.depth {
            *best = (*best).min(self.nodes[node].min_seq);
            return;
        }
        let qd = q.at(d);
        for &(v, c) in &self.nodes[node].children {
            if v > qd {
                break;
            }
            if self.nodes[c].min_seq < *best {
                self.descend(c, d + 1, q, best, visited);
            }
        }
    }
}

/// One shape's bucket: a slot per distinct signature of the shape, in the
/// order the signatures were first inserted.
#[derive(Clone, Debug, Default)]
pub(crate) struct Bucket {
    pub(crate) slots: Vec<SigSlot>,
    /// Slots holding at least one order.
    occupied: usize,
    /// P3: rendering hash → slot indices (creations, then aliases).
    hint: HashMap<u64, Vec<usize>>,
}

/// The index's own counters (frozen §7, P2-frozen §1–§3); the engines add
/// theirs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompactStats {
    /// The antichain flag the index ran with (forced off under `Bounded(n)`).
    pub antichain_effective: bool,
    /// Held orders at the end.
    pub entries: usize,
    /// Buckets (shapes) with at least one held order at the end.
    pub buckets: usize,
    /// The largest number of orders one signature's slot held at any time.
    pub bucket_max: usize,
    /// Slots (signatures) with at least one held order at the end.
    pub signatures: usize,
    /// Every slot created: signatures inserted at least once (P1).
    pub signatures_seen: usize,
    /// `Sig ==` comparisons started in slot resolution (insertions and
    /// queries; the hinted slots and the rest, P3).
    pub sig_tests: usize,
    /// Slots found only by the scan after the hinted ones: equal signatures
    /// with different renderings, each then recorded in the hint (P3).
    pub sig_aliases: usize,
    /// Insertions that stored an order.
    pub admitted: usize,
    /// Insertions refused as exact duplicates.
    pub duplicates: usize,
    pub antichain_dropped_new: usize,
    pub antichain_dropped_old: usize,
    /// `cmp` calls started by insertions (the duplicate scan included).
    pub insert_tests: usize,
    /// `≤` tests started by queries.
    pub containment_tests: usize,
    /// Coordinates read by the queries' `≤` tests (D4).
    pub coordinates_compared: usize,
    /// Item 4: queries answered through an inverted index, and the stored
    /// 64-bit words they read; `Some` iff `BucketKind::Inverted`.
    pub inverted_used: Option<usize>,
    pub inverted_words: Option<usize>,
    /// Item 5: trie nodes entered by queries; `Some` iff `BucketKind::Trie`.
    pub trie_nodes_visited: Option<usize>,
    /// Σ payload bytes of the held orders at the end.
    pub summary_bytes: usize,
    /// Σ `32 × Σ_t |w_t| + 16 × T` over the occupied slots at the end.
    pub sig_bytes_est: usize,
    /// Complete-first only (zero on the stateful engine).
    pub memo_on: bool,
    pub memo_hits: usize,
    pub memo_entries: usize,
    pub memo_clears: usize,
    /// Distinct implementation summaries over the run by the exact `(Sig,
    /// OrdCounts)`, `Some` iff the `impl_distinct` knob is on (D6, P1).
    pub impl_distinct_summaries: Option<usize>,
}

/// The outcome of an insertion (frozen §4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Inserted {
    Stored(u64),
    Duplicate,
    DroppedNew,
}

/// The outcome of a query (frozen §4.2, P2-frozen §1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Covers {
    /// No bucket for the shape (no insertion of that shape so far).
    NoBucket,
    /// The shape's bucket exists, but the signature has no slot or an
    /// emptied one.
    NoSig,
    /// The answering order's `seq`.
    Found(u64),
    /// The signature's slot holds orders; none is `≤` the query.
    NotFound,
}

/// The bucket index (§5.1 item 3, phase 2 items 1–2).
#[derive(Clone, Debug)]
pub(crate) struct CompactIndex {
    buckets: HashMap<SigHash, Bucket>,
    antichain: bool,
    /// Items 4, 5, 7: the slot structure.
    bucket: BucketKind,
    next_seq: u64,
    next_sig_id: SigId,
    stats: CompactStats,
}

impl CompactIndex {
    /// The slice's scan.
    pub(crate) fn new(antichain: bool) -> Self {
        Self::with_bucket(antichain, BucketKind::Scan)
    }

    pub(crate) fn with_bucket(antichain: bool, bucket: BucketKind) -> Self {
        let inverted = matches!(bucket, BucketKind::Inverted(_));
        Self {
            buckets: HashMap::new(),
            antichain,
            bucket,
            next_seq: 0,
            next_sig_id: 0,
            stats: CompactStats {
                antichain_effective: antichain,
                inverted_used: inverted.then_some(0),
                inverted_words: inverted.then_some(0),
                trie_nodes_visited: (bucket == BucketKind::Trie).then_some(0),
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

    /// Held orders.
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

    /// P3 (P2-frozen §7): the slot of `sig` in `bucket` by `Sig ==`, the
    /// hinted slots of its rendering hash `r` first, then the others in slot
    /// order; a slot found by the second pass is an alias, appended to `r`'s
    /// list. Every comparison counts in `sig_tests`. Creates nothing.
    fn find_in(
        stats: &mut CompactStats,
        bucket: &mut Bucket,
        sig: &Sig,
        r: Option<u64>,
    ) -> Option<usize> {
        let hinted: &[usize] = match r {
            Some(r) => bucket.hint.get(&r).map_or(&[][..], Vec::as_slice),
            None => &[],
        };
        for &i in hinted {
            stats.sig_tests += 1;
            if bucket.slots[i].sig == *sig {
                return Some(i);
            }
        }
        let mut found = None;
        for (i, slot) in bucket.slots.iter().enumerate() {
            if hinted.contains(&i) {
                continue;
            }
            stats.sig_tests += 1;
            if slot.sig == *sig {
                found = Some(i);
                break;
            }
        }
        let i = found?;
        if let Some(r) = r {
            bucket.hint.entry(r).or_default().push(i);
            stats.sig_aliases += 1;
        }
        Some(i)
    }

    /// P1: a query's resolution, never creating — whether the shape's bucket
    /// exists, and the signature's slot if it has one.
    fn find(&mut self, s: &CompactSummary) -> (bool, Option<usize>) {
        let Some(bucket) = self.buckets.get_mut(&s.hash) else {
            return (false, None);
        };
        let r = render_hash(&s.sig);
        (true, Self::find_in(&mut self.stats, bucket, &s.sig, r))
    }

    /// An insertion's resolution: the signature's slot, created (bucket and
    /// slot, with a fresh checked id, P2) when absent.
    fn slot_for_insert(&mut self, s: &CompactSummary) -> usize {
        let r = render_hash(&s.sig);
        let bucket = self.buckets.entry(s.hash).or_default();
        if let Some(i) = Self::find_in(&mut self.stats, bucket, &s.sig, r) {
            return i;
        }
        let sig_id = self.next_sig_id;
        self.next_sig_id = sig_id
            .checked_add(1)
            .expect("conformance: more than u32::MAX signatures (SigId overflow)");
        bucket.slots.push(SigSlot {
            sig_id,
            sig: s.sig.clone(),
            sig_est: s.sig_est,
            orders: Vec::new(),
            inverted: None,
            trie: None,
        });
        let i = bucket.slots.len() - 1;
        if let Some(r) = r {
            bucket.hint.entry(r).or_default().push(i);
        }
        self.stats.signatures_seen += 1;
        i
    }

    /// Book a slot's change of occupancy (empty ↔ holding orders).
    fn occupancy(stats: &mut CompactStats, bucket: &mut Bucket, sig_est: usize, filled: bool) {
        if filled {
            stats.signatures += 1;
            stats.sig_bytes_est += sig_est;
            if bucket.occupied == 0 {
                stats.buckets += 1;
            }
            bucket.occupied += 1;
        } else {
            stats.signatures -= 1;
            stats.sig_bytes_est -= sig_est;
            bucket.occupied -= 1;
            if bucket.occupied == 0 {
                stats.buckets -= 1;
            }
        }
    }

    /// Frozen §4.1 inside the signature's slot; returns the signature's id
    /// with the outcome.
    pub(crate) fn insert(&mut self, s: &CompactSummary) -> (SigId, Inserted) {
        let si = self.slot_for_insert(s);
        let antichain = self.antichain;
        let kind = self.bucket;
        let stats = &mut self.stats;
        let bucket = self
            .buckets
            .get_mut(&s.hash)
            .expect("conformance: a resolved bucket exists");
        let sig_id = bucket.slots[si].sig_id;
        let mut dominated: Vec<usize> = Vec::new();
        for (i, held) in bucket.slots[si].orders.iter().enumerate() {
            stats.insert_tests += 1;
            match held.ord.cmp(&s.ord) {
                Some(Ordering::Equal) => {
                    stats.duplicates += 1;
                    return (sig_id, Inserted::Duplicate);
                }
                Some(Ordering::Less) if antichain => {
                    stats.antichain_dropped_new += 1;
                    return (sig_id, Inserted::DroppedNew);
                }
                Some(Ordering::Greater) if antichain => dominated.push(i),
                _ => {}
            }
        }
        let was_empty = bucket.slots[si].orders.is_empty();
        if !dominated.is_empty() {
            let slot = &mut bucket.slots[si];
            let mut removed_bytes = 0;
            let mut kept = Vec::with_capacity(slot.orders.len() - dominated.len());
            for (i, e) in std::mem::take(&mut slot.orders).into_iter().enumerate() {
                if dominated.contains(&i) {
                    removed_bytes += e.ord.payload_bytes();
                    slot.unindex(&e);
                } else {
                    kept.push(e);
                }
            }
            slot.orders = kept;
            stats.antichain_dropped_old += dominated.len();
            stats.entries -= dominated.len();
            stats.summary_bytes -= removed_bytes;
        }
        let seq = self.next_seq;
        self.next_seq = seq
            .checked_add(1)
            .expect("conformance: more than u64::MAX insertions (seq overflow)");
        let slot = &mut bucket.slots[si];
        slot.orders.push(Entry {
            seq,
            ord: s.ord.clone(),
        });
        slot.index_newest(kind);
        let (len, sig_est) = (slot.orders.len(), slot.sig_est);
        stats.admitted += 1;
        stats.entries += 1;
        stats.summary_bytes += s.ord.payload_bytes();
        stats.bucket_max = stats.bucket_max.max(len);
        if was_empty {
            Self::occupancy(stats, bucket, sig_est, true);
        }
        (sig_id, Inserted::Stored(seq))
    }

    /// Frozen §4.2 inside the signature's slot: the first held order `≤` the
    /// query answers (D4's exit). Returns the signature's id, `None` when it
    /// has no slot (P1: the query creates none), with the outcome.
    pub(crate) fn covers(&mut self, s: &CompactSummary) -> (Option<SigId>, Covers) {
        let (existed, si) = self.find(s);
        self.query_slot(s, existed, si)
    }

    /// The order query in an already resolved slot (one resolution per
    /// probe, P2-frozen §1, §7).
    fn query_slot(
        &mut self,
        s: &CompactSummary,
        existed: bool,
        si: Option<usize>,
    ) -> (Option<SigId>, Covers) {
        if !existed {
            return (None, Covers::NoBucket);
        }
        let Some(si) = si else {
            return (None, Covers::NoSig);
        };
        let stats = &mut self.stats;
        let slot = &self.buckets[&s.hash].slots[si];
        if slot.orders.is_empty() {
            return (Some(slot.sig_id), Covers::NoSig);
        }
        // Items 4, 5: a built structure answers, starting no `≤` test.
        let answered = |found: Option<u64>| found.map_or(Covers::NotFound, Covers::Found);
        if let Some(inv) = &slot.inverted {
            let mut words = 0;
            let found = inv.query(&s.ord, &mut words);
            bump(&mut stats.inverted_used, 1);
            bump(&mut stats.inverted_words, words);
            return (Some(slot.sig_id), answered(found));
        }
        if let Some(trie) = &slot.trie {
            let mut visited = 0;
            let found = trie.query(&s.ord, &mut visited);
            bump(&mut stats.trie_nodes_visited, visited);
            return (Some(slot.sig_id), answered(found));
        }
        for held in &slot.orders {
            stats.containment_tests += 1;
            if held.ord.le_counted(&s.ord, &mut stats.coordinates_compared) {
                return (Some(slot.sig_id), Covers::Found(held.seq));
            }
        }
        (Some(slot.sig_id), Covers::NotFound)
    }

    /// Remove one order by its bucket, signature id and admission number
    /// (eviction). The slot and the bucket stay, possibly empty (P2-frozen §1).
    pub(crate) fn remove(&mut self, hash: SigHash, sig_id: SigId, seq: u64) -> Option<OrdCounts> {
        let bucket = self.buckets.get_mut(&hash)?;
        let si = bucket.slots.iter().position(|s| s.sig_id == sig_id)?;
        let i = bucket.slots[si].orders.iter().position(|e| e.seq == seq)?;
        let removed = bucket.slots[si].orders.remove(i);
        bucket.slots[si].unindex(&removed);
        self.stats.entries -= 1;
        self.stats.summary_bytes -= removed.ord.payload_bytes();
        if bucket.slots[si].orders.is_empty() {
            let sig_est = bucket.slots[si].sig_est;
            Self::occupancy(&mut self.stats, bucket, sig_est, false);
        }
        Some(removed.ord)
    }
}

/// Add to a counter that exists only under its structure.
fn bump(counter: &mut Option<usize>, n: usize) {
    if let Some(c) = counter.as_mut() {
        *c += n;
    }
}

/// The outcome of a cache probe.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Probe {
    /// Answered by the memo; no order query.
    MemoHit,
    /// Answered by the order query (the summary joins the memo).
    Hit,
    Miss,
}

/// The complete-first cache on the bucket index (§5.1 item 4(b)).
#[derive(Clone, Debug)]
pub(crate) struct CompactCache {
    index: CompactIndex,
    capacity: Capacity,
    /// `Bounded(n)` only: the global admission order.
    fifo: VecDeque<(SigHash, SigId, u64)>,
    /// `Bounded(n)` only: every summary evicted so far (re-admission detection).
    evicted: HashSet<MemoKey>,
    /// `Some` when the knob is on.
    memo: Option<HashSet<MemoKey>>,
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
        Self::with_bucket(capacity, antichain, probe_memo, BucketKind::Scan)
    }

    /// With the slot structure of items 4, 5, 7.
    pub(crate) fn with_bucket(
        capacity: Capacity,
        antichain: bool,
        probe_memo: bool,
        bucket: BucketKind,
    ) -> Self {
        let effective = antichain && !matches!(capacity, Capacity::Bounded(_));
        Self {
            index: CompactIndex::with_bucket(effective, bucket),
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

    /// P2-frozen §1, §7, frozen §5, §4.2: the signature resolved in its
    /// bucket (never created, P1), then — when it has a slot — the memo by
    /// the exact `(sig_id, counts)`, then the order query; a hit extends the
    /// memo. Returns the outcome and the signature's id, `None` when it has no
    /// slot.
    pub(crate) fn probe(&mut self, s: &CompactSummary) -> (Probe, Option<SigId>) {
        let (existed, si) = self.index.find(s);
        let sig_id = si.map(|i| self.index.buckets[&s.hash].slots[i].sig_id);
        if let (Some(memo), Some(id)) = (self.memo.as_ref(), sig_id) {
            if memo.contains(&(id, s.ord.clone())) {
                self.memo_hits += 1;
                return (Probe::MemoHit, sig_id);
            }
        }
        let (_, covers) = self.index.query_slot(s, existed, si);
        match covers {
            Covers::Found(_) => {
                let id = sig_id.expect("conformance: a found order has a slot");
                if let Some(memo) = self.memo.as_mut() {
                    memo.insert((id, s.ord.clone()));
                }
                (Probe::Hit, sig_id)
            }
            Covers::NoBucket | Covers::NoSig | Covers::NotFound => (Probe::Miss, sig_id),
        }
    }

    /// Admit a sweep's witness `witness`, found for the implementation
    /// summary `probed` (whose probe missed). `false` when nothing was stored:
    /// under `Zero` (nothing is ever admitted), or because the index already
    /// holds an equal or dominating order — which the caller treats as today's
    /// "the probe should have hit" assertion. Under `Bounded(n)` the oldest
    /// order is evicted first when the cache is full, and every eviction
    /// clears the memo; the admission then extends the memo with `(the
    /// witness's sig_id, probed's counts)` (R1's order; P1, P2-frozen §7).
    pub(crate) fn admit(&mut self, witness: &CompactSummary, probed: &CompactSummary) -> bool {
        debug_assert!(
            witness.sig == probed.sig,
            "conformance: a sweep's witness has the probed summary's signature"
        );
        if matches!(self.capacity, Capacity::Zero | Capacity::Bounded(0)) {
            return false;
        }
        if let Capacity::Bounded(n) = self.capacity {
            while self.index.len() >= n {
                let Some((hash, sig_id, seq)) = self.fifo.pop_front() else {
                    break;
                };
                if let Some(ord) = self.index.remove(hash, sig_id, seq) {
                    self.evicted.insert((sig_id, ord));
                    self.evictions += 1;
                    if let Some(memo) = self.memo.as_mut() {
                        memo.clear();
                        self.memo_clears += 1;
                    }
                }
            }
        }
        let (sig_id, seq) = match self.index.insert(witness) {
            (id, Inserted::Stored(seq)) => (id, seq),
            (_, Inserted::Duplicate | Inserted::DroppedNew) => return false,
        };
        self.admissions += 1;
        if matches!(self.capacity, Capacity::Bounded(_)) {
            if self.evicted.contains(&(sig_id, witness.ord.clone())) {
                self.readmissions += 1;
            }
            self.fifo.push_back((witness.hash, sig_id, seq));
        }
        if let Some(memo) = self.memo.as_mut() {
            memo.insert((sig_id, probed.ord.clone()));
        }
        true
    }
}

// ---------------------------------------------------------------------------
// `SVERIFY-P` I2: the set index (`SVERIFY-P.md` §1 items 4–5; the criteria
// `plan/traceForge/criteria/SVERIFY-P-I2.md`). Added below `CompactCache`;
// nothing above this line changed (Q11 option (a): `CompactIndex` untouched).
// `SVERIFY-P` I2b (`criteria/SVERIFY-P-I2B.md`, the owner's rulings of
// 2026-10-26 §6 and §5): each order held once, in one `IndexMap` per slot
// that answers the duplicate check and the exact-hit probe; `exact_hits`.
// ---------------------------------------------------------------------------

/// One signature's slot in the set index: the representative signature (the
/// first occurrence's, I2-2 — later equal occurrences do not replace it) and
/// its orders, each held **once** (I2b-1): the order is the key, its
/// admission number the value, in one `IndexMap` that keeps admission order
/// for the scan and answers the duplicate check and the exact-hit probe by
/// hash, with no `cmp`.
/// `MIN-ENGINES` E7b: the stateless engine's witness cache on the set index
/// (I2): `CompactCache`'s capacity rules and tallies — FIFO eviction under
/// `Bounded(n)` with re-admission detection by `(sig_id, ord)` — with no memo
/// and no antichain (neither is read under `Set`). A probe answers as the set
/// index's `covers`; an admission evicts first, then inserts. After a missed
/// probe no held order is `≤` the probed summary, and the witness's order is
/// `≤` it, so the witness's order is not held: the insertion stores.
#[derive(Clone, Debug)]
pub(crate) struct SetCache {
    index: SetIndex,
    capacity: Capacity,
    fifo: VecDeque<(SigHash, SigId, u64)>,
    evicted: HashSet<MemoKey>,
    admissions: usize,
    evictions: usize,
    readmissions: usize,
}

impl SetCache {
    pub(crate) fn new(capacity: Capacity) -> Self {
        Self {
            index: SetIndex::new(),
            capacity,
            fifo: VecDeque::new(),
            evicted: HashSet::new(),
            admissions: 0,
            evictions: 0,
            readmissions: 0,
        }
    }

    pub(crate) fn capacity(&self) -> Capacity {
        self.capacity
    }

    pub(crate) fn index(&self) -> &SetIndex {
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

    /// The set index's counters in the compact record (I2b-7's mapping; the
    /// memo fields off).
    pub(crate) fn stats(&self) -> CompactStats {
        self.index.stats().as_compact_stats()
    }

    /// A probe: `Hit` iff the set index holds an order `≤` the summary's in its
    /// signature's slot; never `MemoHit` (no memo).
    pub(crate) fn probe(&mut self, s: &CompactSummary) -> (Probe, Option<SigId>) {
        match self.index.covers(s) {
            (id, Covers::Found(_)) => (Probe::Hit, id),
            (id, Covers::NoBucket | Covers::NoSig | Covers::NotFound) => (Probe::Miss, id),
        }
    }

    /// An admission (`CompactCache::admit`'s rules): refused under `Zero`;
    /// under `Bounded(n)` the oldest orders evicted first; then the witness's
    /// order stored, a re-admission counted when it was evicted before.
    pub(crate) fn admit(&mut self, witness: &CompactSummary, probed: &CompactSummary) -> bool {
        debug_assert!(
            witness.sig == probed.sig,
            "conformance: a sweep's witness has the probed summary's signature"
        );
        if matches!(self.capacity, Capacity::Zero | Capacity::Bounded(0)) {
            return false;
        }
        if let Capacity::Bounded(n) = self.capacity {
            while self.index.len() >= n {
                let Some((hash, sig_id, seq)) = self.fifo.pop_front() else {
                    break;
                };
                if let Some(ord) = self.index.remove(hash, sig_id, seq) {
                    self.evicted.insert((sig_id, ord));
                    self.evictions += 1;
                }
            }
        }
        let (sig_id, seq) = match self.index.insert(witness) {
            (id, Inserted::Stored(seq)) => (id, seq),
            (_, Inserted::Duplicate | Inserted::DroppedNew) => return false,
        };
        self.admissions += 1;
        if matches!(self.capacity, Capacity::Bounded(_)) {
            if self.evicted.contains(&(sig_id, witness.ord.clone())) {
                self.readmissions += 1;
            }
            self.fifo.push_back((witness.hash, sig_id, seq));
        }
        true
    }
}

#[derive(Clone, Debug)]
struct SetSlot {
    sig_id: SigId,
    sig: Sig,
    sig_est: usize,
    orders: indexmap::IndexMap<OrdCounts, u64>,
    /// `SVERIFY-P` I3-6: the multiplicity of each held order, index-aligned
    /// with `orders` (an insertion appends; `remove` shifts both); `None` on
    /// a set that does not count (`new`), which then pays nothing for it.
    counts: Option<Vec<u32>>,
}

/// One shape's bucket in the set index: its slots in creation order and the
/// P3 hint (rendering hash → slot indices, creations then aliases). The hint
/// is a `RefCell` so that the read-only query records an alias, as the
/// reference's `covers(&mut self)` does (I2-3).
#[derive(Clone, Debug, Default)]
struct SetBucket {
    slots: Vec<SetSlot>,
    /// `MIN-ENGINES` E7b: the slots holding at least one order (a slot emptied
    /// by the stateless cache's eviction stays, P1, but is not occupied).
    occupied: usize,
    hint: std::cell::RefCell<HashMap<u64, Vec<usize>>>,
}

impl SetBucket {
    /// The slot of `sig` by `Sig ==`: the hinted slots of its rendering hash
    /// `r` first, in list order, then the others in slot order; a slot found
    /// by the second pass is an alias, appended to `r`'s list and counted.
    /// `CompactIndex::find_in`'s rule, through `&self` (`tests` and
    /// `aliases` are the index's `Cell`s). Creates nothing.
    fn find(
        &self,
        sig: &Sig,
        r: Option<u64>,
        tests: &std::cell::Cell<usize>,
        aliases: &std::cell::Cell<usize>,
    ) -> Option<usize> {
        let hint = self.hint.borrow();
        let hinted: &[usize] = match r {
            Some(r) => hint.get(&r).map_or(&[][..], Vec::as_slice),
            None => &[],
        };
        for &i in hinted {
            tests.set(tests.get() + 1);
            if self.slots[i].sig == *sig {
                return Some(i);
            }
        }
        let mut found = None;
        for (i, slot) in self.slots.iter().enumerate() {
            if hinted.contains(&i) {
                continue;
            }
            tests.set(tests.get() + 1);
            if slot.sig == *sig {
                found = Some(i);
                break;
            }
        }
        let i = found?;
        drop(hint);
        if let Some(r) = r {
            self.hint.borrow_mut().entry(r).or_default().push(i);
            aliases.set(aliases.get() + 1);
        }
        Some(i)
    }
}

/// The set index's counters: `CompactStats`' fields of the same names, with
/// the same definitions (`slot_max` is `bucket_max`). Absent by construction:
/// `insert_tests` (identically 0 — an insertion starts no `cmp`, I2-8), the
/// antichain, memo, inverted and trie fields, and `impl_distinct_summaries`
/// (the engine's). No store column (I4's).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SetStats {
    /// Held orders at the end.
    pub entries: usize,
    /// Buckets (shapes) with at least one held order.
    pub buckets: usize,
    /// The largest number of orders one signature's slot holds.
    pub slot_max: usize,
    /// Slots (signatures) with at least one held order.
    pub signatures: usize,
    /// Every slot created: signatures inserted at least once.
    pub signatures_seen: usize,
    /// `Sig ==` comparisons started in slot resolution (insertions and
    /// queries; the hinted slots and the rest).
    pub sig_tests: usize,
    /// Slots found only by the scan after the hinted ones: equal signatures
    /// with different renderings, each then recorded in the hint.
    pub sig_aliases: usize,
    /// Insertions that stored an order.
    pub admitted: usize,
    /// Insertions refused as exact duplicates.
    pub duplicates: usize,
    /// `≤` tests started by queries.
    pub containment_tests: usize,
    /// Coordinates read by the queries' `≤` tests (D4).
    pub coordinates_compared: usize,
    /// Queries answered by the exact-hit probe (I2b-3): the slot held the
    /// query's order itself, so no `≤` test ran and no `≤` coordinate was
    /// read (the probe hashes the query's vector and compares it for
    /// equality; no counter sees that).
    pub exact_hits: usize,
    /// Σ payload bytes of the held orders, held once (I2b-1).
    pub summary_bytes: usize,
    /// Σ `32 × Σ_t |w_t| + 16 × T` over the occupied slots.
    pub sig_bytes_est: usize,
}

impl SetStats {
    /// The counters in the reference's record (I2b-6), for the stateful
    /// engine's `counters.compact` and, through `SetCache::stats`
    /// (`MIN-ENGINES` E7b), the complete-first engine's, so that the store's
    /// columns are filled under `IndexKind::Set`: the thirteen shared fields
    /// carried over (`bucket_max` is `slot_max`), `insert_tests` 0 (no `cmp`
    /// at insertion), the antichain, inverted, trie and memo fields off or
    /// `None`, `impl_distinct_summaries` `None` (each engine sets it as under
    /// `Compact`). `exact_hits` has no counterpart there; it stays in
    /// `SetStats`.
    pub(crate) fn as_compact_stats(&self) -> CompactStats {
        CompactStats {
            antichain_effective: false,
            entries: self.entries,
            buckets: self.buckets,
            bucket_max: self.slot_max,
            signatures: self.signatures,
            signatures_seen: self.signatures_seen,
            sig_tests: self.sig_tests,
            sig_aliases: self.sig_aliases,
            admitted: self.admitted,
            duplicates: self.duplicates,
            antichain_dropped_new: 0,
            antichain_dropped_old: 0,
            insert_tests: 0,
            containment_tests: self.containment_tests,
            coordinates_compared: self.coordinates_compared,
            inverted_used: None,
            inverted_words: None,
            trie_nodes_visited: None,
            summary_bytes: self.summary_bytes,
            sig_bytes_est: self.sig_bytes_est,
            memo_on: false,
            memo_hits: 0,
            memo_entries: 0,
            memo_clears: 0,
            impl_distinct_summaries: None,
        }
    }
}

/// The set index (`SVERIFY-P` I2): the compact summaries of one side as a
/// hash set per signature — the shape bucket by `hash`, the slot by `Sig ==`
/// through the P3 hint exactly as [`CompactIndex`] resolves it, the orders of
/// a slot held once in an `IndexMap<OrdCounts, u64>` (I2b-1) that answers an
/// exact duplicate and the exact-hit probe by hash with no `cmp` — and the
/// admission-ordered scan of [`CompactIndex`]'s query, through `&self`. No
/// antichain and no capacity policy of its own; `remove` (`MIN-ENGINES` E7b)
/// is the stateless cache's FIFO eviction, which drops an order and keeps its
/// slot. The held set is the set of distinct summaries inserted and not
/// removed. On one insertion sequence it equals
/// `CompactIndex::with_bucket(false, BucketKind::Scan)` in every insertion
/// outcome, id and seq, in every query's verdict class, and in every counter
/// but `insert_tests`, `containment_tests` and `coordinates_compared`: the
/// exact-hit probe (I2b-3) answers `Found` with the held order's own `seq`
/// before the scan, so where an earlier-admitted order is also `≤` the query
/// the witness differs (`seq_r ≤ seq_s`) and the two scan counters are
/// smaller by the probe's work. Across insertion orders only the held
/// identities, the occupancy counters, `sig_aliases`, `exact_hits` and each
/// query's `Covers` discriminant are invariant (I2-4). Memory: one
/// `IndexMap` bucket of 48 B per order plus its counts and the index table
/// (criteria I2b-8). `Send`, not `Sync` (`Sig` holds `Box<dyn Message>`; the
/// `Cell`s and `RefCell`s add nothing to that).
///
/// `SVERIFY-P` I3 adds, in this region only: a counting set
/// (`with_multiplicities`), the merge by move (`absorb_by_move`), the freeze
/// by move into a [`SigTable`] and an [`OrderStore`] (`freeze`), and
/// `entries_counted`. `insert` and `covers` are unchanged in what they do;
/// `covers` shares its body with the store's (`covers_in`).
#[derive(Clone, Debug)]
pub(crate) struct SetIndex {
    buckets: HashMap<SigHash, SetBucket>,
    next_seq: u64,
    next_sig_id: SigId,
    /// `SVERIFY-P` I3-6: whether the slots carry multiplicities.
    count: bool,
    /// The insertion-side counters.
    stats: SetStats,
    /// The counters a query advances, through `&self` (I2-3); `stats()`
    /// folds them into its snapshot.
    sig_tests: std::cell::Cell<usize>,
    sig_aliases: std::cell::Cell<usize>,
    containment_tests: std::cell::Cell<usize>,
    coordinates_compared: std::cell::Cell<usize>,
    exact_hits: std::cell::Cell<usize>,
}

impl Default for SetIndex {
    fn default() -> Self {
        Self::new()
    }
}

impl SetIndex {
    pub(crate) fn new() -> Self {
        Self {
            buckets: HashMap::new(),
            next_seq: 0,
            next_sig_id: 0,
            count: false,
            stats: SetStats::default(),
            sig_tests: std::cell::Cell::new(0),
            sig_aliases: std::cell::Cell::new(0),
            containment_tests: std::cell::Cell::new(0),
            coordinates_compared: std::cell::Cell::new(0),
            exact_hits: std::cell::Cell::new(0),
        }
    }

    /// `SVERIFY-P` I3-6: a set that counts multiplicities — a duplicate
    /// advances the held order's count instead of being merely refused
    /// (`duplicates` still counts it); `entries_counted` yields the counts;
    /// `absorb_by_move` sums them.
    pub(crate) fn with_multiplicities() -> Self {
        let mut s = Self::new();
        s.count = true;
        s
    }

    /// `SVERIFY-P` I3-6: whether this set counts multiplicities.
    pub(crate) fn counts_multiplicities(&self) -> bool {
        self.count
    }

    /// The counters, the query-side `Cell`s folded in.
    pub(crate) fn stats(&self) -> SetStats {
        let mut s = self.stats;
        s.sig_tests = self.sig_tests.get();
        s.sig_aliases = self.sig_aliases.get();
        s.containment_tests = self.containment_tests.get();
        s.coordinates_compared = self.coordinates_compared.get();
        s.exact_hits = self.exact_hits.get();
        s
    }

    /// Held orders.
    pub(crate) fn len(&self) -> usize {
        self.stats.entries
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.stats.entries == 0
    }

    /// `SVERIFY-P` I3-4 (f), test builds only: Σ over the slots of the orders
    /// map's capacity — what a worker set keeps after a flush took its maps.
    #[cfg(test)]
    pub(crate) fn orders_capacity_for_test(&self) -> usize {
        self.buckets
            .values()
            .flat_map(|b| b.slots.iter().map(|s| s.orders.capacity()))
            .sum()
    }

    /// `MIN-ENGINES` E7b: remove the order admitted as `seq` from `sig_id`'s slot
    /// — the stateless cache's FIFO eviction. `shift_remove` keeps the slot's
    /// admission order (the scan's); the slot itself stays (P1); the
    /// occupancy counters move as `CompactIndex::remove`'s. `None` if no such
    /// order is held.
    pub(crate) fn remove(&mut self, hash: SigHash, sig_id: SigId, seq: u64) -> Option<OrdCounts> {
        let bucket = self.buckets.get_mut(&hash)?;
        let si = bucket.slots.iter().position(|s| s.sig_id == sig_id)?;
        let slot = &mut bucket.slots[si];
        let i = slot.orders.values().position(|&q| q == seq)?;
        let (ord, _) = slot.orders.shift_remove_index(i)?;
        if let Some(counts) = slot.counts.as_mut() {
            counts.remove(i);
        }
        self.stats.entries -= 1;
        self.stats.summary_bytes -= ord.payload_bytes();
        if slot.orders.is_empty() {
            self.stats.signatures -= 1;
            self.stats.sig_bytes_est -= slot.sig_est;
            bucket.occupied -= 1;
            if bucket.occupied == 0 {
                self.stats.buckets -= 1;
            }
        }
        Some(ord)
    }

    /// An insertion's resolution: the signature's slot, created (bucket and
    /// slot, with a fresh checked id) when absent — `slot_for_insert`'s rule.
    fn slot_for_insert(&mut self, s: &CompactSummary) -> usize {
        let r = render_hash(&s.sig);
        let bucket = self.buckets.entry(s.hash).or_default();
        if let Some(i) = bucket.find(&s.sig, r, &self.sig_tests, &self.sig_aliases) {
            return i;
        }
        self.new_slot(s.hash, s.sig.clone(), s.sig_est, r)
    }

    /// `SVERIFY-P` I3-4: `slot_for_insert` for a flushed slot's own signature,
    /// which is moved into the slot created when absent (no clone) and
    /// dropped when the slot exists.
    fn slot_for_owned(&mut self, hash: SigHash, sig: Sig, sig_est: usize) -> usize {
        let r = render_hash(&sig);
        let bucket = self.buckets.entry(hash).or_default();
        if let Some(i) = bucket.find(&sig, r, &self.sig_tests, &self.sig_aliases) {
            return i;
        }
        self.new_slot(hash, sig, sig_est, r)
    }

    /// The slot's creation, shared by the two resolutions: a fresh checked
    /// id, the hint entry when `r` is `Some`, `signatures_seen` + 1.
    fn new_slot(&mut self, hash: SigHash, sig: Sig, sig_est: usize, r: Option<u64>) -> usize {
        let sig_id = self.next_sig_id;
        self.next_sig_id = sig_id
            .checked_add(1)
            .expect("conformance: more than u32::MAX signatures (SigId overflow)");
        let count = self.count;
        let bucket = self
            .buckets
            .get_mut(&hash)
            .expect("conformance: a resolved bucket exists");
        bucket.slots.push(SetSlot {
            sig_id,
            sig,
            sig_est,
            orders: indexmap::IndexMap::new(),
            counts: count.then(Vec::new),
        });
        let i = bucket.slots.len() - 1;
        if let Some(r) = r {
            bucket.hint.borrow_mut().entry(r).or_default().push(i);
        }
        self.stats.signatures_seen += 1;
        i
    }

    /// Hash-set insertion (I2-2, I2b-2): an exact duplicate is refused by the
    /// slot's map with no `cmp`; otherwise the order is stored once, as the
    /// map's key, with the next checked admission number as its value.
    /// `DroppedNew` is never returned (no antichain).
    pub(crate) fn insert(&mut self, s: &CompactSummary) -> (SigId, Inserted) {
        let si = self.slot_for_insert(s);
        self.store(s.hash, si, std::borrow::Cow::Borrowed(&s.ord), 1)
    }

    /// The store step shared by `insert` and `absorb_by_move` (`SVERIFY-P`
    /// I3-4): the duplicate check by the slot's map (a counting set advances
    /// the held order's multiplicity by `count`), else the order stored once
    /// — cloned from a borrowed order, moved from an owned one — with the
    /// next checked admission number and its multiplicity `count`.
    fn store(
        &mut self,
        hash: SigHash,
        si: usize,
        ord: std::borrow::Cow<'_, OrdCounts>,
        count: u32,
    ) -> (SigId, Inserted) {
        let stats = &mut self.stats;
        let bucket = self
            .buckets
            .get_mut(&hash)
            .expect("conformance: a resolved bucket exists");
        let slot = &mut bucket.slots[si];
        let sig_id = slot.sig_id;
        if let Some(i) = slot.orders.get_index_of(ord.as_ref()) {
            stats.duplicates += 1;
            if let Some(counts) = slot.counts.as_mut() {
                counts[i] = counts[i]
                    .checked_add(count)
                    .expect("conformance: more than u32::MAX occurrences of one summary");
            }
            return (sig_id, Inserted::Duplicate);
        }
        let seq = self.next_seq;
        self.next_seq = seq
            .checked_add(1)
            .expect("conformance: more than u64::MAX insertions (seq overflow)");
        let was_empty = slot.orders.is_empty();
        let ord = ord.into_owned();
        stats.summary_bytes += ord.payload_bytes();
        slot.orders.insert(ord, seq);
        if let Some(counts) = slot.counts.as_mut() {
            counts.push(count);
        }
        stats.admitted += 1;
        stats.entries += 1;
        stats.slot_max = stats.slot_max.max(slot.orders.len());
        if was_empty {
            // The slot becomes occupied (created now, or emptied by an
            // eviction and filled again): the occupancy counters as
            // `CompactIndex::occupancy`'s (`MIN-ENGINES` E7b: by the bucket's
            // occupied slots, not its slot count).
            stats.signatures += 1;
            stats.sig_bytes_est += slot.sig_est;
            if bucket.occupied == 0 {
                stats.buckets += 1;
            }
            bucket.occupied += 1;
        }
        (sig_id, Inserted::Stored(seq))
    }

    /// `SVERIFY-P` I3-4, the merge by move: every held order of `other`
    /// stored into `self` — `other`'s buckets in ascending hash, its slots in
    /// creation order, its orders in admission order — each slot resolved
    /// **once** by `Sig ==` (its signature moved in when the slot is new),
    /// each order **moved** in (no `OrdCounts` clone: the heap buffer keeps
    /// its address) with a fresh checked `seq` in this order; an order `self`
    /// already holds is a duplicate (counted; a counting `self` adds
    /// `other`'s multiplicity to it). `other`'s query counters are its own
    /// work and are not folded in; the occupancy counters follow from the
    /// stores.
    pub(crate) fn absorb_by_move(&mut self, other: SetIndex) {
        let mut buckets: Vec<(SigHash, SetBucket)> = other.buckets.into_iter().collect();
        buckets.sort_unstable_by_key(|(h, _)| *h);
        for (hash, bucket) in buckets {
            for slot in bucket.slots {
                let SetSlot {
                    sig,
                    sig_est,
                    orders,
                    counts,
                    ..
                } = slot;
                let si = self.slot_for_owned(hash, sig, sig_est);
                let mut counts = counts.map(Vec::into_iter);
                for (ord, _seq) in orders {
                    let count = counts.as_mut().and_then(Iterator::next).unwrap_or(1);
                    self.store(hash, si, std::borrow::Cow::Owned(ord), count);
                }
            }
        }
    }

    /// The read-only query (I2-3, I2b-3): the signature's id, `None` when it
    /// has no slot (the query creates none, P1), with the outcome. The
    /// exact-hit probe first: if the slot holds the query's order itself, it
    /// answers `Found` with that order's `seq` — no `≤` test, no `≤`
    /// coordinate read (the hash and the equality compare are not counted),
    /// `exact_hits` + 1. Otherwise the first held order `≤` the query
    /// in admission order answers (D4's exit), exactly `CompactIndex::covers`
    /// under `BucketKind::Scan`. A slot is never removed (P1), so
    /// `(Some(_), NoSig)` is unreachable; but `remove` (the stateless cache's
    /// eviction, `MIN-ENGINES` E7b) may leave a slot with no held order, and
    /// such a slot answers `(Some(id), NotFound)`. The slot's probe and scan
    /// are `covers_in`, shared with [`OrderStore::covers`] (`SVERIFY-P` I3-5).
    pub(crate) fn covers(&self, s: &CompactSummary) -> (Option<SigId>, Covers) {
        let Some(bucket) = self.buckets.get(&s.hash) else {
            return (None, Covers::NoBucket);
        };
        let r = render_hash(&s.sig);
        let Some(si) = bucket.find(&s.sig, r, &self.sig_tests, &self.sig_aliases) else {
            return (None, Covers::NoSig);
        };
        let slot = &bucket.slots[si];
        let mut q = QueryCounts::default();
        let c = covers_in(&slot.orders, &s.ord, &mut q);
        self.exact_hits.set(self.exact_hits.get() + q.exact_hits);
        self.containment_tests
            .set(self.containment_tests.get() + q.containment_tests);
        self.coordinates_compared
            .set(self.coordinates_compared.get() + q.coordinates_compared);
        (Some(slot.sig_id), c)
    }

    /// Every held order with its signature's id, the slot's representative
    /// signature and its admission number (I2-6, I2b-5): buckets in ascending
    /// `SigHash`, slots in creation order, orders in admission order —
    /// deterministic for one insertion history; the order and the
    /// representative's rendering depend on the history (I2-4).
    pub(crate) fn entries(&self) -> impl Iterator<Item = (SigId, &Sig, u64, &OrdCounts)> + '_ {
        let mut hashes: Vec<&SigHash> = self.buckets.keys().collect();
        hashes.sort_unstable();
        hashes.into_iter().flat_map(move |h| {
            self.buckets[h].slots.iter().flat_map(|slot| {
                slot.orders
                    .iter()
                    .map(move |(ord, &seq)| (slot.sig_id, &slot.sig, seq, ord))
            })
        })
    }

    /// `SVERIFY-P` I3-6: `entries` with the bucket's hash first and each
    /// order's multiplicity last (the count of a counting set, `1` on a set
    /// that does not count), in `entries`' order.
    pub(crate) fn entries_counted(
        &self,
    ) -> impl Iterator<Item = (SigHash, SigId, &Sig, u64, &OrdCounts, u32)> + '_ {
        let mut hashes: Vec<&SigHash> = self.buckets.keys().collect();
        hashes.sort_unstable();
        hashes.into_iter().flat_map(move |h| {
            self.buckets[h].slots.iter().flat_map(move |slot| {
                slot.orders.iter().enumerate().map(move |(i, (ord, &seq))| {
                    let count = slot.counts.as_ref().map_or(1, |c| c[i]);
                    (*h, slot.sig_id, &slot.sig, seq, ord, count)
                })
            })
        })
    }

    /// `SVERIFY-P` I3-5, the freeze by move: the index split into the
    /// signature table (per slot its hash, id and `Sig`, in creation order
    /// within the bucket) and the order store (per `SigId` the slot's map,
    /// `shrink_to_fit` so that the entries vector's unused capacity is
    /// returned — the map's headers move, the orders' heap buffers do not).
    /// The query counters and the hints are dropped; `stats()` before the
    /// freeze is the index's record. A set that counts multiplicities loses
    /// them here (the store answers queries; it does not count).
    pub(crate) fn freeze(self) -> (SigTable, OrderStore) {
        let n = self.next_sig_id as usize;
        let mut orders: Vec<indexmap::IndexMap<OrdCounts, u64>> =
            (0..n).map(|_| indexmap::IndexMap::new()).collect();
        let mut table: HashMap<SigHash, Vec<(SigId, Sig)>> =
            HashMap::with_capacity(self.buckets.len());
        for (hash, bucket) in self.buckets {
            let mut slots = Vec::with_capacity(bucket.slots.len());
            for slot in bucket.slots {
                let SetSlot {
                    sig_id,
                    sig,
                    orders: mut held,
                    ..
                } = slot;
                held.shrink_to_fit();
                orders[sig_id as usize] = held;
                slots.push((sig_id, sig));
            }
            table.insert(hash, slots);
        }
        (SigTable { buckets: table }, OrderStore { orders })
    }
}

/// `SVERIFY-P` I3-5: the exact-hit probe, then the admission-ordered scan
/// — the one body of `SetIndex::covers` and `OrderStore::covers`. The
/// counts are added to `q`.
fn covers_in(
    orders: &indexmap::IndexMap<OrdCounts, u64>,
    ord: &OrdCounts,
    q: &mut QueryCounts,
) -> Covers {
    if let Some(&seq) = orders.get(ord) {
        q.exact_hits += 1;
        return Covers::Found(seq);
    }
    for (held, &seq) in orders {
        q.containment_tests += 1;
        if held.le_counted(ord, &mut q.coordinates_compared) {
            return Covers::Found(seq);
        }
    }
    Covers::NotFound
}

/// `SVERIFY-P` I3-5: one query's counts, returned by value by
/// [`OrderStore::covers`] (no `Cell`: the store is shared read-only).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct QueryCounts {
    pub(crate) exact_hits: usize,
    pub(crate) containment_tests: usize,
    pub(crate) coordinates_compared: usize,
}

/// `SVERIFY-P` I3-5: a signature's resolution in a [`SigTable`] — the
/// three cases [`Covers`] distinguishes before any order is probed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SigLookup {
    /// No bucket for the shape.
    NoBucket,
    /// The shape's bucket exists, but no slot has this signature.
    NoSig,
    /// The signature's id.
    Found(SigId),
}

/// `SVERIFY-P` I3-5: the frozen index's signatures — per shape bucket its
/// slots' `(SigId, Sig)` in creation order. `Clone`, and `Send` but not
/// `Sync` (a `Sig` holds `Box<dyn Message>`), so each querying worker owns a
/// clone. Resolution is the creation-order scan by `Sig ==` (`render_hash`
/// is `None` since `MIN-ENGINES` E4, so the set index's hints were always
/// empty and the scan was its only pass).
#[derive(Clone, Debug)]
pub(crate) struct SigTable {
    buckets: HashMap<SigHash, Vec<(SigId, Sig)>>,
}

impl SigTable {
    /// The signature's id, with the `Sig ==` comparisons made added to
    /// `tests` (the set index's `sig_tests`).
    pub(crate) fn resolve(&self, hash: SigHash, sig: &Sig, tests: &mut usize) -> SigLookup {
        let Some(slots) = self.buckets.get(&hash) else {
            return SigLookup::NoBucket;
        };
        for (id, held) in slots {
            *tests += 1;
            if held == sig {
                return SigLookup::Found(*id);
            }
        }
        SigLookup::NoSig
    }

    /// Slots (signatures) in the table.
    pub(crate) fn signatures(&self) -> usize {
        self.buckets.values().map(Vec::len).sum()
    }

    /// Every slot: buckets in ascending `SigHash`, slots in creation order.
    pub(crate) fn entries(&self) -> impl Iterator<Item = (SigHash, SigId, &Sig)> + '_ {
        let mut hashes: Vec<&SigHash> = self.buckets.keys().collect();
        hashes.sort_unstable();
        hashes.into_iter().flat_map(move |h| {
            self.buckets[h].iter().map(move |(id, sig)| (*h, *id, sig))
        })
    }
}

/// `SVERIFY-P` I3-5: the frozen index's orders — per `SigId` the slot's
/// `IndexMap<OrdCounts, u64>` in admission order, plain data, `Sync`, shared
/// read-only through an `Arc`. `covers` answers exactly as
/// `SetIndex::covers` answers on the slot (the same body), with the counts
/// returned by value.
#[derive(Debug)]
pub(crate) struct OrderStore {
    orders: Vec<indexmap::IndexMap<OrdCounts, u64>>,
}

impl OrderStore {
    /// The read-only query on `id`'s slot: the exact-hit probe, then the
    /// first held order `≤` the query in admission order. `NoBucket` and
    /// `NoSig` are the table's answers, never this one's; a slot with no
    /// order answers `NotFound`.
    pub(crate) fn covers(&self, id: SigId, ord: &OrdCounts) -> (Covers, QueryCounts) {
        let mut q = QueryCounts::default();
        let c = covers_in(&self.orders[id as usize], ord, &mut q);
        (c, q)
    }

    /// Held orders.
    pub(crate) fn len(&self) -> usize {
        self.orders.iter().map(indexmap::IndexMap::len).sum()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Every held order with its signature's id and admission number: slots
    /// by ascending `SigId`, orders in admission order.
    pub(crate) fn entries(&self) -> impl Iterator<Item = (SigId, u64, &OrdCounts)> + '_ {
        self.orders.iter().enumerate().flat_map(|(id, m)| {
            m.iter().map(move |(ord, &seq)| (id as SigId, seq, ord))
        })
    }

    /// `SVERIFY-P` I3-5 (f), test builds only: per slot `(len, capacity)` of
    /// its map, by `SigId`.
    #[cfg(test)]
    pub(crate) fn capacities_for_test(&self) -> Vec<(usize, usize)> {
        self.orders.iter().map(|m| (m.len(), m.capacity())).collect()
    }
}
