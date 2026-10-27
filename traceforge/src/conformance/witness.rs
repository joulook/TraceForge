//! The witness cache `W` of `alg.tex` §8.5 and §8.6.
//!
//! > `W` is the *witness cache*, shared across the whole run and initially
//! > empty: graphs of Spec that covered an earlier graph of Impl are tried
//! > before any search. Caching is sound for free, because `cov` is exact and
//! > its outcome does not depend on how `M` was found; a cache hit proves
//! > coverage, and a miss proves nothing and falls through to the sweep.
//!
//! The soundness argument (proof of `thm:cfirst`) is one sentence: "every
//! member of `W` was added … where it was produced by the sweep, so
//! `W ⊆ Graphs(Spec)` throughout the run." That is enforced here as a type
//! invariant rather than a convention: the only way into the cache is
//! [`WitnessCache::admit_from_sweep`], the one mutating method, which takes a
//! [`CompleteExecution`] witness. Its callers are three: the sweeps of the
//! complete-first and gated checkers, and `flat::admit` (`P4-FLAT`), which
//! re-enters it with a [`FlatWitness`] — a graph `FlatCover` returned, whose
//! membership in `Graphs(Spec)` is `thm:flat`'s and is carried by that type's
//! invariant (below).
//!
//! **Deliberately narrower than the paper, and the extension points named.**
//! The paper admits two more sources: a graph `FlatCover` returns (§9.2, which
//! keeps `thm:gated` because the return lies in `Graphs(Spec)` by `thm:flat`),
//! and a complete graph `Cover` returns on a complete `G₁` (§8.7,
//! `lem:coverexact`(2)). Part 8 realised the first by re-entry through this one
//! path, with its own provenance argument on [`FlatWitness`], not by relaxing
//! this method or adding a second; Part 2's `Cover` extension point stands as
//! named (`P4-APPARATUS` criterion 15). (The proof of `thm:gated` names only
//! the two sweeps; backlog A20.)
//!
//! `W` holds the witness at which a successful sweep **stops** (plan §3);
//! caching every swept graph is the paper's cost dial and would be a separately
//! named variant, not this one.
//!
//! **A9.** A witness whose values include one that is not equal to itself can
//! be admitted twice: deduplication is by [`CanonicalGraph`] equality, which
//! such a value defeats. Harmless for coverage (both entries are genuine
//! members of `Graphs(Spec)`); `len` then overcounts, and Part 6 excludes such
//! pairs from its counters.

use crate::conformance::canon::{CanonSet, CanonicalGraph};
use crate::conformance::config::Capacity;
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{wobs, ObsError, Wobs};
use crate::conformance::sig::{cone_from, covered, ord, Summary, VisOrder};
use crate::exec_graph::ExecutionGraph;

/// A complete graph of Spec, with what the two tests read of it computed once.
#[derive(Clone, Debug)]
pub(crate) struct Witness {
    // `MIN-ENGINES` E4: the `wobs` field that sat here was read by nothing
    // since `probe_cone` moved to `cone_from` (which takes the outer graph's
    // rows from its caller); dropping it lets the summary take the admission's
    // rows instead of cloning every observed value a second time.
    graph: ExecutionGraph,
    summary: Summary,
    /// `P5-CFCFG` F1 (gate 4 M1/m1): under `Bounded(n)` only, a 128-bit
    /// fingerprint of the canonical form, so that an eviction can record it
    /// in the evicted set without keeping a graph copy; `None` otherwise.
    fingerprint: Option<u128>,
}

impl Witness {
    pub(crate) fn graph(&self) -> &ExecutionGraph {
        &self.graph
    }

    pub(crate) fn summary(&self) -> &Summary {
        &self.summary
    }
}

/// A graph `FlatCover` returned, prepared **on the flat thread** from a
/// `Probed` whose `complete()` is `Some` (`P4-FLAT` F4, round 02 M3).
///
/// **Type invariant** (fields private; the only constructor is
/// [`FlatWitness::of`], `P4-FLAT-CODE` round 01 M1): the graph passed
/// `Probed::complete` on the flat thread — its offers were empty and every
/// thread, `main` included, had finished — and it was built by the prober
/// primitives from offered events only, so it is consistent, complete, and
/// `nextp_Spec` is empty on it: by `thm:flat`'s soundness it lies in
/// `Graphs(Spec)`. `flat::admit` re-enters `admit_from_sweep` through
/// `CompleteExecution::try_finished`, which re-checks the spawned threads'
/// half; `main`'s half (`morphism.rs`, F33) rests on this invariant. The
/// summary is computed here too, for the adapter's `covered` check.
#[derive(Clone, Debug)]
pub(crate) struct FlatWitness {
    graph: ExecutionGraph,
    summary: Summary,
}

impl FlatWitness {
    /// `Some` iff `probed.complete()` is `Some`.
    pub(crate) fn of(
        probed: &crate::conformance::prober::Probed,
        visible: &[String],
    ) -> Result<Option<Self>, ObsError> {
        let Some(exec) = probed.complete() else {
            return Ok(None);
        };
        let graph = exec.graph();
        let w = wobs(graph, visible)?;
        let summary = Summary::of(exec, w, visible)?;
        Ok(Some(Self {
            graph: graph.clone(),
            summary,
        }))
    }

    pub(crate) fn graph(&self) -> &ExecutionGraph {
        &self.graph
    }

    pub(crate) fn summary(&self) -> &Summary {
        &self.summary
    }
}

/// `W`.
///
/// **`P5-CFCFG` F1 — the capacity.** `Unbounded` is Parts 4–5's cache. `Zero`
/// admits nothing and answers no probe (the vanilla algorithm). `Bounded(n)`
/// holds at most `n` entries in admission order; when full, an admission
/// evicts the oldest entry (FIFO) and forgets it in the deduplication set, so
/// the same graph may be admitted again later (a *re-admission*). The probe
/// order is unchanged: admission order, first hit. The invariant `W ⊆
/// Graphs(Spec)` is untouched: eviction only removes.
#[derive(Clone, Debug)]
pub(crate) struct WitnessCache {
    entries: Vec<Witness>,
    seen: CanonSet,
    visible: Vec<String>,
    capacity: Capacity,
    /// `Bounded(n)` only: the fingerprints of every graph evicted so far in
    /// the run (re-admission is detected here; gate 4 M1 — 16 bytes per
    /// distinct evicted graph, never a graph copy, so a bounded run's
    /// workspace is the `n` entries as the paper states).
    evicted: std::collections::HashSet<u128>,
    admissions: usize,
    evictions: usize,
    readmissions: usize,
}

impl WitnessCache {
    pub(crate) fn new(visible: Vec<String>) -> Self {
        Self::with_capacity(visible, Capacity::Unbounded)
    }

    /// `P5-CFCFG` F1. `Bounded(0)` is refused by the engine before any cache
    /// exists (`cfirst::run`); here it behaves as `Zero`.
    pub(crate) fn with_capacity(visible: Vec<String>, capacity: Capacity) -> Self {
        Self {
            entries: Vec::new(),
            seen: CanonSet::new(),
            visible,
            capacity,
            evicted: std::collections::HashSet::new(),
            admissions: 0,
            evictions: 0,
            readmissions: 0,
        }
    }

    pub(crate) fn capacity(&self) -> Capacity {
        self.capacity
    }

    /// `P5-CFCFG` F1 (gate 4 M1): the canonical forms a bounded cache retains
    /// are exactly its held entries' (`seen`), never the evicted ones' — the
    /// tester pins `retained_canonical_forms() ≤ n`.
    pub(crate) fn retained_canonical_forms(&self) -> usize {
        self.seen.len()
    }

    /// Stored admissions so far, re-admissions included (`P5-CFCFG` F1).
    pub(crate) fn admissions(&self) -> usize {
        self.admissions
    }

    /// Evictions so far (`Bounded(n)` only).
    pub(crate) fn evictions(&self) -> usize {
        self.evictions
    }

    /// Admissions of a graph that was held earlier in the run and evicted.
    pub(crate) fn readmissions(&self) -> usize {
        self.readmissions
    }

    /// Admit a graph a sweep of Spec produced. Returns `false` when an equal
    /// graph (by [`CanonicalGraph`]) is already held — `W` is a set.
    ///
    /// The `CompleteExecution` is the only evidence this takes that the graph
    /// is in `Graphs(Spec)`; the caller's obligation is that it came from a
    /// Must enumeration of Spec. The callers are the two sweeps and
    /// `flat::admit` (`P4-FLAT`), whose obligation is discharged by the
    /// [`FlatWitness`] type invariant — `P4-APPARATUS` criterion 15 keeps one
    /// mutating path, A20.
    pub(crate) fn admit_from_sweep(
        &mut self,
        exec: CompleteExecution<'_>,
    ) -> Result<bool, ObsError> {
        // `P5-CFCFG` F1: `Zero` (and the refused `Bounded(0)`) admits nothing.
        if matches!(self.capacity, Capacity::Zero | Capacity::Bounded(0)) {
            return Ok(false);
        }
        let graph = exec.graph();
        let canon = CanonicalGraph::of(graph, &self.visible)?;
        if self.seen.contains(&canon) {
            return Ok(false);
        }
        // Every fallible step precedes the insertion: a failed admission must
        // leave `W` as it was, or a retry would be answered "already held"
        // for a graph `W` does not hold (tester finding P4-APPARATUS-T1).
        let w = wobs(graph, &self.visible)?;
        let summary = Summary::of(exec, w, &self.visible)?;
        // FIFO eviction when full (`Bounded(n)`): the oldest entry leaves,
        // is forgotten by `seen` (its canonical form recomputed from the
        // graph, which succeeded at its admission) and remembered by
        // `evicted` as a fingerprint.
        let fingerprint = matches!(self.capacity, Capacity::Bounded(_)).then(|| fingerprint_of(&canon));
        if let Capacity::Bounded(n) = self.capacity {
            if self.entries.len() >= n {
                let old = self.entries.remove(0);
                let forgotten = CanonicalGraph::of(&old.graph, &self.visible)
                    .map(|c| self.seen.remove(&c))
                    .unwrap_or(false);
                debug_assert!(
                    forgotten,
                    "conformance: W's seen-set did not hold an evicted witness"
                );
                if let Some(fp) = old.fingerprint {
                    self.evicted.insert(fp);
                }
                self.evictions += 1;
            }
        }
        if fingerprint.is_some_and(|fp| self.evicted.contains(&fp)) {
            self.readmissions += 1;
        }
        let inserted = self.seen.insert(canon);
        debug_assert!(
            inserted,
            "conformance: W's seen-set changed under a single admission"
        );
        self.admissions += 1;
        self.entries.push(Witness {
            graph: graph.clone(),
            summary,
            fingerprint,
        });
        Ok(true)
    }

    /// The completion probe: a witness `M` with `covered(G, M)`, if one is held.
    pub(crate) fn probe_covered(&self, imp: &Summary) -> Option<&Witness> {
        self.entries.iter().find(|m| covered(imp, &m.summary))
    }

    /// [`probe_covered`](Self::probe_covered) with the number of `covered`
    /// calls it made (`P4-CFIRST` criterion 9's `cache_tests`; `covered`
    /// short-circuits on a signature mismatch, so these are calls, not
    /// containment tests). Entries are scanned in admission order; the first
    /// hit wins.
    pub(crate) fn probe_covered_counted(&self, imp: &Summary) -> (Option<&Witness>, usize) {
        let mut tests = 0;
        for m in &self.entries {
            tests += 1;
            if covered(imp, &m.summary) {
                return (Some(m), tests);
            }
        }
        (None, tests)
    }

    /// The witnesses, in admission order (`P4-CFIRST` criterion 11).
    pub(crate) fn entries(&self) -> &[Witness] {
        &self.entries
    }

    /// [`probe_cone`](Self::probe_cone) returning the hit's **index** and the
    /// number of `cone_from` calls made (`P4-GATED` G3, `ln:gsweep`'s `W`
    /// pass; criterion 9's `c1_tests_cache`). Admission order, first hit.
    pub(crate) fn probe_cone_counted(
        &self,
        g1_wobs: &Wobs,
        ord1: &VisOrder,
    ) -> (Option<usize>, usize) {
        let mut tests = 0;
        for (i, m) in self.entries.iter().enumerate() {
            tests += 1;
            if cone_from(g1_wobs, ord1, &m.summary, &self.visible) {
                return (Some(i), tests);
            }
        }
        (None, tests)
    }

    /// The gate probe: a witness `M` with `C₁(G₁, M)`, if one is held.
    ///
    /// `ord(G₁)` is computed once here and each witness is tested from its
    /// stored [`Summary`] through [`cone_from`], so a probe costs one `ord` of
    /// `G₁` plus `|W|` containment passes, not `|W|` recomputations of it
    /// (gate-4 round 01, m1). [`crate::conformance::sig::cone`] is the
    /// reference the tester's corpus test holds this to.
    pub(crate) fn probe_cone(&self, g1: &ExecutionGraph, g1_wobs: &Wobs) -> Option<&Witness> {
        let ord1 = ord(g1, g1_wobs, &self.visible);
        self.entries
            .iter()
            .find(|m| cone_from(g1_wobs, &ord1, &m.summary, &self.visible))
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// `P5-CFCFG` F1 (gate 4 M1): a 128-bit fingerprint of a canonical form — two
/// 64-bit hashes of its `Debug` rendering under different seeds. Precondition
/// (gate 4 round 02 n2): the `Debug` rendering of every message value is a
/// function of its `PartialEq` class — true of derived impls on plain data,
/// which every fixture of the experiment uses; a value whose rendering varies
/// within its equality class (a map with per-instance iteration order, a
/// `PartialEq` that ignores a field) can only **undercount** `readmissions`.
/// Collisions (negligible at 128 bits) are the other inexactness; the held
/// entries are still deduplicated exactly through `seen`.
fn fingerprint_of(canon: &CanonicalGraph) -> u128 {
    use std::hash::{Hash, Hasher};
    let text = format!("{canon:?}");
    let mut a = std::collections::hash_map::DefaultHasher::new();
    0x5f3759dfu64.hash(&mut a);
    text.hash(&mut a);
    let mut b = std::collections::hash_map::DefaultHasher::new();
    0x9e3779b97f4a7c15u64.hash(&mut b);
    text.hash(&mut b);
    ((a.finish() as u128) << 64) | b.finish() as u128
}
