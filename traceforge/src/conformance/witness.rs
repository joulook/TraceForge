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
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{wobs, ObsError, Wobs};
use crate::conformance::sig::{cone_from, covered, ord, Summary, VisOrder};
use crate::exec_graph::ExecutionGraph;

/// A complete graph of Spec, with what the two tests read of it computed once.
#[derive(Clone, Debug)]
pub(crate) struct Witness {
    // `wobs` is read by nothing on the probe path since `probe_cone` moved to
    // `cone_from` (gate-4 round 01 m1); it is kept for the reference `cone`
    // and for Part 6's diagnostics, which explain a witness by its words.
    graph: ExecutionGraph,
    wobs: Wobs,
    summary: Summary,
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
        let summary = Summary::of(exec, &w, visible)?;
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
#[derive(Clone, Debug)]
pub(crate) struct WitnessCache {
    entries: Vec<Witness>,
    seen: CanonSet,
    visible: Vec<String>,
}

impl WitnessCache {
    pub(crate) fn new(visible: Vec<String>) -> Self {
        Self {
            entries: Vec::new(),
            seen: CanonSet::new(),
            visible,
        }
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
        let graph = exec.graph();
        let canon = CanonicalGraph::of(graph, &self.visible)?;
        if self.seen.contains(&canon) {
            return Ok(false);
        }
        // Every fallible step precedes the insertion: a failed admission must
        // leave `W` as it was, or a retry would be answered "already held"
        // for a graph `W` does not hold (tester finding P4-APPARATUS-T1).
        let w = wobs(graph, &self.visible)?;
        let summary = Summary::of(exec, &w, &self.visible)?;
        let inserted = self.seen.insert(canon);
        debug_assert!(
            inserted,
            "conformance: W's seen-set changed under a single admission"
        );
        self.entries.push(Witness {
            graph: graph.clone(),
            wobs: w,
            summary,
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
