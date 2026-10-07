//! The absence certificate of the gated algorithm (`alg.tex` §8.6), carrying
//! the graph it was set at.
//!
//! > The *certificate* `c` is a boolean asserting that every completion of
//! > every extension of the current graph is uncovered. … The certificate,
//! > once set, transfers to every extension, an extension of an extension
//! > being an extension, so below it no gate and no completion test runs
//! > again … A backward revisit does not produce an extension, so
//! > `ln:greset` resets witness and certificate both.
//!
//! The paper states those rules for its **recursive** pseudocode, where `c`
//! is a call parameter and a forward alternative — another value of a choice,
//! another source for a receive — is a sibling call that inherits its parent's
//! `c`. TraceForge is a **worklist** engine: a pop can restore a graph with one
//! earlier value changed, which is *not* an extension of the graph the
//! certificate was set at, and the two rules alone would let a certificate
//! held in context state survive it and report covered graphs (review
//! `P4-APPARATUS` round 01 M2; backlog A19). So a certificate here is not a
//! boolean. It carries its **set point**, and its validity at a graph is
//! Def. ext (`alg.tex` §8.1):
//!
//! > `G'` *extends* `G` when `G.E ⊆ G'.E`, the set `G.E` is
//! > `porf_{G'}`-prefix-closed, and `G'|_{G.E} = G`.
//!
//! # The rule, for a worklist engine
//!
//! **Valid at `G'` iff `G'` extends the set point. The test runs at the point
//! of use** — where `GStep` would skip a gate because of the certificate, and
//! at `ln:gfinal` before reporting under it — on the fully replayed graph the
//! paper's call would receive. It may **not** run after `begin_execution` has
//! blanked the send values: two blanked values compare equal, and a test there
//! would silently become "drop" (round 02 M1). A `RevisitApply` gate runs
//! *before* that blanking, on the fully installed graph, so validating there is
//! sound and is what Part 5 does (`P4-GATED` G2). A pop may *drop eagerly*
//! instead; which of the two an implementation does is a cost choice for the
//! owner (`P4-DISCUSS.md` D5), and the verdict is the same either way. **The choice, stated as criterion 19 states it**
//! (gate-4 round 01, m5): *eager drop at every pop* is sound and free, but
//! every forward alternative is a worklist pop in this engine, so it keeps
//! **strictly less** than the paper, which passes `c` unchanged to every
//! forward alternative and resets only at `ln:greset` (backward revisits);
//! §8.6's `ex:naive` "one failing sweep" saving is then not reproduced.
//! *Test at use* needs the certificate stored **per worklist item** (on each
//! `RevisitEnum`), **per `MustState`** (sufficient, because pops are
//! stamp-descending), or as a **set validated at use**; each matches or
//! exceeds the paper. A **single mutable slot outside `MustState`**, as
//! `ctx.rs` keeps for `H`, is neither, and is not an option for Part 5.
//!
//! # Two consequences, both recorded
//!
//! **The prefix-closure conjunct is implied by the other two on engine
//! graphs** (round 02 M2): the last edge of any path into the set point is po,
//! rf, create or join, and each lands inside it — by contiguity of a thread's
//! indices, by rf agreement, by the origination vector for create, and by the
//! engine installing a `TJoin` only after the child's `End`. It is kept as a
//! `debug_assert!` cross-check, not as an independent clause (A23).
//!
//! **A backward revisit can produce an extension**, when its deletion set
//! misses the set point and the revisited receive lies outside it; the
//! certificate then survives, which `ln:greset` would not allow. Sound by
//! `thm:gated`'s invariant — if `c` then every completion of every extension
//! of `G` is uncovered, and every extension of an extension of the set point
//! is an extension of it — and recorded as a departure from the paper and
//! from plan §3 (A19, D5). **It does not arise under Part 5's engine**: the
//! gated checker keeps the pair per `MustState`, and `backward_revisit` pushes
//! a fresh default for the revisited execution, so no certificate crosses a
//! backward revisit there; validity at use matters for forward pops (`P4-GATED`
//! G2; D5's gate-3 note records the inheriting variant as sound and cheaper).
//!
//! # Placeholders
//!
//! The engine rests a blocked thread on a `Block{Value}`/`Block{Join}` label it
//! removes when the thread unblocks; the paper has no event there. Those
//! positions of the set point are ignored by the test, so an unblocking
//! extension still extends (criteria E5).
//!
//! Only a gate that has swept all of `Graphs(Spec)` and found no witness may
//! set a certificate ([`Certificate::absence_established`]). The paper also
//! lets `Cover`'s exhaustion establish one (§8.7); that is a later part's
//! extension point and is not taken here.

use std::collections::BTreeMap;

use crate::conformance::canon::{CanonPos, CanonicalGraph, Declared};
use crate::conformance::obs::ObsError;
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;

/// Whether every completion of every extension of a specific graph is known
/// to be uncovered — and which graph.
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct Certificate {
    set_at: Option<CanonicalGraph>,
}

impl Certificate {
    /// No claim: the initial value, the value after an eager drop, and the
    /// value [`Certificate::kept_at`] returns where the claim no longer holds.
    pub(crate) fn none() -> Self {
        Self { set_at: None }
    }

    /// The claim, for the graph `g`: established by a sweep of `Graphs(Spec)`
    /// that found no witness passing `C₁` (`ln:gabsent`), which by
    /// `lem:witness` and `cor:absence` certifies every completion of every
    /// extension of `g` uncovered.
    ///
    /// The caller is asserting the sweep was complete and unpruned. There is
    /// no way to check that here, which is why the gate is the only caller.
    pub(crate) fn absence_established(
        g: &ExecutionGraph,
        visible: &[String],
    ) -> Result<Self, ObsError> {
        Ok(Self {
            set_at: Some(CanonicalGraph::of(g, visible)?),
        })
    }

    pub(crate) fn is_set(&self) -> bool {
        self.set_at.is_some()
    }

    /// The graph this certificate speaks about, if set.
    pub(crate) fn set_at(&self) -> Option<&CanonicalGraph> {
        self.set_at.as_ref()
    }

    /// Def. ext: does `g` extend the set point? Called only at the point of
    /// use, on a fully installed graph — never after `begin_execution` has
    /// blanked the send values (a `RevisitApply` gate runs before that, so
    /// validating there is sound — `P4-GATED` G2).
    ///
    /// (i) every non-placeholder position of the set point is present in `g`,
    /// (ii) with the same label and, for a receive, the same source; (iii) the
    /// set point is `porf_g`-prefix-closed, implied by (i) and (ii) on engine
    /// graphs and checked here only under `debug_assertions`. An unset
    /// certificate is valid nowhere — it claims nothing.
    pub(crate) fn valid_at(
        &self,
        g: &ExecutionGraph,
        visible: &[String],
    ) -> Result<bool, ObsError> {
        let Some(set_at) = &self.set_at else {
            return Ok(false);
        };
        let here = CanonicalGraph::of(g, visible)?;

        // (i) every non-placeholder position of the set point is present in g.
        let present = |p: &CanonPos| here.label_at(p).is_some();
        if !set_at
            .events()
            .iter()
            .filter(|(_, l)| !l.is_placeholder())
            .all(|(p, _)| present(p))
        {
            return Ok(false);
        }
        // (ii) over the non-placeholder positions that are present: same label,
        // and for a receive the same source. Independent of (i) by construction,
        // so each clause has its own failing fixture (criterion 18).
        for (p, l) in set_at.events() {
            if l.is_placeholder() || !present(p) {
                continue;
            }
            if here.label_at(p) != Some(l) {
                return Ok(false);
            }
        }
        for (r, s) in set_at.rf() {
            if present(r) && here.rf().get(r) != Some(s) {
                return Ok(false);
            }
        }

        // (iii), as a cross-check only: no event of `g` outside the set point
        // is porf-before a non-placeholder event inside it.
        if cfg!(debug_assertions) {
            let declared = Declared::of(g, visible)?;
            let mut by_pos: BTreeMap<CanonPos, Event> = BTreeMap::new();
            for tid in g.thread_ids() {
                let tk = declared.key(g, tid, Event::new(tid, 0));
                for index in 0..g.thread_size(tid) as u32 {
                    by_pos.insert((tk.clone(), index), Event::new(tid, index));
                }
            }
            let inside: Vec<Event> = set_at
                .events()
                .iter()
                .filter(|(_, l)| !l.is_placeholder())
                .map(|(p, _)| by_pos[p])
                .collect();
            for (p, e) in &by_pos {
                if set_at.label_at(p).is_some() {
                    continue;
                }
                debug_assert!(
                    !inside.iter().any(|&i| *e != i && g.in_porf(*e, i)),
                    "conformance: an event outside a certificate's set point is porf-before \
                     one inside it although labels and sources agree — A23's implication \
                     failed on this graph"
                );
            }
        }
        Ok(true)
    }

    /// Rule 1: the certificate transfers to an extension. The identity, named
    /// so the call site says what it is doing; the caller has established the
    /// extension (an installed event, or `SetND`/`SetRF` on it).
    pub(crate) fn transfer(self) -> Self {
        self
    }

    /// Rule 2 at the point of use: keep the certificate only where it is
    /// valid. This is the "keep and test" side of D5.
    pub(crate) fn kept_at(self, g: &ExecutionGraph, visible: &[String]) -> Result<Self, ObsError> {
        Ok(if self.valid_at(g, visible)? {
            self
        } else {
            Self::none()
        })
    }

    /// Rule 2 at a pop: drop. This is the "drop eagerly" side of D5 — at
    /// **every** pop, forward alternatives included — which is strictly
    /// stronger than the paper's `ln:greset`, which resets only at backward
    /// revisits (criterion 19; module doc).
    pub(crate) fn dropped_on_pop(self) -> Self {
        Self::none()
    }
}
