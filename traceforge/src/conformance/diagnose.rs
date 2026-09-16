//! §7.1's inner-search diagnostics, **recomputed outside the search**, and
//! §7.3's un-Φ'd oracle, which is the same traversal with Φ switched off.
//!
//! # Why this is a second traversal and not an accumulator
//!
//! Blocked item **D**'s ruling. §7.1 wants "the furthest-following prefix a
//! canonically chosen failed `SpecVisit` attempt reached, and the first
//! failing obligation". Neither is obtainable from S3's `Cover`, which is
//! `Found | NoCover | BudgetExhausted` with nothing attached — and the *first
//! failing obligation* is not obtainable from S2 either: `follows`
//! (`morphism::follows`), `matches` (`:442`) and `statuses_agree` (`:416`) all
//! return bare `bool`, so there is nowhere for "(M1) failed at position *i*"
//! to come from. That is three approved S2 signatures with S2's own test
//! module written against those booleans.
//!
//! The owner ruled: **recompute outside the search; S2 and S3 stay sealed.**
//! §7.1 says the diagnostics "do not influence the search", and recomputation
//! makes that trivially and permanently true, where an accumulator threaded
//! through `spec_visit`/`spec_step`/`phi` would need proving write-only across
//! backtracking and clone points.
//!
//! # The cost, named rather than waved
//!
//! A reconstruction can disagree with what the search actually did. That is
//! mitigated the way S4 eventually mitigated `blame_for`: this module answers
//! only when it **reproduces the search's own verdict**, and says "diagnostic
//! unavailable" rather than guess when it does not. Two checks, not one:
//! `Search::cover` is re-run on the reported graph and must answer `NoCover`,
//! *and* this module's own traversal must answer `NoCover` too. A
//! reconstruction that silently disagrees is worse than none.
//!
//! Nothing here renders. The phrases come from
//! [`crate::conformance::report`]'s vocabulary.

use std::sync::Arc;

use crate::conformance::morphism::{
    follows, matches, statuses, statuses_agree, CompleteExecution,
};
use crate::conformance::obs::{wobs, ObsError, Wobs};
use crate::conformance::probe::Offer;
use crate::conformance::prober::{install, install_nondet, install_recv, probe_from, Probed};
use crate::conformance::report::{
    self, Diagnostics, Obligation, ReportCause, ReportGate, VisTrace,
};
use crate::conformance::search::{Cover, Search};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::Config;

/// What one traversal concluded. Deliberately the same three answers as
/// `Cover`, so that "did the recomputation reproduce the search's verdict?"
/// is a comparison rather than an interpretation — but a **separate type**, so
/// that nothing here can be mistaken for S3's answer or fed back into it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Answer {
    Found,
    NoCover,
    Exhausted,
}

/// The implementation side, fixed for one recomputation.
struct Outer<'a> {
    graph: &'a ExecutionGraph,
    wobs: Wobs,
    complete: bool,
}

/// The best failed attempt seen so far.
///
/// "Best" needed an order and §7.1's word did not name one — `follows` is a
/// conjunction over visible-thread rows, so a prefix longer on one row may be
/// shorter on another and the natural length is a *vector*. Filed as **A13**
/// and amended: the tie-break is **lexicographic on the per-thread
/// prefix-length vector, in the declared visible order, then installation
/// order** — which here is "first encountered", the traversal being
/// deterministic.
pub(crate) struct Best {
    vector: Vec<usize>,
    graph: Option<ExecutionGraph>,
    /// How many offers were *accepted*. Exposed so the tie-break can be tested
    /// in its discriminating case — two incomparable attempts, and a repeat of
    /// the standing best — rather than only observed end to end on whatever
    /// pair happens to be to hand (gate-4 round 1, m8).
    accepted: usize,
}

impl Best {
    pub(crate) fn new(n: usize) -> Self {
        Best {
            vector: vec![0; n],
            graph: None,
            accepted: 0,
        }
    }

    /// Strictly greater, lexicographically **in the declared visible order**.
    /// Equality does not replace: that is the "then installation order" half,
    /// and it is what makes the choice deterministic rather than a function of
    /// which branch the traversal happened to walk last.
    ///
    /// The rule has to be an order on *vectors* because `follows` is a
    /// conjunction over visible-thread rows, so two failed attempts can be
    /// incomparable — one longer on `alpha`, the other longer on `zulu`. §7.1
    /// said "best" and named no such order; A13 fixes it here.
    pub(crate) fn offer(&mut self, vector: Vec<usize>, graph: &ExecutionGraph) {
        if self.graph.is_none() || vector > self.vector {
            self.vector = vector;
            self.graph = Some(graph.clone());
            self.accepted += 1;
        }
    }

    pub(crate) fn vector(&self) -> &[usize] {
        &self.vector
    }

    pub(crate) fn accepted(&self) -> usize {
        self.accepted
    }
}

/// One recomputation over the specification, with Φ on (diagnostics) or off
/// (the naive oracle).
pub(crate) struct Recompute {
    config: Config,
    spec: Arc<dyn Fn() + Send + Sync>,
    visible: Vec<String>,
    budget: usize,
    use_phi: bool,
}

impl Recompute {
    pub(crate) fn new(
        config: Config,
        spec: Arc<dyn Fn() + Send + Sync>,
        visible: Vec<String>,
        budget: usize,
        use_phi: bool,
    ) -> Self {
        Recompute {
            config,
            spec,
            visible,
            budget,
            use_phi,
        }
    }

    /// Answer coverability, discarding the diagnostics. §7.3's
    /// `--naive-oracle` is this with `use_phi = false`.
    pub(crate) fn answer(&self, g1: &ExecutionGraph, complete: bool) -> Result<Answer, ObsError> {
        self.answer_counting(g1, complete).map(|(a, _)| a)
    }

    /// The same, reporting how many `SpecVisit` nodes it actually spent.
    ///
    /// Exposed so that "Φ and the un-Φ traversal spend the same budget" can be
    /// asserted as the **node count** it names, rather than inferred from the
    /// two answers coinciding (gate-4 round 2, m1). Equal answers are weaker:
    /// two traversals of different sizes can agree.
    pub(crate) fn answer_counting(
        &self,
        g1: &ExecutionGraph,
        complete: bool,
    ) -> Result<(Answer, usize), ObsError> {
        let mut best = Best::new(self.visible.len());
        let outer = Outer {
            graph: g1,
            wobs: wobs(g1, &self.visible)?,
            complete,
        };
        let mut fuel = self.budget;
        let answer = self.visit(&outer, ExecutionGraph::default(), &mut fuel, &mut best)?;
        Ok((answer, self.budget - fuel))
    }

    /// The diagnostics, or a reason there are none.
    ///
    /// This is the only entry point that decides "available"; the guard is
    /// the whole mitigation blocked item **D** attached to its own ruling.
    pub(crate) fn diagnose(&self, g1: &ExecutionGraph, complete: bool) -> Diagnostics {
        // Check one: S3's own search, re-run on the reported graph.
        let search = Search::new(
            self.config.clone(),
            Arc::clone(&self.spec),
            self.visible.clone(),
            self.budget,
        );
        match search.cover(g1, complete, ExecutionGraph::default()) {
            Ok(Cover::NoCover) => {}
            Ok(Cover::Found(_)) => {
                return Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                    because: "re-running the search on the reported graph found a cover, so \
                              this recomputation does not describe the same question the \
                              gate answered"
                        .to_owned(),
                }
            }
            Ok(Cover::BudgetExhausted) => {
                return Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                    because: "re-running the search on the reported graph ran out of budget, \
                              so it did not reproduce the gate's \u{22a5}"
                        .to_owned(),
                }
            }
            Err(e) => {
                return Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                    because: format!(
                        "re-running the search on the reported graph raised a usage error: {e}"
                    ),
                }
            }
        }

        // Check two: this module's own traversal.
        let mut best = Best::new(self.visible.len());
        let outer = match wobs(g1, &self.visible) {
            Ok(w) => Outer {
                graph: g1,
                wobs: w,
                complete,
            },
            Err(e) => {
                return Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                    because: format!("the implementation graph's observations could not be extracted: {e}"),
                }
            }
        };
        let mut fuel = self.budget;
        match self.visit(&outer, ExecutionGraph::default(), &mut fuel, &mut best) {
            Ok(Answer::NoCover) => {}
            Ok(other) => {
                return Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                    because: format!(
                        "the recomputation answered {other:?} where the search answered \u{22a5}"
                    ),
                }
            }
            Err(e) => {
                return Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                    because: format!("the recomputation raised a usage error: {e}"),
                }
            }
        }

        let Some(graph) = best.graph else {
            return Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                because: "no specification attempt followed the implementation graph at all, \
                          not even the empty one"
                    .to_owned(),
            };
        };
        let prefix = self
            .visible
            .iter()
            .cloned()
            .zip(best.vector.iter().copied())
            .collect();
        match self.obligation(&outer, &graph) {
            Ok(Some(obligation)) => Diagnostics::Available { prefix, obligation },
            // The morphism holds on this attempt and no extension of it
            // covers, which §7.1's four values cannot express (round-5 B1).
            // Saying so is better than emitting a Φ claim that is false.
            Ok(None) => Diagnostics::Unavailable {
                kind: report::UnavailableKind::NoValueForIt,
                because: "the morphism holds on the furthest-following attempt and no \
                          extension of it covers, which §7.1's obligation list has no \
                          value for; see F-7"
                    .to_owned(),
            },
            Err(e) => Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                because: format!("the failing obligation could not be identified: {e}"),
            },
        }
    }

    // -- the traversal ----------------------------------------------------

    fn visit(
        &self,
        outer: &Outer<'_>,
        graph: ExecutionGraph,
        fuel: &mut usize,
        best: &mut Best,
    ) -> Result<Answer, ObsError> {
        if *fuel == 0 {
            return Ok(Answer::Exhausted);
        }
        *fuel -= 1;

        let probed = self.probe(graph);

        // Record this node as an attempt if it follows. The empty graph
        // follows trivially, so `best` is always populated on a run that gets
        // this far.
        let spec_wobs = wobs(probed.graph(), &self.visible)?;
        if follows(
            probed.graph(),
            outer.graph,
            &spec_wobs,
            &outer.wobs,
            &self.visible,
        ) {
            let vector = self
                .visible
                .iter()
                .map(|n| spec_wobs.of(n).len())
                .collect::<Vec<_>>();
            best.offer(vector, probed.graph());
        }

        if self.done(outer, &probed, &spec_wobs)? {
            return Ok(Answer::Found);
        }

        let mut exhausted = false;
        for offer in probed.offers() {
            if self.use_phi && !self.phi(outer, probed.graph(), offer)? {
                continue;
            }
            match self.branch(outer, probed.graph(), offer, fuel, best)? {
                Answer::Found => return Ok(Answer::Found),
                Answer::Exhausted => exhausted = true,
                Answer::NoCover => {}
            }
        }
        Ok(if exhausted {
            Answer::Exhausted
        } else {
            Answer::NoCover
        })
    }

    fn branch(
        &self,
        outer: &Outer<'_>,
        graph: &ExecutionGraph,
        offer: &Offer,
        fuel: &mut usize,
        best: &mut Best,
    ) -> Result<Answer, ObsError> {
        let mut exhausted = false;
        let step = |this: &Self,
                        extended: ExecutionGraph,
                        through_step: bool,
                        fuel: &mut usize,
                        best: &mut Best|
         -> Result<Option<Answer>, ObsError> {
            // `SpecStep`'s follow check. With Φ off (the naive oracle) it
            // stays on: the un-Φ'd search is the draft's `SpecStep` without
            // the Φ *filter on the loop's range*, not without the morphism.
            if through_step {
                let w = wobs(&extended, &this.visible)?;
                if !follows(
                    &extended,
                    outer.graph,
                    &w,
                    &outer.wobs,
                    &this.visible,
                ) {
                    return Ok(Some(Answer::NoCover));
                }
            }
            match this.visit(outer, extended, fuel, best)? {
                Answer::Found => Ok(None),
                a => Ok(Some(a)),
            }
        };

        macro_rules! try_one {
            ($extended:expr, $through:expr) => {{
                match step(self, $extended, $through, fuel, best)? {
                    None => return Ok(Answer::Found),
                    Some(Answer::Exhausted) => exhausted = true,
                    Some(_) => {}
                }
            }};
        }

        match offer.label() {
            // **The two shields `search.rs` carries, and the reason they are
            // here too** (gate-4 round 1, m4). An empty option list skips the
            // loop and falls through to `NoCover` below — a ⊥ produced for a
            // reason that is not "no cover exists". `search.rs` records
            // removing that shape six times; this file is a second traversal
            // over the same offers and had none of the guards. The un-Φ'd
            // oracle needs them most: with `use_phi = false` the `phi` arm
            // never runs, so `branch` is the *only* place an empty list could
            // be caught, and the oracle is the one artefact whose whole
            // purpose is to be an independent answer.
            LabelEnum::CToss(_) | LabelEnum::Choice(_) => {
                let values = offer.nondet_values();
                assert!(
                    !values.is_empty(),
                    "conformance: the nondet offer at {} has no values, so it is not a \
                     choice point",
                    offer.pos()
                );
                for value in values {
                    let extended = install_nondet(self.config.clone(), graph.clone(), offer, value);
                    try_one!(extended, false);
                }
            }
            LabelEnum::RecvMsg(_) => {
                let options = self.rf_options(offer);
                assert!(
                    !options.is_empty(),
                    "conformance: the receive offer at {} has neither a source nor \
                     permission to read nothing, so it should not have been offered",
                    offer.pos()
                );
                for rf in options {
                    let extended = install_recv(self.config.clone(), graph.clone(), offer, rf);
                    try_one!(extended, true);
                }
            }
            LabelEnum::SendMsg(_) => {
                let extended = install(self.config.clone(), graph.clone(), offer);
                try_one!(extended, true);
            }
            // The same `unreachable!` `search.rs` carries, for the same
            // reason: a probe only ever offers choice points, and answering
            // "no" for anything else would drop it from the loop's range and
            // manufacture a \u{22a5}.
            other => unreachable!("conformance: a probe offered a {other}, which is not a choice point"),
        }

        Ok(if exhausted {
            Answer::Exhausted
        } else {
            Answer::NoCover
        })
    }

    fn phi(
        &self,
        outer: &Outer<'_>,
        graph: &ExecutionGraph,
        offer: &Offer,
    ) -> Result<bool, ObsError> {
        let check = |extended: &ExecutionGraph| -> Result<bool, ObsError> {
            let w = wobs(extended, &self.visible)?;
            Ok(follows(
                extended,
                outer.graph,
                &w,
                &outer.wobs,
                &self.visible,
            ))
        };
        match offer.label() {
            LabelEnum::RecvMsg(_) => {
                let options = self.rf_options(offer);
                // `phi` runs *first* and shields `branch`, so `branch`'s
                // assertion alone would never be reached under Φ — the sixth
                // instance `search.rs` records, and the one its fifth fix
                // missed.
                assert!(
                    !options.is_empty(),
                    "conformance: the receive offer at {} has neither a source nor \
                     permission to read nothing, so it should not have been offered",
                    offer.pos()
                );
                for rf in options {
                    let extended = install_recv(self.config.clone(), graph.clone(), offer, rf);
                    if check(&extended)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            LabelEnum::CToss(_) | LabelEnum::Choice(_) => {
                // `Ok(false)` here would drop the offer from Φ's range in
                // silence, and if it were the only offer that is a
                // manufactured ⊥.
                let Some(v) = offer.nondet_values().first().copied() else {
                    panic!(
                        "conformance: a nondet offer with no values is not a choice point \
                         (at {})",
                        offer.pos()
                    )
                };
                let extended = install_nondet(self.config.clone(), graph.clone(), offer, v);
                check(&extended)
            }
            LabelEnum::SendMsg(_) => {
                let extended = install(self.config.clone(), graph.clone(), offer);
                check(&extended)
            }
            other => unreachable!("conformance: a probe offered a {other}, which is not a choice point"),
        }
    }

    fn rf_options(&self, offer: &Offer) -> Vec<Option<Event>> {
        let mut out: Vec<Option<Event>> = offer.sources().iter().copied().map(Some).collect();
        if offer.may_read_nothing() {
            out.push(None);
        }
        out
    }

    fn done(
        &self,
        outer: &Outer<'_>,
        probed: &Probed,
        spec_wobs: &Wobs,
    ) -> Result<bool, ObsError> {
        if !matches(
            probed.graph(),
            outer.graph,
            spec_wobs,
            &outer.wobs,
            &self.visible,
        ) {
            return Ok(false);
        }
        if !outer.complete {
            return Ok(true);
        }
        if !probed.offers().is_empty() {
            return Ok(false);
        }
        let Some(exec) = probed.complete() else {
            return Ok(false);
        };
        let spec_statuses = statuses(exec, spec_wobs, &self.visible)?;
        let imp_statuses = statuses(
            CompleteExecution::assume_finished_at_gate(outer.graph),
            &outer.wobs,
            &self.visible,
        )?;
        Ok(statuses_agree(&spec_statuses, &imp_statuses))
    }

    fn probe(&self, graph: ExecutionGraph) -> Probed {
        let spec = Arc::clone(&self.spec);
        probe_from(self.config.clone(), graph, move || spec())
    }

    // -- the first failing obligation --------------------------------------

    /// §7.1's four values, in §7.1's order: (M1), then (M2), then (M3), then
    /// "no offerable event passed Φ".
    ///
    /// The order is the enumeration's, not an accident: (M1) is a statement
    /// about the observation *sequences*, which a user can check by eye; (M2)
    /// is about order between matched pairs; (M3) needs a complete execution
    /// on both sides and is only meaningful there. Φ-emptiness is the
    /// fall-through, because it is what is left when the morphism holds on
    /// the attempt and the attempt still could not be extended.
    fn obligation(
        &self,
        outer: &Outer<'_>,
        graph: &ExecutionGraph,
    ) -> Result<Option<Obligation>, ObsError> {
        let spec_wobs = wobs(graph, &self.visible)?;

        // (M1)
        for name in &self.visible {
            let s = spec_wobs.of(name);
            let i = outer.wobs.of(name);
            for (k, ((_, a), (_, b))) in s.iter().zip(i).enumerate() {
                if a != b {
                    return Ok(Some(Obligation::ObservationMismatch {
                        thread: name.clone(),
                        position: k,
                        spec: report::obs_text(a),
                        imp: report::obs_text(b),
                    }));
                }
            }
            if s.len() != i.len() {
                let k = s.len().min(i.len());
                return Ok(Some(Obligation::ObservationMismatch {
                    thread: name.clone(),
                    position: k,
                    spec: s
                        .get(k)
                        .map(|(_, o)| report::obs_text(o))
                        .unwrap_or_else(report::nothing_text),
                    imp: i
                        .get(k)
                        .map(|(_, o)| report::obs_text(o))
                        .unwrap_or_else(report::nothing_text),
                }));
            }
        }

        // (M2). The matched pairs are the i-th visible event of `t` on each
        // side, for as far as both sides have one — the same pairing
        // `morphism::matched_pairs` builds. `vo` is `porf` restricted to
        // visible events but computed *through* invisible ones, which is what
        // `in_porf` answers; the diagonal is excluded because `vo` is
        // irreflexive and `in_porf(e, e)` is true.
        let mut pairs: Vec<(Event, Event)> = Vec::new();
        for name in &self.visible {
            let s = spec_wobs.of(name);
            let i = outer.wobs.of(name);
            for ((se, _), (ie, _)) in s.iter().zip(i) {
                pairs.push((*ie, *se));
            }
        }
        for (ie1, se1) in &pairs {
            for (ie2, se2) in &pairs {
                let spec_ordered = se1 != se2 && graph.in_porf(*se1, *se2);
                let imp_ordered = ie1 != ie2 && outer.graph.in_porf(*ie1, *ie2);
                if spec_ordered && !imp_ordered {
                    return Ok(Some(Obligation::MissingPullBack {
                        spec_from: report::event_text(*se1),
                        spec_to: report::event_text(*se2),
                        imp_from: report::event_text(*ie1),
                        imp_to: report::event_text(*ie2),
                    }));
                }
            }
        }

        // (M3), only where it is defined.
        if outer.complete {
            if let Some(spec_exec) = CompleteExecution::try_finished(graph) {
                let spec_statuses = statuses(spec_exec, &spec_wobs, &self.visible)?;
                let imp_statuses = statuses(
                    CompleteExecution::assume_finished_at_gate(outer.graph),
                    &outer.wobs,
                    &self.visible,
                )?;
                for name in &self.visible {
                    let a = spec_statuses.get(name);
                    let b = imp_statuses.get(name);
                    if a != b {
                        return Ok(Some(Obligation::StatusMismatch {
                            thread: name.clone(),
                            spec: a.copied().map(report::status_text).unwrap_or("absent").to_owned(),
                            imp: b.copied().map(report::status_text).unwrap_or("absent").to_owned(),
                        }));
                    }
                }
            }
        }

        // §7.1's fourth value, **verified before it is emitted**.
        //
        // Round-5 review, B1: this used to return the variant unconditionally,
        // and the first fixture anyone built for it showed the sentence to be
        // false — an offerable specification event *had* passed Φ at the very
        // attempt the report names. The cause is structural rather than
        // incidental. Φ-emptiness is a property of a traversal **leaf**, and
        // `graph` here is `best.graph`, the max-vector *following* attempt:
        // `Best::offer` replaces only on a strictly greater vector, so an
        // extension installing an **invisible** event leaves `best.graph`
        // unmoved. A non-leaf best attempt is therefore ordinary, not exotic.
        //
        // So ask. If no offer passes Φ the value is true and is emitted; if
        // some offer does, we know the morphism held on this attempt and that
        // no extension of it covered, which is a *different* statement and
        // §7.1 has no value for it — so say nothing rather than say something
        // false. Introducing that fifth value is §7.1's own question and is
        // routed to the owner with F-7, A13 and H-1.
        let probed = self.probe(graph.clone());
        for offer in probed.offers() {
            if self.phi(outer, probed.graph(), offer)? {
                return Ok(None);
            }
        }
        Ok(Some(Obligation::NoOfferablePassedPhi))
    }
}

/// §7.3's final paragraph: the canonical linearisation of `obsposet(G)`, and
/// the status vector beside it.
///
/// **The linearisation is named, deterministic and tested**, because `vis(G)`
/// is a *set* — "the set of linear extensions of `vo(G)`, labelled by `obs_G`
/// and paired with `status_G|_Tvis`" — so two `vo`-incomparable visible events
/// with distinct observations give `|vis(G)| ≥ 2`, and concurrency among
/// visible events is the ordinary case (it is what (M2) exists to compare).
/// Pinning "the word" without naming a linearisation pins whichever one the
/// implementation happened to emit: a schedule-dependent snapshot, the
/// flaky-by-construction test criterion 1 exists to prevent.
///
/// **The rule**: repeatedly take the `vo`-minimal visible events that remain,
/// and among them the one whose ⟨declared thread name, index in that thread's
/// row⟩ key is smallest. Declared names are compared as strings, so the order
/// is a property of the *declaration* and not of spawn order, `ThreadId`
/// allocation, or the schedule.
pub(crate) fn canonical_vis(
    graph: &ExecutionGraph,
    visible: &[String],
    complete: Option<CompleteExecution<'_>>,
) -> Result<VisTrace, ObsError> {
    let w = wobs(graph, visible)?;

    // ⟨name, index-in-row⟩ keyed events.
    let mut remaining: Vec<(String, usize, Event)> = Vec::new();
    for name in visible {
        for (k, (e, _)) in w.of(name).iter().enumerate() {
            remaining.push((name.clone(), k, *e));
        }
    }

    let mut word = Vec::new();
    while !remaining.is_empty() {
        // Minimal under `vo` among what is left.
        let mut candidates: Vec<usize> = (0..remaining.len())
            .filter(|&i| {
                !remaining.iter().enumerate().any(|(j, (_, _, other))| {
                    j != i && *other != remaining[i].2 && graph.in_porf(*other, remaining[i].2)
                })
            })
            .collect();
        // A cycle would leave no minimal element. `vo` is `porf` restricted,
        // and `porf` is a partial order on a real graph, so this cannot
        // happen — but answering an arbitrary element would make the
        // linearisation silently non-canonical, which is the one thing this
        // function exists to prevent.
        assert!(
            !candidates.is_empty(),
            "conformance: the visible events of this graph have no vo-minimal element, so \
             vo is not a partial order on them"
        );
        candidates.sort_by(|&a, &b| {
            (&remaining[a].0, remaining[a].1).cmp(&(&remaining[b].0, remaining[b].1))
        });
        let pick = candidates[0];
        let (name, k, _) = remaining.remove(pick);
        let obs = &w.of(&name)[k].1;
        word.push(format!("{name}: {}", report::obs_text(obs)));
    }

    // The status half. `None` means the graph is not a complete execution, so
    // (M3) is outside its domain: the vector is then absent rather than
    // fabricated, which is the same rule `status_of` follows.
    let statuses = match complete {
        Some(exec) => {
            let m = statuses(exec, &w, visible)?;
            visible
                .iter()
                .map(|n| {
                    (
                        n.clone(),
                        m.get(n)
                            .copied()
                            .map(report::status_text)
                            .unwrap_or("absent")
                            .to_owned(),
                    )
                })
                .collect()
        }
        None => visible
            .iter()
            .map(|n| (n.clone(), "not a complete execution".to_owned()))
            .collect::<Vec<(String, String)>>(),
    };

    Ok(VisTrace { word, statuses })
}

/// The specification-side first mismatch a triaged report is presented next to
/// (§7.3's final paragraph). Derived from the report's own diagnostics, so the
/// two cannot drift apart.
pub(crate) fn spec_side_first_mismatch(d: &Diagnostics, cause: &ReportCause) -> String {
    match (d, cause) {
        (Diagnostics::Available { obligation, .. }, _) => obligation.to_string(),
        (_, ReportCause::VisibleError { .. }) => {
            "not applicable: this report is a failed assertion, not a `Cover` answer".to_owned()
        }
        (
            Diagnostics::Unavailable {
                kind: report::UnavailableKind::Diverged,
                because,
            },
            _,
        ) => format!("unavailable ({because})"),
        // The recomputation agreed; §7.1 has no name for what it found (A14).
        // Said as itself rather than folded into "unavailable", which would
        // read as a failure of the recomputation.
        (
            Diagnostics::Unavailable {
                kind: report::UnavailableKind::NoValueForIt,
                ..
            },
            _,
        ) => "no §7.1 obligation names this failure; see A14".to_owned(),
        (Diagnostics::NotApplicable, _) => "not applicable".to_owned(),
    }
}

/// Whether a gate's report was raised on a complete implementation graph.
///
/// `Gate::Completion` is the only gate that may pass `outer_complete = true`
/// (§5.5, owner ruling 2026-09-12) — the flag is **positional**, carried by
/// the site rather than derived from the graph. A §4.4 visible-error report is
/// not a gate firing at all, and the execution it names was pruned rather than
/// finished, so it is not complete either.
pub(crate) fn outer_complete(gate: ReportGate) -> bool {
    matches!(gate, ReportGate::Completion)
}
