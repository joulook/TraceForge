//! The inner search over the specification.
//!
//! Given an implementation graph `G₁`, find a specification graph that covers
//! it, or report that none does. This is `alg.tex`'s `alg:cover`, transcribed:
//! `Cover` tries the seed the outer search carries and then rebuilds from
//! empty; `SpecVisit` recurses over the offered events; `SpecStep` checks the
//! chosen extension and recurses; `Done` decides when a graph is a finished
//! cover.
//!
//! Three things about the shape, because each is a place the transcription
//! could go wrong quietly.
//!
//! **Every offered event is a backtrack point.** `alg.tex:866-869`: "tries
//! every offerable event and not one of them … Looping is what makes the
//! search find that order whenever one exists". A search that took the first
//! offer would be right whenever the gate leaves one event offerable, which is
//! the common case, and wrong exactly on the examples the draft exists to
//! exhibit.
//!
//! **The node is the probe's *output* graph.** A probe returns the prefix it
//! replayed plus the forced bookkeeping its threads performed — `Begin`,
//! `End`, `Unique`, and the `Block(Value)` a disabled receive installs. Those
//! are the labels (M3) reads, so a node carrying the pre-probe graph could not
//! answer Ex. blocking at all.
//!
//! **Exhausting a budget is not ⊥.** ⊥ is what makes the tool speak: it means
//! no specification graph covers this implementation graph. A search that ran
//! out of room has not established that, so [`Cover::BudgetExhausted`] is a
//! separate answer and propagates as one. Reporting a violation because the
//! search gave up would be worse than hanging, since the hang is visible.

use std::sync::Arc;

use crate::conformance::morphism::{follows, matches, statuses, statuses_agree, CompleteExecution};
use crate::conformance::obs::{wobs, ObsError, Wobs};
use crate::conformance::probe::Offer;
use crate::conformance::prober::{install, install_nondet, install_recv, probe_from, Probed};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::Config;

/// What the search found.
#[derive(Debug)]
pub(crate) enum Cover {
    /// A specification graph covering `G₁`. The outer search keeps it as the
    /// next heuristic seed.
    Found(ExecutionGraph),
    /// The draft's ⊥: no specification graph covers `G₁`. **This is a
    /// report.**
    NoCover,
    /// The search hit its node budget. **Not** a report — it says nothing
    /// about whether a cover exists.
    BudgetExhausted,
}

impl Cover {
    fn is_found(&self) -> bool {
        matches!(self, Cover::Found(_))
    }
}

/// A node ceiling, so that a non-terminating search fails loudly instead of
/// hanging.
///
/// The draft's termination argument uses the lexicographic measure
/// `⟨N_Spec − |G.E|, k⟩` (`alg.tex:1085-1088`), whose premise is that
/// installing an event is the only thing that changes `|G.E|`. That premise
/// does **not** transport unexamined: `unblock_ready` deletes a `Block(Value)`
/// label when its receive becomes enabled, so a probe graph is non-monotone
/// (backlog **F34**). Until that is settled, the ceiling is what stands
/// between a transport gap and a test suite that hangs rather than fails.
struct Budget {
    remaining: usize,
}

impl Budget {
    fn spend(&mut self) -> bool {
        if self.remaining == 0 {
            return false;
        }
        self.remaining -= 1;
        true
    }
}

/// Everything about the implementation side that is fixed for one `Cover`
/// call.
///
/// `G₁` does not change while the search runs, so its observations are
/// extracted once here. That is not the memoisation §6.1 forbids: §6.1
/// defers a cache *across* gate calls, because a revisit invalidates a
/// suffix. This lives and dies with a single call.
struct Outer<'a> {
    graph: &'a ExecutionGraph,
    wobs: Wobs,
    /// Whether the outer graph is complete, passed by the call site — the
    /// completion gate passes `true`, the in-execution gates `false`. It
    /// gates the second and third conjuncts of `Done`.
    complete: bool,
}

/// The inner search.
pub(crate) struct Search {
    config: Config,
    /// The specification program, re-run once per probe. Held behind an `Arc`
    /// because `probe_from` takes the closure by value and the search runs it
    /// many times.
    spec: Arc<dyn Fn() + Send + Sync>,
    visible: Vec<String>,
    budget: usize,
}

impl Search {
    pub(crate) fn new(
        config: Config,
        spec: Arc<dyn Fn() + Send + Sync>,
        visible: Vec<String>,
        budget: usize,
    ) -> Self {
        Self {
            config,
            spec,
            visible,
            budget,
        }
    }

    /// `Cover(G₁, H)` — extend the seed the outer search carries; failing
    /// that, build again from empty.
    ///
    /// The rebuild is not a retry of the same search: a seed that cannot be
    /// extended may still be a prefix of nothing useful, while a graph built
    /// from scratch explores the whole space. `alg.tex:792-795`.
    ///
    /// **Budget accounting, stated properly** — two earlier versions of this
    /// paragraph gave reasons that were not the reason.
    ///
    /// Each attempt gets its **own** budget, so one `cover` call can spend up
    /// to **twice** the ceiling: the seed search, and then the rebuild.
    /// Callers sizing the ceiling against a per-gate cost budget should know
    /// that.
    ///
    /// Exhaustion on the seed attempt returns immediately rather than
    /// rebuilding. This is a **policy, not a correctness requirement**, and it
    /// has a cost: the rebuild would get a fresh budget and might well return
    /// `Found`, which would be a sound answer — so returning early can forgo
    /// a cover that was findable. It is chosen because exhaustion means the
    /// seed attempt was inconclusive, and spending a second budget on top of
    /// an inconclusive first one makes a single gate's worst case 2× while
    /// still not establishing anything about the seed. If the false-alarm
    /// cost of the forgone covers ever shows up in §11.5's floor, reverse it:
    /// rebuilding after exhaustion is strictly more likely to find a cover.
    ///
    /// Exhaustion on the **rebuild** propagates, and must: at that point
    /// neither attempt has established "no cover exists".
    /// **Preconditions on the caller**, none of which the types enforce:
    ///
    /// - `seed` must be a graph of this specification — in practice the `H`
    ///   a previous `cover` returned, or `ExecutionGraph::default()`. Nothing
    ///   checks it, and a graph from elsewhere would be replayed against a
    ///   program that never produced it.
    /// - `outer_complete` must be true only when the outer execution really
    ///   has finished. Passing it wrongly does **not** give a wrong answer —
    ///   `done` calls `assume_finished_at_gate`, which **panics** if `g1` has
    ///   a running spawned thread. S4 discharges this positionally: only the
    ///   completion gate passes `true` (`conformance::ctx::Gate`).
    /// - Scope is enforced when the offer is **produced**, not when it is
    ///   installed. `probe_install` bypasses handler entry entirely, so the
    ///   `reject_out_of_scope` guards are not on the install path in any
    ///   configuration — this is a property of *where* the guards sit, not of
    ///   which `Must` the installs build, as an earlier version of this
    ///   comment claimed. (Their count is also build-conditional: eight with
    ///   `--features symbolic`, seven without.)
    /// - This must run on a **dedicated OS thread**. `probe_from` sets the
    ///   thread-local current `Must` and runs the specification on the calling
    ///   thread, so calling `cover` from inside an outer execution would nest
    ///   two runtimes in one thread's scoped state. `ConfCtx` owns that
    ///   thread; nothing else may call this from within an execution.
    pub(crate) fn cover(
        &self,
        g1: &ExecutionGraph,
        outer_complete: bool,
        seed: ExecutionGraph,
    ) -> Result<Cover, ObsError> {
        let outer = Outer {
            graph: g1,
            wobs: wobs(g1, &self.visible)?,
            complete: outer_complete,
        };

        let mut budget = Budget {
            remaining: self.budget,
        };
        let from_seed = self.spec_visit(&outer, seed, &mut budget)?;
        if from_seed.is_found() || matches!(from_seed, Cover::BudgetExhausted) {
            return Ok(from_seed);
        }

        let mut budget = Budget {
            remaining: self.budget,
        };
        self.spec_visit(&outer, ExecutionGraph::default(), &mut budget)
    }

    /// `SpecVisit(G₁, G)`.
    fn spec_visit(
        &self,
        outer: &Outer<'_>,
        graph: ExecutionGraph,
        budget: &mut Budget,
    ) -> Result<Cover, ObsError> {
        if !budget.spend() {
            return Ok(Cover::BudgetExhausted);
        }

        // One probe answers two questions at once: what this graph can do
        // next, and — because the prober applies no Φ — whether it can do
        // anything at all, which is `Done`'s `next_Spec(G) = ∅` conjunct.
        let probed = self.probe(graph);

        // A declared visible thread never spawned is a §8 violation by the
        // *specification program* — the user's own mistake. It propagates as
        // an error rather than being folded into any `Cover` answer: as ⊥ it
        // would report a conformance violation that is not one, and as
        // `BudgetExhausted` it would claim the search ran out of room, which
        // is a different lie. ⊥ is a report, and nothing else may wear its
        // clothes.
        if self.done(outer, &probed)? {
            return Ok(Cover::Found(probed.graph().clone()));
        }

        let mut exhausted = false;
        for offer in probed.offers() {
            // Φ defines the loop's *range* (`alg.tex:845-851`), so an offer
            // that fails it is not a backtrack point at all.
            if !self.phi(outer, probed.graph(), offer)? {
                continue;
            }
            let outcome = self.branch(outer, probed.graph(), offer, budget)?;
            if outcome.is_found() {
                return Ok(outcome);
            }
            if matches!(outcome, Cover::BudgetExhausted) {
                exhausted = true;
            }
        }

        // Exhaustion anywhere below means this subtree was not fully
        // explored, so "no cover" has not been established for it.
        Ok(if exhausted {
            Cover::BudgetExhausted
        } else {
            Cover::NoCover
        })
    }

    /// The three cases of `alg.tex:800-808`, each looping its own decisions.
    fn branch(
        &self,
        outer: &Outer<'_>,
        graph: &ExecutionGraph,
        offer: &Offer,
        budget: &mut Budget,
    ) -> Result<Cover, ObsError> {
        let mut exhausted = false;

        // Every extension starts from a *clone*. A failed branch must leave
        // nothing behind for its siblings — the A3 resolution's functional
        // reading — and the failure mode if it does is silent, since an
        // accumulating graph still answers, just wrongly.
        // A macro rather than a closure: a closure would borrow `budget`
        // mutably for the whole match, and the `?` on an error has to leave
        // this function rather than be absorbed into a `Cover`.
        macro_rules! try_one {
            ($extended:expr, $through_step:expr) => {{
                let outcome = if $through_step {
                    self.spec_step(outer, $extended, budget)?
                } else {
                    self.spec_visit(outer, $extended, budget)?
                };
                if outcome.is_found() {
                    return Ok(outcome);
                }
                exhausted |= matches!(outcome, Cover::BudgetExhausted);
            }};
        }

        match offer.label() {
            // A nondet goes straight to `SpecVisit` (`ln:innernd`), not
            // through `SpecStep`: the value changes no observation, so there
            // is nothing for a follow check to reject that Φ did not already.
            LabelEnum::CToss(_) | LabelEnum::Choice(_) => {
                let values = offer.nondet_values();
                // An empty option list would skip the loop entirely and fall
                // through to `NoCover` below — a manufactured ⊥, and the fifth
                // instance of that shape found in this file. `phi` was already
                // fixed to panic on exactly this condition; leaving `branch`
                // to answer ⊥ for it meant the two disagreed about whether it
                // was possible. A nondet offer always has options: a `CToss`
                // has two and a `Choice`'s range cannot be empty.
                assert!(
                    !values.is_empty(),
                    "conformance: the nondet offer at {} has no values, so it \
                     is not a choice point",
                    offer.pos()
                );
                for value in values {
                    let extended = install_nondet(self.config.clone(), graph.clone(), offer, value);
                    try_one!(extended, false);
                }
            }
            // A receive loops its sources, ⊥ included when it may read
            // nothing, and each goes through `SpecStep` — Φ promised *some*
            // source works, not the one taken (`alg.tex:853-856`).
            LabelEnum::RecvMsg(_) => {
                let options = self.rf_options(offer);
                // Same reason as the nondet arm above. An offered receive
                // always has at least one option: a blocking receive with no
                // sources is never offered — the preflight turns it into a
                // `Block(Value)` — and a non-blocking one can always read ⊥.
                assert!(
                    !options.is_empty(),
                    "conformance: the receive offer at {} has neither a source \
                     nor permission to read nothing, so it should not have been \
                     offered",
                    offer.pos()
                );
                for rf in options {
                    let extended = install_recv(self.config.clone(), graph.clone(), offer, rf);
                    try_one!(extended, true);
                }
            }
            // A send carries no decision, so the extension is the whole of it.
            LabelEnum::SendMsg(_) => {
                let extended = install(self.config.clone(), graph.clone(), offer);
                try_one!(extended, true);
            }
            other => {
                unreachable!("conformance: a probe offered a {other}, which is not a choice point")
            }
        }

        Ok(if exhausted {
            Cover::BudgetExhausted
        } else {
            Cover::NoCover
        })
    }

    /// `SpecStep(G₁, G)` — reject the extension, or recurse into it.
    ///
    /// The draft's first conjunct is `consistent_Spec(G)`, and it has no code
    /// here by design: §5.3's claim is that a probe execution *is* the
    /// linearisation witness, so every graph the prober produces is consistent
    /// by construction. Two routes install something the *search* chose rather
    /// than something the prober produced — `install_recv`'s source and
    /// `install_nondet`'s value — and each has its own argument. The source
    /// one is that `Offer::sources()` is exactly the consistent set, which
    /// holds because symmetric spawning is excluded (backlog **A11**; the
    /// symmetry filter is the only thing that narrowed it further and it is
    /// inert without a `sym_id`). The value one is that consistency is
    /// *vacuous* on nondet values — `cons.rs` has no `CToss` or `Choice` arm
    /// at all.
    fn spec_step(
        &self,
        outer: &Outer<'_>,
        graph: ExecutionGraph,
        budget: &mut Budget,
    ) -> Result<Cover, ObsError> {
        if self.follows(outer, &graph)? {
            self.spec_visit(outer, graph, budget)
        } else {
            Ok(Cover::NoCover)
        }
    }

    /// `Φ(e)` — may this offered event be taken?
    ///
    /// `alg.tex:845-851`: existential over the sources for a receive, and "the
    /// test is on the extension and not on `G`" for everything else.
    ///
    /// The draft adds that an invisible event "changes no `wobs_t` and adds no
    /// `vo` edge between visible events, so it always passes". That is true
    /// here too — an event installed at the frontier is `porf`-maximal, so it
    /// creates no path between two events that already exist — but this
    /// computes Φ for invisible events anyway rather than short-circuiting.
    /// Computing gives the same answer and rests on no argument; the
    /// short-circuit is a real saving and is left as an optimisation with a
    /// proof obligation attached.
    fn phi(
        &self,
        outer: &Outer<'_>,
        graph: &ExecutionGraph,
        offer: &Offer,
    ) -> Result<bool, ObsError> {
        match offer.label() {
            // A loop rather than `.any(..)`, so an error propagates instead of
            // being read as "this source does not work". `unwrap_or(false)`
            // here would turn a specification that violates §8 into an offer
            // that silently leaves the loop's range, narrowing the search and
            // losing covers — a report manufactured out of a usage error.
            LabelEnum::RecvMsg(_) => {
                let options = self.rf_options(offer);
                // The **sixth** instance of this file's recurring shape, and
                // the one the fifth fix missed. `branch` grew this assertion
                // in round 5; `phi` runs *first* and shields it, so an empty
                // option list never reached it. An offer dropped here leaves
                // Φ's range silently, and if it was the only offer the loop
                // is empty and `SpecVisit` answers `NoCover` — a ⊥ produced
                // for a reason that is not "no cover exists". Measured: with
                // `rf_options` forced empty, 11 tests fail and **none** carries
                // `branch`'s message, because none of them gets that far.
                assert!(
                    !options.is_empty(),
                    "conformance: the receive offer at {} has neither a source \
                     nor permission to read nothing, so it should not have been \
                     offered",
                    offer.pos()
                );
                for rf in options {
                    let extended = install_recv(self.config.clone(), graph.clone(), offer, rf);
                    if self.follows(outer, &extended)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            LabelEnum::CToss(_) | LabelEnum::Choice(_) => {
                // The extension, not the value: a nondet's value changes no
                // observation, so any of them answers the same question.
                // `nondet_values()` is non-empty for both kinds — a `CToss`
                // offers two booleans and a `Choice`'s range cannot be empty,
                // since `lib.rs` panics before installing one. An empty list
                // would mean an offer with no options at all, which is not a
                // choice point; answering `Ok(false)` would silently drop it
                // from the loop's range, and if it were the only offer that
                // is a manufactured ⊥.
                let v = offer
                    .nondet_values()
                    .first()
                    .copied()
                    .expect("conformance: a nondet offer with no values is not a choice point");
                let extended = install_nondet(self.config.clone(), graph.clone(), offer, v);
                self.follows(outer, &extended)
            }
            LabelEnum::SendMsg(_) => {
                let extended = install(self.config.clone(), graph.clone(), offer);
                self.follows(outer, &extended)
            }
            // Matching `branch`, which calls this case `unreachable!`. The two
            // disagreed: `branch` treated a non-choice-point offer as
            // impossible while this answered `Ok(false)`, silently dropping it
            // from the loop's range — and if it were the only offer, returning
            // ⊥ for a reason that is not "no cover exists". One of the two had
            // to be wrong; a probe only ever offers choice points, so it was
            // this one. Developer's test pass, third instance of the same
            // shape.
            other => {
                unreachable!("conformance: a probe offered a {other}, which is not a choice point")
            }
        }
    }

    /// The sources a receive offer may take, ⊥ included when it may read
    /// nothing.
    ///
    /// `alg.tex:801` writes this as `s ∈ G.Slbl ∪ {⊥}` — every send in the
    /// graph. `Offer::sources()` is TraceForge's own rf enumeration, which is
    /// the *consistent* subset of that; see `spec_step`'s note and A11.
    fn rf_options(&self, offer: &Offer) -> Vec<Option<Event>> {
        let mut out: Vec<Option<Event>> = offer.sources().iter().copied().map(Some).collect();
        if offer.may_read_nothing() {
            out.push(None);
        }
        out
    }

    /// `Done(G₁, G)` — three conjuncts, the second and third conditional on
    /// the outer graph being complete.
    fn done(&self, outer: &Outer<'_>, probed: &Probed) -> Result<bool, ObsError> {
        let spec_wobs = wobs(probed.graph(), &self.visible)?;
        if !matches(
            probed.graph(),
            outer.graph,
            &spec_wobs,
            &outer.wobs,
            &self.visible,
        ) {
            return Ok(false);
        }
        if !outer.complete {
            return Ok(true);
        }

        // The emptiness conjunct, asked directly.
        //
        // An earlier version of this read it off `Probed::complete()`, whose
        // doc comment here claimed it "yields a witness exactly when the probe
        // offered nothing". That is false, and review round 3 of the criteria
        // had already said so: `complete()` is `offers.is_empty() &&
        // is_complete(graph)`. Collapsing the two meant that a probe with no
        // offers whose graph failed the spawned-thread check would answer
        // `false` here, fall through to a loop over an empty offer set, and
        // return `NoCover` — **a manufactured ⊥**, which is the one thing the
        // criteria are emphatic must never happen. Found by the developer's
        // test pass.
        if !probed.offers().is_empty() {
            return Ok(false);
        }

        // The witness must now exist, and the argument is worth stating rather
        // than leaving to `expect`'s message. `is_complete` rejects a spawned
        // thread in two ways, and both have to be ruled out:
        //
        // - **Last label is neither `End` nor `Block`.** A probe offers
        //   nothing exactly when no thread can take another step, so every
        //   thread has finished or blocked. Main is exempt from the check
        //   anyway, never having an `End` (A8).
        // - **An empty row**, where `thread_last` is `None`. This is the arm
        //   review round 3 named and the `expect` comment first ignored: it
        //   cannot happen, because `handle_tcreate` appends the thread's
        //   `Begin` as it creates it, so no spawned thread ever has an empty
        //   row at any point a probe could return.
        //
        // If this ever fires, one of those two has stopped being true, and
        // the right response is to find out which — not to answer `NoCover`.
        let exec = probed.complete().expect(
            "conformance: a probe offered nothing, so every thread should rest \
             at End or Block; the completeness witness was refused anyway",
        );
        let spec_statuses = statuses(exec, &spec_wobs, &self.visible)?;
        let impl_statuses = statuses(
            CompleteExecution::assume_finished_at_gate(outer.graph),
            &outer.wobs,
            &self.visible,
        )?;
        Ok(statuses_agree(&spec_statuses, &impl_statuses))
    }

    /// "`G` follows `G₁`" — the prefix form of (M1), plus (M2) over the pairs
    /// the matching relates.
    fn follows(&self, outer: &Outer<'_>, graph: &ExecutionGraph) -> Result<bool, ObsError> {
        let spec_wobs = wobs(graph, &self.visible)?;
        Ok(follows(
            graph,
            outer.graph,
            &spec_wobs,
            &outer.wobs,
            &self.visible,
        ))
    }

    /// One probe of the specification against `graph`.
    fn probe(&self, graph: ExecutionGraph) -> Probed {
        let spec = Arc::clone(&self.spec);
        probe_from(self.config.clone(), graph, move || spec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conformance::probe::NondetValue;
    use crate::conformance::testing::names;
    use crate::event_label::LabelEnum;
    use crate::thread::{main_thread_id, ThreadId};
    use crate::{recv_msg_block, send_msg, thread, Nondet};

    // ------------------------------------------------------------- harness

    /// A program the tests can run many times.
    type Prog = Arc<dyn Fn() + Send + Sync>;

    fn prog<F: Fn() + Send + Sync + 'static>(f: F) -> Prog {
        Arc::new(f)
    }

    fn cfg() -> Config {
        Config::builder().build()
    }

    fn spawn_named<F>(name: &str, f: F) -> thread::JoinHandle<()>
    where
        F: FnOnce() + Send + 'static,
    {
        thread::Builder::new()
            .name(name.to_string())
            .spawn(f)
            .unwrap()
    }

    fn probe_of(p: &Prog, graph: ExecutionGraph) -> Probed {
        let p = Arc::clone(p);
        probe_from(cfg(), graph, move || p())
    }

    fn search_for(p: &Prog, visible: &[&str], budget: usize) -> Search {
        Search::new(cfg(), Arc::clone(p), names(visible), budget)
    }

    fn outer_of<'a>(graph: &'a ExecutionGraph, visible: &[&str], complete: bool) -> Outer<'a> {
        Outer {
            graph,
            wobs: wobs(graph, &names(visible)).expect("wobs of the outer graph"),
            complete,
        }
    }

    /// What to install for one chosen offer.
    enum Decision {
        Send,
        Recv(Option<Event>),
        Value(NondetValue),
    }

    /// Drive a program forward by probe-and-install, `choose` deciding at each
    /// step. Stops when the probe offers nothing or `choose` returns `None`.
    ///
    /// This is how every implementation graph `G₁` in this module is built. A
    /// hand-built `G₁` is what criterion 12 permits at S3 — there is no outer
    /// gate yet — but driving the real prober is strictly better: the graph has
    /// whatever shape TraceForge actually gives it, including the `Block` and
    /// `End` labels (M3) reads, and the rf choices are ones the checker's own
    /// enumeration offered.
    ///
    /// The step count is bounded so that a mistake here fails loudly rather
    /// than spinning.
    fn drive<C>(p: &Prog, mut choose: C) -> ExecutionGraph
    where
        C: FnMut(&[Offer], &ExecutionGraph) -> Option<(usize, Decision)>,
    {
        let mut graph = ExecutionGraph::default();
        for _ in 0..64 {
            let (offers, probed_graph) = probe_of(p, graph).into_parts();
            if offers.is_empty() {
                return probed_graph;
            }
            let Some((i, decision)) = choose(&offers, &probed_graph) else {
                return probed_graph;
            };
            graph = match decision {
                Decision::Send => install(cfg(), probed_graph, &offers[i]),
                Decision::Recv(rf) => install_recv(cfg(), probed_graph, &offers[i], rf),
                Decision::Value(v) => install_nondet(cfg(), probed_graph, &offers[i], v),
            };
        }
        panic!("drive: more than 64 steps; the program is not the small one this test meant");
    }

    /// Take the first offer, and for a decision take its first option.
    fn greedy(offers: &[Offer], _g: &ExecutionGraph) -> Option<(usize, Decision)> {
        let o = &offers[0];
        let d = match o.kind() {
            "send" => Decision::Send,
            "recv" => Decision::Recv(o.sources().first().copied()),
            "nondet" | "choice" => Decision::Value(o.nondet_values()[0]),
            other => panic!("greedy: unexpected offer kind {other}"),
        };
        Some((0, d))
    }

    /// Run `p` to exhaustion under the greedy policy.
    fn complete_graph(p: &Prog) -> ExecutionGraph {
        drive(p, greedy)
    }

    /// The `ThreadId` a declared visible name resolves to in `graph`.
    fn tid_of(graph: &ExecutionGraph, name: &str) -> ThreadId {
        wobs(graph, &names(&[name]))
            .expect("wobs")
            .row(name)
            .expect("the name is in this wobs")
            .thread()
            .unwrap_or_else(|| panic!("`{name}` is not spawned in this graph"))
    }

    /// The receive labels of `tid`, in program order, with their sources.
    fn recvs(graph: &ExecutionGraph, tid: ThreadId) -> Vec<(Event, Option<Event>)> {
        (0..graph.thread_size(tid) as u32)
            .map(|i| Event::new(tid, i))
            .filter_map(|e| graph.recv_label(e).map(|r| (e, r.rf())))
            .collect()
    }

    /// The `Choice` results in `tid`'s row, in program order.
    fn choices(graph: &ExecutionGraph, tid: ThreadId) -> Vec<usize> {
        (0..graph.thread_size(tid) as u32)
            .filter_map(|i| match graph.label(Event::new(tid, i)) {
                LabelEnum::Choice(c) => Some(c.result()),
                _ => None,
            })
            .collect()
    }

    fn found(c: Cover) -> ExecutionGraph {
        match c {
            Cover::Found(g) => g,
            other => panic!("expected a cover, got {other:?}"),
        }
    }

    // ------------------------------------------------------------ programs

    /// Ex. relay's `P₂`: `A ∥ R ∥ C`, with the invisible `R` forwarding.
    fn relay_impl() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
            });
            let cid = c.thread().id();
            let r = spawn_named("r", move || {
                let v: i32 = recv_msg_block();
                send_msg(cid, v);
            });
            send_msg(r.thread().id(), 1i32);
        })
    }

    /// Ex. relay's `P₁`: `A ∥ C`, no relay.
    fn relay_spec() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(c.thread().id(), 1i32);
        })
    }

    /// Ex. sched: two visible sends of the same value to a visible receiver.
    fn sched_prog() -> Prog {
        prog(|| {
            let mid = main_thread_id();
            let _b1 = spawn_named("b1", move || send_msg(mid, 7i32));
            let _b2 = spawn_named("b2", move || send_msg(mid, 7i32));
            let _v: i32 = recv_msg_block();
        })
    }

    /// Ex. restart's `Impl`: two `pp` sends, `1` then `6`.
    fn restart_impl() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {});
            let cid = c.thread().id();
            send_msg(cid, 1i32);
            send_msg(cid, 6i32);
        })
    }

    /// Ex. restart's `Spec`: `n := nondet({5,6})`, then `1`, then `n`.
    fn restart_spec() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {});
            let cid = c.thread().id();
            let n = (5..=6usize).nondet();
            send_msg(cid, 1i32);
            send_msg(cid, n as i32);
        })
    }

    /// Ex. rebuild / Ex. traces: two senders, one receiver, one receive.
    fn rebuild_prog() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
            });
            let cid = c.thread().id();
            let _a = spawn_named("a", move || send_msg(cid, 1i32));
            let _b = spawn_named("b", move || send_msg(cid, 2i32));
        })
    }

    /// Ex. blocking's `Impl`: `C` receives twice, and the second blocks.
    fn blocking_impl() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
                let _: i32 = recv_msg_block();
            });
            send_msg(c.thread().id(), 1i32);
        })
    }

    /// Ex. blocking's `Spec`: `C` receives once.
    fn blocking_spec() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(c.thread().id(), 1i32);
        })
    }

    /// Ex. naive's family, with `C`'s first send carrying `v`.
    fn naive(k: usize, v: i32) -> Prog {
        prog(move || {
            let a = spawn_named("a", || {});
            let mid = main_thread_id();
            let mut handles = Vec::new();
            for i in 0..k {
                handles.push(spawn_named(&format!("b{i}"), move || send_msg(mid, 1i32)));
            }
            send_msg(a.thread().id(), v);
            for _ in 0..k {
                let _: i32 = recv_msg_block();
            }
        })
    }

    /// The provenance program. `inv` is **invisible**, so a receive reading its
    /// send adds no `vo` edge between visible events and (M2) cannot rule it
    /// out — which is what lets two different sources both satisfy Φ.
    fn provenance_prog() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
                let _: i32 = recv_msg_block();
            });
            let cid = c.thread().id();
            let _inv = spawn_named("inv", move || send_msg(cid, 7i32));
            let _b2 = spawn_named("b2", move || {
                send_msg(cid, 7i32);
                send_msg(cid, 5i32);
            });
        })
    }

    /// One visible send of `v`, into a thread that drains it.
    fn one_send(v: i32) -> Prog {
        prog(move || {
            let sink = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), v);
        })
    }

    /// A non-blocking receive with a send available: its options are that send
    /// **and** ⊥.
    fn may_read_nothing_prog() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {
                let _v: Option<i32> = crate::recv_msg();
            });
            let cid = c.thread().id();
            let _s = spawn_named("s", move || send_msg(cid, 3i32));
        })
    }

    /// One visible send of `1`, then a second of `2`.
    fn two_sends() -> Prog {
        prog(|| {
            let c = spawn_named("c", || {});
            let cid = c.thread().id();
            send_msg(cid, 1i32);
            send_msg(cid, 2i32);
        })
    }

    // ------------------------------------------------------------------- Φ

    /// Φ is on the **extension**: a send whose value the outer graph does not
    /// record at that position is out of the loop's range.
    ///
    /// To break it: evaluate Φ on `G` rather than on `G ⊕ e` (the empty graph
    /// follows everything, so both halves would say `true`).
    #[test]
    fn phi_rejects_a_send_the_outer_graph_does_not_record() {
        let vis = &["main"];
        let g_one = complete_graph(&one_send(1));
        let g_two = complete_graph(&one_send(2));

        let spec = one_send(1);
        let s = search_for(&spec, vis, 64);
        let probed = probe_of(&spec, ExecutionGraph::default());
        let offer = &probed.offers()[0];
        assert_eq!(offer.kind(), "send");

        assert!(
            s.phi(&outer_of(&g_one, vis, false), probed.graph(), offer)
                .unwrap(),
            "a send of 1 against an outer graph recording 1"
        );
        assert!(
            !s.phi(&outer_of(&g_two, vis, false), probed.graph(), offer)
                .unwrap(),
            "a send of 1 against an outer graph recording 2 must leave the range"
        );
    }

    /// Ex. sched, the half that is the example's point: while only the send
    /// the outer graph did **not** order before the receive is present, the
    /// receive is not offerable; once the other send is there, it is.
    ///
    /// Φ is existential over the sources, so the second half also shows a Φ
    /// that is true because *some* source works while another does not.
    ///
    /// To break it: drop `order_is_reflected` from `follows` — the first
    /// assertion then passes Φ, which is the branch the example says dies.
    #[test]
    fn phi_holds_the_receive_back_until_the_ordered_send_is_there() {
        let vis = &["main", "b1", "b2"];
        let p = sched_prog();

        // G₁: the receive reads the *second* source the checker enumerates.
        let mut chosen = None;
        let g1 = drive(&p, |offers, _g| {
            if let Some(i) = offers.iter().position(|o| o.kind() == "send") {
                return Some((i, Decision::Send));
            }
            let i = offers.iter().position(|o| o.kind() == "recv").unwrap();
            let s = offers[i].sources()[1];
            chosen = Some(s);
            Some((i, Decision::Recv(Some(s))))
        });
        let chosen = chosen.expect("the receive was driven");
        let outer = outer_of(&g1, vis, true);
        let s = search_for(&p, vis, 512);

        // Build the specification side with only the *other* send installed.
        let other = drive(&p, |offers, _g| {
            offers
                .iter()
                .position(|o| o.kind() == "send" && o.pos().thread != chosen.thread)
                .map(|i| (i, Decision::Send))
        });
        let probed = probe_of(&p, other);
        let recv = probed
            .offers()
            .iter()
            .find(|o| o.kind() == "recv")
            .expect("the receive is enabled once one send is there");
        assert_eq!(recv.sources().len(), 1, "only the other send is available");
        assert!(
            !s.phi(&outer, probed.graph(), recv).unwrap(),
            "the receive must not be offerable while only the unordered send is pending"
        );

        // Now install the send G₁ ordered before the receive as well.
        let (offers, graph) = probe_of(&p, probed.graph().clone()).into_parts();
        let i = offers
            .iter()
            .position(|o| o.kind() == "send" && o.pos().thread == chosen.thread)
            .expect("the other send is still offered");
        let both = install(cfg(), graph, &offers[i]);
        let probed = probe_of(&p, both);
        let recv = probed
            .offers()
            .iter()
            .find(|o| o.kind() == "recv")
            .expect("the receive is still enabled");
        assert_eq!(recv.sources().len(), 2, "both sends are now available");
        assert!(
            s.phi(&outer, probed.graph(), recv).unwrap(),
            "Φ is existential: one of the two sources works"
        );
    }

    /// Ex. sched holds: `Cover` finds a graph, and it is the one that reads
    /// the source the outer graph ordered before the receive.
    #[test]
    fn ex_sched_holds() {
        let vis = &["main", "b1", "b2"];
        let p = sched_prog();

        let mut chosen = None;
        let g1 = drive(&p, |offers, _g| {
            if let Some(i) = offers.iter().position(|o| o.kind() == "send") {
                return Some((i, Decision::Send));
            }
            let i = offers.iter().position(|o| o.kind() == "recv").unwrap();
            let s = offers[i].sources()[1];
            chosen = Some(s);
            Some((i, Decision::Recv(Some(s))))
        });
        let chosen = chosen.expect("the receive was driven");

        let s = search_for(&p, vis, 512);
        let g = found(s.cover(&g1, true, ExecutionGraph::default()).unwrap());

        let main = main_thread_id();
        let rs = recvs(&g, main);
        assert_eq!(rs.len(), 1, "one receive");
        assert_eq!(
            rs[0].1,
            Some(chosen),
            "the cover must read the send the outer graph ordered before the receive"
        );
    }

    // ---------------------------------------------------------------- Done

    /// `Done`'s first conjunct on its own: a graph that *follows* is not a
    /// graph that *matches*.
    ///
    /// To break it: use `follows` in `done` instead of `matches` — the first
    /// assertion then reports a cover one event early.
    #[test]
    fn done_needs_matching_not_merely_following() {
        let vis = &["main"];
        let p = two_sends();
        let g1 = complete_graph(&p);
        let outer = outer_of(&g1, vis, false);
        let s = search_for(&p, vis, 64);

        let one = drive(&p, {
            let mut taken = 0;
            move |_offers, _g| {
                taken += 1;
                (taken <= 1).then_some((0, Decision::Send))
            }
        });
        assert!(
            !s.done(&outer, &probe_of(&p, one)).unwrap(),
            "one send of two follows but does not match"
        );

        let both = complete_graph(&p);
        assert!(
            s.done(&outer, &probe_of(&p, both)).unwrap(),
            "both sends match, and the outer graph can still grow"
        );
    }

    /// **Criterion 5's central conjunct.** The outer graph is complete and the
    /// specification graph already matches it — but the specification can still
    /// take a step, so it is not a graph of Spec yet and `Done` is false.
    ///
    /// The step it can take is one **Φ rejects**, which is the whole point:
    /// asking the Φ-filtered range instead of the undirected `next_Spec` would
    /// read this graph as complete, `Done` would hold, `Cover` would return the
    /// graph, and the tool would go silent on a real violation.
    ///
    /// To break it: replace `probed.complete()`'s offer test with one over the
    /// Φ-filtered offers — both assertions below invert.
    #[test]
    fn done_asks_the_undirected_offer_set_not_the_filtered_range() {
        let vis = &["main"];
        let impl_p = one_send(1);
        let spec_p = two_sends();
        let g1 = complete_graph(&impl_p);
        let s = search_for(&spec_p, vis, 512);

        // The specification graph with just its first send: it matches G₁.
        let one = drive(&spec_p, {
            let mut taken = 0;
            move |_offers, _g| {
                taken += 1;
                (taken <= 1).then_some((0, Decision::Send))
            }
        });
        let probed = probe_of(&spec_p, one);
        assert!(
            !probed.offers().is_empty(),
            "the specification can still send its second message"
        );
        for offer in probed.offers() {
            assert!(
                !s.phi(&outer_of(&g1, vis, true), probed.graph(), offer)
                    .unwrap(),
                "every remaining offer is outside the Φ-filtered range"
            );
        }

        assert!(
            s.done(&outer_of(&g1, vis, false), &probed).unwrap(),
            "while the outer graph can grow, matching is enough"
        );
        assert!(
            !s.done(&outer_of(&g1, vis, true), &probed).unwrap(),
            "once the outer graph is complete, the specification must be complete too"
        );

        assert!(
            matches!(
                s.cover(&g1, true, ExecutionGraph::default()).unwrap(),
                Cover::NoCover
            ),
            "no graph of this specification covers a single send of 1"
        );
    }

    // --------------------------------------------------------- the examples

    /// Ex. relay: `P₂ ⊑ P₁` through the invisible relay.
    #[test]
    fn ex_relay_holds() {
        let vis = &["main", "c"];
        let g1 = complete_graph(&relay_impl());
        let spec = relay_spec();
        let s = search_for(&spec, vis, 512);
        let g = found(s.cover(&g1, true, ExecutionGraph::default()).unwrap());
        let c = tid_of(&g, "c");
        assert_eq!(recvs(&g, c).len(), 1, "the specification's single receive");
    }

    /// Ex. restart: two `Cover` calls, and the second cannot extend what the
    /// first returned.
    ///
    /// The nondet value order is pinned by `Offer::nondet_values`, which for a
    /// `Choice` is its inclusive range in ascending order — `5` then `6`. So
    /// the first call takes `5`, which the outer graph does not yet separate
    /// from `6`; the second call must abandon it.
    ///
    /// To break it: drop `Cover`'s second attempt (`ln:rebuild`) — the last
    /// assertion then fails with `NoCover`, which is the false report the
    /// example exists to exhibit.
    #[test]
    fn ex_restart_needs_the_rebuild() {
        let vis = &["main", "c"];
        let impl_p = restart_impl();
        let spec_p = restart_spec();

        // Gate 1: the outer graph has only the first send.
        let g1_one = drive(&impl_p, {
            let mut taken = 0;
            move |_offers, _g| {
                taken += 1;
                (taken <= 1).then_some((0, Decision::Send))
            }
        });
        let s = search_for(&spec_p, vis, 512);
        let seed = found(s.cover(&g1_one, false, ExecutionGraph::default()).unwrap());
        assert_eq!(
            choices(&seed, main_thread_id()),
            vec![5],
            "the first value in range order, which the outer graph does not yet separate"
        );

        // Gate 2: the outer graph is complete and records the second send.
        let g1_both = complete_graph(&impl_p);
        let mut budget = Budget { remaining: 512 };
        assert!(
            matches!(
                s.spec_visit(&outer_of(&g1_both, vis, true), seed.clone(), &mut budget)
                    .unwrap(),
                Cover::NoCover
            ),
            "the choice lies behind the graph, so extending it cannot undo it"
        );

        let g = found(s.cover(&g1_both, true, seed).unwrap());
        assert_eq!(
            choices(&g, main_thread_id()),
            vec![6],
            "the rebuild runs the value loop past 5 and takes 6"
        );
    }

    /// Ex. rebuild: the carried graph conflicts with the outer graph after a
    /// revisit, so no extension of it follows and `Cover` must build again.
    ///
    /// The revisit itself is the outer search's, which is S4's; here the two
    /// outer graphs are built directly, which is what criterion 12 permits.
    #[test]
    fn ex_rebuild_after_a_conflicting_seed() {
        let vis = &["a", "b", "c"];
        let p = rebuild_prog();

        // Step 2: `a` has sent and `c` has read it; `b` has not run.
        let g1_before = drive(&p, |offers, g| {
            let a = tid_of(g, "a");
            if let Some(i) = offers
                .iter()
                .position(|o| o.kind() == "send" && o.pos().thread == a)
            {
                return Some((i, Decision::Send));
            }
            let i = offers.iter().position(|o| o.kind() == "recv")?;
            let s = offers[i].sources()[0];
            Some((i, Decision::Recv(Some(s))))
        });

        let s = search_for(&p, vis, 512);
        let seed = found(
            s.cover(&g1_before, false, ExecutionGraph::default())
                .unwrap(),
        );

        // After the revisit: both sends are there and `c` reads `b`'s.
        let g1_after = drive(&p, |offers, g| {
            let b = tid_of(g, "b");
            if let Some(i) = offers.iter().position(|o| o.kind() == "send") {
                return Some((i, Decision::Send));
            }
            let i = offers.iter().position(|o| o.kind() == "recv").unwrap();
            let src = *offers[i]
                .sources()
                .iter()
                .find(|e| e.thread == b)
                .expect("b's send is available");
            Some((i, Decision::Recv(Some(src))))
        });

        let mut budget = Budget { remaining: 512 };
        assert!(
            matches!(
                s.spec_visit(&outer_of(&g1_after, vis, true), seed.clone(), &mut budget)
                    .unwrap(),
                Cover::NoCover
            ),
            "the carried graph's receive already reads the wrong send"
        );

        let g = found(s.cover(&g1_after, true, seed).unwrap());
        let c = tid_of(&g, "c");
        let b = tid_of(&g, "b");
        assert_eq!(
            recvs(&g, c)[0].1.map(|e| e.thread),
            Some(b),
            "the rebuilt cover reads b's send"
        );
    }

    /// Ex. blocking: the two graphs carry the same visible events and both are
    /// complete, and what separates them is a status. `Cover` must **report**.
    ///
    /// The completeness flag is what makes (M3) reachable at all, so the same
    /// call with the flag `false` finds a cover — which is how this test also
    /// establishes that the flag is used rather than accepted and ignored.
    ///
    /// To break it: drop the `statuses_agree` conjunct from `done` — the first
    /// assertion then returns `Found` and the tool goes silent on this one.
    #[test]
    fn ex_blocking_reports() {
        let vis = &["main", "c"];
        let g1 = complete_graph(&blocking_impl());
        let spec = blocking_spec();
        let s = search_for(&spec, vis, 512);

        assert!(
            matches!(
                s.cover(&g1, true, ExecutionGraph::default()).unwrap(),
                Cover::NoCover
            ),
            "a status-only difference must be reported once both graphs are complete"
        );
        assert!(
            s.cover(&g1, false, ExecutionGraph::default())
                .unwrap()
                .is_found(),
            "with the completeness flag false, (M3) is not consulted"
        );
    }

    /// Ex. naive, as a cost test. **The metric is nodes expanded** — one per
    /// call to `spec_visit`, which is exactly what `Budget::spend` counts — and
    /// the ceiling is the budget itself: exceeding it returns
    /// `BudgetExhausted`, which this test fails on.
    ///
    /// With `k = 5`, `Alg. naive` explores `(k!)² = 14400` complete graphs.
    /// The inner search here is allowed **one node per attempt**: every offer
    /// at the empty graph is outside Φ's range, because `C`'s send carries the
    /// wrong value and no `Bᵢ` has sent in the outer graph yet.
    ///
    /// The second half shows the ceiling is real rather than decorative: with
    /// no budget at all the answer is `BudgetExhausted`, not `NoCover`.
    #[test]
    fn ex_naive_stays_within_a_node_ceiling() {
        let k = 5;
        let vis_owned: Vec<String> = std::iter::once("main".to_string())
            .chain(std::iter::once("a".to_string()))
            .chain((0..k).map(|i| format!("b{i}")))
            .collect();
        let vis: Vec<&str> = vis_owned.iter().map(String::as_str).collect();

        let impl_p = naive(k, 0);
        let spec_p = naive(k, 1);

        // The outer graph right after C's first send — the gate that reports.
        let g1 = drive(&impl_p, |offers, _g| {
            let i = offers
                .iter()
                .position(|o| o.kind() == "send" && o.pos().thread == main_thread_id())?;
            Some((i, Decision::Send))
        });

        let tight = search_for(&spec_p, &vis, 1);
        assert!(
            matches!(
                tight.cover(&g1, false, ExecutionGraph::default()).unwrap(),
                Cover::NoCover
            ),
            "one node per attempt must be enough, against (k!)² = 14400 naive graphs"
        );

        let none = search_for(&spec_p, &vis, 0);
        assert!(
            matches!(
                none.cover(&g1, false, ExecutionGraph::default()).unwrap(),
                Cover::BudgetExhausted
            ),
            "the ceiling has to bite, or the first assertion proves nothing"
        );
    }

    // ------------------------------------------------- the remaining cases

    /// `Cover`'s failing case: nothing the specification can do carries the
    /// value the outer graph records.
    #[test]
    fn cover_reports_when_no_specification_graph_matches() {
        let vis = &["main"];
        let g1 = complete_graph(&one_send(2));
        let spec = one_send(1);
        let s = search_for(&spec, vis, 512);
        assert!(
            matches!(
                s.cover(&g1, true, ExecutionGraph::default()).unwrap(),
                Cover::NoCover
            ),
            "a send of 2 is covered by no graph of a program that sends 1"
        );
    }

    /// **Criterion 13.** A budget ceiling may not be dressed as ⊥. Both halves
    /// matter: the program that *has* a cover and the program that has
    /// **none** must give the same answer when the search has no room, because
    /// ⊥ is a report and the search has established nothing.
    ///
    /// To break it: fold `BudgetExhausted` into `NoCover` anywhere — in
    /// `spec_visit`'s tail, in `branch`'s, or in `cover`'s first test.
    #[test]
    fn an_exhausted_budget_is_never_a_report() {
        let vis = &["main", "c"];

        let covered = complete_graph(&relay_impl());
        let spec = relay_spec();
        for budget in [0, 1, 2] {
            let s = search_for(&spec, vis, budget);
            assert!(
                matches!(
                    s.cover(&covered, true, ExecutionGraph::default()).unwrap(),
                    Cover::BudgetExhausted
                ),
                "budget {budget}: a cover exists and was not reached"
            );
        }

        let uncovered = complete_graph(&blocking_impl());
        let s = search_for(&blocking_spec(), vis, 1);
        assert!(
            matches!(
                s.cover(&uncovered, true, ExecutionGraph::default())
                    .unwrap(),
                Cover::BudgetExhausted
            ),
            "no cover exists here either, but the search did not establish that"
        );
    }

    /// **Criterion 13, the other half.** A usage error must not wear ⊥'s
    /// clothes either. The specification never spawns a declared visible
    /// thread, which §8 forbids; the search must surface that as an error and
    /// not as "no specification graph covers this".
    ///
    /// The name reads as the empty sequence on a partial graph, so the error
    /// can only be raised where completeness is known — which is inside
    /// `done`, on a graph that has already matched. That is the path this
    /// pins.
    #[test]
    fn a_specification_that_breaks_section_8_is_an_error_not_a_report() {
        let vis = &["main", "c", "ghost"];
        let impl_p = prog(|| {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
            });
            let _ghost = spawn_named("ghost", || {});
            send_msg(c.thread().id(), 1i32);
        });
        let g1 = complete_graph(&impl_p);
        let s = search_for(&blocking_spec(), vis, 512);

        match s.cover(&g1, true, ExecutionGraph::default()) {
            Err(ObsError::NotSpawned { name }) => assert_eq!(name, "ghost"),
            other => panic!("expected a NotSpawned error, got {other:?}"),
        }
    }

    /// **Criterion 3.** Two sibling branches from one parent graph: the first
    /// fails and the second succeeds, and the parent must not have moved.
    ///
    /// The value loop is the site — `install_nondet` at `5` and then at `6`
    /// from the same node. If the clone were shared, the second install would
    /// meet an occupied frontier position and `probe_install`'s assertion would
    /// fire; and a graph carrying both choices would answer, just wrongly.
    #[test]
    fn a_failed_branch_leaves_nothing_for_its_sibling() {
        let vis = &["main", "c"];
        let g1 = complete_graph(&restart_impl());
        let spec_p = restart_spec();
        let s = search_for(&spec_p, vis, 512);
        let outer = outer_of(&g1, vis, true);

        let probed = probe_of(&spec_p, ExecutionGraph::default());
        let offer = &probed.offers()[0];
        assert_eq!(offer.kind(), "choice");
        assert_eq!(
            offer.nondet_values(),
            vec![NondetValue::Choice(5), NondetValue::Choice(6)],
            "the whole range, in range order"
        );

        let before = format!("{}", probed.graph());
        let mut budget = Budget { remaining: 512 };
        let out = s
            .branch(&outer, probed.graph(), offer, &mut budget)
            .unwrap();
        assert_eq!(
            before,
            format!("{}", probed.graph()),
            "the parent graph moved while its branches ran"
        );

        let g = found(out);
        assert_eq!(
            choices(&g, main_thread_id()),
            vec![6],
            "exactly one choice, and it is the sibling that succeeded"
        );
    }

    /// **Criterion 12's provenance case.** Φ is existential over the sources,
    /// so the source that made Φ true need not be the source `SpecStep` goes
    /// on to take. Here they differ: the invisible thread's send satisfies Φ
    /// first, and the graph `Cover` returns reads `b2`'s.
    ///
    /// `inv` being invisible is what makes the two sources both admissible —
    /// (M2) constrains only pairs the matching relates, so reading `inv`'s send
    /// adds no `vo` edge that the outer graph must already have. The `inv`
    /// branch then dies one level down, where `c`'s second receive can only
    /// read `b2`'s first send and the outer graph records `5` there.
    ///
    /// To break it: install `Φ`'s witness in `branch` instead of the loop's
    /// `rf` — the last assertion then names `inv`'s send.
    #[test]
    fn the_installed_source_is_the_one_taken_not_phis_witness() {
        let vis = &["b2", "c"];
        let p = provenance_prog();

        // G₁: both of `c`'s receives read `b2`.
        let g1 = drive(&p, |offers, g| {
            if let Some(i) = offers.iter().position(|o| o.kind() == "send") {
                return Some((i, Decision::Send));
            }
            let b2 = tid_of(g, "b2");
            let i = offers.iter().position(|o| o.kind() == "recv").unwrap();
            let src = *offers[i]
                .sources()
                .iter()
                .find(|e| e.thread == b2)
                .expect("b2 has a send available");
            Some((i, Decision::Recv(Some(src))))
        });
        let b2 = tid_of(&g1, "b2");
        let c = tid_of(&g1, "c");
        let inv = {
            // `inv` is not a declared visible name, so find it as the thread
            // that is neither main, nor b2, nor c.
            let mut ts = g1.thread_ids();
            ts.retain(|t| *t != main_thread_id() && *t != b2 && *t != c);
            assert_eq!(ts.len(), 1, "exactly one invisible sender");
            *ts.iter().next().unwrap()
        };

        let s = search_for(&p, vis, 4096);
        let outer = outer_of(&g1, vis, true);

        // The node at which `c`'s first receive is offered with two sources.
        let node = drive(&p, |offers, _g| {
            offers
                .iter()
                .position(|o| o.kind() == "send" && o.pos().index == 1)
                .map(|i| (i, Decision::Send))
        });
        let probed = probe_of(&p, node);
        let recv = probed
            .offers()
            .iter()
            .find(|o| o.kind() == "recv")
            .expect("c's first receive is enabled");
        assert_eq!(recv.sources().len(), 2, "inv's send and b2's first send");
        assert!(s.phi(&outer, probed.graph(), recv).unwrap());

        let witness = s
            .rf_options(recv)
            .into_iter()
            .find(|rf| {
                let extended = install_recv(cfg(), probed.graph().clone(), recv, *rf);
                s.follows(&outer, &extended).unwrap()
            })
            .expect("Φ said some source works");
        assert_eq!(
            witness.map(|e| e.thread),
            Some(inv),
            "Φ's witness is the invisible thread's send"
        );

        // `branch` is entered at *this* node, so the distinction is forced: a
        // whole-`Cover` call may reach `c`'s receive by a path on which only
        // one source exists, and then the witness and the taken source cannot
        // differ. Driving the node directly is what makes the test bite.
        let mut budget = Budget { remaining: 4096 };
        let g = found(s.branch(&outer, probed.graph(), recv, &mut budget).unwrap());
        let rs = recvs(&g, tid_of(&g, "c"));
        assert_eq!(rs.len(), 2, "c's two receives");
        assert_eq!(
            rs[0].1.map(|e| e.thread),
            Some(tid_of(&g, "b2")),
            "the installed source is the one the loop took, not Φ's witness"
        );
        assert_ne!(
            rs[0].1.map(|e| e.thread),
            witness.map(|e| e.thread),
            "the witness and the taken source must actually differ, or this proves nothing"
        );

        // And the same answer through the whole call, so the node above is not
        // an artefact of how it was reached.
        let whole = found(s.cover(&g1, true, ExecutionGraph::default()).unwrap());
        assert_eq!(
            recvs(&whole, tid_of(&whole, "c"))[0].1.map(|e| e.thread),
            Some(tid_of(&whole, "b2"))
        );
    }

    /// **Criterion 12's retry case**, stated on its own so it does not rest on
    /// Ex. restart alone: a seed that cannot be extended, and a rebuild from
    /// empty that succeeds. Both attempts are exercised in one `Cover` call,
    /// and the first is shown to fail by calling `spec_visit` on the seed
    /// directly.
    #[test]
    fn cover_retries_from_empty_when_the_seed_fails() {
        let vis = &["main", "c"];
        let impl_p = restart_impl();
        let spec_p = restart_spec();
        let s = search_for(&spec_p, vis, 512);

        // A seed that pins the wrong value.
        let seed = drive(&spec_p, |offers, _g| {
            let o = &offers[0];
            match o.kind() {
                "choice" => Some((0, Decision::Value(NondetValue::Choice(5)))),
                "send" => Some((0, Decision::Send)),
                other => panic!("unexpected {other}"),
            }
        });
        assert_eq!(choices(&seed, main_thread_id()), vec![5]);

        let g1 = complete_graph(&impl_p);
        let outer = outer_of(&g1, vis, true);
        let mut budget = Budget { remaining: 512 };
        assert!(
            matches!(
                s.spec_visit(&outer, seed.clone(), &mut budget).unwrap(),
                Cover::NoCover
            ),
            "the seed is a complete specification graph that does not match"
        );

        let g = found(s.cover(&g1, true, seed).unwrap());
        assert_eq!(choices(&g, main_thread_id()), vec![6]);
    }

    /// The search must try more than the first offer of the range. Here the
    /// first offer in probe order is outside Φ's range and a later one is
    /// inside it, so a search that looked only at `offers[0]` would report.
    ///
    /// This is the weaker of the two readings of criterion 12's backtracking
    /// bullet; the stronger one — a Φ-*passing* first offer that dead-ends —
    /// is discussed in the report.
    #[test]
    fn the_search_looks_past_the_first_offer() {
        let vis = &["a", "b", "c"];
        let p = rebuild_prog();

        // G₁: only `b` has sent, and `c` has read it.
        let g1 = drive(&p, |offers, g| {
            let b = tid_of(g, "b");
            if let Some(i) = offers
                .iter()
                .position(|o| o.kind() == "send" && o.pos().thread == b)
            {
                return Some((i, Decision::Send));
            }
            let i = offers.iter().position(|o| o.kind() == "recv")?;
            let src = offers[i].sources()[0];
            Some((i, Decision::Recv(Some(src))))
        });

        let s = search_for(&p, vis, 512);
        let outer = outer_of(&g1, vis, false);
        let probed = probe_of(&p, ExecutionGraph::default());
        let kinds: Vec<_> = probed.offers().iter().map(Offer::kind).collect();
        assert_eq!(kinds, vec!["send", "send"], "both senders are offered");

        let inside: Vec<bool> = probed
            .offers()
            .iter()
            .map(|o| s.phi(&outer, probed.graph(), o).unwrap())
            .collect();
        assert_eq!(
            inside,
            vec![false, true],
            "the first offer is outside the range and the second is inside it"
        );

        assert!(
            s.cover(&g1, false, ExecutionGraph::default())
                .unwrap()
                .is_found(),
            "the loop must reach the second offer"
        );
    }

    /// ⊥ is one of the source loop's options, not a fallback. The outer graph
    /// has the non-blocking receive reading **nothing** while a send it could
    /// have read is sitting in the graph, so the only cover reads ⊥.
    ///
    /// To break it: drop `may_read_nothing`'s `None` from `rf_options` — the
    /// receive then has no admissible option on the branch where the send is
    /// already installed, and `Cover` reports a violation that is not one.
    #[test]
    fn the_source_loop_includes_reading_nothing() {
        let vis = &["s", "c"];
        let p = may_read_nothing_prog();

        // G₁: install the send first, then have `c` read ⊥ anyway.
        let g1 = drive(&p, |offers, _g| {
            if let Some(i) = offers.iter().position(|o| o.kind() == "send") {
                return Some((i, Decision::Send));
            }
            let i = offers.iter().position(|o| o.kind() == "recv")?;
            assert!(
                !offers[i].sources().is_empty() && offers[i].may_read_nothing(),
                "the receive should have both a source and ⊥"
            );
            Some((i, Decision::Recv(None)))
        });

        let s = search_for(&p, vis, 512);
        let g = found(s.cover(&g1, true, ExecutionGraph::default()).unwrap());
        let rs = recvs(&g, tid_of(&g, "c"));
        assert_eq!(rs.len(), 1);
        assert_eq!(rs[0].1, None, "the cover must read nothing, as G₁ does");
    }

    /// **Criterion 13's backtracking case.** The first offer of the range
    /// passes Φ and dead-ends; a later one passes Φ and succeeds. So the offer
    /// loop — `ln:innerloop`, the draft's completeness mechanism — is what
    /// finds the cover, and a search that took the first Φ-passing offer would
    /// report a violation that is not there.
    ///
    /// The mechanism, which is what makes this case exist at all: installing a
    /// **receive** does not only add options. It consumes that receive's one
    /// chance to read, against the sources present *at that moment*, and
    /// forecloses every source a later send would have supplied. `alg.tex:865-867`
    /// says exactly this — "it does not say that an arbitrary offerable event
    /// begins such an order".
    ///
    /// Concretely, at `P₁` — the empty graph extended with `inv`'s send and
    /// re-probed — `c`'s first receive is offered with the single source
    /// `inv.send`. Reading it gives `Recv(7)`, and `Obs` records the value and
    /// not the sender, so it is a prefix of `G₁`'s `[Recv(7), Recv(5)]` and Φ
    /// passes. But `c`'s *second* receive can then only read `b2`'s first send
    /// (`7`) under FIFO, while `G₁` records `5` there, so every descendant
    /// dies. Installing `b2`'s send first gives `c`'s receive both sources, and
    /// the cover reads `b2`'s.
    ///
    /// To break it: `break` out of `spec_visit`'s offer loop after the first
    /// Φ-passing member — the final assertion then fails with `NoCover`. The
    /// two `branch` assertions above it are unaffected, which is the point:
    /// they establish that the two offers really do differ, so the last
    /// assertion is not vacuous.
    #[test]
    fn the_offer_loop_backtracks_past_a_phi_passing_dead_end() {
        let vis = &["b2", "c"];
        let p = provenance_prog();

        // G₁: both of `c`'s receives read `b2`.
        let g1 = drive(&p, |offers, g| {
            if let Some(i) = offers.iter().position(|o| o.kind() == "send") {
                return Some((i, Decision::Send));
            }
            let b2 = tid_of(g, "b2");
            let i = offers.iter().position(|o| o.kind() == "recv").unwrap();
            let src = *offers[i]
                .sources()
                .iter()
                .find(|e| e.thread == b2)
                .expect("b2 has a send available");
            Some((i, Decision::Recv(Some(src))))
        });

        let s = search_for(&p, vis, 4096);
        let outer = outer_of(&g1, vis, true);

        // `P₁`: the empty graph extended with `inv`'s send, re-probed.
        let (offers0, g0) = probe_of(&p, ExecutionGraph::default()).into_parts();
        let inv = {
            let b2 = tid_of(&g0, "b2");
            let c = tid_of(&g0, "c");
            let mut ts = g0.thread_ids();
            ts.retain(|t| *t != main_thread_id() && *t != b2 && *t != c);
            assert_eq!(ts.len(), 1, "exactly one invisible sender");
            *ts.iter().next().unwrap()
        };
        let i = offers0
            .iter()
            .position(|o| o.pos().thread == inv)
            .expect("`inv`'s send is offered at the empty graph");
        assert_eq!(offers0[i].kind(), "send");
        // `P₁` is the probe **output** — the shape a `Cover` seed has, since
        // `Cover::Found` carries `probed.graph()`. That matters here and is
        // not incidental: the installed graph it came from lacks `inv`'s `End`
        // and is offered back in the order `["send", "recv"]`, while `P₁`
        // itself is offered in the order `["recv", "send"]`. The dead-ending
        // offer is first only at `P₁`. See the report's observation on offer
        // order.
        let node = probe_of(&p, install(cfg(), g0, &offers0[i]))
            .graph()
            .clone();
        let p1 = probe_of(&p, node.clone());

        // The order this test relies on, asserted rather than assumed.
        let kinds: Vec<_> = p1.offers().iter().map(Offer::kind).collect();
        assert_eq!(
            kinds,
            vec!["recv", "send"],
            "the dead-ending offer comes first in probe order at P₁"
        );

        let recv = p1.offers().iter().find(|o| o.kind() == "recv").unwrap();
        let send = p1.offers().iter().find(|o| o.kind() == "send").unwrap();
        assert_eq!(
            recv.sources().len(),
            1,
            "only `inv`'s send is available to `c`'s first receive here"
        );
        assert_eq!(
            recv.sources()[0].thread,
            inv,
            "and the one source is `inv`'s send"
        );

        // Both are inside Φ's range, so both are backtrack points.
        assert!(
            s.phi(&outer, p1.graph(), recv).unwrap(),
            "reading `inv`'s 7 is a prefix of G₁'s [Recv(7), Recv(5)]"
        );
        assert!(
            s.phi(&outer, p1.graph(), send).unwrap(),
            "`b2`'s first send carries 7, which is what G₁ records at that \
             position of `b2`'s row"
        );

        // The first dead-ends and the second succeeds.
        let mut budget = Budget { remaining: 4096 };
        assert!(
            matches!(
                s.branch(&outer, p1.graph(), recv, &mut budget).unwrap(),
                Cover::NoCover
            ),
            "taking the receive first forecloses the source the cover needs"
        );
        let mut budget = Budget { remaining: 4096 };
        assert!(
            s.branch(&outer, p1.graph(), send, &mut budget)
                .unwrap()
                .is_found(),
            "taking the send first leaves both sources available"
        );

        // And the loop is what gets there.
        let mut budget = Budget { remaining: 4096 };
        assert!(
            matches!(
                s.spec_visit(&outer, node.clone(), &mut budget).unwrap(),
                Cover::Found(_)
            ),
            "the offer loop must go past the first Φ-passing offer"
        );

        // The same through a whole `Cover` call taking `P₁` as its seed, which
        // is how a node of this shape reaches the search in practice.
        assert!(
            s.cover(&g1, true, node).unwrap().is_found(),
            "and the seeded call must find it too"
        );
    }

    /// **Criterion 5, round 3 M1.** `done` treats `Probed::complete()` as the
    /// emptiness test `next_Spec(G) = ∅`, but it is the conjunction of that
    /// with `is_complete(graph)`. The two are not the same condition, and the
    /// divergence would manufacture ⊥.
    ///
    /// This walks every node of a drive of each program in the suite and
    /// records whether the two ever disagree.
    #[test]
    fn probed_complete_agrees_with_the_emptiness_test_on_these_programs() {
        let programs: Vec<Prog> = vec![
            relay_impl(),
            relay_spec(),
            sched_prog(),
            restart_impl(),
            restart_spec(),
            rebuild_prog(),
            blocking_impl(),
            blocking_spec(),
            provenance_prog(),
            two_sends(),
        ];
        for p in &programs {
            let mut graph = ExecutionGraph::default();
            for _ in 0..64 {
                let probed = probe_of(p, graph);
                assert_eq!(
                    probed.offers().is_empty(),
                    probed.complete().is_some(),
                    "`Probed::complete()` diverged from the emptiness test at:\n{}",
                    probed.graph()
                );
                let (offers, g) = probed.into_parts();
                if offers.is_empty() {
                    break;
                }
                let (i, d) = greedy(&offers, &g).unwrap();
                graph = match d {
                    Decision::Send => install(cfg(), g, &offers[i]),
                    Decision::Recv(rf) => install_recv(cfg(), g, &offers[i], rf),
                    Decision::Value(v) => install_nondet(cfg(), g, &offers[i], v),
                };
            }
        }
    }
}
