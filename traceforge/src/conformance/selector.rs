//! The two selector knobs of `P4-SELECTOR` (`IMPL-PLAN-algorithms.md` §3, §6).
//!
//! **Knob A, [`Selector`]** — the Must selector: which runnable task the engine
//! runs next. The paper's convention (`alg.tex` §8.5) is that `e ← next_P(G)`
//! takes the element a *selector, a fixed function of the graph* picks, and
//! that Must's completeness holds for every such selector. TruSt's proof
//! actually assumes a **fixed total order on events respecting program order**
//! (backlog A25), so every variant here is one: an order on pairs
//! `(orig(t), i)` with `orig(t)` the thread's *origination vector* — the
//! `TCreate` event indices from `main` down to `t` — which, unlike a `TaskId`
//! (assigned per execution) or a `ThreadId` (numbered by insertion order,
//! which the selector itself influences under nested spawns), is a function
//! of the graph and stable across selectors, runs and revisits.
//!
//! The selector is consulted only by a conformance run or a probe
//! (`Must::next_task`'s predicate `conf.is_some() || probe.is_some()`); plain
//! `verify` keeps today's `schedule_policy` path untouched. A probe always
//! runs under [`Selector::Ltr`] — `prober::probe_from` forces it — so that the
//! inner search's recorded offer order does not depend on the outer run's
//! choice.
//!
//! **Knob B, [`InnerOrder`]** — the inner search's offer order: how
//! `Search::spec_visit` orders the offers of a probe, the values of a nondet
//! and the sources of a receive. It permutes and never discards, so by
//! `lem:coverexact` it changes the work and the first report, never the
//! answer (unlimited budget). It travels on `ConfConfig`, not on the engine
//! `Config`, so no probe or derived run can see it.
//!
//! **Cost, recorded in A25.** Origination order coincides with `TaskId` order
//! when `main` spawns every thread; on nested-spawn programs the conformance
//! default (`Ltr` over origination vectors) and the probe's recorded order
//! both differ from the engine's `TaskId`-order `LTR`.

use serde::{Deserialize, Serialize};

use crate::conformance::probe::{NondetValue, Offer};
use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::runtime::task::TaskId;
use crate::thread::ThreadId;

/// Knob A: the Must selector of a conformance run.
///
/// Fieldless, so it is a pure function of the graph by construction: no
/// state, no rng. Each variant is a fixed total order on events respecting
/// program order (see the module doc and `P4-SELECTOR` S5).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub enum Selector {
    /// Ascending lexicographic order on origination vectors, then ascending
    /// index. Today's left-to-right order wherever `main` spawns every thread.
    #[default]
    Ltr,
    /// The candidate thread with the fewest events in the paper's sense
    /// (sends, receives, tosses, choices, assertion failures), ties by
    /// ascending origination vector. A fixed order on the paper's events
    /// `⟨orig, n⟩`; on engine labels it is not one (S5), which criterion 5
    /// checks empirically.
    FewestEvents,
    /// Descending lexicographic order on origination vectors, then ascending
    /// index: the most recently spawned candidate first.
    Reverse,
}

impl Selector {
    /// Pick one task from `candidates`, which the caller has already filtered
    /// by `is_thread_runnable`. `None` iff `candidates` is empty.
    ///
    /// A function of `graph` and the candidate set only: every key below is
    /// read from the graph through the task's thread.
    pub(crate) fn pick(self, graph: &ExecutionGraph, candidates: &[TaskId]) -> Option<TaskId> {
        let orig = |t: TaskId| {
            graph
                .get_thread_tclab(graph.to_thread_id(t))
                .origination_vec()
        };
        match self {
            Selector::Ltr => candidates.iter().copied().min_by_key(|&t| orig(t)),
            Selector::Reverse => candidates.iter().copied().max_by_key(|&t| orig(t)),
            Selector::FewestEvents => candidates
                .iter()
                .copied()
                .min_by_key(|&t| (paper_events(graph, graph.to_thread_id(t)), orig(t))),
        }
    }
}

/// The number of events of thread `t` in the paper's sense: its sends,
/// receives, tosses, choices and assertion failures. Bookkeeping labels —
/// `Begin`, `End`, `TCreate`, `TJoin`, `Unique`, the other `Block`s — are not
/// events of the paper's language (criterion 2).
pub(crate) fn paper_events(graph: &ExecutionGraph, t: ThreadId) -> usize {
    (0..graph.thread_size(t) as u32)
        .filter(|&i| match graph.label(Event::new(t, i)) {
            LabelEnum::SendMsg(_)
            | LabelEnum::RecvMsg(_)
            | LabelEnum::CToss(_)
            | LabelEnum::Choice(_) => true,
            LabelEnum::Block(b) => matches!(b.btype(), BlockType::Assert),
            _ => false,
        })
        .count()
}

/// Knob B: the order in which the inner search tries the offers of a probe,
/// the values of a nondet and the sources of a receive.
///
/// Every policy is a permutation of its input on each of the three sequences
/// (criterion 8): nothing is ever dropped.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum InnerOrder {
    /// The order recorded today: offers as the probe parked them, a nondet's
    /// values ascending, a receive's sources as enumerated then ⊥.
    #[default]
    Recorded,
    /// All three sequences reversed.
    Reverse,
    /// Nondet values: the listed values first, in the listed order, then the
    /// remaining values in recorded order; listed values that do not occur are
    /// ignored. A `CToss` value `false`/`true` is matched as `0`/`1`. Offers
    /// and sources unchanged.
    Pinned(Vec<usize>),
    /// Offers whose parked label is a send first, stable among themselves,
    /// then the rest. Values and sources unchanged.
    SendsFirst,
}

impl InnerOrder {
    /// Order a probe's offers.
    pub(crate) fn offers<'a>(&self, offers: &'a [Offer]) -> Vec<&'a Offer> {
        let mut out: Vec<&'a Offer> = offers.iter().collect();
        match self {
            InnerOrder::Recorded | InnerOrder::Pinned(_) => {}
            InnerOrder::Reverse => out.reverse(),
            InnerOrder::SendsFirst => {
                // `sort_by_key` is stable, so sends keep their recorded order
                // among themselves and so do the rest.
                out.sort_by_key(|o| !matches!(o.label(), LabelEnum::SendMsg(_)));
            }
        }
        out
    }

    /// Order a nondet offer's values.
    pub(crate) fn values(&self, mut values: Vec<NondetValue>) -> Vec<NondetValue> {
        match self {
            InnerOrder::Recorded | InnerOrder::SendsFirst => {}
            InnerOrder::Reverse => values.reverse(),
            InnerOrder::Pinned(pins) => {
                let mut out = Vec::with_capacity(values.len());
                for &p in pins {
                    if let Some(i) = values.iter().position(|v| as_usize(*v) == p) {
                        out.push(values.remove(i));
                    }
                }
                out.extend(values);
                values = out;
            }
        }
        values
    }

    /// Order a receive offer's sources, ⊥ (`None`) included.
    pub(crate) fn sources(&self, mut sources: Vec<Option<Event>>) -> Vec<Option<Event>> {
        match self {
            InnerOrder::Recorded | InnerOrder::Pinned(_) | InnerOrder::SendsFirst => {}
            InnerOrder::Reverse => sources.reverse(),
        }
        sources
    }
}

/// The `usize` a pin names: a `Choice`'s value, or `0`/`1` for a toss.
fn as_usize(v: NondetValue) -> usize {
    match v {
        NondetValue::Toss(b) => usize::from(b),
        NondetValue::Choice(n) => n,
    }
}
