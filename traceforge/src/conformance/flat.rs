//! `FlatCover` — `flat.tex` §9's coverage engine for the **completion
//! question** (`P4-FLAT` F2–F4; `alg:flat`).
//!
//! Given a complete implementation graph `G₁`, decide whether some graph of a
//! communication-flat specification covers it, returning that graph or ⊥. The
//! engine branches on **values** (`ln:fnd`) and on **sources** (`ln:fsrc`) and
//! nowhere else: saturation installs sends and choices in a fixed least-thread
//! order, every receive of a covering witness sits at a receive position of
//! `sig(G₁)` (flatness), and those positions are resolved one slot at a time in
//! a canonical order extending `ord(G₁)`. No installation order is explored and
//! no revisit is performed. `thm:flat` makes it exact when the specification is
//! communication-flat; eligibility is decided before the outer run
//! (`precheck.rs`), and the adapter in the complete-first and gated completion
//! sinks substitutes it for the directed sweep (`CompletionCover::Flat`).
//!
//! **Thread.** Every call runs on its own scoped 32 MiB thread, as the sweeps
//! do: the prober sets and clears the thread's current `Must`, which the
//! failure path reads, so it never runs on the outer run's thread. A panic on
//! the flat thread is re-raised on the caller's with `resume_unwind`.
//!
//! **Defence in depth** (`P4-FLAT` F4). Every offered send or receive is
//! checked visible: an offered event lies in a consistent partial graph, so
//! an invisible one proves the specification is not communication-flat, and
//! the run panics naming it rather than answering without `thm:flat`'s
//! guarantee. (This guarantees no false witness and no false refusal; the
//! public path refuses such a specification before the outer run.)

use std::sync::Arc;
use std::time::Instant;

use crate::conformance::morphism::{
    follows, matches, statuses, statuses_agree, vo, CompleteExecution,
};
use crate::conformance::obs::{resolve_visible, wobs, ObsError, Wobs};
use crate::conformance::probe::Offer;
use crate::conformance::prober::{install, install_nondet, install_recv, probe_from, Probed};
use crate::conformance::report::FlatCounters;
use crate::conformance::search::spec_assertion;
use crate::conformance::sig::VPosMap;
use crate::conformance::witness::FlatWitness;
use crate::event::Event;
use crate::event_label::{Annotation, LabelEnum, Visibility};
use crate::exec_graph::ExecutionGraph;
use crate::thread::ThreadId;
use crate::Config;

/// What a `FlatCover` run needs of the specification side (`P4-FLAT` F2):
/// the stripped `Config` (no callbacks, no dot/trace files, unbounded — as
/// `cfirst::sweep` strips it), the program and the declared names.
#[derive(Clone)]
pub(crate) struct FlatCtx {
    config: Config,
    spec: Arc<dyn Fn() + Send + Sync>,
    visible: Vec<String>,
}

impl FlatCtx {
    pub(crate) fn new(
        config: &Config,
        visible: &[String],
        spec: &Arc<dyn Fn() + Send + Sync>,
    ) -> Self {
        let mut config = config.clone();
        config.max_iterations = None;
        config.callbacks = Arc::new(std::sync::Mutex::new(Vec::new()));
        config.dot_file = None;
        config.trace_file = None;
        config.error_trace_file = None;
        config.turmoil_trace_file = None;
        Self {
            config,
            spec: Arc::clone(spec),
            visible: visible.to_vec(),
        }
    }
}

/// One slot of the canonical order: a receive position of `sig(G₁)`, as the
/// declared name of its thread and its visible index.
#[derive(Clone, Debug)]
struct Slot {
    thread: String,
    #[allow(dead_code)]
    index: usize,
}

/// The outer side of the search, fixed for one call.
struct Outer<'a> {
    g1: &'a ExecutionGraph,
    wobs: Wobs,
    statuses: std::collections::BTreeMap<String, crate::conformance::morphism::Status>,
    slots: Vec<Slot>,
}

/// `P4-FLAT` F4: admit a `FlatCover` witness to `W` through the cache's one
/// mutating method (`P4-APPARATUS` criterion 15's structural pin). The
/// provenance is the [`FlatWitness`] type invariant (its fields are private,
/// its only constructor takes a `Probed` whose `complete()` was `Some` on the
/// flat thread): consistent, complete, no offer left ⇒ in `Graphs(Spec)` by
/// `thm:flat`. `try_finished` re-checks only the spawned threads' half of
/// completeness; `main`'s half (`morphism.rs`, F33) is the invariant's, so
/// this is a re-entry into `admit_from_sweep`'s contract, not a fresh
/// assumption.
pub(crate) fn admit(
    cache: &mut crate::conformance::witness::WitnessCache,
    w: FlatWitness,
) -> Result<bool, ObsError> {
    let exec = CompleteExecution::try_finished(w.graph())
        .expect("conformance: a FlatWitness holds a complete graph by construction");
    cache.admit_from_sweep(exec)
}

/// `FlatCover(G₁)` on its own thread: the witness and this call's counters
/// (`calls = 1`). `Err` is a §8 input error from `wobs`.
pub(crate) fn flat_cover(
    ctx: &FlatCtx,
    g1: &ExecutionGraph,
) -> Result<(Option<FlatWitness>, FlatCounters), ObsError> {
    let ctx = ctx.clone();
    let g1 = g1.clone();
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("conformance-flat-cover".to_owned())
            .stack_size(32 * 1024 * 1024)
            .spawn_scoped(s, move || flat_cover_here(&ctx, &g1))
            .expect("conformance: the FlatCover thread could not be spawned");
        match handle.join() {
            Ok(r) => r,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

fn flat_cover_here(
    ctx: &FlatCtx,
    g1: &ExecutionGraph,
) -> Result<(Option<FlatWitness>, FlatCounters), ObsError> {
    let started = Instant::now();
    let g1_wobs = wobs(g1, &ctx.visible)?;
    let exec = CompleteExecution::assume_finished_at_gate(g1);
    let g1_statuses = statuses(exec, &g1_wobs, &ctx.visible)?;
    let slots = canonical_order(g1, &g1_wobs, &ctx.visible);
    let outer = Outer {
        g1,
        wobs: g1_wobs,
        statuses: g1_statuses,
        slots,
    };
    let mut counters = FlatCounters {
        calls: 1,
        ..FlatCounters::default()
    };
    let root = ExecutionGraph::default();
    let found = visit(ctx, &outer, root, 0, 1, &mut counters)?;
    if found.is_some() {
        counters.witnesses = 1;
    }
    counters.wall_time_ms = started.elapsed().as_millis();
    Ok((found, counters))
}

/// `P4-FLAT` F3: the receive positions of `sig(G₁)`, totally ordered by a
/// topological sort of `ord(G₁)` restricted to them (`vo` pairwise — `sig::ord`
/// is the same relation), ties broken by `(declared name, index)`.
fn canonical_order(g1: &ExecutionGraph, g1_wobs: &Wobs, visible: &[String]) -> Vec<Slot> {
    let vpos = VPosMap::of(g1, g1_wobs, visible);
    let mut recvs: Vec<(Event, Slot)> = vpos
        .events()
        .filter(|(e, _)| matches!(g1.label(*e), LabelEnum::RecvMsg(_)))
        .map(|(e, p)| {
            (
                e,
                Slot {
                    thread: p.thread.clone(),
                    index: p.index,
                },
            )
        })
        .collect();
    recvs.sort_by(|a, b| (&a.1.thread, a.1.index).cmp(&(&b.1.thread, b.1.index)));
    let mut out: Vec<Slot> = Vec::with_capacity(recvs.len());
    let mut placed = vec![false; recvs.len()];
    while out.len() < recvs.len() {
        // The least unplaced receive (by name, index) with no unplaced
        // `vo`-predecessor; `vo` is a strict partial order, so one exists.
        let next = (0..recvs.len())
            .filter(|&i| !placed[i])
            .find(|&i| {
                (0..recvs.len())
                    .filter(|&j| !placed[j] && j != i)
                    .all(|j| !vo(g1, recvs[j].0, recvs[i].0))
            })
            .expect("conformance: FlatCover's canonical order found a cycle in vo");
        placed[next] = true;
        out.push(recvs[next].1.clone());
    }
    out
}

fn offer_is_visible(graph: &ExecutionGraph, offer: &Offer, visible: &[String]) -> bool {
    let annotation = match offer.label() {
        LabelEnum::SendMsg(l) => l.annotation(),
        LabelEnum::RecvMsg(l) => l.annotation(),
        _ => return true,
    };
    let pos = offer.pos();
    let named = graph
        .get_thread_tclab(pos.thread)
        .name()
        .as_deref()
        .is_some_and(|n| visible.iter().any(|v| v == n));
    named && annotation != Annotation::Explicit(Visibility::Invisible)
}

fn follows_outer(
    ctx: &FlatCtx,
    outer: &Outer<'_>,
    graph: &ExecutionGraph,
) -> Result<bool, ObsError> {
    let w = wobs(graph, &ctx.visible)?;
    Ok(follows(graph, outer.g1, &w, &outer.wobs, &ctx.visible))
}

/// `FlatVisit(G₁, G, i)` (`alg:flat`), `i` zero-based here.
fn visit(
    ctx: &FlatCtx,
    outer: &Outer<'_>,
    graph: ExecutionGraph,
    i: usize,
    depth: usize,
    c: &mut FlatCounters,
) -> Result<Option<FlatWitness>, ObsError> {
    c.visits += 1;
    c.max_depth = c.max_depth.max(depth);
    let spec = Arc::clone(&ctx.spec);
    let probed: Probed = probe_from(ctx.config.clone(), graph, move || spec());
    if let Some(e) = spec_assertion(probed.graph()) {
        panic!(
            "conformance: FlatCover reached a specification assertion failure, which the \
             precheck rules out: {e}"
        );
    }
    for offer in probed.offers() {
        if !offer_is_visible(probed.graph(), offer, &ctx.visible) {
            panic!(
                "conformance: FlatCover: the specification is not communication-flat — its \
                 thread {} offers an invisible {} at {} (P4-FLAT F4; eligibility is decided \
                 by the precheck, which this run skipped)",
                offer.pos().thread,
                offer.kind(),
                offer.pos()
            );
        }
    }

    // `ln:fsat`: the least-thread non-receive offer.
    let nextsat = probed
        .offers()
        .iter()
        .filter(|o| !matches!(o.label(), LabelEnum::RecvMsg(_)))
        .min_by_key(|o| o.pos().thread);
    if let Some(offer) = nextsat {
        return match offer.label() {
            LabelEnum::CToss(_) | LabelEnum::Choice(_) => {
                // `ln:fnd`: every value, in the recorded order.
                for v in offer.nondet_values() {
                    c.nd_branches += 1;
                    let g = install_nondet(ctx.config.clone(), probed.graph().clone(), offer, v);
                    if let Some(w) = visit(ctx, outer, g, i, depth + 1, c)? {
                        return Ok(Some(w));
                    }
                }
                Ok(None)
            }
            LabelEnum::SendMsg(_) => {
                // `ln:fsend`: install, test following, the branch dies on failure.
                let g = install(ctx.config.clone(), probed.graph().clone(), offer);
                if follows_outer(ctx, outer, &g)? {
                    visit(ctx, outer, g, i, depth + 1, c)
                } else {
                    c.send_kills += 1;
                    Ok(None)
                }
            }
            other => panic!(
                "conformance: FlatCover: a probe offered a {} label, which the prober's \
                 offers never carry",
                other
            ),
        };
    }

    // `e = ⊥`: every thread stands at a receive or at nothing.
    if i < outer.slots.len() {
        // `ln:fslot`: the thread of `r_i` must stand at a receive.
        let slot = &outer.slots[i];
        let tid: Option<ThreadId> = resolve_visible(probed.graph(), &slot.thread)?;
        let offer = tid.and_then(|t| {
            probed
                .offers()
                .iter()
                .find(|o| o.pos().thread == t && matches!(o.label(), LabelEnum::RecvMsg(_)))
        });
        let Some(offer) = offer else {
            c.slot_kills += 1;
            return Ok(None);
        };
        // `ln:fsrc`: every consistent source in the recorded order, then ⊥.
        let mut options: Vec<Option<Event>> = offer.sources().iter().map(|s| Some(*s)).collect();
        if offer.may_read_nothing() {
            options.push(None);
        }
        let mut passed = false;
        for rf in options {
            c.source_branches += 1;
            let g = install_recv(ctx.config.clone(), probed.graph().clone(), offer, rf);
            if !follows_outer(ctx, outer, &g)? {
                continue;
            }
            passed = true;
            c.source_recursions += 1;
            if let Some(w) = visit(ctx, outer, g, i + 1, depth + 1, c)? {
                return Ok(Some(w));
            }
        }
        if !passed {
            c.source_kills += 1;
        }
        return Ok(None);
    }

    // `ln:fdone`: `nextp = ∅`, matches, and the statuses agree.
    if !probed.offers().is_empty() {
        c.done_kills += 1;
        return Ok(None);
    }
    let w = wobs(probed.graph(), &ctx.visible)?;
    if !matches(probed.graph(), outer.g1, &w, &outer.wobs, &ctx.visible) {
        c.done_kills += 1;
        return Ok(None);
    }
    let Some(exec) = probed.complete() else {
        c.done_kills += 1;
        return Ok(None);
    };
    let spec_statuses = statuses(exec, &w, &ctx.visible)?;
    if !statuses_agree(&spec_statuses, &outer.statuses) {
        c.done_kills += 1;
        return Ok(None);
    }
    match FlatWitness::of(&probed, &ctx.visible)? {
        Some(witness) => Ok(Some(witness)),
        None => {
            c.done_kills += 1;
            Ok(None)
        }
    }
}
