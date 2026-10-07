//! The gate's state: what conformance carries on the outer `Must`.
//!
//! `conf-plan.md` §3 item 1, §4.1–§4.4. One [`ConfCtx`] lives on the outer
//! `Must` for the duration of a conformance run. It owns three things: the
//! specification program (consulted through a probe worker), the carried `H`,
//! and the report sink.
//!
//! Everything here is inert unless `Must::conf` is `Some`, which it is only
//! for a run that asked for conformance.

use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::Arc;
use std::thread::JoinHandle;

use crate::conformance::canon::CanonicalGraph;
use crate::conformance::obs::{resolve_visible, ObsError};
use crate::conformance::report::{ConfCounters, CoverCounters, ReportGate, SearchEnd};
use crate::conformance::search::{Cover, Search, SearchOpts};
use crate::conformance::selector::paper_events;
use crate::conformance::selector::InnerOrder;
use crate::event::Event;
use crate::event_label::{AsEventLabel, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::must::MustState;
use crate::Config;

/// Which of conformance's engines this context belongs to (four until Part
/// 3 — outer, precheck, triage and the test-only oracle; [`ConfMode::Enumerate`]
/// is the stateful checker's fifth, `P4-STATEFUL` T2).
///
/// §9 names three — "the outer conf run, the probe `Must`, and the err-freedom
/// precheck" — and S5 adds triage as a fourth `Must` that is also *not* the
/// probe. The probe has its own field on `Must` (`probe: Option<ProbeCtx>`);
/// every other engine carries a `ConfCtx`, and until S5 they could not be told
/// apart, which is why `reject_out_of_scope` had only two answers for three
/// engines (blocked item **E**).
///
/// Only [`ConfMode::Outer`] has a `Cover` gate ([`ConfMode::Enumerate`] runs a
/// completion sink inside `gate`, nothing more). The gate-disabled modes exist so that
/// `conf.is_some()` is true — which is what arms §9's handler-entry guards and
/// keeps `store_replay_information`'s exemption (`store_replay_information`'s conformance early return) in force —
/// without a probe worker or a `Cover` call behind it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ConfMode {
    /// The run that explores the implementation and calls the gate.
    Outer,
    /// §5.4's specification err-freedom run. Gate off, guards on.
    Precheck,
    /// §7.3's per-report completion run. Gate off, guards on.
    Triage,
    /// §11.6's oracle enumeration run (test-only). Gate off, guards on, **and
    /// visible assertion failures do not prune** — see
    /// [`ConfCtx::report_visible_error`]. Its production twin is
    /// [`ConfMode::Enumerate`].
    ///
    /// S6 criteria round 3, B1. The oracle must enumerate `Graphs(P)`
    /// exhaustively, and an ungated context is *not* automatically prune-free:
    /// `report_visible_error` needs only `conf.is_some()`, so a declared
    /// visible thread's failed assertion would prune the oracle's own run,
    /// truncate every other thread's row and under-approximate `vis(P)` — the
    /// permissive direction on the specification side.
    ///
    /// **This mode never inhabits a reporting engine** (the reporting twin is
    /// [`ConfMode::Enumerate`], `P4-STATEFUL`). [`ConfCtx::new`] is
    /// the only constructor that builds a [`ProbeWorker`], and it hard-codes
    /// `Outer` rather than taking a mode; [`ConfCtx::gate_disabled`] is the
    /// only other constructor and sets `worker: None`. So no mirror assert is
    /// needed to keep `Collect` out of the gate's path.
    Collect,
    /// `P4-STATEFUL` T2: the stateful checker's enumeration run — `Collect`'s
    /// no-prune behaviour, a production engine label, and a completion sink
    /// (T3) instead of a `Vec` of every graph.
    Enumerate,
    /// `P4-CFIRST` C1: the complete-first checker's outer run — `Enumerate`'s
    /// behaviour under its own label, and the only mode that may carry the
    /// early-error cut (C5).
    CFirstOuter,
    /// `P4-CFIRST` C2: one sweep of the specification inside the complete-first
    /// checker's `Covered` — `Enumerate`'s behaviour under its own label.
    CFirstSweep,
    /// `P4-GATED` G1: the gated checker's outer run — an enumerating run with a
    /// completion sink *and* a gate sink at the growing gates, under its own
    /// label; the only mode whose stop ends the run at `try_revisit`'s head.
    GatedOuter,
    /// `P4-GATED` G4: one sweep of the specification inside the gated
    /// checker's `Gate` or `Covered`, under its own label.
    GatedSweep,
}

impl ConfMode {
    /// The name this engine uses in a §9 rejection.
    pub(crate) fn engine_label(self) -> &'static str {
        match self {
            ConfMode::Outer => "conformance",
            ConfMode::Precheck => "precheck",
            ConfMode::Triage => "triage",
            ConfMode::Collect => "oracle",
            ConfMode::Enumerate => "stateful",
            ConfMode::CFirstOuter => "complete-first",
            ConfMode::CFirstSweep => "complete-first sweep",
            ConfMode::GatedOuter => "gated",
            ConfMode::GatedSweep => "gated sweep",
        }
    }

    /// `P4-CFIRST` C1: the production enumerating modes — never prune (unless
    /// the cut is on, C5), take a completion sink, make no `Cover` call.
    pub(crate) fn enumerates(self) -> bool {
        matches!(
            self,
            ConfMode::Enumerate
                | ConfMode::CFirstOuter
                | ConfMode::CFirstSweep
                | ConfMode::GatedOuter
                | ConfMode::GatedSweep
        )
    }
}

/// What a completion sink tells the `Enumerate` run to do next (`P4-STATEFUL`
/// T3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SinkVerdict {
    Continue,
    /// Request the run to stop at this completion (`stop_at_first_report`).
    Stop,
}

/// `P4-STATEFUL` T3: a per-completion hook, called with the completed graph
/// and the live `MustState` at `Gate::Completion`.
pub(crate) type CompletionSink = Box<dyn FnMut(&ExecutionGraph, &MustState) -> SinkVerdict>;

/// `P4-GATED` G1: which kind of worklist pop a `RevisitApply` gate follows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RevisitKind {
    /// A receive re-installed with an alternative source (the paper's sibling
    /// `GStep(e, SetRF(G, e, s), M, c)` — `e` the receive).
    Forward,
    /// A send re-installed at a revisited receive (`ln:greset` — `e` the send).
    Backward,
}

/// `P4-GATED` G1: what a growing gate knows about the event it follows.
#[derive(Clone, Debug)]
pub(crate) struct GateAt {
    /// The installed position: the fresh send or receive, or the popped
    /// receive at `RevisitApply`.
    pub(crate) at: Event,
    /// `Some` at `RevisitApply`, `None` at the fresh gates.
    pub(crate) revisit: Option<RevisitKind>,
    /// At `RevisitApply`, the receive's new source (`None` for an inbox
    /// placement, which §9 keeps out of scope).
    pub(crate) source: Option<Event>,
    /// At a backward `RevisitApply`, a clone of the **outgoing** state's
    /// carried pair (the state `backward_revisit` just pushed).
    pub(crate) outgoing_carry: Option<crate::conformance::gated::Carry>,
}

/// `P4-GATED` G1: what the gate sink tells the run to do next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GateVerdict {
    Continue,
    /// First-failure mode: report the gated partial graph at this gate and
    /// stop the whole search. A prune, with the report pushed first.
    Report,
    /// A gate-sweep abort: stop the whole search with no report. A prune.
    Stop,
}

/// `P4-GATED` G1: a per-gate hook, called at `FreshSend`, `FreshRecv` and
/// `RevisitApply` with the site, the graph and the live `MustState`.
pub(crate) type GateSink =
    Box<dyn FnMut(Gate, &GateAt, &ExecutionGraph, &MustState) -> GateVerdict>;

/// Which of §4.1's four gates fired.
///
/// Recorded on every report because it is the first thing anyone debugging a
/// conformance failure wants, and because the completion gate is the only one
/// that may pass `outer_complete = true` — a report naming a different gate
/// alongside the complete regime is a bug in this file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Gate {
    /// Tail of `handle_send`, after `calc_revisits` *and* `register_send`.
    FreshSend,
    /// `visit_rfs`, after the canonical rf or ⊥ is installed.
    FreshRecv,
    /// `try_revisit`, after the popped alternative has been applied.
    RevisitApply,
    /// `complete_execution`, before `check_blocked`.
    Completion,
}

impl Gate {
    /// §5.5, as ruled by the owner on 2026-09-12: the completeness flag is
    /// **positional**, not a predicate over the graph.
    ///
    /// The draft identified it with `next_Impl(G₁) = ∅`; that is false at a
    /// reachable gate — one firing on the program's last event, where no
    /// further implementation event exists but the execution is still running.
    /// Reaching `complete_execution` *is* the condition "no thread can take
    /// another step", so the site carries the fact and nothing derives it.
    ///
    /// It stays true for a **blocked** ending as well as a completed one:
    /// `Status::Blocked` is a value (M3) is defined on, and equating
    /// completeness with `AllThreadsCompleted` would skip the statuses
    /// conjunct for every deadlocked execution.
    fn outer_complete(self) -> bool {
        matches!(self, Gate::Completion)
    }
}

/// Why a report was recorded.
#[derive(Clone, Debug)]
pub(crate) enum ReportKind {
    /// The draft's ⊥: no specification graph covers this implementation
    /// graph. `Cover` established it; the search did not merely run out of
    /// room.
    NoCover,
    /// §4.4: a **visible** thread failed an assertion. The theorem speaks
    /// about visible behaviour, so this is a conformance report; an invisible
    /// thread's failed assertion is a diagnostic and never reaches here.
    VisibleError { thread: String, pos: Event },
}

/// One recorded conformance failure.
///
/// **This is the minimal sink the owner ruled for on 2026-09-12**, and the
/// ruling came with a boundary: it records enough to identify the occasion —
/// which gate fired, where the implementation graph was, which failure — and
/// nothing else. Formatting, files, triage, deduplication, ranking,
/// minimisation and any differential harness are §7 and belong to S5, which
/// builds on this type and may replace it.
///
/// The property that made the ruling the right one: a test can observe a
/// report without anything being rendered.
///
/// `Debug` is written out rather than derived: `MustState` has none, and
/// deriving one for it would print a whole execution graph twice over at every
/// `{:?}`.
#[derive(Clone)]
pub(crate) struct Report {
    /// Which of §4.1's gates fired — `None` for a `VisibleError`, which is
    /// not a gate firing at all and can happen at any point in an execution.
    ///
    /// This was `Gate`, hard-coded to `Completion` for the visible-error case
    /// (developer's gate-3 report, F-E). That made the field wrong for every
    /// §4.4 report, in a struct whose own doc says naming the wrong gate is a
    /// bug — and criterion 13 lists "which gate fired" as one of three things
    /// the minimal sink must record, so a wrong value there is worse than an
    /// absent one.
    pub(crate) gate: Option<Gate>,
    pub(crate) kind: ReportKind,
    /// The implementation graph's size when the gate fired — enough to tell
    /// two reports from the same run apart without holding a graph per
    /// report.
    pub(crate) events: usize,
    /// **The in-memory clone captured at report time** (§7.3, criterion 3).
    ///
    /// S4's `Report` deliberately did not hold one; capturing it is S5's, and
    /// it is compatible with S4's criterion 13, which bounded the sink's
    /// *responsibilities* — no formatting, files, triage, dedup, ranking,
    /// minimisation — and said in terms that S5 "builds the reporting product
    /// on it and may replace the type".
    ///
    /// A clone, not a serialization: §7.3 chose the in-memory graph *because*
    /// the serde round-trip loses predicates but for `recover_lost_data`.
    ///
    /// **The `recvs` index is stale on a `FreshRecv` capture**, and the
    /// argument that this is harmless is pinned in
    /// [`crate::conformance::triage`] rather than left to be re-derived.
    pub(crate) graph: ExecutionGraph,
    /// §7.1's serialized half, **built here rather than retained as state**.
    ///
    /// The first version of this held a `MustState` clone alongside `graph`
    /// and serialized it later. That was wrong twice over, and the second way
    /// is the one worth recording: `MustState` *contains* the graph, so the
    /// report held **two** identical `ExecutionGraph`s — and it also held the
    /// whole `RQueue`, whose size is not bounded by `|G₁|` at all. The
    /// `O(reports × |G₁|)` figure in the criteria was written before S5 chose
    /// to retain a `MustState`, and restating it afterwards was an error
    /// rather than a measurement (gate-4 round 1, M3).
    ///
    /// So the serialization happens **at capture**, off the borrowed
    /// `MustState`, which is cloned transiently for
    /// `ReplayInformation::create`'s by-value argument and dropped as soon as
    /// the JSON exists. What the report retains is one `ExecutionGraph` —
    /// which triage and the diagnostics both need, and which cannot be
    /// recovered from the JSON without the predicate loss §7.3 rejects — and
    /// one `String`.
    pub(crate) replay: crate::conformance::report::ReplaySnapshot,
}

impl std::fmt::Debug for Report {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Report")
            .field("gate", &self.gate)
            .field("kind", &self.kind)
            .field("events", &self.events)
            .finish_non_exhaustive()
    }
}

/// Something that stopped the search from answering, which is **not** a
/// report.
///
/// Kept apart from [`Report`] for the reason that recurs throughout this
/// module: ⊥ is a claim about the program, exhaustion is a claim about the
/// search. Folding the second into the first reports a conformance violation
/// that was never established.
#[derive(Clone, Debug)]
pub(crate) struct Exhaustion {
    pub(crate) gate: Gate,
    pub(crate) events: usize,
}

/// An assertion failure that is **not** a conformance report (§4.4).
///
/// Two ways to get here, and the reason is recorded because they are
/// different claims:
///
/// - an **invisible** thread failed an assertion — the theorem does not speak
///   about it, so reporting it would claim a violation of something never
///   promised;
/// - a thread failed one *after* this execution was already pruned — the
///   execution is doomed and the report that pruned it already names the
///   occasion, so a second `Report` would claim something about a graph that
///   no longer exists.
///
/// **`AfterPrune` does not imply the thread was visible, and must not be read
/// that way** (gate-4 round 3, m2 — an earlier version of this doc asserted it
/// did). The classification is positional: `conf_assert_failure` tests the
/// prune latch before it tests visibility, so an invisible thread reaching
/// that branch would be recorded `AfterPrune` too.
///
/// The case is *believed* unreachable, and the argument is written here rather
/// than left in a test's doc comment, because this is where the claim would be
/// relied on. `conf_prune` calls `stop()`, so after a prune the only thread
/// that runs on is the one that triggered it; §4.4 prunes only on the visible
/// branch; and a gate firing on an **invisible** thread's own fresh event
/// cannot newly fail, because that event is `porf`-maximal — it is therefore
/// the source of no `porf` path between two events that already exist, so it
/// adds no `vo` edge between pre-existing visible events and leaves `matches`
/// unchanged. (That last step is the one the argument needs and the one an
/// earlier statement of it omitted: `done` passes the whole graph to `matches`
/// and to `statuses`, not just the observation set, so "same observations" is
/// not sufficient on its own.)
///
/// **What is not closed**: §4.1 exempts CToss/Choice revisits from the
/// revisit-apply gate, so after such a pop the replayed prefix — carrying
/// visible communication events that are not re-gated — is first seen by
/// whichever fresh event gates next, and that may be an invisible thread's.
/// The argument then needs the prefix's coverability to have been settled in
/// an earlier execution. Nobody has shown that, and nobody has constructed an
/// instance either. Treat the implication as unproven.
#[derive(Clone, Debug)]
pub(crate) struct Diagnostic {
    /// The declared visible name where the thread has one, the runtime task
    /// name otherwise — the same key a [`Report`] uses, so the two can be
    /// joined.
    pub(crate) thread: String,
    /// **What this denotes depends on `reason`, and it must**: for
    /// `InvisibleThread` it is the position of the `Block(Assert)` that was
    /// installed, a real event in the graph; for `AfterPrune` **nothing was
    /// installed**, so it is the position the failing statement *would* have
    /// occupied — which may hold conformance's own `Block(ConfPrune)` or lie
    /// past the end of the row. It still identifies which statement failed,
    /// in program order, which is what it is for. Do not resolve it as an
    /// event without checking `reason` (gate-4 round 2, M1).
    pub(crate) pos: Event,
    pub(crate) reason: DiagnosticReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DiagnosticReason {
    InvisibleThread,
    AfterPrune,
}

/// What a gate call tells the engine to do next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GateOutcome {
    /// Carry on with this execution.
    Continue,
    /// §4.2: the caller must record nothing further, block every thread with
    /// `Block(ConfPrune)` and stop. Already-queued revisits at shallower
    /// stamps survive — this is the draft's DFS prune, not an abandonment.
    Prune,
}

/// A declared visible thread that violates §8.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum VisibleThreadError {
    /// §8: a declared visible thread was spawned *after* its program had
    /// already communicated.
    SpawnedLate {
        name: String,
        create: Event,
        after: Event,
    },
    /// `P4-MIXED` M4: an `Explicit(Visible)` send or receive on a thread no
    /// declared name resolves to (the paper's first condition on annotations).
    UndeclaredVisible {
        thread: String,
        pos: Event,
        site: String,
    },
}

impl std::fmt::Display for VisibleThreadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VisibleThreadError::SpawnedLate {
                name,
                create,
                after,
            } => write!(
                f,
                "visible thread `{name}` is created at {create}, which is \
                 porf-after the communication event {after}; §8 requires each \
                 declared visible thread to be spawned before its program \
                 communicates"
            ),
            VisibleThreadError::UndeclaredVisible { thread, pos, site } => write!(
                f,
                "a `Visible` annotation on undeclared thread `{thread}` at {pos}; only \
                 declared visible threads may annotate an operation `v` (mixed \
                 visibility, the first condition) (site `{site}`)"
            ),
        }
    }
}

/// `P4-MIXED` M8's count on one complete graph: the `SendMsg`/`RecvMsg` labels
/// of declared threads that `is_visible` rejects.
pub(crate) fn invisible_ops_of_visible_threads(
    graph: &ExecutionGraph,
    visible: &[String],
) -> usize {
    let mut n = 0;
    for name in visible {
        let Ok(Some(tid)) = resolve_visible(graph, name) else {
            continue;
        };
        for index in 0..graph.thread_size(tid) as u32 {
            let e = Event::new(tid, index);
            if matches!(
                graph.label(e),
                LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_)
            ) && !crate::conformance::obs::is_visible(graph, e, visible)
            {
                n += 1;
            }
        }
    }
    n
}

/// §8's spawn-order guard.
///
/// **Owner ruling 2026-09-12 (blocked item E): S4 builds this.** It had been
/// specified and assigned to no step — `morphism.rs`'s own module doc says it
/// "belongs to `verify`", and §12 gave `conformance/mod.rs` to nobody — while
/// three approved properties of S2 rest on it: positional matching, (M1)'s
/// thread key, and (M2)'s edge set.
///
/// **What "before its program communicates" means, and why this form.** §8's
/// harm is stated in `morphism.rs`: a visible thread spawned after its program
/// has communicated "makes its `TCreate` an ordering between visible events
/// rather than a common ancestor of them". The condition that prevents exactly
/// that is: **no communication event is `porf`-before the thread's `TCreate`**.
///
/// A stricter literal reading — the `TCreate` must be `porf`-*before* every
/// communication event — is **not** what is checked here, and the two are not
/// equivalent: they differ on events that are simply unordered, which are
/// harmless, since with no `porf` path there is no induced order between
/// visible events. The weaker condition is the one that matches the harm, and
/// rejecting unordered spawns would refuse programs §8 has no quarrel with.
///
/// **Main is exempt**, and trivially so: its create label is the synthetic one
/// `ExecutionGraph::new` installs, which nothing precedes.
///
/// **A7's residual is not discharged by this.** The guard constrains
/// *declared visible* names only, so a late-spawned **invisible** thread still
/// contributes its create edge, and (M2)'s assumption is not closed in
/// general.
///
/// Cost: one pass over the graph's communication events per declared visible
/// name, with an `in_porf` query each. It runs only when `conf.is_some()`.
pub(crate) fn check_spawn_order(
    graph: &ExecutionGraph,
    visible: &[String],
) -> Result<(), VisibleThreadError> {
    let comm: Vec<Event> = graph
        .thread_ids()
        .into_iter()
        .flat_map(|t| (0..graph.thread_size(t) as u32).map(move |i| Event::new(t, i)))
        .filter(|e| {
            matches!(
                graph.label(*e),
                LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_)
            )
        })
        .collect();

    for name in visible {
        if name == "main" {
            continue;
        }
        // A name that resolves to nothing is `NotSpawned`, which is a
        // different §8 condition and already has its own error on the
        // extraction path. Silence here, rather than a second opinion.
        let Ok(Some(tid)) = resolve_visible(graph, name) else {
            continue;
        };
        let create = graph.get_thread_tclab(tid).pos();
        for e in &comm {
            if graph.in_porf(*e, create) {
                return Err(VisibleThreadError::SpawnedLate {
                    name: name.clone(),
                    create,
                    after: *e,
                });
            }
        }
    }
    Ok(())
}

/// A job for the probe worker: one `Cover` call.
struct Job {
    g1: ExecutionGraph,
    complete: bool,
    seed: ExecutionGraph,
}

/// What comes back from the worker: the search's own answer, or the payload
/// of a panic raised inside it.
///
/// The second case is not exotic — it is how the **specification** program's
/// §9 rejections and its Rust-level panics arrive. (A `traceforge::assert`
/// failure in a probe no longer panics: since Part 2 it installs a
/// `Block(Assert)` and the search returns `ObsError::SpecNotAssertionSafe`
/// through the first case.) Before this, such a
/// panic killed the worker thread, dropped the sender, and surfaced on the
/// calling thread as `RecvError`: §9 requires an "outside conformance scope"
/// error *naming the event*, and the user got "the probe worker died
/// mid-search" (gate-4 review, M1). That is F-C's defect one layer out — a
/// failure turned into a different failure that has lost its origin, at the
/// one boundary S4 introduced.
type Answer = Result<(Result<Cover, ObsError>, CoverCounters), Box<dyn std::any::Any + Send>>;

/// A dedicated OS thread that owns every probe.
///
/// **This is not an optimisation; it is required for correctness.**
/// `prober::probe_from` sets the thread-local "current `Must`" and runs the
/// specification program on the calling thread, and its own rustdoc says so:
/// calling it from inside another execution "would nest two runtimes in one
/// thread's scoped state; the conformance search will therefore own a
/// dedicated OS thread for probing". Every gate fires from *inside* the outer
/// execution, on a thread the outer scheduler owns, so the search cannot run
/// there — it would clobber the outer `Must` pointer and nest two
/// continuation pools.
///
/// One long-lived worker rather than a thread per gate: gates fire per event,
/// and thread creation per event is a cost the ordinary path would notice if
/// it ever leaked out of `conf.is_some()`.
///
/// The graphs are cloned across the channel. That is the price of the
/// isolation and is paid only in conformance mode.
struct ProbeWorker {
    jobs: Sender<Job>,
    answers: Receiver<Answer>,
    handle: Option<JoinHandle<()>>,
}

impl ProbeWorker {
    fn new(search: Search) -> Self {
        let (jobs, job_rx) = channel::<Job>();
        let (answer_tx, answers) = channel::<Answer>();
        let handle = std::thread::Builder::new()
            .name("traceforge-conformance-probe".to_owned())
            .spawn(move || {
                while let Ok(job) = job_rx.recv() {
                    let answer = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        search.cover_counted(&job.g1, job.complete, job.seed)
                    }));
                    let failed = answer.is_err();
                    if answer_tx.send(answer).is_err() || failed {
                        break;
                    }
                }
            })
            .expect("conformance: could not spawn the probe worker thread");
        Self {
            jobs,
            answers,
            handle: Some(handle),
        }
    }

    fn cover(
        &self,
        g1: &ExecutionGraph,
        complete: bool,
        seed: ExecutionGraph,
    ) -> (Result<Cover, ObsError>, CoverCounters) {
        self.jobs
            .send(Job {
                g1: g1.clone(),
                complete,
                seed,
            })
            .expect("conformance: the probe worker died");
        match self
            .answers
            .recv()
            .expect("conformance: the probe worker died mid-search")
        {
            Ok(answer) => answer,
            // Re-raise on the calling thread with the original payload, so a
            // specification program's §9 rejection or Rust-level panic reaches
            // the caller as itself rather than as a channel error. (A
            // `traceforge::assert` failure in a probe does not come this way
            // since Part 2; see `Answer`'s doc.)
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    /// End the worker and wait for it. Idempotent.
    fn shutdown(&mut self) {
        let (jobs, _) = channel::<Job>();
        drop(std::mem::replace(&mut self.jobs, jobs));
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

impl Drop for ProbeWorker {
    /// The backstop, **not** the normal path (gate-4 review, m1).
    ///
    /// `explore` installs the outer `Must` in the `CURRENT_MUST` thread-local
    /// and never clears it, so when `verify_conformance` drops its own `Rc`
    /// the refcount is still 1: the `Must` is not dropped, this is not
    /// dropped, and the worker would stay parked in `recv` holding the
    /// specification closure until something else replaced the thread-local.
    /// `ConfCtx::shutdown`, called where the run ends, is the normal path.
    fn drop(&mut self) {
        self.shutdown();
    }
}

/// Conformance state on the outer `Must`.
pub(crate) struct ConfCtx {
    /// `None` on a **gate-disabled** context (§5.4's precheck, §7.3's triage).
    ///
    /// The gate is the probe worker: with no worker there is no `Cover` call,
    /// so `gate` answers `Continue` without consulting anything. What is
    /// *not* disabled is §9's guard arming or `store_replay_information`'s
    /// exemption, both of which key off `conf.is_some()` — and keeping those
    /// on is the entire reason these two engines carry a `ConfCtx` at all.
    worker: Option<ProbeWorker>,
    mode: ConfMode,
    visible: Vec<String>,
    /// §4.3: **one mutable `H`, and it is never snapshotted into `MustState`.**
    ///
    /// The draft carries `H` down the DFS and restores it on backtrack; the
    /// worklist engine pops revisits at arbitrary stamps, so the current `H`
    /// at a pop is generally not the one the draft would carry there. Keeping
    /// it single is sound because `Cover` succeeds only by producing a graph
    /// that matches `G₁` — which `H` seeded the search cannot make a success
    /// wrong — and complete because on extend-failure `Cover` rebuilds from
    /// empty. `H` is a heuristic cache; staleness costs a rebuild, not an
    /// answer. (Proof obligation O2, §10.)
    ///
    /// This is why `push_state`/`try_pop_state` need no conformance changes at
    /// all, and a future reader who "fixes" the stale cache by snapshotting it
    /// would be adding cost, not correctness.
    h: ExecutionGraph,
    reports: Vec<Report>,
    exhaustions: Vec<Exhaustion>,
    /// §4.4's other half. An **invisible** thread's failed assertion is not a
    /// conformance report and must not prune: the theorem does not speak about
    /// it, so reporting it would claim a violation of something never
    /// promised, and pruning on it would cut a subtree for a reason the
    /// morphism cannot see. It is still worth surfacing, so it is kept here —
    /// separately, and it is not a [`Report`].
    diagnostics: Vec<Diagnostic>,
    /// Criterion 11's must-not-fire guard. `complete_execution` runs for every
    /// ending, including the one this context just pruned, so without this the
    /// completion gate would fire on a pruned graph — where (M3) is outside
    /// its domain and `status_of` panics by design.
    pruned: bool,
    /// §7.4, default false. Set from `ConfConfig`.
    stop_at_first_report: bool,
    /// §7.4's mechanism, and **blocked item G's ruling**: one flag, set by the
    /// gate when a report is recorded, tested where `explore` decides to
    /// continue.
    ///
    /// Not a drained `rqueue` — a drained queue is **indistinguishable from
    /// an exhausted one**, which is exactly the distinction blocked item B
    /// requires the verdict to carry. Not `config.max_iterations` set from the
    /// gate either, for the same reason plus the collision: the verdict must
    /// tell a bound the *user* set from one the *gate* set, and reusing the
    /// field destroys that.
    ///
    /// Inert when `conf` is `None`, since it lives here.
    stop_requested: bool,
    /// `P4-CFIRST` C5: the early-error cut. Set only on a `CFirstOuter`
    /// context (`set_cut`); when on, a visible assertion failure prunes and
    /// reports exactly as under `Outer`.
    cut: bool,
    /// `P4-GATED` G1: the gated checker's gate sink (`GatedOuter` only).
    gate_sink: Option<GateSink>,
    /// **Why the outer loop stopped — a carried fact, never an inference.**
    ///
    /// Blocked item B's ruling: the "conforms" case is constructible only when
    /// reports and exhaustions are both empty *and* the search completed, and
    /// "the search completed" is a distinct carried fact. `complete_execution`
    /// records it at each of the three sites where it decides the run is over,
    /// so the three are told apart by construction.
    end: SearchEnd,
    /// Needed by §7.1's serialized snapshot, which is built at capture rather
    /// than retained as state — `ReplayInformation::create` takes the run's
    /// `Config` alongside the linearisation.
    config: Config,
    /// §11.6's per-execution graph capture. `None` — the default in **both**
    /// constructors — means the hook does not run at all.
    ///
    /// **Ungated, not `#[cfg(test)]`.** `cfg(test)` is false for
    /// `traceforge/tests/*.rs`, benches and doctests, so gating this field
    /// would compile `ConfCtx` to two different shapes and only one of them
    /// would be exercised by `cargo build` — F-12's hazard. `pub(crate)` is
    /// not a semver surface, so nothing here reaches the public API.
    ///
    /// No existing hook yields a per-execution graph: `ExecutionObserver::after`
    /// receives an `EndCondition` and a `CoverageInfo` but no graph, `take_graph`
    /// is destructive, and the report sink captures graphs only on reports.
    collected: Option<Vec<ExecutionGraph>>,
    /// The number of visible observations the last gate saw, for F42's
    /// inertness skip. `None` before the first gate of an execution.
    last_visible_obs: Option<usize>,
    /// `P4-ENUMERATOR` criterion 9: set by the gate that saw the inner search
    /// abort on a specification assertion. Once set, every gate is inert and
    /// `report_visible_error` records instead of reporting; `run` returns
    /// `Err` on it ahead of reports and end.
    spec_error: Option<(String, Event)>,
    /// Criterion 13.
    counters: ConfCounters,
    /// Criterion 13: key-level counters are computed only when set.
    instrument: bool,
    /// `P4-STATEFUL` T3: the completion sink of an `Enumerate` run.
    sink: Option<CompletionSink>,
    /// How many gates F42's inertness skip suppressed — a *different* reason
    /// from [`Self::skipped_gates`], counted separately so a figure can say
    /// which.
    inert_gates: usize,
    /// How many gates F49's replay-frontier skip suppressed on this run.
    ///
    /// **Counted, not merely skipped** (review `P3-A16`, M4). A skipped gate is
    /// a check that did not happen, so a run with a non-zero count established
    /// "no gate *that ran* found a violation" — which is weaker than
    /// refinement. F43 set the precedent for exhaustions; this is the same
    /// obligation for skips, and any figure derived from a run must assert it
    /// is zero or state what it was.
    skipped_gates: usize,
    /// Visible assertion failures seen under [`ConfMode::Collect`] or
    /// [`ConfMode::Enumerate`], which do not prune (S6 round 3, B1). Always
    /// empty on every other mode.
    ///
    /// Kept out of `diagnostics` so the public `ConfNote` need not grow a
    /// variant: the oracle is test-only, and the stateful engine
    /// (`P4-STATEFUL` T4) reads this list itself to answer §5.4's question.
    collect_errors: Vec<(String, Event)>,
}

impl ConfCtx {
    /// Today's constructor, kept signature-stable (`P4-SELECTOR` S3, route
    /// (a)): the inner search runs in `Recorded` order.
    pub(crate) fn new(
        config: Config,
        spec: Arc<dyn Fn() + Send + Sync>,
        visible: Vec<String>,
        budget: usize,
        stop_at_first_report: bool,
    ) -> Self {
        Self::new_with_inner_order(
            config,
            spec,
            visible,
            budget,
            stop_at_first_report,
            InnerOrder::Recorded,
        )
    }

    /// The constructor that carries knob B. It must be a constructor and not
    /// a setter: the `Search` is moved into the `ProbeWorker`, whose thread
    /// starts at once, so nothing set afterwards would reach it.
    pub(crate) fn new_with_inner_order(
        config: Config,
        spec: Arc<dyn Fn() + Send + Sync>,
        visible: Vec<String>,
        budget: usize,
        stop_at_first_report: bool,
        inner_order: InnerOrder,
    ) -> Self {
        Self::new_with_opts(
            config,
            spec,
            visible,
            budget,
            stop_at_first_report,
            SearchOpts {
                inner_order,
                ..SearchOpts::default()
            },
        )
    }

    /// The constructor that carries every inner-search option (`P4-ENUMERATOR`
    /// criterion 4, route (a)); `new` and `new_with_inner_order` delegate here
    /// with the defaults. A constructor and not a setter: the `Search` is
    /// moved into the `ProbeWorker`, whose thread starts at once.
    pub(crate) fn new_with_opts(
        config: Config,
        spec: Arc<dyn Fn() + Send + Sync>,
        visible: Vec<String>,
        budget: usize,
        stop_at_first_report: bool,
        opts: SearchOpts,
    ) -> Self {
        let instrument = opts.instrument;
        let search = Search::new(config.clone(), spec, visible.clone(), budget).with_opts(opts);
        Self {
            worker: Some(ProbeWorker::new(search)),
            mode: ConfMode::Outer,
            config,
            visible,
            h: ExecutionGraph::default(),
            reports: Vec::new(),
            exhaustions: Vec::new(),
            diagnostics: Vec::new(),
            pruned: false,
            stop_at_first_report,
            stop_requested: false,
            cut: false,
            gate_sink: None,
            end: SearchEnd::Unknown,
            collected: None,
            collect_errors: Vec::new(),
            skipped_gates: 0,
            last_visible_obs: None,
            inert_gates: 0,
            spec_error: None,
            counters: ConfCounters::default(),
            instrument,
            sink: None,
        }
    }

    /// A context with no gate: `conf.is_some()` without a probe worker.
    ///
    /// §5.4's precheck and §7.3's triage both need exactly this — "conformance's
    /// *gate* is off in that run; its *guards* are not" — and neither has a
    /// specification to probe. §8's spawn-order guard still runs, because a
    /// declared visible name spawned late is a §8 violation in *whichever*
    /// program commits it, and the precheck is the only engine that ever sees
    /// the specification's own complete graphs from outside the search.
    pub(crate) fn gate_disabled(config: Config, visible: Vec<String>, mode: ConfMode) -> Self {
        assert!(
            mode != ConfMode::Outer,
            "conformance: the outer run is the engine that has a gate; a gate-disabled \
             outer context would explore the implementation and check nothing"
        );
        Self {
            worker: None,
            mode,
            config,
            visible,
            h: ExecutionGraph::default(),
            reports: Vec::new(),
            exhaustions: Vec::new(),
            diagnostics: Vec::new(),
            pruned: false,
            stop_at_first_report: false,
            stop_requested: false,
            cut: false,
            gate_sink: None,
            end: SearchEnd::Unknown,
            collected: None,
            collect_errors: Vec::new(),
            skipped_gates: 0,
            last_visible_obs: None,
            inert_gates: 0,
            spec_error: None,
            counters: ConfCounters::default(),
            instrument: false,
            sink: None,
        }
    }

    pub(crate) fn mode(&self) -> ConfMode {
        self.mode
    }

    /// §7.1's serialized half, at capture time.
    ///
    /// **Only rendered reports go through this method — the outer run's, and
    /// the complete-first outer run's cut reports (`P4-CFIRST` C5).** The precheck's
    /// and triage's sinks are read for their *contents* — did anything assert?
    /// — and then discarded, so serializing them would linearise a graph nobody
    /// reads, on the two engines whose graphs are most likely to violate
    /// `top_sort`'s precondition. The stateful engine (`P4-STATEFUL` T3) takes
    /// its reports' snapshots at its completion sink, through
    /// `report::replay_snapshot` directly, not through here.
    fn snapshot(
        &self,
        graph: &ExecutionGraph,
        state: &MustState,
        pos: Option<Event>,
    ) -> crate::conformance::report::ReplaySnapshot {
        use crate::conformance::report;
        // `P4-CFIRST` C5: a cut report is rendered, so it is serialized here
        // like the outer run's.
        let rendered =
            self.mode == ConfMode::Outer || (self.mode == ConfMode::CFirstOuter && self.cut);
        if !rendered {
            return report::replay_not_produced();
        }
        report::replay_snapshot(graph, state, &self.config, pos)
    }

    /// §7.4: has a report asked the outer loop to stop?
    pub(crate) fn stop_requested(&self) -> bool {
        self.stop_requested
    }

    /// Record why the outer loop stopped. First writer wins: the run ends
    /// once, and a later overwrite would be a second opinion about a fact that
    /// was already observed.
    pub(crate) fn record_end(&mut self, end: SearchEnd) {
        if self.end == SearchEnd::Unknown {
            self.end = end;
        }
    }

    pub(crate) fn end(&self) -> SearchEnd {
        self.end
    }

    pub(crate) fn reports(&self) -> &[Report] {
        &self.reports
    }

    pub(crate) fn exhaustions(&self) -> &[Exhaustion] {
        &self.exhaustions
    }

    pub(crate) fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// `P4-STATEFUL` T3: install the completion sink of an `Enumerate` run.
    pub(crate) fn set_sink(&mut self, sink: CompletionSink) {
        assert!(
            self.mode.enumerates(),
            "conformance: a completion sink belongs to an enumerating run"
        );
        self.sink = Some(sink);
    }

    /// `P4-CFIRST` C5: arm the early-error cut on the complete-first outer
    /// run, and with it the stop flag (`gate_disabled` hard-codes it `false`,
    /// and `report_visible_error`'s stop is gated on it — round 01 M4).
    pub(crate) fn set_cut(&mut self, cut: bool, stop_at_first_report: bool) {
        assert!(
            self.mode == ConfMode::CFirstOuter,
            "conformance: the early-error cut belongs to the complete-first outer run"
        );
        self.cut = cut;
        self.stop_at_first_report = cut && stop_at_first_report;
    }

    /// `P4-GATED` G1: install the gate sink on the gated checker's outer run.
    pub(crate) fn set_gate_sink(&mut self, sink: GateSink) {
        assert!(
            self.mode == ConfMode::GatedOuter,
            "conformance: a gate sink belongs to the gated checker's outer run"
        );
        self.gate_sink = Some(sink);
    }

    /// `P4-GATED` G1: whether a requested stop ends the run at `try_revisit`'s
    /// head — only the gated checker's outer run (the closed engines keep
    /// their behaviour, F81).
    pub(crate) fn stops_revisits(&self) -> bool {
        self.mode == ConfMode::GatedOuter
    }

    /// Criterion 9: the specification assertion the inner search aborted on.
    pub(crate) fn spec_error(&self) -> Option<&(String, Event)> {
        self.spec_error.as_ref()
    }

    /// Criterion 13.
    pub(crate) fn counters(&self) -> &ConfCounters {
        &self.counters
    }

    /// Fold one `Cover` call's counters into the run's (criterion 13).
    fn account_cover(&mut self, cc: &CoverCounters) {
        let c = &mut self.counters;
        c.spec_visit_calls += cc.spec_visit_calls;
        c.spec_visit_calls_extend += cc.spec_visit_calls_extend;
        c.spec_visit_calls_rebuild += cc.spec_visit_calls_rebuild;
        c.memo_hits += cc.memo_hits;
        c.rebuilds_taken += usize::from(cc.rebuild_taken);
        c.rebuilds_skipped_initial_seed += usize::from(cc.rebuild_skipped_initial_seed);
        c.rebuilds_skipped_exhausted_seed += usize::from(cc.rebuild_skipped_exhausted_seed);
        c.distinct_keys_run_wide = cc.run_wide_distinct_so_far;
        c.f63_distinct_run_wide = cc.f63_run_wide_distinct_so_far;
        c.per_cover.push(cc.clone());
    }

    /// Criterion 13's first-report figure and report keys. The key of a
    /// `RevisitApply` report graph is the graph as cut by `revisit_view`.
    fn note_report(&mut self, gate: ReportGate, graph: &ExecutionGraph) {
        if self.counters.paper_events_at_first_report.is_none() {
            let paper: usize = graph
                .thread_ids()
                .into_iter()
                .map(|t| paper_events(graph, t))
                .sum();
            self.counters.paper_events_at_first_report = Some(paper);
        }
        if self.instrument {
            if let Ok(k) = CanonicalGraph::of(graph, &self.visible) {
                self.counters
                    .report_keys
                    .push((gate, format!("{:?}", k.key())));
            }
        }
    }

    /// End the probe worker. Called where the conformance run ends; `Drop` is
    /// the backstop for every other way out.
    pub(crate) fn shutdown(&mut self) {
        if let Some(w) = self.worker.as_mut() {
            w.shutdown();
        }
    }

    pub(crate) fn is_pruned(&self) -> bool {
        self.pruned
    }

    /// §4.4, invisible case: record and carry on. No report, no prune.
    pub(crate) fn record_invisible_error(&mut self, thread: String, pos: Event) {
        self.diagnostics.push(Diagnostic {
            thread,
            pos,
            reason: DiagnosticReason::InvisibleThread,
        });
    }

    /// A failed assertion arriving after this execution was pruned.
    ///
    /// `thread` is the **declared visible name** when the thread has one, so
    /// S5 can join this to the `Report` that pruned the execution; the runtime
    /// task name is used only for a thread that is not declared visible.
    pub(crate) fn record_after_prune(&mut self, thread: String, pos: Event) {
        self.diagnostics.push(Diagnostic {
            thread,
            pos,
            reason: DiagnosticReason::AfterPrune,
        });
    }

    pub(crate) fn visible(&self) -> &[String] {
        &self.visible
    }

    /// Called by `Must` when an execution **ends**, before `try_revisit` pops
    /// the next alternative.
    ///
    /// This is the real boundary, and getting it wrong was the developer's
    /// F-B: the latch used to be cleared only in `begin_execution`, but
    /// `try_revisit` — and with it the revisit-apply gate — runs at the *end*
    /// of `complete_execution`, before the next execution begins. So the first
    /// revisit popped after any prune was applied with the gate inert, which
    /// is precisely the doomed re-execution §4.1 says this gate exists to
    /// skip.
    pub(crate) fn end_execution(&mut self) {
        self.pruned = false;
    }

    /// Called when a new execution begins. Redundant with
    /// [`Self::end_execution`] and kept deliberately: two clears cannot be
    /// wrong, one missing clear silences a gate for a whole execution.
    pub(crate) fn begin_execution(&mut self) {
        self.pruned = false;
        // **F42's cache must not cross an execution boundary** (review
        // `P3-skips`, M1 — a verdict-changing defect, found independently by
        // the reviewer and the developer).
        //
        // Without this, the route is: a pruned execution returns at
        // `if self.pruned` *above* F42's block, so its `Completion` gate never
        // reaches the reset; `conf_revisit_gate` does not fire `RevisitApply`
        // for `CToss`/`Choice` revisits, so that reset can be missed too; and
        // the next execution's first fresh-add gate then compares its
        // observation count against a value cached **in a different
        // execution**. The per-event maximality argument F42 rests on is
        // simply false across that boundary — the code was silently relying on
        // the weaker "`Completion` always runs" fallback.
        //
        // Measured on the eager 2PC pair at N=4: **174 reports before this
        // line, 148 after**, and 148 is what F42-disabled gives. So the report
        // set was not preserved. With the line, F42 is verdict-identical to
        // F42-disabled at zero cost — the inert counts are unchanged.
        self.last_visible_obs = None;
    }

    /// The revisit-apply gate pruned, so the alternative is abandoned before
    /// it ever runs and the latch must not carry into the next pop.
    pub(crate) fn abandon_revisit(&mut self) {
        self.pruned = false;
    }

    /// Turn on §11.6's per-execution graph capture.
    ///
    /// Off by default in both constructors, so a run that does not ask for it
    /// pays nothing and behaves identically.
    pub(crate) fn collect_graphs(&mut self) {
        self.collected = Some(Vec::new());
    }

    /// The graphs captured by [`Self::collect_graphs`], in completion order.
    ///
    /// Empty when capture was never turned on — the caller asked for the
    /// graphs of a run that was not collecting, which is a caller bug, but
    /// returning an empty slice keeps the read side total.
    pub(crate) fn collected(&self) -> &[ExecutionGraph] {
        self.collected.as_deref().unwrap_or(&[])
    }

    /// How many gates F42's inertness skip suppressed.
    pub(crate) fn inert_gates(&self) -> usize {
        self.inert_gates
    }

    /// How many gates F49's skip suppressed. See the field for why it matters.
    pub(crate) fn skipped_gates(&self) -> usize {
        self.skipped_gates
    }

    /// Visible assertion failures recorded by a [`ConfMode::Collect`] or
    /// [`ConfMode::Enumerate`] run (the stateful engine reads them at its
    /// completion sink, `P4-STATEFUL` T4).
    pub(crate) fn collect_errors(&self) -> &[(String, Event)] {
        &self.collect_errors
    }

    /// §4.4: record a visible thread's failed assertion and prune.
    ///
    /// **Except under [`ConfMode::Collect`] and the enumerating modes with the
    /// cut off** (S6 criteria round 3, B1; `P4-STATEFUL` criterion 1, "no
    /// pruning"; `P4-CFIRST` C5). The
    /// oracle's enumeration run reaches this the same way any gate-disabled
    /// engine does — `conf_assert_failure` consults neither the probe, nor the
    /// worker, nor the mode — and pruning there would append `Block(ConfPrune)`
    /// to *every* thread, truncating each sibling visible thread's row and
    /// ending the execution, so `vis(P)` would be under-approximated. The
    /// failure is still recorded, as a diagnostic carrying the **declared**
    /// visible name: a silent `Continue` is the failure mode a careless
    /// implementation produces here, and it is the one to guard against.
    pub(crate) fn report_visible_error(
        &mut self,
        thread: String,
        pos: Event,
        events: usize,
        state: &MustState,
        graph: &ExecutionGraph,
    ) -> GateOutcome {
        if self.pruned {
            return GateOutcome::Continue;
        }
        // Criterion 9: after the abort nothing reports; the failure is kept
        // as a diagnostic, like a post-prune one.
        if self.spec_error.is_some() {
            self.record_after_prune(thread, pos);
            return GateOutcome::Continue;
        }
        // `P4-CFIRST` C5: no prune iff `Collect || (enumerates() && !cut)`;
        // `Precheck` and `Triage` keep pruning and reporting, which
        // `precheck::run` reads.
        if self.mode == ConfMode::Collect || (self.mode.enumerates() && !self.cut) {
            // Recorded, never silent — a bare `Continue` here is the failure
            // mode a careless implementation produces, and it would hide a
            // visible error from the oracle entirely.
            //
            // Deliberately **not** a `Diagnostic`: `DiagnosticReason` is
            // rendered by the publicly re-exported `ConfNote`, so a new variant
            // there would grow the public surface, which §11.6's criterion 17
            // forbade for the test-only `Collect` path; `Enumerate` reuses the
            // same channel and the stateful engine renders what it reads from
            // it (`P4-STATEFUL` T4). `pos` is a real event — the
            // `Block(Assert)` is installed above `conf_assert_failure`'s
            // visibility split — and `thread` is the **declared** visible name.
            self.collect_errors.push((thread, pos));
            return GateOutcome::Continue;
        }
        self.note_report(ReportGate::NotAGate, graph);
        self.reports.push(Report {
            gate: None,
            kind: ReportKind::VisibleError { thread, pos },
            events,
            graph: graph.clone(),
            replay: self.snapshot(graph, state, Some(pos)),
        });
        self.pruned = true;
        if self.stop_at_first_report {
            self.stop_requested = true;
        }
        GateOutcome::Prune
    }

    /// Which program a §8 violation belongs to.
    ///
    /// §8 makes these the *user's* error in whichever program committed them,
    /// and the first version of this blamed the specification unconditionally
    /// (developer's gate-3 report, F-D). The second version asked
    /// `wobs(g1)` — **which cannot raise `NotSpawned` at all**: `resolve`
    /// returns `Ok(None)`, `visible_events` turns that into `Row::Unspawned`,
    /// and `wobs` succeeds. `statuses` is what raises it. So the fix reached
    /// `AmbiguousName` and left the never-spawned case blaming the wrong
    /// program — worse than before, because the working half invites trust in
    /// the mechanism (the developer's re-run caught exactly that).
    ///
    /// This runs **both** extractions `Search::done` runs on the
    /// implementation side, which between them raise every `ObsError` the
    /// search can produce. It is still a reconstruction at the catch site
    /// rather than a side carried out of the search on the error, and the
    /// better shape is recorded for S5: `Search::cover` would return an error
    /// that names its origin, which no reconstruction can get wrong. Changing
    /// that signature reaches S3's approved tests, so it is not done here.
    ///
    /// Only ever called on the error path, which then panics.
    /// **The reconstruction is checked against the error it is explaining**
    /// (gate-4 review, and the developer's own suggestion at gate 3).
    /// `ObsError` derives `Eq`, so this costs a comparison. The hazard it
    /// closes: a third `ObsError`-raising extraction appearing in
    /// `Search::done` would make this sequence mis-blame *in silence*. With
    /// the check, it surfaces as a visible mismatch instead of a confident
    /// wrong answer — which is the difference between the two failures this
    /// project keeps relearning.
    fn blame_for(&self, g1: &ExecutionGraph, raised: &ObsError) -> &'static str {
        use crate::conformance::morphism::{statuses, CompleteExecution};
        use crate::conformance::obs::wobs;

        let reproduced: Option<ObsError> = match wobs(g1, &self.visible) {
            Err(e) => Some(e),
            Ok(w) => match CompleteExecution::try_finished(g1) {
                Some(exec) => statuses(exec, &w, &self.visible).err(),
                None => None,
            },
        };
        match reproduced {
            Some(ref e) if e == raised => "implementation",
            // The implementation is clean, so the specification raised it.
            None => "specification",
            // It raised a *different* error. Neither attribution is
            // established, and saying so is better than picking one.
            Some(_) => "implementation or specification (attribution unresolved)",
        }
    }

    /// One gate. §4.1 fixes the four sites; this decides what happens at each.
    pub(crate) fn gate(
        &mut self,
        gate: Gate,
        g1: &ExecutionGraph,
        state: &MustState,
    ) -> GateOutcome {
        self.gate_at(gate, None, g1, state)
    }

    /// [`gate`](Self::gate) with the event it follows (`P4-GATED` G1): the
    /// fresh gates pass the installed position and `RevisitApply` the popped
    /// one with its revisit kind, source and outgoing carry. `None` from the
    /// callers that have no gate sink to feed.
    pub(crate) fn gate_at(
        &mut self,
        gate: Gate,
        site: Option<GateAt>,
        g1: &ExecutionGraph,
        state: &MustState,
    ) -> GateOutcome {
        // §11.6's capture, and it is the **first** statement deliberately.
        //
        // Placed above `if self.pruned` and above the `worker.is_none()`
        // return below: anywhere lower and it is dead in exactly the mode the
        // oracle runs in, which has no worker. It is **discriminated on
        // `Gate::Completion`** because `gate` is the single entry point for all
        // four `Gate` variants across five call sites in `must.rs`
        // (`:1037` FreshSend, `:2252`/`:2305` FreshRecv, `:2883` RevisitApply,
        // `:1965` Completion). An undiscriminated hook would record
        // mid-execution graphs, on which `next_P(G) != {}` and the draft's
        // Def. visg is undefined — "a graph that still admits an event has
        // neither a status nor a set of visible traces".
        self.counters.gate_invocations += 1;
        if gate == Gate::Completion {
            if let Some(sink) = self.collected.as_mut() {
                sink.push(g1.clone());
            }
            // Criterion 13: `L` and the explored complete graphs. Every
            // execution's completion fires here, pruned ones included; the
            // key is taken only for unpruned ones (a pruned graph carries
            // `Block(ConfPrune)`, on which the canonical form is unreachable).
            self.counters.executions += 1;
            let paper: usize = g1
                .thread_ids()
                .into_iter()
                .map(|t| paper_events(g1, t))
                .sum();
            self.counters.max_paper_events_per_execution =
                self.counters.max_paper_events_per_execution.max(paper);
            if self.instrument && !self.pruned {
                if let Ok(k) = CanonicalGraph::of(g1, &self.visible) {
                    self.counters
                        .explored_complete_keys
                        .push(format!("{:?}", k.key()));
                }
            }
            // `P4-MIXED` M8: invisible operations of visible threads on this
            // unpruned completion (read at entry, before any `Cover`), maximum
            // over the run. A receive that blocks is a `Block{Value}`, no
            // event, and is not counted.
            if !self.pruned {
                let n = invisible_ops_of_visible_threads(g1, &self.visible);
                self.counters.invisible_ops_of_visible_threads =
                    self.counters.invisible_ops_of_visible_threads.max(n);
            }
        }
        // Criterion 9: once the inner search aborted, every gate is inert.
        if self.spec_error.is_some() {
            self.counters.gate_skipped_aborted += 1;
            return GateOutcome::Continue;
        }
        if self.pruned {
            self.counters.gate_skipped_pruned += 1;
            return GateOutcome::Continue;
        }

        // **F49: a gate fired mid-replay cannot observe the graph, so it is
        // skipped.** Algorithm-level; see `backlog/flaws.md` F49 and the note
        // below — this changes *when* the algorithm checks, and the owner
        // should rule on it.
        //
        // `initialize_for_execution` blanks **every** send value at the start
        // of each execution (`exec_graph.rs:104-114`), deliberately: without
        // it, code that assumes a replay already carries values is silently
        // wrong. Values come back only as each event is re-executed, and
        // `process_event` removes the event from `unreplayed_events` as that
        // happens.
        //
        // A **fresh**-add gate can therefore fire while a *different* visible
        // thread still holds events from the previous execution that have not
        // been replayed. `wobs` walks every visible thread's row, so it reaches
        // one of those sends and trips `obs.rs`'s pending-value assertion —
        // which is a working guard on a precondition the gate violates. That
        // is F49, and it needs **two** visible threads that branch, because one
        // must be adding a fresh event while the other is behind the replay
        // frontier.
        //
        // **§8's guard runs BEFORE the skip** (F52). A gate suppressed by
        // F49's replay-frontier skip must still check §8's precondition: a
        // declared visible thread spawned after its program has communicated is
        // the *user's* error in whichever program commits it, not a conformance
        // verdict, and it does not stop being one because the gate could not
        // observe the graph. An earlier version sat below the skip, so a skipped
        // gate skipped this too — and the comment claimed a single change where
        // there were two.
        if let Err(e) = check_spawn_order(g1, &self.visible) {
            panic!("conformance: {e}");
        }

        // Skipping is the conservative repair: the observation genuinely does
        // not exist yet, so there is nothing for the gate to compare.
        //
        // **What this rests on is weaker than A16, and A16 is a theorem.**
        // (Review `P3-A16`.) An earlier version of this comment called the
        // monotonicity "the draft's to confirm and not established here".
        // Both halves were wrong. It *is* established — it is the
        // contrapositive of `lem:gate`, proved in full at
        // `popl-conf/tex/appendix.tex:123-166` — and it is **not the
        // proposition this skip needs**. The draft's proof of `thm:alg` pivots
        // on "every place the outer search abandons a branch is a place it
        // reports", and **a skip abandons no branch**: the execution continues
        // and every later gate still fires.
        //
        // **Discriminated on the gate variant, and it must be.** An
        // undiscriminated skip also suppresses `Gate::Completion` — the one
        // gate `thm:alg`'s soundness depends on — and "completion always runs
        // fully replayed" is an *unchecked condition* that three things in this
        // tree contradict: `unreplayed_events`' own doc calls its entries
        // "never consulted"; `must.rs` records the completion gate having
        // already fired on an unreplayed graph once, with one route closed and
        // no argument it was the only one; and an **invisible** thread's
        // `Block(Assert)` — which the draft admits — enters
        // `unreplayed_events` and survives the restoration into the next
        // execution (`cut_to_stamp` for a forward revisit, `revisit_view` for
        // a backward one: both keep every label stamped at or below the
        // revisited receive). An earlier version of this comment claimed the
        // entry "can never be drained". `P4-STATEFUL` gate 3 measured it
        // (`stateful_tests::c03_an_invisible_block_assert_surviving_a_revisit`,
        // a forward revisit restored by `cut_to_stamp`, and its
        // `…_backward_revisit` twin, restored by `revisit_view`; the path is
        // told by the receive's stamp against the revisiting send's): on both
        // sides `w`'s `Block(Assert)`, stamped
        // below `c`'s receive, is in the next execution's graph — so
        // `initialize_for_execution` entered it into `unreplayed_events` — and
        // the set is empty at this gate. `process_event` is the set's only
        // remover, so the entry was drained when the restarted thread
        // re-executed the `assert`. The route — `is_thread_runnable`'s
        // `Assert` arm admitting the thread (`i < index`), then
        // `handle_block`'s replay branch — is read, not run. Even so,
        // the gate must stay discriminated: left undiscriminated, any path
        // that *does* reach completion with an unreplayed entry would skip the
        // completion gate, never call `cover`, and **miss a violation in
        // silence**.
        if gate != Gate::Completion && !g1.unreplayed_events.is_empty() {
            self.skipped_gates += 1;
            self.counters.gate_skipped_replay += 1;
            return GateOutcome::Continue;
        }

        // The precondition the discrimination above relies on, **checked
        // rather than assumed** — the rule `check_spawn_order` follows a few
        // lines below. If this ever fires, the skip is not an adequate repair
        // and the narrower per-event predicate ("a send some visible row needs
        // is still pending") is required instead.
        assert!(
            gate != Gate::Completion || g1.unreplayed_events.is_empty(),
            "conformance: the completion gate fired on a graph with {} unreplayed \
             event(s). F49's skip assumes this cannot happen, and the soundness \
             argument for it rests on that assumption",
            g1.unreplayed_events.len()
        );

        // **No consistency check runs here, deliberately** (criterion 2, and
        // gate-4 review m4: the criterion says leaving this unstated is not
        // acceptable). F38 records that the consistency checker contributes
        // nothing under this fragment — `is_consistent` is vacuous in scope —
        // so calling it would add cost and decide nothing, and a graph it
        // happened to reject would have its conformance verdict silently
        // skipped. `Cover` carries the whole weight.

        // `P4-STATEFUL` T3: the stateful checker's completion sink, after the
        // §8 guard and the completion assertion above, before the gate-disabled
        // return. Only at `Completion`; `pruned` and `spec_error` are never set
        // in `Enumerate` mode, so every completion reaches here. Under
        // `CFirstOuter` with the cut on, a pruned completion returns at the
        // `pruned` test above and never reaches the sink (`P4-CFIRST` C5).
        if gate == Gate::Completion {
            if let Some(sink) = self.sink.as_mut() {
                if sink(g1, state) == SinkVerdict::Stop {
                    self.stop_requested = true;
                }
            }
        }

        // `P4-GATED` G1: the gate sink, at the three growing gates, after the
        // F49 skip and the completion assertion and before the gate-disabled
        // return. `Report` and `Stop` are prunes: the snapshot is taken here,
        // before `conf_prune` appends `Block(ConfPrune)`.
        if gate != Gate::Completion {
            if let (Some(sink), Some(site)) = (self.gate_sink.as_mut(), site.as_ref()) {
                match sink(gate, site, g1, state) {
                    GateVerdict::Continue => {}
                    GateVerdict::Report => {
                        let events: usize =
                            g1.thread_ids().into_iter().map(|t| g1.thread_size(t)).sum();
                        self.note_report(ReportGate::of(Some(gate)), g1);
                        let replay = crate::conformance::report::replay_snapshot(
                            g1,
                            state,
                            &self.config,
                            None,
                        );
                        self.reports.push(Report {
                            gate: Some(gate),
                            kind: ReportKind::NoCover,
                            events,
                            graph: g1.clone(),
                            replay,
                        });
                        self.pruned = true;
                        self.stop_requested = true;
                        return GateOutcome::Prune;
                    }
                    GateVerdict::Stop => {
                        self.pruned = true;
                        self.stop_requested = true;
                        return GateOutcome::Prune;
                    }
                }
            }
        }

        // **A gate-disabled context has nothing to ask.** §8's guard above
        // still ran — a §8 violation is the user's error in whichever program
        // commits it, and the precheck is the only engine that sees the
        // specification's own graphs from outside the search — but there is no
        // probe worker, no seed and no `Cover` call.
        if self.worker.is_none() {
            self.counters.gate_skipped_disabled += 1;
            return GateOutcome::Continue;
        }

        // **F57: this sits below the gate-disabled return, deliberately.**
        // The inertness test costs one `wobs` walk per fresh event, and its
        // only use is to skip a `cover` call. A gate-disabled context (precheck,
        // triage, oracle) never calls `cover`, so above that return the walk
        // bought nothing: measured at 15–24% of oracle runtime on a one-sender
        // fixture, where the per-gate cost doubled as the graph doubled (F57).
        // Below it, gate-enabled contexts are
        // unaffected — `worker` is fixed at construction (`Some` in `new`,
        // `None` in `gate_disabled`) and never taken — and the published
        // `inert_gates` count comes only from the gate-enabled context.
        //
        // **F42: a fresh gate that changed nothing observable is skipped.**
        //
        // The gate's question is "does some specification graph cover `G₁`?".
        // A **fresh** event added by an *invisible* thread cannot change that
        // answer, and the argument is already written out above `Diagnostic`:
        // such an event is `porf`-**maximal**, so it is the source of no `porf`
        // path between two events that already exist — it therefore adds no
        // `vo` edge between pre-existing visible events, and leaves both the
        // observations and `matches` unchanged.
        //
        // The cheap test for "the fresh event was invisible" is that the
        // **visible observation count did not change**. A fresh visible send
        // or receive contributes exactly one observation and an invisible one
        // none, so the count moves iff the event is visible (`is_visible`).
        // This costs one graph walk,
        // against a whole specification execution for the probe it avoids.
        //
        // **Only the two fresh gates.** `RevisitApply` changes an existing
        // receive's `rf`, which can reorder pre-existing events and is exactly
        // the case the maximality argument does not cover; `Completion` is the
        // gate soundness rests on. Both always run.
        //
        // **What is not closed**, and it is recorded above `Diagnostic` rather
        // than discovered here: §4.1 exempts CToss/Choice revisits from the
        // revisit-apply gate, so after such a pop a replayed prefix carrying
        // visible events is first seen by whichever fresh event gates next.
        // Skipping that gate leaves the prefix unchecked *in this execution* —
        // and it is checked at `Completion`, which always runs, for the same
        // reason F49's skip is sound: **a skip abandons no branch**. That is
        // the whole argument; it is weaker than the unproven implication the
        // `Diagnostic` note flags, and it does not depend on it.
        if matches!(gate, Gate::FreshSend | Gate::FreshRecv) {
            let seen = crate::conformance::obs::wobs(g1, &self.visible)
                .map(|w| self.visible.iter().map(|n| w.of(n).len()).sum::<usize>())
                .ok();
            if let Some(seen) = seen {
                if self.last_visible_obs == Some(seen) {
                    self.inert_gates += 1;
                    self.counters.gate_skipped_inert += 1;
                    return GateOutcome::Continue;
                }
                self.last_visible_obs = Some(seen);
            }
        } else {
            // A revisit or a completion may change what is observed without
            // adding an event, so the cache cannot be trusted across them.
            //
            // **Redundant under `explore`'s current ordering, and kept on
            // purpose** (developer, `P3-F57`, finding 2). An execution runs
            // `begin_execution` (which also clears this cache, F55), then its
            // fresh gates, then `Completion`, then `try_revisit`'s
            // `RevisitApply` gates. So `begin_execution`'s reset always runs
            // before the next fresh gate reads the cache, and deleting this
            // arm alone changes no measured result. It stays so that the
            // cache's soundness does not rest on that ordering: a revisit that
            // is followed by a fresh gate *without* an intervening
            // `begin_execution` would otherwise read a stale count.
            self.last_visible_obs = None;
        }

        let events: usize = g1.thread_ids().into_iter().map(|t| g1.thread_size(t)).sum();

        // The seed is *cloned*, not taken. Taking it left `self.h` empty on
        // every `BudgetExhausted` — which is `Continue`, so the run goes on —
        // and every later gate then paid a full rebuild until the next
        // `Found` (gate-4 review, m2). Sound either way, since O2 says a
        // stale `H` costs a rebuild rather than an answer, but "the cache is
        // silently dropped whenever the search runs out of room" is not what
        // the field's rustdoc leads a reader to expect.
        let seed = self.h.clone();
        self.counters.cover_calls += 1;
        let (answer, cc) = self
            .worker
            .as_ref()
            .expect("conformance: the worker was checked present at the gate-disabled return above")
            .cover(g1, gate.outer_complete(), seed);
        // Counted on every outcome, the aborting call included (gate-4 round
        // 01, m1): `per_cover.len() == cover_calls` holds on aborted runs too.
        self.account_cover(&cc);
        match answer {
            Ok(Cover::Found(h)) => {
                self.h = h;
                GateOutcome::Continue
            }
            Ok(Cover::NoCover) => {
                self.note_report(ReportGate::of(Some(gate)), g1);
                self.reports.push(Report {
                    gate: Some(gate),
                    kind: ReportKind::NoCover,
                    events,
                    graph: g1.clone(),
                    replay: self.snapshot(g1, state, None),
                });
                self.pruned = true;
                if self.stop_at_first_report {
                    self.stop_requested = true;
                }
                GateOutcome::Prune
            }
            // Exhaustion establishes nothing, so it neither reports nor
            // prunes: pruning on it would cut a subtree on the strength of a
            // search that ran out of room (ruling 1: inconclusive, never a
            // report).
            Ok(Cover::BudgetExhausted) => {
                self.exhaustions.push(Exhaustion { gate, events });
                self.counters.cover_exhaustions += 1;
                GateOutcome::Continue
            }
            // Criterion 9: the specification is not assertion-safe. Recorded,
            // the end written **first** (so no later ending overwrites it),
            // the outer run asked to stop, every later gate inert; no report,
            // no prune (`Continue`, since a `Prune` at a fresh gate would
            // `block_exec`). `run` returns `Err` on it.
            Err(ObsError::SpecNotAssertionSafe { thread, pos }) => {
                self.record_end(SearchEnd::SpecNotAssertionSafe);
                self.spec_error = Some((thread, pos));
                self.stop_requested = true;
                GateOutcome::Continue
            }
            // A §8 violation is a user error in **whichever** program committed
            // it, and it is never folded into ⊥. Which program is re-derived
            // here rather than assumed: `Search::done` extracts observations
            // from the *implementation* graph too, so an `ObsError` reaching
            // this arm is as likely to be about `g1` as about a probe's graph.
            // Blaming the specification unconditionally — the developer's F-D
            // — is this project's recurring shape, a `Result` that has lost
            // which side produced it.
            Err(e) => panic!(
                "conformance: the {} program is not a valid input: {e}",
                self.blame_for(g1, &e)
            ),
        }
    }
}
