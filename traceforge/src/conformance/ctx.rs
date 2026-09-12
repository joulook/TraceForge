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

use crate::conformance::obs::{resolve_visible, ObsError};
use crate::conformance::search::{Cover, Search};
use crate::event::Event;
use crate::event_label::{AsEventLabel, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::Config;

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
#[derive(Clone, Debug)]
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
        }
    }
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
/// §9 rejections and its own failed assertions arrive. Before this, such a
/// panic killed the worker thread, dropped the sender, and surfaced on the
/// calling thread as `RecvError`: §9 requires an "outside conformance scope"
/// error *naming the event*, and the user got "the probe worker died
/// mid-search" (gate-4 review, M1). That is F-C's defect one layer out — a
/// failure turned into a different failure that has lost its origin, at the
/// one boundary S4 introduced.
type Answer = Result<Result<Cover, ObsError>, Box<dyn std::any::Any + Send>>;

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
                        search.cover(&job.g1, job.complete, job.seed)
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
    ) -> Result<Cover, ObsError> {
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
            // specification program's §9 rejection or failed assertion reaches
            // the caller as itself rather than as a channel error.
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
    worker: ProbeWorker,
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
}

impl ConfCtx {
    pub(crate) fn new(
        config: Config,
        spec: Arc<dyn Fn() + Send + Sync>,
        visible: Vec<String>,
        budget: usize,
    ) -> Self {
        let search = Search::new(config, spec, visible.clone(), budget);
        Self {
            worker: ProbeWorker::new(search),
            visible,
            h: ExecutionGraph::default(),
            reports: Vec::new(),
            exhaustions: Vec::new(),
            diagnostics: Vec::new(),
            pruned: false,
        }
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

    /// End the probe worker. Called where the conformance run ends; `Drop` is
    /// the backstop for every other way out.
    pub(crate) fn shutdown(&mut self) {
        self.worker.shutdown();
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
    }

    /// The revisit-apply gate pruned, so the alternative is abandoned before
    /// it ever runs and the latch must not carry into the next pop.
    pub(crate) fn abandon_revisit(&mut self) {
        self.pruned = false;
    }

    /// §4.4: record a visible thread's failed assertion and prune.
    pub(crate) fn report_visible_error(
        &mut self,
        thread: String,
        pos: Event,
        events: usize,
    ) -> GateOutcome {
        if self.pruned {
            return GateOutcome::Continue;
        }
        self.reports.push(Report {
            gate: None,
            kind: ReportKind::VisibleError { thread, pos },
            events,
        });
        self.pruned = true;
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
    pub(crate) fn gate(&mut self, gate: Gate, g1: &ExecutionGraph) -> GateOutcome {
        if self.pruned {
            return GateOutcome::Continue;
        }

        // **No consistency check runs here, deliberately** (criterion 2, and
        // gate-4 review m4: the criterion says leaving this unstated is not
        // acceptable). F38 records that the consistency checker contributes
        // nothing under this fragment — `is_consistent` is vacuous in scope —
        // so calling it would add cost and decide nothing, and a graph it
        // happened to reject would have its conformance verdict silently
        // skipped. `Cover` carries the whole weight.
        //
        // §8's precondition, checked rather than assumed. A violation is the
        // *user's* mistake in the implementation program, not a conformance
        // verdict, so it is raised loudly and is never folded into ⊥ — the
        // same rule `ObsError` follows in the search.
        if let Err(e) = check_spawn_order(g1, &self.visible) {
            panic!("conformance: {e}");
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
        match self.worker.cover(g1, gate.outer_complete(), seed) {
            Ok(Cover::Found(h)) => {
                self.h = h;
                GateOutcome::Continue
            }
            Ok(Cover::NoCover) => {
                self.reports.push(Report {
                    gate: Some(gate),
                    kind: ReportKind::NoCover,
                    events,
                });
                self.pruned = true;
                GateOutcome::Prune
            }
            // Exhaustion establishes nothing, so it neither reports nor
            // prunes: pruning on it would cut a subtree on the strength of a
            // search that ran out of room.
            Ok(Cover::BudgetExhausted) => {
                self.exhaustions.push(Exhaustion { gate, events });
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
