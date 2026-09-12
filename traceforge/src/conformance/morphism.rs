//! Does one graph witness another?
//!
//! The draft's morphism (`popl-conf/tex/ref2.tex`, Def. morph) is a bijection
//! between the visible events of `G₁` and those of `G₂` such that
//!
//! - **(M1)** observations agree,
//! - **(M2)** order is reflected: `⟨φ(e), φ(e')⟩ ∈ vo_{G₂}` implies
//!   `⟨e, e'⟩ ∈ vo_{G₁}`,
//! - **(M3)** statuses agree on `Tvis`.
//!
//! `cor:sound` fixes the sides: `G₁` is the implementation and `G₂` the
//! specification. So (M2) runs from the specification **back** to the
//! implementation — the implementation may order two visible events the
//! specification leaves incomparable, never the reverse. Getting that
//! backwards would pass every easy case and admit real violations, which is
//! why it is stated here rather than left to the reader of the loop.
//!
//! On top of those, `alg.tex` Def. follow gives the form the search actually
//! uses, in which the specification graph may still be *partial*:
//!
//! > `G₂` *follows* `G₁` when `wobs_t(G₂)` is a prefix of `wobs_t(G₁)` for
//! > every `t ∈ Tvis`, and (M2) holds for the pairs φ matches. It *matches*
//! > `G₁` when moreover `wobs_t(G₂) = wobs_t(G₁)` for every `t ∈ Tvis`.
//!
//! Both clauses quantify over `Tvis`, and `wobs_t` is *defined* only there.
//! Comparing over all threads would be false on virtually every real pair,
//! since the two sides need not have the same invisible threads at all.
//!
//! **What §8's visible-thread precondition underwrites here.** §8 requires
//! that the two programs declare the same visible names and that each is
//! spawned exactly once, before the program communicates. That guard is not
//! implemented yet (it belongs to `verify`), and three things in this module
//! rest on it rather than on anything checked locally:
//!
//! 1. the positional matching — the i-th visible event of `t` on one side
//!    corresponds to the i-th on the other only if `t` means the same thread;
//! 2. (M1)'s thread key, since names are what pair the two sides;
//! 3. (M2)'s edge set, because a visible thread spawned *after* its program
//!    has communicated makes its `TCreate` an ordering between visible events
//!    rather than a common ancestor of them (see `vo` and A7).
//!
//! Callers must establish it. Nothing here detects its violation — and note
//! from A7 that even once implemented it would not close item 3: §8's witness
//! constrains *declared visible* names only, so a late-spawned **invisible**
//! thread still contributes a create edge, and it says nothing about `join` at
//! all.
//!
//! This module composes none of that into Φ or `Done`; those belong to the
//! search (S3). Nor does it implement §6.2's suffix-restricted (M2) check,
//! which is an optimisation of the extend path that does not exist here and
//! whose soundness argument (O3) is listed as argued rather than proved.

use std::collections::BTreeMap;

use crate::conformance::obs::{Obs, ObsError, Wobs};
use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::thread::ThreadId;

/// A visible thread's status at a complete execution (CA §3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Status {
    Errored,
    Done,
    Blocked,
}

/// Both sides' rows for one declared name, refusing a name neither `Wobs` was
/// built for.
///
/// The comparison entry points take `visible` as a separate argument from the
/// `Wobs` values, so a caller can pass a list that does not match what was
/// extracted. `Wobs::of` answers the empty slice for an absent key, which
/// would make such a name compare *equal* on both sides and the whole
/// comparison pass vacuously — the same silent-vacuous-pass shape that the
/// `main`-resolution bug had. `statuses` is already loud in this case; these
/// are now loud too.
fn rows_for<'a>(
    spec: &'a Wobs,
    imp: &'a Wobs,
    name: &str,
) -> (&'a [(Event, Obs)], &'a [(Event, Obs)]) {
    let s = spec
        .row(name)
        .unwrap_or_else(|| panic!("conformance: `{name}` is not in the specification's wobs; the declared-visible list does not match what was extracted"));
    let i = imp
        .row(name)
        .unwrap_or_else(|| panic!("conformance: `{name}` is not in the implementation's wobs; the declared-visible list does not match what was extracted"));
    (s.observations(), i.observations())
}

/// (M1) restricted to a prefix: every thread's specification observations are
/// a prefix of the implementation's.
///
/// This is the half of Def. follow the inner search maintains while its graph
/// is still partial.
pub(crate) fn observations_follow(spec: &Wobs, imp: &Wobs, visible: &[String]) -> bool {
    visible.iter().all(|name| {
        let (s, i) = rows_for(spec, imp, name);
        s.len() <= i.len() && s.iter().zip(i).all(|((_, a), (_, b))| a == b)
    })
}

/// (M1) in full: every thread's observations agree exactly.
///
/// Unequal lengths are a clean negative answer, not a truncation — zipping two
/// sequences of different lengths and comparing the overlap is the classic way
/// to accept a specification that simply stopped early, so the length check
/// comes first and is not a formality.
pub(crate) fn observations_match(spec: &Wobs, imp: &Wobs, visible: &[String]) -> bool {
    visible.iter().all(|name| {
        let (s, i) = rows_for(spec, imp, name);
        s.len() == i.len() && s.iter().zip(i).all(|((_, a), (_, b))| a == b)
    })
}

/// The pairs φ relates: the i-th visible event of `t` on each side, for as far
/// as both sides have one.
///
/// Returned as `(implementation event, specification event)`. Where the two
/// rows differ in length the matching is defined on the shorter — which is
/// what Def. follow means by "the pairs φ matches", and is why (M2) is
/// meaningful on a partial specification graph at all.
fn matched_pairs(spec: &Wobs, imp: &Wobs, visible: &[String]) -> Vec<(Event, Event)> {
    let mut pairs = Vec::new();
    for name in visible {
        let (s, i) = rows_for(spec, imp, name);
        for ((se, _), (ie, _)) in s.iter().zip(i) {
            pairs.push((*ie, *se));
        }
    }
    pairs
}

/// `e₁ →vo e₂` in one graph.
///
/// `vo` is `porf` restricted to visible events but computed *through*
/// invisible ones, which is exactly what `ExecutionGraph::in_porf` answers —
/// it walks the real graph, so an ordering that reaches `e₂` from `e₁` only by
/// way of invisible threads is found.
///
/// It must be `in_porf` and not a label's cached clock. `calc_views` builds a
/// label's clock from its *predecessor's* clock plus the predecessor's rf,
/// never its own, so a visible receive's cached clock does not contain the
/// send it reads — precisely the matched pair (M2) asks about. `in_porf`'s
/// `RecvMsg` arm repairs that. Those same lines also make `in_porf(e, e)`
/// true, hence the explicit diagonal exclusion: `vo` is irreflexive, and a
/// reflexive query would make (M2) demand `e →vo e` on the other side.
///
/// Note this relation is strictly larger than the draft's `(po ∪ rf)⁺`,
/// because TraceForge threads are dynamic and the engine records their
/// lifecycle: `in_porf` also follows thread-creation and join edges. Those
/// edges are genuine constraints on the executions the program can produce, so
/// this is the *more* accurate relation rather than a looser one — but the
/// draft's theorems are proved in a model that has no such events, and that
/// transport is unwritten. Recorded as `backlog/algorithm-issues.md` A7, with
/// the owner's ruling outstanding.
fn vo(graph: &ExecutionGraph, a: Event, b: Event) -> bool {
    a != b && graph.in_porf(a, b)
}

/// (M2): every `vo` edge between matched pairs on the specification side pulls
/// back to a `vo` edge on the implementation side.
///
/// Quadratic in the matched pairs, which §6.2 accepts at fragment scale. The
/// suffix-restricted form is S3's.
pub(crate) fn order_is_reflected(
    spec_graph: &ExecutionGraph,
    imp_graph: &ExecutionGraph,
    spec: &Wobs,
    imp: &Wobs,
    visible: &[String],
) -> bool {
    let pairs = matched_pairs(spec, imp, visible);
    for (ie1, se1) in &pairs {
        for (ie2, se2) in &pairs {
            if vo(spec_graph, *se1, *se2) && !vo(imp_graph, *ie1, *ie2) {
                return false;
            }
        }
    }
    true
}

/// Evidence that a graph is a finished execution.
///
/// (M3) is defined only at a complete execution (§6.3 opens "At a complete
/// execution"). Applied to a partial graph it answers *blocked* for every
/// thread that merely has not finished yet — a wrong answer rather than an
/// error, which is the worst shape a precondition violation can take.
///
/// The precondition cannot be checked from the graph alone. Every *spawned*
/// thread that has stopped ends with an `End` or a `Block`, and that much is
/// verified here; but **main never receives an `End` label** (backlog A8), so
/// no graph distinguishes "main returned" from "main is parked mid-execution".
/// Asserting only the checkable half is what let a probe graph — in which main
/// is parked at its first choice point — pass and be reported as *done*
/// (backlog F33).
///
/// So the obligation is moved into the type. A caller cannot reach [`statuses`]
/// without constructing one of these, and each constructor says what evidence
/// it rests on.
#[derive(Clone, Copy)]
pub(crate) struct CompleteExecution<'a> {
    graph: &'a ExecutionGraph,
}

impl<'a> CompleteExecution<'a> {
    /// An implementation graph, at a point where the engine has finished the
    /// execution — the **completion gate's** constructor, and nobody else's.
    ///
    /// The residual obligation, and genuinely the caller's: the gate knows
    /// the execution ended, and the graph cannot say so for main (A8). Naming
    /// it here makes the claim explicit and greppable instead of implicit in
    /// a function's precondition, which is what F33 showed goes unnoticed.
    ///
    /// **It does not close F33 on its own, and is not meant to.** A caller
    /// holding a probe's graph can still reach it and reconstruct the
    /// original defect — review round 2 of `P3-S3-search` did exactly that in
    /// three lines, and found an existing test doing it by accident. No type
    /// can prevent it, because no graph distinguishes "main returned" from
    /// "main is parked". What closes the probe path is
    /// [`crate::conformance::prober::Probed::complete`], which checks the
    /// offer set and cannot be handed a graph those offers did not come from.
    /// **Any probe-derived graph must go through that.**
    #[track_caller]
    pub(crate) fn assume_finished_at_gate(graph: &'a ExecutionGraph) -> Self {
        Self::try_finished(graph).expect("a finished execution has no running spawned thread")
    }

    /// The checkable half on its own: every *spawned* thread has stopped.
    ///
    /// `None` means the graph is provably still running, which a caller can
    /// act on. It does **not** mean the converse — `Some` leaves main's half
    /// on the caller, which is the whole reason this type exists.
    pub(crate) fn try_finished(graph: &'a ExecutionGraph) -> Option<Self> {
        is_complete(graph).then_some(Self { graph })
    }

    pub(crate) fn graph(&self) -> &'a ExecutionGraph {
        self.graph
    }
}

/// (M3): the statuses of the visible threads.
///
/// Takes a [`CompleteExecution`] rather than a graph, because the precondition
/// cannot be recovered from a graph and asserting only its checkable half is
/// what produced F33.
///
/// A declared visible thread with no thread in the graph is an error at this
/// point, where it could not be one during extraction: on a complete execution
/// §8 requires every declared visible name to have been spawned exactly once,
/// so an unresolved name here is either a name that does not exist or a
/// resolution bug — and collapsing it to an empty row would hide both.
pub(crate) fn statuses(
    exec: CompleteExecution<'_>,
    wobs: &Wobs,
    visible: &[String],
) -> Result<BTreeMap<String, Status>, ObsError> {
    let graph = exec.graph();
    let mut out = BTreeMap::new();
    for name in visible {
        // Two different failures, and blaming the user for the first would be
        // wrong: a name that is not a key at all means the caller passed a
        // `visible` list that does not match the one `wobs` was built from —
        // an internal bug — whereas a key present but `Unspawned` means the
        // program really did not spawn a declared visible thread, which is the
        // §8 violation the caller must report.
        let row = wobs.row(name).unwrap_or_else(|| {
            panic!(
                "conformance: `{name}` is not in this wobs; the declared-visible \
                 list does not match what was extracted"
            )
        });
        if row.is_unspawned() {
            return Err(ObsError::NotSpawned { name: name.clone() });
        }
        // The `ThreadId` comes off the row the extractor already resolved.
        // Resolving again here would be a second code path, and the two can
        // disagree — `resolve` refuses an ambiguous name and a convenience
        // re-lookup would not.
        let tid = wobs
            .row(name)
            .and_then(|r| r.thread())
            .expect("checked resolved just above");
        out.insert(name.clone(), status_of(graph, tid));
    }
    Ok(out)
}

/// One thread's status, in the draft's precedence order: errored beats done.
///
/// The scan for a failed assertion covers the **whole row**, and that is
/// load-bearing rather than defensive. `traceforge::assert` installs its
/// `Block(Assert)` without yielding to the scheduler, and thread exit takes no
/// scheduler round-trip either, so a thread can append `End` *after* its
/// failed assertion and the execution still counts as complete — a row reading
/// `… BLK Assert, END`. A rule that looked only at the last label would call
/// that thread *done*, which is exactly the misfire the draft's precedence
/// order exists to prevent. (The engine behaviour itself is filed as F28; this
/// rule is correct before and after any fix, so it does not depend on one.)
///
/// **Departure from §6.3, which says "done if its last label is `End`".**
/// The main thread never gets an `End` label. `handle_tend` has four call
/// sites — `thread.rs:256`, `task.rs:143`, and `future/mod.rs:159` and `:288`
/// — and every one is inside a wrapper around a *spawned* body;
/// `Execution::run` spawns
/// the program's own body as a raw task with no such wrapper, so main's row
/// ends at whatever it did last — a `TCreate`, a `TJoin`, a send. Verified on
/// a real `verify` run, not only in the test harness: `w` ends `BEGIN, END`
/// while main ends `BEGIN, TCREATE, TJOIN`. Read literally, §6.3 therefore
/// classifies main as *blocked* in **every** execution, and `"main"` is the
/// reserved visible name of §8's own worked example.
///
/// So the rule here is *blocked if the last label is a `Block`, else done*,
/// which agrees with §6.3 on every spawned thread — a finished one ends with
/// `End` and a stuck one with `Block` — and gives main the right answer too.
/// It is sound only because (M3) runs exclusively on complete executions: on a
/// partial graph a thread that is merely mid-execution would also fail the
/// `Block` test and be called done. Filed for the owner as a §6.3 correction.
fn status_of(graph: &ExecutionGraph, tid: ThreadId) -> Status {
    let size = graph.thread_size(tid) as u32;
    for index in 0..size {
        if let LabelEnum::Block(blab) = graph.label(Event::new(tid, index)) {
            // A `BlockType` discriminator the compiler does not flag, and one
            // criterion 3's list of four does not name (gate-4 round 3, m3).
            // `ConfPrune` is not `Assert`, so it falls through — right, and
            // load-bearing in both directions: a prune must not make a clean
            // thread look errored, and the blanket `ConfPrune` appended over a
            // §4.4 `Assert` must not hide it, which is why this scans every
            // index instead of reading the last label.
            if matches!(blab.btype(), BlockType::Assert) {
                return Status::Errored;
            }
        }
    }
    match graph.thread_last(tid) {
        Some(LabelEnum::Block(blab)) => match blab.btype() {
            BlockType::Assume | BlockType::Assert | BlockType::Value(_, _) | BlockType::Join(_) => {
                Status::Blocked
            }
            // §6.3 puts a pruned graph outside (M3)'s domain, and this is
            // where the restriction is *checked* rather than assumed: every
            // thread of a pruned graph rests at `Block(ConfPrune)`, so
            // classifying it would report the whole execution `Blocked` — a
            // wrong answer, quietly. S4's gate must not fire on a pruned
            // execution (`conf-plan.md` §4.2, criterion 11).
            //
            // **It is not a complete backstop, and an earlier version of this
            // comment overstated it** (gate-4 round 3, m3). The `Assert` scan
            // above runs over *all* indices and returns `Status::Errored`
            // before this match is reached — so for a thread carrying both a
            // `Block(Assert)` and the blanket `Block(ConfPrune)`, which is
            // exactly §4.4's visible-error case, this arm is pre-empted and
            // stays silent. It fires for any visible thread without an
            // `Assert`, which is the common case, but a §4.4 prune with a
            // single declared visible thread would slip past it.
            BlockType::ConfPrune => unreachable!(
                "conformance: (M3) status extraction reached a pruned graph; \
                 the gate fired on an execution it had already pruned"
            ),
        },
        _ => Status::Done,
    }
}

/// Whether every thread has stopped.
///
/// A *spawned* thread has stopped when its last label is an `End` or a
/// `Block`. **Main is exempt**, because it never receives an `End` at all —
/// see [`status_of`] — so there is no label that marks it finished and no way
/// to distinguish "main returned" from "main is mid-execution" by reading its
/// row. That half of the precondition is therefore the caller's to establish:
/// §6.3 places (M3) at the completion gate, which is reached only when the
/// execution is over.
///
/// This checks the half that *is* checkable rather than asserting nothing,
/// and rather than asserting something false. `EndCondition` is deliberately
/// not consulted: statuses are per-thread and read off the graph, which also
/// insulates conformance from the order-dependent short-circuit recorded as
/// F29.
fn is_complete(graph: &ExecutionGraph) -> bool {
    graph
        .thread_ids()
        .into_iter()
        .filter(|t| *t != crate::thread::main_thread_id())
        .all(|t| {
            match graph.thread_last(t) {
                Some(LabelEnum::End(_)) => true,
                Some(LabelEnum::Block(blab)) => match blab.btype() {
                    // Every `BlockType` is a resting state, `ConfPrune`
                    // included: a thread carrying one cannot take another
                    // step, which is the only question this function asks.
                    //
                    // The domain restriction §6.3 puts on (M3) — status
                    // extraction must never run on a **pruned** graph — is a
                    // different claim, and answering it `false` here would be
                    // the project's recurring defect: a domain error turned
                    // into an answer ("not complete") that a caller would act
                    // on. It is enforced where it can be stated, in
                    // [`status_of`], which panics rather than classifying.
                    BlockType::Assume
                    | BlockType::Assert
                    | BlockType::Value(_, _)
                    | BlockType::Join(_)
                    | BlockType::ConfPrune => true,
                },
                _ => false,
            }
        })
}

/// (M3) proper: do the two sides agree on every visible thread's status?
pub(crate) fn statuses_agree(
    spec_statuses: &BTreeMap<String, Status>,
    imp_statuses: &BTreeMap<String, Status>,
) -> bool {
    spec_statuses == imp_statuses
}

/// Does `Obs`-level and order-level agreement hold for a partial
/// specification graph — the draft's *follows*?
///
/// Composing this with the search's own bookkeeping is S3's job; it is here
/// because the prefix comparison is where a morphism's off-by-one errors live,
/// and it belongs beside the extractor that produces the sequences.
pub(crate) fn follows(
    spec_graph: &ExecutionGraph,
    imp_graph: &ExecutionGraph,
    spec: &Wobs,
    imp: &Wobs,
    visible: &[String],
) -> bool {
    observations_follow(spec, imp, visible)
        && order_is_reflected(spec_graph, imp_graph, spec, imp, visible)
}

/// The draft's *matches*: `follows`, with observations equal rather than a
/// prefix. Still not `Done`, which additionally requires (M3).
pub(crate) fn matches(
    spec_graph: &ExecutionGraph,
    imp_graph: &ExecutionGraph,
    spec: &Wobs,
    imp: &Wobs,
    visible: &[String],
) -> bool {
    observations_match(spec, imp, visible)
        && order_is_reflected(spec_graph, imp_graph, spec, imp, visible)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conformance::obs::wobs;
    use crate::conformance::prober::{install, probe_from};
    use crate::conformance::testing::{names, run_once};
    use crate::thread::main_thread_id;
    use crate::{recv_msg_block, send_msg, thread, Config};

    fn spawn_named<F>(name: &str, f: F) -> thread::JoinHandle<()>
    where
        F: FnOnce() + Send + 'static,
    {
        thread::Builder::new()
            .name(name.to_string())
            .spawn(f)
            .unwrap()
    }

    fn cfg() -> Config {
        Config::builder().build()
    }

    /// main sends `v`; an invisible sink drains it.
    fn one_send(v: i32) -> impl Fn() + Send + Sync + 'static {
        move || {
            let sink = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), v);
        }
    }

    // ---------------------------------------------------------------- (M1)

    /// (M1) holds on identical programs and fails when a value differs.
    ///
    /// To break it: drop the value from `Obs::Send`. The failing half then
    /// passes and this test catches it.
    #[test]
    fn observations_agree_or_do_not() {
        let vis = names(&["main"]);
        let a = run_once(cfg(), one_send(1));
        let b = run_once(cfg(), one_send(1));
        let c = run_once(cfg(), one_send(2));

        let (wa, wb, wc) = (
            wobs(&a, &vis).unwrap(),
            wobs(&b, &vis).unwrap(),
            wobs(&c, &vis).unwrap(),
        );
        assert!(observations_match(&wa, &wb, &vis));
        assert!(!observations_match(&wa, &wc, &vis), "values differ");
    }

    /// The prefix form: shorter-but-agreeing follows, longer does not.
    ///
    /// This is the pair criterion 8 asks for specifically, because the prefix
    /// comparison is where off-by-one errors live. To break it: replace the
    /// length check in `observations_follow` with a `zip` over the overlap —
    /// the second assertion then fails.
    #[test]
    fn a_shorter_spec_follows_and_a_longer_one_does_not() {
        let vis = names(&["main"]);
        let two = run_once(cfg(), || {
            let sink = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), 1i32);
            send_msg(sink.thread().id(), 2i32);
        });
        let one = run_once(cfg(), one_send(1));

        let w_two = wobs(&two, &vis).unwrap();
        let w_one = wobs(&one, &vis).unwrap();

        assert!(
            observations_follow(&w_one, &w_two, &vis),
            "one send is a prefix of two"
        );
        assert!(
            !observations_match(&w_one, &w_two, &vis),
            "a prefix is not a match"
        );
        assert!(
            !observations_follow(&w_two, &w_one, &vis),
            "two sends cannot follow one"
        );
    }

    // ---------------------------------------------------------------- (M2)

    /// (M2) holds between a graph and itself, and `vo` is irreflexive.
    ///
    /// Self-comparison is the tightest possible (M2) and would fail
    /// immediately if the diagonal were not excluded, since every event is
    /// `in_porf`-related to itself.
    #[test]
    fn order_is_reflected_against_itself_and_the_diagonal_is_excluded() {
        let vis = names(&["main"]);
        let g = run_once(cfg(), one_send(1));
        let w = wobs(&g, &vis).unwrap();
        assert!(order_is_reflected(&g, &g, &w, &w, &vis));

        let e = w.of("main")[0].0;
        assert!(!vo(&g, e, e), "vo must be irreflexive");
    }

    /// `vo` finds an order that runs *through* an invisible thread.
    ///
    /// main sends to an invisible relay, the relay forwards to visible `c`.
    /// main's send and `c`'s receive are on different threads with no direct
    /// edge, yet the relay's `rf` chain orders them — which is what "porf
    /// restricted to visible events, computed through invisible ones" means.
    #[test]
    fn vo_runs_through_invisible_paths() {
        let vis = names(&["main", "c"]);
        let g = run_once(cfg(), || {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
            });
            let cid = c.thread().id();
            let relay = spawn_named("relay", move || {
                let v: i32 = recv_msg_block();
                send_msg(cid, v);
            });
            send_msg(relay.thread().id(), 9i32);
        });
        let w = wobs(&g, &vis).unwrap();
        let send = w.of("main")[0].0;
        let recv = w.of("c")[0].0;
        assert!(
            vo(&g, send, recv),
            "main's send must be vo-before c's receive, through the relay"
        );
        assert!(!vo(&g, recv, send), "and not the other way");
    }

    // ------------------------------------------------------- the join gap

    /// Spec joins a visible thread, Impl does not.
    ///
    /// Derived, not asserted. In the joining program `w`'s send precedes
    /// main's send in every execution, so `vo(s_w, s_main)` holds there; in
    /// the non-joining program the two are concurrent, so it does not. (M2)
    /// therefore fails in this direction — and that is the *correct* answer,
    /// because the non-joining program really does admit the order
    /// `[7, 5]` that the joining one cannot produce. See A7.
    #[test]
    fn a_join_on_the_spec_side_is_an_order_the_impl_lacks() {
        let vis = names(&["main", "w"]);
        let joining = run_once(cfg(), || {
            let w = spawn_named("w", || {
                let sink = spawn_named("sink_w", || {
                    let _: i32 = recv_msg_block();
                });
                send_msg(sink.thread().id(), 5i32);
            });
            let _ = w.join();
            let sink = spawn_named("sink_m", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), 7i32);
        });
        let free = run_once(cfg(), || {
            let _w = spawn_named("w", || {
                let sink = spawn_named("sink_w", || {
                    let _: i32 = recv_msg_block();
                });
                send_msg(sink.thread().id(), 5i32);
            });
            let sink = spawn_named("sink_m", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), 7i32);
        });

        let wj = wobs(&joining, &vis).unwrap();
        let wf = wobs(&free, &vis).unwrap();
        assert!(
            observations_match(&wj, &wf, &vis),
            "(M1) holds: same values on both sides"
        );

        let sw = wj.of("w")[0].0;
        let sm = wj.of("main")[0].0;
        assert!(
            vo(&joining, sw, sm),
            "the join orders w's send before main's"
        );
        let fw = wf.of("w")[0].0;
        let fm = wf.of("main")[0].0;
        assert!(!vo(&free, fw, fm), "without the join they are concurrent");

        // spec = joining, impl = free: the spec edge does not pull back.
        assert!(!order_is_reflected(&joining, &free, &wj, &wf, &vis));
        // The other orientation: the impl is more ordered, which (M2) allows.
        assert!(order_is_reflected(&free, &joining, &wf, &wj, &vis));
    }

    /// The shape both early review rounds missed: a join in which **neither**
    /// participant is visible still orders two visible events.
    ///
    /// Invisible `u` joins invisible `w`; `w` has received from visible main,
    /// and after the join `u` sends to visible `c`. So main's send is ordered
    /// before `c`'s receive even though the join touches no visible thread.
    /// This is why A7's resolution (b) has to be "no join at all".
    ///
    /// **The mechanism is `calc_views`, not `in_porf`'s `TJoin` arm**, and the
    /// correction matters because the arm is the natural place to look. A
    /// mutation audit settled it: deleting `in_porf`'s `TJoin` arm fails
    /// nothing in the crate, while deleting `cons.rs::calc_views`'s TEnd fold
    /// (`cons.rs:390`) fails this test and the one above it. `calc_views`
    /// folds the joined thread's clock into the *successor* of the `TJoin`, so
    /// by the time anything a visible event can reach is reached, the cached
    /// clock already carries it. `in_porf`'s arm only fires when the queried
    /// `second` **is** the `TJoin` event — and `vo` is called only on matched
    /// pairs, which are `Obs::Send`/`Obs::Recv` events and never a `TJoin`. It
    /// is therefore unreachable from this module, which is also why no test
    /// here can pin it.
    ///
    /// To break it: make `vo` program-order-only, or drop that `calc_views`
    /// fold.
    #[test]
    fn a_join_between_two_invisible_threads_still_orders_visible_events() {
        let vis = names(&["main", "c"]);
        let g = run_once(cfg(), || {
            let c = spawn_named("c", || {
                let _: i32 = recv_msg_block();
            });
            let cid = c.thread().id();
            let w = spawn_named("w", || {
                let _: i32 = recv_msg_block();
            });
            let wid = w.thread().id();
            let _u = spawn_named("u", move || {
                let _ = w.join();
                send_msg(cid, 1i32);
            });
            send_msg(wid, 4i32);
        });

        let w = wobs(&g, &vis).unwrap();
        let main_send = w.of("main")[0].0;
        let c_recv = w.of("c")[0].0;
        assert!(
            vo(&g, main_send, c_recv),
            "main's send is vo-before c's receive, via u's join of w — a join \
             with no visible participant (A7 resolution (b))"
        );
    }

    // ---------------------------------------------------------------- (M3)

    /// A visible thread that fails an assertion extracts as *errored*, not
    /// *done* — from a real run, because the `… BLK Assert, END` row this
    /// turns on is engine behaviour a hand-built graph would only assume.
    ///
    /// To break it: replace the row scan in `status_of` with a look at the
    /// last label. This test then reports `Done`.
    #[test]
    fn an_asserting_visible_thread_is_errored_not_done() {
        let vis = names(&["w"]);
        let g = run_once(
            Config::builder().with_keep_going_after_error(true).build(),
            || {
                let _w = spawn_named("w", || {
                    crate::assert(false);
                });
            },
        );
        let w = wobs(&g, &vis).unwrap();
        let st = statuses(CompleteExecution::assume_finished_at_gate(&g), &w, &vis).unwrap();
        assert_eq!(st["w"], Status::Errored, "graph:\n{g}");
    }

    /// A visible thread blocked on a receive nothing can satisfy extracts as
    /// *blocked* — the third status, and the one whose TraceForge encoding
    /// least resembles the draft's (which has no block label at all).
    #[test]
    fn a_blocked_visible_thread_is_blocked() {
        let vis = names(&["main", "w"]);
        let g = run_once(cfg(), || {
            let _w = spawn_named("w", || {
                let _: i32 = recv_msg_block();
            });
        });
        let w = wobs(&g, &vis).unwrap();
        let st = statuses(CompleteExecution::assume_finished_at_gate(&g), &w, &vis).unwrap();
        assert_eq!(st["w"], Status::Blocked);
        assert_eq!(st["main"], Status::Done);
    }

    /// (M3) is restricted to `Tvis`: an invisible thread left blocked on one
    /// side and finished on the other must not make the statuses disagree.
    ///
    /// Its only assertion is a *positive* one — that two things agree — which
    /// is the shape that goes vacuous silently, so the difference it is
    /// supposed to be ignoring is checked rather than assumed: asked over a
    /// name list that includes the hidden threads, the two sides really do
    /// disagree.
    ///
    /// **What actually breaks it, from the mutation audit**: only removing
    /// `is_complete`'s `main` exemption, which breaks nearly every (M3) test
    /// here. The restriction itself is enforced by `statuses`'s signature —
    /// it iterates `visible` and can see nothing else — so "compare statuses
    /// over all threads", which this comment used to name, is not a mutation
    /// of this module at all. The non-vacuity control below is what gives the
    /// test teeth; `adversarial::m3_ignores_invisible_threads` states the same
    /// property on a different program.
    #[test]
    fn invisible_thread_statuses_do_not_affect_m3() {
        let vis = names(&["main"]);
        let blocked_invisible = run_once(cfg(), || {
            let _stuck = spawn_named("stuck", || {
                let _: i32 = recv_msg_block();
            });
        });
        let finished_invisible = run_once(cfg(), || {
            let _fine = spawn_named("fine", || {});
        });

        let a = wobs(&blocked_invisible, &vis).unwrap();
        let b = wobs(&finished_invisible, &vis).unwrap();
        let sa = statuses(
            CompleteExecution::assume_finished_at_gate(&blocked_invisible),
            &a,
            &vis,
        )
        .unwrap();
        let sb = statuses(
            CompleteExecution::assume_finished_at_gate(&finished_invisible),
            &b,
            &vis,
        )
        .unwrap();
        assert!(
            statuses_agree(&sa, &sb),
            "invisible threads must not enter (M3): {sa:?} vs {sb:?}"
        );

        // Not vacuous: asked over a list that *does* name them, the two hidden
        // threads really do have different statuses. Without this the test
        // would still pass if they were both `Done` — that is, if there were
        // nothing for the restriction to be excluding.
        let hidden_status = |g: &ExecutionGraph, n: &str| {
            let list = names(&[n]);
            statuses(
                CompleteExecution::assume_finished_at_gate(g),
                &wobs(g, &list).unwrap(),
                &list,
            )
            .unwrap()[n]
        };
        assert_eq!(hidden_status(&blocked_invisible, "stuck"), Status::Blocked);
        assert_eq!(hidden_status(&finished_invisible, "fine"), Status::Done);
    }

    /// (M3)'s **failing** case — the draft's Ex. blocking, and the reason
    /// (M3) exists at all.
    ///
    /// Two programs whose visible observations are identical (both empty) but
    /// whose visible thread ends differently: one blocked on a receive nothing
    /// can satisfy, the other finished. (M1) cannot tell them apart, because a
    /// blocked receive contributes no observation. (M3) must.
    ///
    /// To break it: compare only (M1), or drop the `Block` arm from
    /// `status_of`. This test then reports agreement.
    #[test]
    fn statuses_disagree_when_one_side_blocks_and_the_other_finishes() {
        let vis = names(&["main", "w"]);
        let blocks = run_once(cfg(), || {
            let _w = spawn_named("w", || {
                let _: i32 = recv_msg_block();
            });
        });
        let finishes = run_once(cfg(), || {
            let _w = spawn_named("w", || {});
        });

        let wb = wobs(&blocks, &vis).unwrap();
        let wf = wobs(&finishes, &vis).unwrap();

        // (M1) is blind to the difference: neither side observes anything.
        assert!(
            observations_match(&wb, &wf, &vis),
            "both sides have empty visible traces"
        );

        let sb = statuses(
            CompleteExecution::assume_finished_at_gate(&blocks),
            &wb,
            &vis,
        )
        .unwrap();
        let sf = statuses(
            CompleteExecution::assume_finished_at_gate(&finishes),
            &wf,
            &vis,
        )
        .unwrap();
        assert_eq!(sb["w"], Status::Blocked);
        assert_eq!(sf["w"], Status::Done);
        assert!(
            !statuses_agree(&sb, &sf),
            "(M3) must separate a blocked visible thread from a finished one"
        );
    }

    /// A declared visible thread that was never spawned is an error at (M3),
    /// where completeness makes it detectable — not the empty row that
    /// extraction has to return on a partial graph.
    #[test]
    fn a_never_spawned_visible_thread_is_an_error_at_m3() {
        let vis = names(&["main", "ghost"]);
        let g = run_once(cfg(), || {});
        let w = wobs(&g, &vis).unwrap();
        assert_eq!(
            statuses(CompleteExecution::assume_finished_at_gate(&g), &w, &vis).unwrap_err(),
            crate::conformance::obs::ObsError::NotSpawned {
                name: "ghost".to_string()
            }
        );
    }

    /// A finished execution's graph, and the same graph with one *spawned*
    /// thread's final label removed so its row ends mid-execution.
    ///
    /// Both halves are needed together: the first is the positive control that
    /// this program really does produce a witness, so the second's refusal is
    /// attributable to the missing label and not to anything else about the
    /// program.
    fn whole_and_running() -> (ExecutionGraph, ExecutionGraph) {
        let vis = names(&["main", "w"]);
        let g = run_once(cfg(), || {
            let sink = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
            });
            let sid = sink.thread().id();
            let w = spawn_named("w", move || {
                send_msg(sid, 1i32);
            });
            let _ = w.join();
        });
        let w = wobs(&g, &vis).unwrap();
        let wid = w.of("w")[0].0.thread;

        // Drop w's End, leaving its row ending on its send: still running.
        let mut partial = g.clone();
        partial.remove_last(wid);
        assert!(
            matches!(partial.thread_last(wid), Some(LabelEnum::SendMsg(_))),
            "the premise: w's row must now end on a label that is neither End \
             nor Block, or this fixture is testing nothing"
        );
        (g, partial)
    }

    /// (M3)'s completeness precondition is now a type, not an assertion.
    ///
    /// A graph with a spawned thread still running cannot produce a
    /// `CompleteExecution`, so `statuses` is unreachable for it — the refusal
    /// is a value the caller must handle rather than a panic it might not
    /// provoke.
    ///
    /// To break it: make `is_complete` return `true` unconditionally, or drop
    /// its `_ => false` arm. Removing the `main` exemption breaks it too, in
    /// the other direction — the positive control then fails.
    #[test]
    fn a_graph_with_a_running_spawned_thread_yields_no_witness() {
        let (whole, partial) = whole_and_running();
        assert!(CompleteExecution::try_finished(&whole).is_some());
        assert!(
            CompleteExecution::try_finished(&partial).is_none(),
            "a running spawned thread must not witness completeness"
        );
    }

    /// The gate constructor's own half of the same refusal: it does not
    /// silently accept what `try_finished` rejects.
    ///
    /// `assume_finished_at_gate` names main's residual obligation as the
    /// caller's, but it is not a blank cheque — the *checkable* half is still
    /// enforced, by a panic, because at the completion gate a running spawned
    /// thread is an internal inconsistency rather than a caller's choice to
    /// handle.
    ///
    /// Written because a mutation audit found nothing anywhere in the crate
    /// that fails when the `expect` is replaced by `unwrap_or(Self { graph })`:
    /// every other call site passes a graph that really is finished, so the
    /// panic was unreachable in testing and could have been deleted unnoticed.
    /// The expected message is matched in full rather than merely asserting
    /// *some* panic, since any assertion inside the fixture would otherwise
    /// satisfy the test.
    #[test]
    #[should_panic(expected = "a finished execution has no running spawned thread")]
    fn the_completion_gate_refuses_a_running_spawned_thread_loudly() {
        let (_whole, partial) = whole_and_running();
        let _ = CompleteExecution::assume_finished_at_gate(&partial);
    }

    /// main parks at its send; `w` is spawned with an empty body and finishes.
    fn parks_main_at_a_send() {
        let _w = spawn_named("w", || {});
        send_msg(main_thread_id(), 1i32);
    }

    /// **F33, fixed** — and the A/B that says *what* fixed it.
    ///
    /// A probe graph leaves main parked mid-execution, and no graph can say so:
    /// main never gets an `End` label (A8), so the spawned-thread check passes
    /// on it. Before the witness type, such a graph passed the completeness
    /// assertion and `statuses` reported main as *done*.
    ///
    /// The two halves run the **same program** and differ only in whether the
    /// probe still has an offer outstanding:
    ///
    /// - parked at its send, one offer → `complete()` refuses, while
    ///   `try_finished` on that same graph accepts. The refusal is therefore
    ///   the offer set's doing, not the spawned-thread check's.
    /// - install that offer, re-probe, no offers → `complete()` answers
    ///   `Some`, and main is *done* for real this time.
    ///
    /// The second half is why this is not a restatement of
    /// `adversarial::m3_no_longer_reports_a_parked_main_as_done`: without it,
    /// `Probed::complete()` returning `None` unconditionally passes both.
    ///
    /// To break it: drop the `!offers.is_empty()` guard and the first half
    /// fails (F33 is back); make `complete()` always answer `None` and the
    /// second fails.
    #[test]
    fn a_probe_with_offers_outstanding_yields_no_witness() {
        let probed = probe_from(cfg(), ExecutionGraph::default(), parks_main_at_a_send);
        assert_eq!(
            probed.offers().len(),
            1,
            "main should have parked at its send"
        );
        assert_eq!(probed.offers()[0].pos().thread, main_thread_id());

        // The checkable half alone would have let it through — which is
        // precisely how F33 happened.
        assert!(
            CompleteExecution::try_finished(probed.graph()).is_some(),
            "the spawned-thread check passes, so it is not what saves us"
        );
        assert!(
            probed.complete().is_none(),
            "a probe with offers outstanding is not a complete execution"
        );

        // The other side of the A/B: install the one offer and re-probe. Same
        // program, same spawned-thread check, no offers left — and now the
        // witness exists and main really is done.
        let (offers, graph) = probed.into_parts();
        let graph = install(cfg(), graph, &offers[0]);
        let exhausted = probe_from(cfg(), graph, parks_main_at_a_send);
        assert!(
            exhausted.offers().is_empty(),
            "main's send was installed, so nothing is left to decide: {:?}",
            exhausted
                .offers()
                .iter()
                .map(|o| o.kind())
                .collect::<Vec<_>>()
        );

        let vis = names(&["main", "w"]);
        let w = wobs(exhausted.graph(), &vis).unwrap();
        let exec = exhausted
            .complete()
            .expect("an exhausted probe is a complete execution");
        assert_eq!(statuses(exec, &w, &vis).unwrap()["main"], Status::Done);
    }

    /// Main extracts as *done*, which §6.3's literal rule would get wrong.
    ///
    /// To break it: restore §6.3's wording — `Some(End(_)) => Done, _ =>
    /// Blocked`. Main then reports `Blocked` in every execution and this test
    /// catches it; no other status test does, because every other visible
    /// thread here is spawned and really does end with `End`.
    #[test]
    fn main_is_done_even_though_it_has_no_end_label() {
        let vis = names(&["main"]);
        let g = run_once(cfg(), one_send(1));
        let w = wobs(&g, &vis).unwrap();

        // The premise: main really has no End.
        assert!(
            !matches!(g.thread_last(main_thread_id()), Some(LabelEnum::End(_))),
            "the test is pointless if main ends with End"
        );
        let st = statuses(CompleteExecution::assume_finished_at_gate(&g), &w, &vis).unwrap();
        assert_eq!(st["main"], Status::Done, "graph:\n{g}");
    }
}
