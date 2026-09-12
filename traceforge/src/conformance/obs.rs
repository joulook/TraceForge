//! What a graph shows of its visible threads.
//!
//! One extractor serves both sides. The implementation and the specification
//! are both ordinary TraceForge programs (`conf-plan.md` §2), so their graphs
//! are the same kind of object and nothing here branches on which side it was
//! called for — a second extractor would quietly reintroduce the domain
//! mapping that ruling removed.
//!
//! The draft (`popl-conf/tex/alg.tex:653-656`) defines the sequence this
//! module computes:
//!
//! > For `t ∈ Tvis` let `wobs_t(G)` be the sequence of observations of the
//! > visible events of `t` in `G`, in program order. A morphism matches the
//! > i-th visible event of `t` in `G₁` with the i-th visible event of `t` in
//! > `G₂`.

use std::collections::BTreeMap;

use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::msg::Val;
use crate::thread::ThreadId;

/// One observation of one visible event.
///
/// A send observes **its value and nothing else** — in particular *not* its
/// destination, which the draft deliberately leaves unobserved (CA §4). The
/// relay example turns on that: a program that forwards a message through an
/// invisible thread must look the same as one that sends it directly, and it
/// cannot if the destination is compared.
///
/// A receive observes the value *of the send it reads*, or ⊥ when it reads
/// nothing.
///
/// There is deliberately **no thread component**, though the draft's
/// observation has one. In the draft a thread identifier is literally the same
/// symbol on both sides — threads are static and every program declares the
/// same visible threads — whereas TraceForge hands out `ThreadId`s per program
/// in spawn order, so the same declared name gets different ids on the two
/// sides whenever their invisible threads differ. Carrying one would make
/// (M1) a function of spawn order. It is safe to drop rather than merely
/// convenient: `wobs` is keyed by thread and the matching relates the i-th
/// event of `t` to the i-th event of `t`, so the component would be equal on
/// both sides of every comparison the algorithm performs. That is a property
/// of the matching — if the matching ever stops being thread-preserving, this
/// reasoning lapses with it.
#[derive(Clone, Debug)]
pub(crate) enum Obs {
    Send(Val),
    /// `None` is ⊥: a receive that read nothing.
    Recv(Option<Val>),
}

impl Obs {
    /// The Rust type of the observed message, for diagnostics only.
    ///
    /// Two programs that use different Rust types for what the user thinks is
    /// one message compare unequal at every position, and without this a
    /// report cannot say why. It is **not** consulted when comparing: at a
    /// position where the two sides genuinely diverge, differing types is an
    /// ordinary non-conformance rather than a usage error, so raising on a
    /// type mismatch would turn real reports into crashes. Surfacing it is a
    /// reporting concern (§7.1), not a comparison one.
    pub(crate) fn type_name(&self) -> Option<&str> {
        match self {
            Obs::Send(v) => Some(v.type_name.as_str()),
            Obs::Recv(v) => v.as_ref().map(|v| v.type_name.as_str()),
        }
    }
}

/// Written out rather than derived, so the value comparison is visibly the
/// engine's own `msg_equals` (that is what `PartialEq for Val` is) and the
/// diagnostic `type_name` visibly takes no part in it.
impl PartialEq for Obs {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Obs::Send(a), Obs::Send(b)) => a == b,
            (Obs::Recv(None), Obs::Recv(None)) => true,
            (Obs::Recv(Some(a)), Obs::Recv(Some(b))) => a == b,
            _ => false,
        }
    }
}

/// A visible thread's row, as the extractor found it.
#[derive(Clone, Debug)]
pub(crate) enum Row {
    /// The name resolved to this thread, and these are its visible events in
    /// program order. The `ThreadId` is kept so that later consumers — (M3),
    /// which needs the row and not just the observations — do not resolve the
    /// name a second time. A second lookup is a second code path, and the two
    /// can disagree: the one in `resolve` refuses an ambiguous name, and a
    /// convenience re-lookup written later would not.
    Resolved(ThreadId, Vec<(Event, Obs)>),
    /// The name resolved to no thread in this graph.
    ///
    /// On a **partial** graph this is the ordinary case of a declared thread
    /// that has not been spawned yet, and it behaves as the empty sequence.
    /// On a **complete** graph it is an error — §8 requires every declared
    /// visible name to be spawned exactly once — and that is where it is
    /// raised, in [`crate::conformance::morphism::statuses`].
    ///
    /// The two cannot be told apart from the graph alone: an unspawned thread
    /// and a misspelled name both have no `ThreadInfo`. So the distinction is
    /// carried here rather than collapsed, and resolved where completeness is
    /// known. Collapsing it to "empty sequence" is the failure this variant
    /// exists to prevent: a lookup bug would then give an empty row on *both*
    /// sides and (M1) would hold vacuously for the thread it lost.
    Unspawned,
}

impl Row {
    /// The observations, with an unspawned thread reading as the empty
    /// sequence — correct on a partial graph, and the only reading (M1)/(M2)
    /// need.
    pub(crate) fn observations(&self) -> &[(Event, Obs)] {
        match self {
            Row::Resolved(_, evs) => evs,
            Row::Unspawned => &[],
        }
    }

    pub(crate) fn is_unspawned(&self) -> bool {
        matches!(self, Row::Unspawned)
    }

    /// The thread this row resolved to, if it resolved.
    pub(crate) fn thread(&self) -> Option<ThreadId> {
        match self {
            Row::Resolved(tid, _) => Some(*tid),
            Row::Unspawned => None,
        }
    }
}

/// `wobs` for every declared visible thread of one graph.
///
/// Keyed by **declared name**, which is what pairs the two sides (§8), never
/// by `ThreadId`.
#[derive(Clone, Debug)]
pub(crate) struct Wobs {
    rows: BTreeMap<String, Row>,
}

impl Wobs {
    pub(crate) fn row(&self, name: &str) -> Option<&Row> {
        self.rows.get(name)
    }

    /// The observation values of `name`, unspawned reading as empty.
    ///
    /// **An absent key also reads as empty**, which is not the same thing and
    /// is a trap: a `visible` list that does not match what this `Wobs` was
    /// built from would then compare equal on both sides and pass vacuously.
    /// Callers comparing two `Wobs` should go through `morphism::rows_for`,
    /// which refuses an absent key; use this only where a missing name is
    /// genuinely indistinguishable from an empty one.
    pub(crate) fn of(&self, name: &str) -> &[(Event, Obs)] {
        self.rows.get(name).map(Row::observations).unwrap_or(&[])
    }

    pub(crate) fn names(&self) -> impl Iterator<Item = &str> {
        self.rows.keys().map(String::as_str)
    }

    pub(crate) fn unspawned(&self) -> impl Iterator<Item = &str> {
        self.rows
            .iter()
            .filter(|(_, r)| r.is_unspawned())
            .map(|(n, _)| n.as_str())
    }
}

/// Resolve a declared visible-thread name to its `ThreadId`.
///
/// Resolution goes through each thread's `ThreadInfo`, **never** by scanning
/// rows for `TCreate` labels — and the difference is not stylistic. `main` is
/// named by a *synthetic* `TCreate` built in `ExecutionGraph::new`, whose
/// position collides with main's own `Begin`, and main's row contains no
/// `TCreate` at all; every spawned thread, by contrast, has a real `TCreate`
/// in its **parent's** row. So a row scan — which is how the engine walks
/// creations elsewhere — finds every thread except the one §8's own worked
/// example declares visible.
///
/// A name matching two threads is an error rather than a silent first-match:
/// §8 requires each declared visible name to be spawned exactly once, and
/// `"main"` is reserved, so a second thread carrying a declared name means the
/// program has broken the precondition positional matching rests on.
///
/// Exposed to S4 under the name `resolve_visible`, which is the only thing
/// §8's spawn-order guard needs from this module — it must not grow a second
/// name-resolution path of its own (S2's one-path rule).
pub(crate) fn resolve_visible(
    graph: &ExecutionGraph,
    name: &str,
) -> Result<Option<ThreadId>, ObsError> {
    resolve(graph, name)
}

fn resolve(graph: &ExecutionGraph, name: &str) -> Result<Option<ThreadId>, ObsError> {
    let mut found = None;
    for tid in graph.thread_ids() {
        if graph.get_thread_tclab(tid).name().as_deref() == Some(name) {
            if found.is_some() {
                return Err(ObsError::AmbiguousName {
                    name: name.to_owned(),
                });
            }
            found = Some(tid);
        }
    }
    Ok(found)
}

/// Something the extractor cannot answer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ObsError {
    /// Two threads carry the same declared visible name.
    AmbiguousName { name: String },
    /// A declared visible name has no thread in a graph where every declared
    /// thread must have one. Raised by `statuses`, not by `wobs` — see
    /// [`Row::Unspawned`].
    NotSpawned { name: String },
}

impl std::fmt::Display for ObsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ObsError::AmbiguousName { name } => write!(
                f,
                "two threads are named `{name}`; a declared visible name must \
                 identify exactly one thread (conf-plan.md §8)"
            ),
            ObsError::NotSpawned { name } => write!(
                f,
                "declared visible thread `{name}` was never spawned in this \
                 complete execution (conf-plan.md §8)"
            ),
        }
    }
}

/// Extract `wobs` for `visible` from `graph`.
///
/// Total on partial graphs: a declared thread that does not yet exist yields
/// [`Row::Unspawned`], which reads as the empty sequence. The inner search
/// calls this repeatedly on partial specification graphs (§5.5), so that
/// totality is a requirement and not a courtesy.
///
/// Recomputed from scratch on every call. §6.1 defers the incremental
/// append-cache deliberately — a revisit invalidates a suffix, and a stale
/// suffix is exactly the kind of wrong answer that would never show itself.
pub(crate) fn wobs(graph: &ExecutionGraph, visible: &[String]) -> Result<Wobs, ObsError> {
    let mut rows = BTreeMap::new();
    for name in visible {
        let row = match resolve(graph, name)? {
            None => Row::Unspawned,
            Some(tid) => Row::Resolved(tid, visible_events(graph, tid)),
        };
        rows.insert(name.clone(), row);
    }
    Ok(Wobs { rows })
}

/// Walk one thread's row in program order, collecting its visible events.
fn visible_events(graph: &ExecutionGraph, tid: ThreadId) -> Vec<(Event, Obs)> {
    let mut out = Vec::new();
    for index in 0..graph.thread_size(tid) as u32 {
        let pos = Event::new(tid, index);
        if let Some(obs) = observe(graph, pos) {
            out.push((pos, obs));
        }
    }
    out
}

/// The observation of one label, or `None` if it is not a visible event.
///
/// The match is exhaustive by variant on purpose. A blanket `_ => None` would
/// make a future `LabelEnum` variant a silent omission from every visible
/// trace; written this way it is a compile error, which is the only form of
/// this check that survives someone else editing the enum.
fn observe(graph: &ExecutionGraph, pos: Event) -> Option<Obs> {
    match graph.label(pos) {
        LabelEnum::SendMsg(slab) => {
            // The engine blanks every send value at the start of every
            // execution (`ExecutionGraph::initialize_for_execution`), and
            // restores them one at a time as each send re-executes. Its own
            // comment says the blanking exists to catch code that assumes a
            // replay already carries values — and an extractor called at a
            // mid-replay gate is exactly such code. The failure would be
            // silent rather than loud: `Val`'s equality is `msg_equals`, so
            // two blanked sends compare *equal* and a blanked one against a
            // real one compares unequal. Hence the assertion; discharging the
            // precondition by argument instead would have to be redone every
            // time a gate moves.
            //
            // This guards only the value *this* send contributes to its own
            // thread's row. The value a **receive** observes comes from the
            // send it reads, on some other row, and is checked separately in
            // the `RecvMsg` arm below — one assertion does not cover both.
            assert!(
                !slab.val().is_pending(),
                "conformance: observed a send at {pos} whose value is still \
                 pending. `wobs` was called before this send was re-executed; \
                 its value was blanked by initialize_for_execution and has not \
                 come back yet (conf-plan.md §6.1)"
            );
            Some(Obs::Send(slab.val().clone()))
        }
        LabelEnum::RecvMsg(rlab) => {
            // A receive observes what it *read*, not anything recorded on
            // itself; `None` is the draft's ⊥. `recv_val` is the accessor
            // that accounts for monitor sends carrying a per-reader value.
            //
            // The same pending-value precondition applies here, and it is a
            // *separate* check rather than a duplicate: the value a receive
            // observes lives on the send it reads, which may sit on any
            // thread — visible or invisible — and is therefore not covered by
            // the assertion on the send arm above. A visible thread with no
            // sends of its own, which is the commonest client shape, would
            // otherwise pass through the extractor without that assertion ever
            // running and observe a blanked value. The message names both
            // positions because the offending event is on another row.
            let val = rlab.rf().map(|rf| match graph.label(rf) {
                LabelEnum::SendMsg(slab) => {
                    let v = slab.recv_val(rlab).clone();
                    assert!(
                        !v.is_pending(),
                        "conformance: the receive at {pos} reads the send at \
                         {rf}, whose value is still pending. `wobs` was called \
                         before that send was re-executed; its value was blanked \
                         by initialize_for_execution and has not come back yet \
                         (conf-plan.md §6.1)"
                    );
                    v
                }
                other => unreachable!("receive at {pos} reads from a {other}, not a send"),
            });
            Some(Obs::Recv(val))
        }

        // Not visible events: bookkeeping, control, and thread lifecycle.
        LabelEnum::Begin(_)
        | LabelEnum::End(_)
        | LabelEnum::TCreate(_)
        | LabelEnum::TJoin(_)
        | LabelEnum::Unique(_)
        | LabelEnum::CToss(_)
        | LabelEnum::Choice(_)
        | LabelEnum::Block(_) => None,

        // Out of conformance scope (§9). These are *not* silently skipped,
        // because `Inbox` in particular is a receive-like event that (M2) can
        // see and (M1) cannot: its `rfs` edges feed `in_porf`, so skipping it
        // would compare two programs across an event that constrains the
        // ordering while contributing no observation — two programs differing
        // only in what a visible thread's `inbox` consumed would become
        // indistinguishable. §9's handler-entry guard is the primary defence
        // and arrives in S4; until then this is the only one.
        LabelEnum::Inbox(_) => unreachable!(
            "conformance: `inbox` at {pos} is outside conformance scope \
             (conf-plan.md §9) and must be rejected at handler entry"
        ),
        LabelEnum::Sample(_) => unreachable!(
            "conformance: `sample` at {pos} is outside conformance scope \
             (conf-plan.md §9) and must be rejected at handler entry"
        ),
        #[cfg(feature = "symbolic")]
        LabelEnum::SymbolicVar(_) | LabelEnum::ConstraintEval(_) => unreachable!(
            "conformance: symbolic execution at {pos} is outside conformance \
             scope (conf-plan.md §9) and must be rejected at handler entry"
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conformance::testing::{names, run_once};
    use crate::thread::main_thread_id;
    use crate::{recv_msg, recv_msg_block, send_msg, thread, Config};

    fn spawn_named<F>(name: &str, f: F) -> thread::JoinHandle<()>
    where
        F: FnOnce() + Send + 'static,
    {
        thread::Builder::new()
            .name(name.to_string())
            .spawn(f)
            .unwrap()
    }

    /// A send observes its value and **not** its destination (CA §4).
    ///
    /// This is the unit form of Ex. relay: the same value sent to two
    /// different threads must look identical, or a program that routes through
    /// an invisible relay could never match one that sends directly.
    ///
    /// To break it: add the destination to `Obs::Send`. This test then fails,
    /// because the two runs send to different threads.
    #[test]
    fn a_send_does_not_observe_its_destination() {
        let direct = run_once(Config::builder().build(), || {
            let sink = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), 1i32);
        });
        let elsewhere = run_once(Config::builder().build(), || {
            let a = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
            });
            let _b = spawn_named("other", || {
                let _: i32 = recv_msg_block();
            });
            // Same value, different destination.
            send_msg(a.thread().id(), 1i32);
        });

        let vis = names(&["main"]);
        let d = wobs(&direct, &vis).unwrap();
        let e = wobs(&elsewhere, &vis).unwrap();
        assert_eq!(d.of("main").len(), 1);
        assert_eq!(
            d.of("main")[0].1,
            e.of("main")[0].1,
            "the destination must not be observed"
        );
    }

    /// A receive observes the value of the send it read.
    #[test]
    fn a_receive_observes_what_it_read() {
        let g = run_once(Config::builder().build(), || {
            let _w = spawn_named("w", || {
                send_msg(main_thread_id(), 7i32);
            });
            let _v: i32 = recv_msg_block();
        });
        let w = wobs(&g, &names(&["main", "w"])).unwrap();
        assert_eq!(w.of("main").len(), 1, "main has one visible event");
        match &w.of("main")[0].1 {
            Obs::Recv(Some(v)) => assert!(v == &Val::new(7i32)),
            other => panic!("expected a receive of 7, got {other:?}"),
        }
    }

    /// A non-blocking receive that reads nothing observes ⊥ — and *is* an
    /// observation, because a `RecvMsg` label exists for it.
    #[test]
    fn a_non_blocking_receive_reading_nothing_observes_bottom() {
        let g = run_once(Config::builder().build(), || {
            let _: Option<i32> = recv_msg();
        });
        let w = wobs(&g, &names(&["main"])).unwrap();
        assert_eq!(w.of("main").len(), 1);
        assert_eq!(w.of("main")[0].1, Obs::Recv(None));
    }

    /// A blocking receive with nothing to read contributes **no** observation,
    /// because the engine installs a `Block` and never a `RecvMsg`.
    ///
    /// This is the (M1) half of Ex. blocking, and it is the case criterion 2's
    /// "⊥ when `rf` is `None`" wording leaves ambiguous: the two situations
    /// differ in whether a receive label exists at all, not in its `rf`.
    /// Contrast with the test above, on the same program shape.
    #[test]
    fn a_blocking_receive_with_nothing_to_read_observes_nothing() {
        let g = run_once(Config::builder().build(), || {
            let _: i32 = recv_msg_block();
        });
        let w = wobs(&g, &names(&["main"])).unwrap();
        assert!(
            w.of("main").is_empty(),
            "a blocked receive is not an observation: {:?}",
            w.of("main")
        );
    }

    /// The blocker from review round 1: the same declared name gets different
    /// `ThreadId`s on the two sides, and (M1) must not notice.
    ///
    /// One run spawns two invisible workers before the visible `"w"`, so `w`
    /// is thread 3 there and thread 1 in the other run. The observations must
    /// be identical.
    ///
    /// To break it: put the `ThreadId` into `Obs` and derive `PartialEq`. This
    /// test fails; no other test in this file does, which is exactly why it
    /// exists.
    #[test]
    fn the_same_name_with_different_thread_ids_observes_the_same() {
        let plain = run_once(Config::builder().build(), || {
            let _w = spawn_named("w", || {
                send_msg(main_thread_id(), 5i32);
            });
            let _v: i32 = recv_msg_block();
        });
        let padded = run_once(Config::builder().build(), || {
            let _x = spawn_named("invisible_one", || {});
            let _y = spawn_named("invisible_two", || {});
            let _w = spawn_named("w", || {
                send_msg(main_thread_id(), 5i32);
            });
            let _v: i32 = recv_msg_block();
        });

        let vis = names(&["w"]);
        let a = wobs(&plain, &vis).unwrap();
        let b = wobs(&padded, &vis).unwrap();

        // The premise: the ids really do differ.
        let ta = a.of("w")[0].0.thread;
        let tb = b.of("w")[0].0.thread;
        assert_ne!(ta, tb, "the test is pointless unless the ids differ");

        assert_eq!(a.of("w").len(), b.of("w").len());
        assert_eq!(a.of("w")[0].1, b.of("w")[0].1);
    }

    /// `"main"` is a declared visible name (§8) and must resolve — **and must
    /// carry a visible event**, or the test passes vacuously: a lookup that
    /// misses `main` returns the empty sequence, and empty equals empty.
    ///
    /// To break it: resolve names by scanning rows for `TCreate` labels
    /// instead of through `ThreadInfo`. Every other test here still passes,
    /// because every other visible thread is spawned; this one fails, because
    /// main's `TCreate` is synthetic and appears in no row.
    #[test]
    fn main_resolves_and_carries_its_events() {
        let g = run_once(Config::builder().build(), || {
            let sink = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), 3i32);
        });
        let w = wobs(&g, &names(&["main"])).unwrap();
        assert!(
            matches!(w.row("main"), Some(Row::Resolved(_, _))),
            "main must resolve, not read as unspawned"
        );
        assert_eq!(
            w.of("main").len(),
            1,
            "main must carry a visible event or this test is vacuous"
        );
    }

    /// A declared thread that does not exist in the graph is marked, not
    /// silently empty — the distinction (M3) later turns into an error.
    #[test]
    fn an_absent_declared_thread_is_marked_unspawned() {
        let g = run_once(Config::builder().build(), || {});
        let w = wobs(&g, &names(&["main", "never_spawned"])).unwrap();
        assert!(w.row("never_spawned").unwrap().is_unspawned());
        assert!(w.of("never_spawned").is_empty());
        assert_eq!(w.unspawned().collect::<Vec<_>>(), vec!["never_spawned"]);
    }

    /// Two threads carrying one declared name breaks the precondition
    /// positional matching rests on, so it is refused rather than resolved to
    /// whichever came first.
    #[test]
    fn a_duplicated_declared_name_is_refused() {
        let g = run_once(Config::builder().build(), || {
            let _a = spawn_named("w", || {});
            let _b = spawn_named("w", || {});
        });
        let err = wobs(&g, &names(&["w"])).unwrap_err();
        assert_eq!(
            err,
            ObsError::AmbiguousName {
                name: "w".to_string()
            }
        );
    }

    /// Extraction at a mid-replay point is refused, on **both** paths.
    ///
    /// This is criterion 2's required test, and it is the one that finds the
    /// gap review round 5 caught: the send-side assertion does not cover a
    /// receive, whose observed value lives on the send it reads — possibly on
    /// an invisible thread. A visible thread with no sends of its own passes
    /// the send arm without ever reaching it.
    ///
    /// No gate is needed to reach the state. `initialize_for_execution` is
    /// exactly what `Must::begin_execution` calls at the start of every
    /// execution, and it is what blanks the values.
    ///
    /// To break it: drop either assertion in `observe`. Without the receive
    /// one, this test's second half stops panicking and the two differing
    /// programs compare *equal* — a lost report with no diagnostic.
    #[test]
    #[should_panic(expected = "reads the send at")]
    fn extracting_a_receive_at_a_mid_replay_point_is_refused() {
        let mut g = run_once(Config::builder().build(), || {
            let _w = spawn_named("w", || {
                send_msg(main_thread_id(), 7i32);
            });
            let _v: i32 = recv_msg_block();
        });
        // main has no sends of its own, so only the receive path can catch it.
        g.initialize_for_execution();
        let _ = wobs(&g, &names(&["main"]));
    }

    /// The send-side half of the same precondition, on a thread that does send.
    #[test]
    #[should_panic(expected = "observed a send at")]
    fn extracting_a_send_at_a_mid_replay_point_is_refused() {
        let mut g = run_once(Config::builder().build(), || {
            let sink = spawn_named("sink", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(sink.thread().id(), 1i32);
        });
        g.initialize_for_execution();
        let _ = wobs(&g, &names(&["main"]));
    }

    /// Invisible threads contribute nothing, however busy they are.
    #[test]
    fn invisible_threads_contribute_nothing() {
        let g = run_once(Config::builder().build(), || {
            let chatty = spawn_named("chatty", || {
                let _: i32 = recv_msg_block();
            });
            send_msg(chatty.thread().id(), 1i32);
        });
        // "chatty" is not declared visible, so only main's row is extracted.
        let w = wobs(&g, &names(&["main"])).unwrap();
        assert_eq!(w.names().collect::<Vec<_>>(), vec!["main"]);
        assert_eq!(w.of("main").len(), 1);
    }
}
