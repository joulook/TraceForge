//! Running probe executions.
//!
//! One *probe* runs a program once, in probe mode, and returns the choice
//! points it reached. See [`super::probe`] for what probe mode does to the
//! engine; this module is the driver.
//!
//! A probe is a single forward execution — there is no exploration loop, no
//! revisit queue, and no second iteration. Whatever the program does before
//! every thread parks, blocks or finishes is the whole of it.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::probe::Offer;
use crate::event::Event;
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::runtime::execution::Execution;
use crate::runtime::thread::continuation::{ContinuationPool, CONTINUATION_POOL};
use crate::Config;

/// Clears the thread's current-`Must` pointer when it goes out of scope.
///
/// A probe sets that pointer and must clear it, including when the probe
/// panics — and panicking is a *designed* path here, because probing a program
/// that uses an operation outside conformance scope is a hard error. Without
/// this, a rejected probe would leave the pointer dangling for whatever runs
/// next on the same thread.
struct CurrentMustGuard;

impl Drop for CurrentMustGuard {
    fn drop(&mut self) {
        Must::set_current(None);
    }
}

/// Run `f` once in probe mode and return the choice points it reached.
///
///
/// The offers come back in the order the probe reached them, which depends on
/// the schedule: `main` runs first under the default left-to-right policy, so
/// its choice point is recorded before a spawned thread's even though the
/// spawn happened earlier. Tests here assert that order because it is stable
/// for a fixed policy, but only the *set* is meaningful to the search — every
/// thread is run until it parks, so which offers exist does not depend on the
/// order they were collected in.
///
/// This runs the program on the calling thread. Calling it from inside another
/// execution would nest two runtimes in one thread's scoped state; the
/// conformance search will therefore own a dedicated OS thread for probing.
pub(crate) fn probe_once<F>(config: Config, f: F) -> Vec<Offer>
where
    F: Fn() + Send + Sync + 'static,
{
    probe_from(config, ExecutionGraph::default(), f).0
}

/// Probe `f` against an existing partial graph.
///
/// The events already in `graph` are replayed — the handlers recognise them by
/// position and feed back what they recorded — and each thread parks at the
/// first choice point *past* that prefix. Returns those offers together with
/// the graph as the probe left it: the prefix plus whatever forced bookkeeping
/// the threads performed on the way (thread creation, `Begin`/`End`, channel
/// creation, a `Block` for a receive with nothing to read). Those are not
/// choices, so installing them is not a decision.
pub(crate) fn probe_from<F>(
    config: Config,
    graph: ExecutionGraph,
    f: F,
) -> (Vec<Offer>, ExecutionGraph)
where
    F: Fn() + Send + Sync + 'static,
{
    let must = Rc::new(RefCell::new(Must::with_initial_graph(config, graph)));
    must.borrow_mut().enable_probe();
    Must::set_current(Some(Rc::clone(&must)));
    let _guard = CurrentMustGuard;

    let f = Arc::new(f);
    CONTINUATION_POOL.set(&ContinuationPool::new(), || {
        let execution = Execution::new(Rc::clone(&must));
        Must::begin_execution(&must);
        let f = Arc::clone(&f);
        execution.run(move || f());
    });

    // No park may outlive the probe: one that does means a handler recorded an
    // offer and its API path returned to user code instead of suspending.
    assert!(
        !must.borrow().probe_park_pending(),
        "probe ended with an unconsumed park: some API path reached a \
         choice-point handler without suspending its thread"
    );
    let offers = must.borrow_mut().probe_take_offers();
    let graph = must.borrow_mut().take_graph();
    (offers, graph)
}

/// The concrete sends a receive offer could read.
///
/// This is the same enumeration the offer already carries in
/// [`Offer::sources`], recomputed from a graph; it exists so a caller holding
/// only a graph can ask. It reports **sends only**: whether the receive may
/// instead read nothing is not a property of the graph but of the receive, and
/// is carried by [`Offer::may_read_nothing`]. An empty result therefore means
/// "no send is available", which for a blocking receive means the thread is
/// not enabled and for a non-blocking one leaves ⊥ as its single option.
///
/// Computed on a copy of the graph, so asking changes nothing.
pub(crate) fn recv_sources(config: Config, graph: &ExecutionGraph, offer: &Offer) -> Vec<Event> {
    let mut scratch = Must::with_initial_graph(config, graph.clone());
    scratch.probe_recv_sources(offer.label().clone())
}

/// Extend a graph with one offer the search has chosen.
///
/// The offer's label is installed at the position it would have occupied, so
/// the next probe replays it as part of the prefix and the program continues
/// from just after it.
pub(crate) fn install(config: Config, graph: ExecutionGraph, offer: &Offer) -> ExecutionGraph {
    let mut must = Must::with_initial_graph(config, graph);
    must.probe_install(offer.label().clone());
    must.take_graph()
}

/// Extend a graph with a receive offer, reading from `rf`.
///
/// `None` is the receive reading nothing, which only a non-blocking receive
/// may do.
pub(crate) fn install_recv(
    config: Config,
    graph: ExecutionGraph,
    offer: &Offer,
    rf: Option<Event>,
) -> ExecutionGraph {
    let mut must = Must::with_initial_graph(config, graph);
    let pos = must.probe_install(offer.label().clone());
    must.probe_set_rf(pos, rf);
    must.take_graph()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::loc::CommunicationModel;
    use crate::thread::main_thread_id;
    use crate::{recv_msg, recv_msg_block, send_msg, thread};
    use std::sync::atomic::{AtomicBool, Ordering};

    fn two_senders() {
        let _a = thread::spawn(|| {
            send_msg(main_thread_id(), 1i32);
        });
        let _b = thread::spawn(|| {
            send_msg(main_thread_id(), 2i32);
        });
    }

    /// Every thread parks at its first enabled choice point, one offer each.
    #[test]
    fn probe_records_one_offer_per_thread() {
        let offers = probe_once(Config::builder().build(), two_senders);
        let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
        assert_eq!(kinds, vec!["send", "send"], "offers: {offers:?}");
        assert_ne!(offers[0].pos().thread, offers[1].pos().thread);
    }

    fn send_then_recv() {
        let _t = thread::spawn(|| {
            send_msg(main_thread_id(), 1i32);
        });
        let _v: i32 = recv_msg_block();
    }

    /// A blocking receive with nothing to read is **not** a choice point.
    ///
    /// It is not enabled, so the specification thread cannot take that step;
    /// offering it would tell the search a step exists that the semantics does
    /// not allow. The receive becomes a `Block` in the graph instead, which is
    /// also what records the thread as blocked rather than finished.
    #[test]
    fn a_blocking_receive_with_no_source_is_not_offered() {
        let (offers, _graph) = probe_from(
            Config::builder().build(),
            ExecutionGraph::default(),
            send_then_recv,
        );
        let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
        assert_eq!(kinds, vec!["send"], "offers: {offers:?}");
    }

    /// A *non-blocking* receive is enabled even with nothing to read, because
    /// reading nothing is one of its options.
    #[test]
    fn a_non_blocking_receive_is_offered_and_may_read_nothing() {
        let offers = probe_once(Config::builder().build(), || {
            let _v: Option<i32> = recv_msg();
        });
        assert_eq!(offers.len(), 1, "offers: {offers:?}");
        assert_eq!(offers[0].kind(), "recv");
        assert!(offers[0].sources().is_empty());
        assert!(offers[0].may_read_nothing());
    }

    static RAN_PAST_CHOICE_POINT: AtomicBool = AtomicBool::new(false);

    /// The property the whole mechanism rests on: a probe records what the
    /// program *would* do next and stops there. If user code ran on past the
    /// choice point it would be running on a value the probe invented, and the
    /// offers would no longer describe the program's next step.
    #[test]
    fn probe_does_not_run_user_code_past_a_choice_point() {
        RAN_PAST_CHOICE_POINT.store(false, Ordering::SeqCst);

        let offers = probe_once(Config::builder().build(), || {
            let _b = crate::nondet();
            RAN_PAST_CHOICE_POINT.store(true, Ordering::SeqCst);
        });

        assert_eq!(offers.len(), 1);
        assert_eq!(offers[0].kind(), "nondet");
        assert!(
            !RAN_PAST_CHOICE_POINT.load(Ordering::SeqCst),
            "user code ran after the parked choice point"
        );
    }

    static RAN_PAST_TYPED_NONDET: AtomicBool = AtomicBool::new(false);

    /// The same property for `<bool>::nondet()`, the spelling the crate's own
    /// documentation recommends. It reaches the same handler by a different
    /// path, and an unhooked path hands the program a fabricated value.
    #[test]
    fn probe_does_not_run_user_code_past_a_typed_nondet() {
        RAN_PAST_TYPED_NONDET.store(false, Ordering::SeqCst);

        let offers = probe_once(Config::builder().build(), || {
            let _b = <bool as crate::TypeNondet>::nondet();
            RAN_PAST_TYPED_NONDET.store(true, Ordering::SeqCst);
        });

        assert_eq!(offers.len(), 1);
        assert_eq!(offers[0].kind(), "nondet");
        assert!(
            !RAN_PAST_TYPED_NONDET.load(Ordering::SeqCst),
            "user code ran after the parked choice point"
        );
    }

    fn two_sends() {
        send_msg(main_thread_id(), 1i32);
        send_msg(main_thread_id(), 2i32);
    }

    /// Probe, install, probe: the loop the conformance search runs on.
    ///
    /// The first probe can only see the program's first choice point, because
    /// the thread parks there. Installing that offer puts it in the graph, so
    /// the next probe replays it and the thread carries on to the *next*
    /// choice point. Advancing the program is therefore done by extending the
    /// graph, never by resuming a suspended execution.
    #[test]
    fn probe_install_probe_advances_the_program() {
        let config = Config::builder().build();

        let (first, graph) = probe_from(config.clone(), ExecutionGraph::default(), two_sends);
        assert_eq!(first.len(), 1, "only the first send is offered: {first:?}");

        let graph = install(config.clone(), graph, &first[0]);

        let (second, _) = probe_from(config, graph, two_sends);
        assert_eq!(
            second.len(),
            1,
            "only the second send is offered: {second:?}"
        );
        assert_eq!(
            second[0].pos().index,
            first[0].pos().index + 1,
            "the second probe should reach the next event of the same thread"
        );
    }

    /// An installed send is replayed by the next probe rather than offered
    /// again — and it also *enables* the receive that had nothing to read.
    #[test]
    fn installing_a_send_enables_the_receive_that_was_blocked() {
        let config = Config::builder().build();

        let (first, graph) = probe_from(config.clone(), ExecutionGraph::default(), send_then_recv);
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].kind(), "send");

        let graph = install(config.clone(), graph, &first[0]);

        let (second, graph) = probe_from(config.clone(), graph, send_then_recv);
        let kinds: Vec<_> = second.iter().map(|o| o.kind()).collect();
        assert_eq!(kinds, vec!["recv"], "offers: {second:?}");
        assert_eq!(second[0].sources().len(), 1, "the installed send");
        assert!(!second[0].may_read_nothing(), "a blocking receive");

        // Choosing it completes the program: nothing is left to decide.
        let rf = second[0].sources()[0];
        let graph = install_recv(config.clone(), graph, &second[0], Some(rf));
        let (third, _) = probe_from(config, graph, send_then_recv);
        assert!(third.is_empty(), "offers: {third:?}");
    }

    fn two_senders_one_recv() {
        let _a = thread::spawn(|| {
            send_msg(main_thread_id(), 1i32);
        });
        let _b = thread::spawn(|| {
            send_msg(main_thread_id(), 2i32);
        });
        let _v: i32 = recv_msg_block();
    }

    /// A receive offers every send it could read, from the checker's own
    /// enumeration, so the search inherits the delivery semantics of the
    /// communication model rather than inventing its own.
    #[test]
    fn a_receive_offers_its_available_sources() {
        let config = Config::builder().build();

        let (first, graph) = probe_from(
            config.clone(),
            ExecutionGraph::default(),
            two_senders_one_recv,
        );
        let kinds: Vec<_> = first.iter().map(|o| o.kind()).collect();
        assert_eq!(kinds, vec!["send", "send"], "offers: {first:?}");

        let graph = install(config.clone(), graph, &first[0]);
        let graph = install(config.clone(), graph, &first[1]);

        let (second, graph) = probe_from(config.clone(), graph, two_senders_one_recv);
        assert_eq!(second.len(), 1);
        assert_eq!(second[0].kind(), "recv");
        assert_eq!(second[0].sources().len(), 2, "both sends are available");

        // The standalone enumeration agrees with the offer's.
        let sources = recv_sources(config, &graph, &second[0]);
        assert_eq!(sources, second[0].sources());
    }

    fn spawn_join_send() {
        let t = thread::spawn(|| 7i32);
        let _ = t.join();
        send_msg(main_thread_id(), 1i32);
    }

    /// A thread blocked on a join must be freed within the same probe once the
    /// thread it waits for finishes, and go on to its next choice point.
    ///
    /// Getting this wrong is not a missing optimisation: a probe that returned
    /// no offers here would tell the search the specification is stuck, and
    /// the search would report a conformance violation that does not exist.
    #[test]
    fn a_join_is_released_within_the_same_probe() {
        let offers = probe_once(Config::builder().build(), spawn_join_send);
        let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
        assert_eq!(kinds, vec!["send"], "offers: {offers:?}");
    }

    static RAN_PAST_NAMED_NONDET: AtomicBool = AtomicBool::new(false);

    /// `named_nondet` is the third spelling of a boolean choice, and the one
    /// the tokio compatibility layer uses throughout. Review round 1 found it
    /// unhooked; this pins it.
    #[test]
    fn probe_does_not_run_user_code_past_a_named_nondet() {
        RAN_PAST_NAMED_NONDET.store(false, Ordering::SeqCst);

        let offers = probe_once(Config::builder().build(), || {
            let _b = crate::named_nondet("probe-test");
            RAN_PAST_NAMED_NONDET.store(true, Ordering::SeqCst);
        });

        assert_eq!(offers.len(), 1);
        assert_eq!(offers[0].kind(), "nondet");
        assert!(
            !RAN_PAST_NAMED_NONDET.load(Ordering::SeqCst),
            "user code ran after the parked choice point"
        );
    }

    /// Operations outside conformance scope are refused, loudly. Probing a
    /// program that uses one would otherwise commit a choice the search never
    /// sees — `inbox` picks a subset and queues revisits.
    #[test]
    #[should_panic(expected = "outside conformance scope")]
    fn probing_an_out_of_scope_operation_is_refused() {
        let _ = probe_once(Config::builder().build(), || {
            let _msgs = crate::inbox();
        });
    }

    /// Re-probing a graph without installing anything changes nothing: the
    /// same offers, and a genuinely blocked thread still ends its row with the
    /// `Block` that records it as blocked.
    ///
    /// This is what lets the search ask the same question twice — and what
    /// keeps a blocked thread's status readable off the graph rather than
    /// having to be remembered separately.
    #[test]
    fn re_probing_an_unchanged_graph_is_idempotent() {
        let config = Config::builder().build();

        let (first, graph) = probe_from(config.clone(), ExecutionGraph::default(), send_then_recv);
        let first_kinds: Vec<_> = first.iter().map(|o| o.kind()).collect();
        let before = format!("{graph}");

        let (second, graph2) = probe_from(config, graph, send_then_recv);
        let second_kinds: Vec<_> = second.iter().map(|o| o.kind()).collect();
        let after = format!("{graph2}");

        assert_eq!(first_kinds, second_kinds, "offers changed on a re-probe");
        assert_eq!(before, after, "the graph changed on a re-probe");

        // The blocked thread's *last* label is its Block: status is readable
        // from the graph, not remembered elsewhere.
        let blocked_last = graph2
            .thread_ids()
            .into_iter()
            .filter_map(|t| graph2.thread_last(t))
            .any(|lab| matches!(lab, crate::event_label::LabelEnum::Block(_)));
        assert!(
            blocked_last,
            "the blocked receive should still end its thread's row:\n{after}"
        );
    }

    /// A config outside conformance scope is refused when probe mode is
    /// enabled, not when some later operation happens to notice.
    ///
    /// `conf-plan.md` §9 calls this constructor-side check "the guarantee",
    /// because a `Config` can reach a `Must` without passing the builder's
    /// validation.
    #[test]
    #[should_panic(expected = "mailbox is out of scope")]
    fn probing_under_an_out_of_scope_config_is_refused() {
        let config = Config::builder()
            .with_cons_type(crate::ConsType::Mailbox)
            .build();
        let _ = probe_once(config, || {});
    }

    /// The config check tests the *model*, so the deprecated `MO` spelling is
    /// caught too — it maps to `TotalOrder` just as `Mailbox` does, and
    /// checking the enum variant alone would have missed it.
    #[test]
    #[should_panic(expected = "mailbox is out of scope")]
    fn the_deprecated_mailbox_spelling_is_also_refused() {
        #[allow(deprecated)]
        let config = Config::builder()
            .with_cons_type(crate::ConsType::MO)
            .build();
        let _ = probe_once(config, || {});
    }

    /// A channel carries its own communication model, which no config check
    /// can see. `conf-plan.md` §9 asks for a handler-entry guard for exactly
    /// this case: a default (in-scope) config with an out-of-scope channel.
    #[test]
    #[should_panic(expected = "outside conformance scope")]
    fn an_out_of_scope_channel_is_refused_under_an_in_scope_config() {
        let _ = probe_once(Config::builder().build(), || {
            let (tx, _rx) = crate::channel::Builder::<i32>::new()
                .with_comm(CommunicationModel::TotalOrder)
                .build();
            tx.send_msg(1);
        });
    }

    /// The *receive* half of the same guard, which until now was derived from
    /// the `comm` plumbing rather than executed. Nothing is ever sent, so the
    /// send guard cannot be what fires.
    #[test]
    #[should_panic(expected = "a TotalOrder (mailbox) receive")]
    fn an_out_of_scope_channel_is_refused_on_the_receive_side_too() {
        let _ = probe_once(Config::builder().build(), || {
            let (_tx, rx) = crate::channel::Builder::<i32>::new()
                .with_comm(CommunicationModel::TotalOrder)
                .build();
            let _ = rx.recv_msg();
        });
    }

    /// Probe mode is specified for asyn/p2p/cd (`conf-plan.md` §1), but every
    /// other test here runs under the default config, which is `FIFO`/p2p.
    /// These cover the other two: a probe must offer the same two sends under
    /// each, because which sends are *enabled* does not depend on the
    /// delivery model — only which ones a receive may read does.
    #[test]
    fn probing_works_under_the_other_in_scope_models() {
        for cons in [crate::ConsType::Bag, crate::ConsType::Causal] {
            let config = Config::builder().with_cons_type(cons).build();
            let offers = probe_once(config, two_senders);
            let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
            assert_eq!(kinds, vec!["send", "send"], "under {cons:?}: {offers:?}");
        }
    }

    /// Branching on a symbolic constraint is a choice point outside
    /// conformance scope (`conf-plan.md` §1), and `handle_constraint_eval`
    /// rejects it ahead of its replay branch. Creating the variable is *not*
    /// rejected: that is forced bookkeeping, not a choice.
    #[test]
    #[cfg(feature = "symbolic")]
    #[should_panic(expected = "symbolic constraint evaluation")]
    fn a_symbolic_branch_is_refused() {
        let _ = probe_once(Config::builder().build(), || {
            let b = crate::symbolic::fresh_bool();
            let _ = crate::symbolic::eval(b);
        });
    }

    /// A rejected probe still clears the thread's current-`Must` pointer.
    ///
    /// Rejection is a panic, and panicking is a designed path here, so the
    /// [`CurrentMustGuard`] must run on unwind — otherwise the next thing to
    /// run on this thread inherits a dangling pointer to the probe's `Must`.
    #[test]
    fn a_rejected_probe_leaves_no_current_must() {
        let attempt = std::panic::catch_unwind(|| {
            let _ = probe_once(Config::builder().build(), || {
                let (tx, _rx) = crate::channel::Builder::<i32>::new()
                    .with_comm(CommunicationModel::TotalOrder)
                    .build();
                tx.send_msg(1);
            });
        });
        assert!(
            attempt.is_err(),
            "the out-of-scope probe should have been rejected"
        );
        assert!(
            Must::current().is_none(),
            "a rejected probe left its Must installed on this thread"
        );
    }

    /// Deterministic bookkeeping is not a choice point: a program that only
    /// spawns and joins offers nothing and still terminates.
    #[test]
    fn probe_of_a_choice_free_program_offers_nothing() {
        let offers = probe_once(Config::builder().build(), || {
            let t = thread::spawn(|| 7i32);
            let _ = t.join();
        });
        assert!(offers.is_empty(), "offers: {offers:?}");
    }
}
