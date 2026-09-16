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

use crate::conformance::morphism::CompleteExecution;
use crate::conformance::probe::{NondetValue, Offer};
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
    probe_from(config, ExecutionGraph::default(), f)
        .offers()
        .to_vec()
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
pub(crate) fn probe_from<F>(config: Config, graph: ExecutionGraph, f: F) -> Probed
where
    F: Fn() + Send + Sync + 'static,
{
    let must = Rc::new(RefCell::new(Must::with_initial_graph(config, graph)));
    must.borrow_mut().enable_probe();
    Must::set_current(Some(Rc::clone(&must)));
    let _guard = CurrentMustGuard;

    let f = Arc::new(f);
    // **The pool is drained explicitly, and it must be** (F50).
    //
    // `Drop for ContinuationPool` deliberately does *not* free its stacks: it
    // runs from a thread-local destructor, and freeing means resuming each
    // continuation, which reads the generator crate's own thread-local —
    // forbidden during TLS destruction on Linux. So it marks them unreusable
    // and returns; the `ManuallyDrop` generator, and its `mmap`ed stack, are
    // never released.
    //
    // **The mechanism is the plain one, and an earlier version of this comment
    // got it wrong** (gate 3). It said the leak happened "because `probe_park`
    // is `loop { switch() }` — a parked thread never finishes, so its
    // `PooledContinuation` is never returned to the pool". That is false, and
    // it is self-refuting: if the continuations were never *in* the pool,
    // `drain_and_free` — which frees only what is in it — could not fix
    // anything. `Execution::cleanup` (`runtime/execution.rs:293-308`) calls
    // `cancel_gen()` then `reinitialize_generator()` on every unfinished task,
    // which marks it reusable, so `PooledContinuation::drop` does return it.
    //
    // The real mechanism: **one pool per `probe_from` call, dropped without
    // draining, once per search node.**
    // `Search::cover` probes once per node, so the mappings accumulate until
    // `mmap` fails with `ENOMEM` **at 394 MB RSS** — not memory exhaustion
    // but `vm.max_map_count`, measured at 63,196 mappings against a limit of
    // 65,530.
    //
    // `drain_and_free` is the path that exists for exactly this, and it was
    // called from `parallel_verify.rs` alone. It is called here inside the
    // scope, during normal execution, which is its documented precondition.
    let pool = ContinuationPool::new();
    CONTINUATION_POOL.set(&pool, || {
        let execution = Execution::new(Rc::clone(&must));
        Must::begin_execution(&must);
        let f = Arc::clone(&f);
        execution.run(move || f());
        pool.drain_and_free();
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
    Probed { offers, graph }
}

/// What one probe produced: the offers, and the graph the probe left behind.
///
/// The graph is the probe's **output** — the prefix it replayed plus whatever
/// forced bookkeeping the threads performed, including the `End` and `Block`
/// labels that (M3) reads. It is not the graph that went in.
///
/// The two are kept together deliberately. `CompleteExecution` is obtainable
/// from a probe only when the probe offered nothing — an empty offer set is
/// exactly `next_Spec(G) = ∅` — and if the offers could be supplied
/// separately from the graph, an empty slice paired with any graph at all
/// would reconstruct backlog F33 verbatim: a graph whose `main` is parked,
/// witnessed complete, and reported *done*. A caller cannot fabricate the
/// pairing because only `probe_from` builds one of these.
pub(crate) struct Probed {
    offers: Vec<Offer>,
    graph: ExecutionGraph,
}

impl Probed {
    pub(crate) fn offers(&self) -> &[Offer] {
        &self.offers
    }

    pub(crate) fn graph(&self) -> &ExecutionGraph {
        &self.graph
    }

    /// Witness this graph complete, if the probe is exhausted.
    ///
    /// `None` means the probe still had offers, so some thread of the program
    /// can take another step and the execution is not over. This is a real
    /// check rather than an assertion, and it is the specification side's
    /// answer to F33 — `Done`'s own `next_Spec(G) = ∅` conjunct, computed
    /// once, here, rather than a second time by different means.
    pub(crate) fn complete(&self) -> Option<CompleteExecution<'_>> {
        if !self.offers.is_empty() {
            return None;
        }
        CompleteExecution::try_finished(&self.graph)
    }

    /// Split the pair. **Test-only**: the one non-test caller that wanted
    /// this discards the graph, so nothing in the shipping path needs the two
    /// halves apart, and keeping them together is what stops an empty offer
    /// slice being paired with an arbitrary graph.
    #[cfg(test)]
    pub(crate) fn into_parts(self) -> (Vec<Offer>, ExecutionGraph) {
        (self.offers, self.graph)
    }
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

/// Extend a graph with one **send** offer the search has chosen.
///
/// The offer's label is installed at the position it would have occupied, so
/// the next probe replays it as part of the prefix and the program continues
/// from just after it.
///
/// A send is the only offer this is complete for, because a send carries no
/// decision: §5.2's install is "the parked label, plus the decision as a
/// frontier-event operation", and a send has none. A receive needs its source
/// ([`install_recv`]) and a nondet needs its value ([`install_nondet`]).
///
/// **Both are refused rather than accepted-and-defaulted**, and the reason is
/// worth stating. A nondet label carries the value the *probe* rolled, and
/// that roll comes from the config's seed — which `ConfigBuilder` defaults to
/// `rand::rng().next_u64()`. Installing a nondet through here would therefore
/// take a **uniformly random** option, silently, and the conformance verdict
/// would vary run to run. That is worse than the "always take the first
/// option" failure F35 describes, because it presents as flakiness rather
/// than as a readable bug. Found by the developer's adversarial pass (O-3),
/// before any search existed to make the mistake.
pub(crate) fn install(config: Config, graph: ExecutionGraph, offer: &Offer) -> ExecutionGraph {
    assert_eq!(
        offer.kind(),
        "send",
        "conformance: `install` takes a send offer; a {} offer carries a \
         decision and must go through {} (conf-plan.md §5.2)",
        offer.kind(),
        match offer.kind() {
            "recv" => "`install_recv`",
            "nondet" | "choice" => "`install_nondet`",
            _ => "the operation for its kind",
        }
    );
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
    // The decision must be one the offer actually made available, and the two
    // ways it can fail to be are both silent — developer finding O-4, the same
    // species as O-3 and with a worse failure mode.
    //
    // `rf = None` on a *blocking* receive is ⊥ for a receive that cannot read
    // nothing: the resulting graph shows `RECV() [TIMEOUT]`, a behaviour the
    // program does not have, and re-probing it does not terminate (the
    // developer killed a run at 600s). A hang is what a caller sees, with
    // nothing pointing at the cause.
    //
    // A source the offer did not list is one the checker's own enumeration
    // said this receive cannot consistently read — the analogue of a `Choice`
    // value outside its range, which `probe_set_value` already refuses.
    //
    // `search.rs`'s `rf_options` builds exactly the admissible set, so no
    // caller trips either today. That is the point: before this, the
    // invariant lived only in the caller.
    match rf {
        None => assert!(
            offer.may_read_nothing(),
            "conformance: cannot install ⊥ on the blocking receive at {}; it \
             must read one of its {} source(s), and a receive that reads \
             nothing here is a behaviour the program does not have",
            offer.pos(),
            offer.sources().len()
        ),
        Some(src) => assert!(
            offer.sources().contains(&src),
            "conformance: {src} is not among the sources offered for the \
             receive at {}; the checker's enumeration says this receive cannot \
             consistently read it",
            offer.pos()
        ),
    }
    let mut must = Must::with_initial_graph(config, graph);
    let pos = must.probe_install(offer.label().clone());
    must.probe_set_rf(pos, rf);
    must.take_graph()
}

/// Extend a graph with a nondeterministic offer, taking `value`.
///
/// The third of `conf-plan.md` §5.2's install operations, and the one S1
/// originally omitted (backlog F35). Without it the search cannot branch on a
/// nondet's values at all: it would have to accept whatever value the probe
/// happened to produce, which is "always take the first option" and loses
/// completeness — a specification that conforms only on the second value
/// would be reported as violating.
///
/// `value` must be one of [`Offer::nondet_values`]; installing anything else
/// panics, since a value outside a `Choice`'s range is one the program could
/// never have produced.
pub(crate) fn install_nondet(
    config: Config,
    graph: ExecutionGraph,
    offer: &Offer,
    value: NondetValue,
) -> ExecutionGraph {
    let mut must = Must::with_initial_graph(config, graph);
    let pos = must.probe_install(offer.label().clone());
    must.probe_set_value(pos, value);
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
        )
        .into_parts();
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

        let (first, graph) =
            probe_from(config.clone(), ExecutionGraph::default(), two_sends).into_parts();
        assert_eq!(first.len(), 1, "only the first send is offered: {first:?}");

        let graph = install(config.clone(), graph, &first[0]);

        let (second, _) = probe_from(config, graph, two_sends).into_parts();
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

        let (first, graph) =
            probe_from(config.clone(), ExecutionGraph::default(), send_then_recv).into_parts();
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].kind(), "send");

        let graph = install(config.clone(), graph, &first[0]);

        let (second, graph) = probe_from(config.clone(), graph, send_then_recv).into_parts();
        let kinds: Vec<_> = second.iter().map(|o| o.kind()).collect();
        assert_eq!(kinds, vec!["recv"], "offers: {second:?}");
        assert_eq!(second[0].sources().len(), 1, "the installed send");
        assert!(!second[0].may_read_nothing(), "a blocking receive");

        // Choosing it completes the program: nothing is left to decide.
        let rf = second[0].sources()[0];
        let graph = install_recv(config.clone(), graph, &second[0], Some(rf));
        let (third, _) = probe_from(config, graph, send_then_recv).into_parts();
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
        )
        .into_parts();
        let kinds: Vec<_> = first.iter().map(|o| o.kind()).collect();
        assert_eq!(kinds, vec!["send", "send"], "offers: {first:?}");

        let graph = install(config.clone(), graph, &first[0]);
        let graph = install(config.clone(), graph, &first[1]);

        let (second, graph) = probe_from(config.clone(), graph, two_senders_one_recv).into_parts();
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

        let (first, graph) =
            probe_from(config.clone(), ExecutionGraph::default(), send_then_recv).into_parts();
        let first_kinds: Vec<_> = first.iter().map(|o| o.kind()).collect();
        let before = format!("{graph}");

        let (second, graph2) = probe_from(config, graph, send_then_recv).into_parts();
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

    /// Lines in `/proc/self/maps`, which is one per `mmap`ed region.
    ///
    /// The count, not the byte total, is the quantity F50 is about: the probe
    /// died with `ENOMEM` at a peak RSS of 394 MB, which is nowhere near
    /// exhaustion and is instead the signature of `vm.max_map_count` — 65,530
    /// on this machine, against 63,196 mappings measured in the failing run.
    #[cfg(target_os = "linux")]
    fn mapping_count() -> usize {
        std::fs::read_to_string("/proc/self/maps")
            .expect("/proc/self/maps is readable on Linux")
            .lines()
            .count()
    }

    /// **A probe frees the coroutine stacks it allocated** (F50).
    ///
    /// `Drop for ContinuationPool` deliberately does not free its stacks — it
    /// runs from a thread-local destructor, and freeing means resuming a
    /// continuation, which reads the generator crate's own thread-local, which
    /// Linux forbids during TLS destruction. `drain_and_free` is the path that
    /// exists for exactly that, and until this fix `probe_from` did not call
    /// it. `Search::cover` probes once per search node, so the mappings
    /// accumulated until `mmap` refused.
    ///
    /// **Measured**, 200 probes of a three-thread program, alone in a process:
    ///
    /// | | mappings gained |
    /// |---|---|
    /// | with `drain_and_free` | **0** |
    /// | without it (mutation) | **1200** |
    ///
    /// Six per probe: three threads, two mappings each (stack and guard page).
    ///
    /// # Why it runs in a child process, and it has to
    ///
    /// The first version of this measured `/proc/self/maps` around the loop in
    /// the ordinary test thread. It passed under `--test-threads=1` and
    /// **failed on every run under the default parallel harness**, which is
    /// how the suite is normally invoked — and the failure was not the probe's.
    /// `/proc/self/maps` is process-wide, so the window also counts whatever
    /// the other ~350 conformance tests allocate on their own threads
    /// meanwhile. Measured, with the *fix in place* and the loop asserting
    /// nothing: the process gained **1998, 1988 and 2090** mappings across
    /// three runs of that window, against a true probe contribution of 0.
    ///
    /// Most of that ambient figure is real leakage from elsewhere and is a
    /// finding in its own right (see the developer's S7-fixes report:
    /// `conformance::testing::run_once` and `lib.rs`'s `explore` create a
    /// `ContinuationPool` per call and never drain it, at six mappings a call)
    /// — but none of it is attributable to `probe_from`, and a test that
    /// cannot tell the two apart measures the harness rather than the code.
    ///
    /// So the loop runs in a **fresh child process** with `--test-threads=1`
    /// and nothing else in it, where `/proc/self/maps` does mean what the
    /// measurement needs it to mean. The child is
    /// [`f50_probe_loop_child`], `#[ignore]`d so it runs only when named.
    ///
    /// **Mutation, MEASURED**: delete `pool.drain_and_free()` from
    /// `probe_from` and this test fails, surfacing the child's own assertion
    /// (`200 probes gained 1200 mappings`). The same mutation leaves the whole
    /// `--lib` suite green (363 passed either way) and kills
    /// `bench::two_pc_scaling` with
    /// `failed to alloc sys stack: ENOMEM` from `generator`'s `stack/mod.rs`:
    /// the leak costs nothing but resources until it costs everything.
    ///
    /// Linux-only, because `/proc/self/maps` is. On another platform the
    /// property is untested rather than asserted vacuously.
    #[test]
    #[cfg(target_os = "linux")]
    fn a_probe_frees_its_coroutine_stacks() {
        const CHILD: &str = "conformance::prober::tests::f50_probe_loop_child";

        let exe = std::env::current_exe().expect("the test binary knows its own path");
        let out = std::process::Command::new(exe)
            .args(["--exact", CHILD, "--ignored", "--test-threads=1"])
            .output()
            .expect("re-running this test binary for one ignored test");

        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);

        // A filter that matches nothing also exits 0, which would be a silent
        // pass. The child must say it ran exactly one test.
        assert!(
            stdout.contains("1 passed") || stdout.contains("1 failed"),
            "the child did not run {CHILD}; filter or name drift.\n\
             --- child stdout ---\n{stdout}\n--- child stderr ---\n{stderr}"
        );
        assert!(
            out.status.success(),
            "the probe leaked coroutine stacks (F50).\n\
             --- child stdout ---\n{stdout}\n--- child stderr ---\n{stderr}"
        );
    }

    /// The loop [`a_probe_frees_its_coroutine_stacks`] runs in a child process.
    ///
    /// `#[ignore]`d so that it runs **only** when named, which is what keeps
    /// the measurement alone in its process; running it in the ordinary
    /// parallel suite is exactly the thing that made the first version of this
    /// test fail for reasons that had nothing to do with the probe.
    #[test]
    #[ignore = "F50: measured in a child process by a_probe_frees_its_coroutine_stacks"]
    #[cfg(target_os = "linux")]
    fn f50_probe_loop_child() {
        const WARMUP: usize = 10;
        const PROBES: usize = 200;
        // Six mappings per leaked probe, so 1200 is the leaking figure; 100 is
        // two orders of magnitude inside it and still absorbs an allocator
        // taking a fresh arena during the window.
        const BOUND: usize = 100;

        for _ in 0..WARMUP {
            let _ = probe_once(Config::builder().build(), two_senders);
        }
        let before = mapping_count();
        for _ in 0..PROBES {
            let _ = probe_once(Config::builder().build(), two_senders);
        }
        let after = mapping_count();

        let delta = after.saturating_sub(before);
        assert!(
            delta < BOUND,
            "{PROBES} probes gained {delta} mappings ({before} -> {after}). A probe \
             leaking its stacks gains about six per probe; `probe_from` is not \
             calling `ContinuationPool::drain_and_free` (F50)"
        );
    }

    /// **F51's two unmeasured sites**: `testmode::test` and `exec_pool`'s
    /// worker loop.
    ///
    /// The lead measured `lib.rs`'s `explore` (0 mappings gained over 100
    /// `verify` calls, 800 with the drain removed) and **read** the other
    /// two. Reading a `drain_and_free` call is not the same as establishing
    /// that the stacks come back: `exec_pool`'s call sits after the worker
    /// loop exits, on a thread the measuring thread does not own, and
    /// `testmode`'s sits after a `CONTINUATION_POOL.set` whose pool is shared
    /// across every sample. Either could be on a path the run does not take,
    /// and `/proc/self/maps` is the only witness that settles it.
    ///
    /// **Measured**, this tree, 2026-09-16 (developer's P3-skips pass), each
    /// loop alone in a child process:
    ///
    /// | site | loop | mappings gained, fixed | with the drain deleted |
    /// |---|---|---|---|
    /// | `testmode::test` | 100 calls x 4 samples | **0** | **600** |
    /// | `exec_pool::worker_loop` | 50 parallel `verify` calls, 2 workers | **0** | **300** |
    ///
    /// Six per leaked `test` call — three threads, two mappings each (stack
    /// and guard page), one pool however many samples the call took — and six
    /// per leaked parallel `verify` call across its two workers. The zero is
    /// literal: both children pass with `BOUND` set to 1. `BOUND` is left at
    /// 100 rather than 1 so that an allocator taking a fresh arena inside the
    /// window cannot turn a correct run red; that is two orders of magnitude
    /// inside the leaking figure.
    ///
    /// Both run in a fresh
    /// child process with `--test-threads=1`, for the reason
    /// [`a_probe_frees_its_coroutine_stacks`] gives at length:
    /// `/proc/self/maps` is process-wide, so measured in the ordinary parallel
    /// harness the window also counts what the other ~350 conformance tests
    /// allocate meanwhile, and the ambient figure (~2000 mappings) swamps the
    /// true contribution.
    ///
    /// Linux-only, because `/proc/self/maps` is.
    #[test]
    #[cfg(target_os = "linux")]
    fn the_remaining_pool_sites_free_their_coroutine_stacks() {
        for child in [
            "conformance::prober::tests::f51_testmode_child",
            "conformance::prober::tests::f51_exec_pool_child",
        ] {
            let exe = std::env::current_exe().expect("the test binary knows its own path");
            let out = std::process::Command::new(exe)
                .args(["--exact", child, "--ignored", "--test-threads=1"])
                .output()
                .expect("re-running this test binary for one ignored test");
            let stdout = String::from_utf8_lossy(&out.stdout);
            let stderr = String::from_utf8_lossy(&out.stderr);
            // A filter that matches nothing also exits 0, which would be a
            // silent pass. The child must say it ran exactly one test.
            assert!(
                stdout.contains("1 passed") || stdout.contains("1 failed"),
                "the child did not run {child}; filter or name drift.\n\
                 --- child stdout ---\n{stdout}\n--- child stderr ---\n{stderr}"
            );
            assert!(
                out.status.success(),
                "{child} reported leaked coroutine stacks (F51).\n\
                 --- child stdout ---\n{stdout}\n--- child stderr ---\n{stderr}"
            );
        }
    }

    /// `testmode::test` shares **one** pool across all its samples and drains
    /// it once at the end, so the leaking figure is per *call*, not per
    /// sample: six mappings — three threads, two mappings each (stack and
    /// guard page) — however many samples the call took.
    ///
    /// **Mutation, MEASURED**: delete `pool.drain_and_free()` from
    /// `testmode::test` and this child fails; the figures are in the report
    /// for task `P3-skips-dev`.
    #[test]
    #[ignore = "F51: measured in a child process by the_remaining_pool_sites_free_their_coroutine_stacks"]
    #[cfg(target_os = "linux")]
    fn f51_testmode_child() {
        const WARMUP: usize = 5;
        const CALLS: usize = 100;
        // Six mappings per leaked call, so 600 is the leaking figure; 100 is
        // well inside it and still absorbs an allocator taking a fresh arena.
        const BOUND: usize = 100;

        for _ in 0..WARMUP {
            let _ = crate::test(Config::builder().build(), two_senders, 4);
        }
        let before = mapping_count();
        for _ in 0..CALLS {
            let _ = crate::test(Config::builder().build(), two_senders, 4);
        }
        let after = mapping_count();

        let delta = after.saturating_sub(before);
        assert!(
            delta < BOUND,
            "{CALLS} `test` calls gained {delta} mappings ({before} -> {after}). A \
             call leaking its pool gains about six; `testmode::test` is not \
             calling `ContinuationPool::drain_and_free` (F51)"
        );
    }

    /// `exec_pool`'s worker loop drains the pool it owns, **on the worker
    /// thread**, after the loop exits.
    ///
    /// The measurement has a precondition the other two do not: the workers
    /// must have finished before `/proc/self/maps` is read, or the drain has
    /// simply not happened yet and a passing run would mean nothing.
    /// `ExecutionPool::explore` returning is what establishes it — it joins
    /// its workers — so the count is taken strictly after the `verify` call
    /// returns, and never inside one.
    ///
    /// The leaking figure is per *worker* per `verify` call, so it scales with
    /// the machine; the bound is set against the smallest leak that could
    /// occur (one worker, six mappings a call) rather than against this
    /// machine's core count.
    ///
    /// **Mutation, MEASURED**: delete `continuation_pool.drain_and_free()`
    /// from `worker_loop` and this child fails; the figures are in the report
    /// for task `P3-skips-dev`.
    #[test]
    #[ignore = "F51: measured in a child process by the_remaining_pool_sites_free_their_coroutine_stacks"]
    #[cfg(target_os = "linux")]
    fn f51_exec_pool_child() {
        const WARMUP: usize = 5;
        const CALLS: usize = 50;
        const BOUND: usize = 100;

        let cfg = || {
            Config::builder()
                .with_parallel(true)
                .with_parallel_workers(2)
                .build()
        };
        for _ in 0..WARMUP {
            let _ = crate::verify(cfg(), two_senders);
        }
        let before = mapping_count();
        for _ in 0..CALLS {
            let _ = crate::verify(cfg(), two_senders);
        }
        let after = mapping_count();

        let delta = after.saturating_sub(before);
        assert!(
            delta < BOUND,
            "{CALLS} parallel `verify` calls gained {delta} mappings ({before} -> \
             {after}). A worker leaking its pool gains about six per call per \
             worker; `exec_pool::worker_loop` is not calling \
             `ContinuationPool::drain_and_free` (F51)"
        );
    }

    /// The same 200 probes answer the same thing every time.
    ///
    /// `drain_and_free` resumes each pooled continuation with `Exit` and drops
    /// its generator, which is a real operation on the engine's state rather
    /// than a deallocation the compiler could elide. So the claim that F50's
    /// fix "changes resource use and not verdicts" needs an assertion, and the
    /// cheapest honest one is that the offers are identical across a run long
    /// enough for the leak to have mattered.
    ///
    /// The `--lib` suite passing identically with and without the fix (363
    /// passed both ways) is the broader version of the same check; this one
    /// pins it at the probe.
    #[test]
    fn draining_the_pool_does_not_change_what_a_probe_offers() {
        let first = probe_once(Config::builder().build(), two_senders);
        let first: Vec<_> = first.iter().map(|o| (o.kind(), o.pos())).collect();
        for i in 0..200 {
            let again = probe_once(Config::builder().build(), two_senders);
            let again: Vec<_> = again.iter().map(|o| (o.kind(), o.pos())).collect();
            assert_eq!(again, first, "probe {i} disagreed with the first");
        }
    }
}
