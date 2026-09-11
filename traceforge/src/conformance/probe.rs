//! Probe mode: running a program *without* committing its choices.
//!
//! Conformance checking needs to ask a specification program "what could you
//! do next, from this partial execution graph?" and then try the answers one
//! at a time, backtracking freely. TraceForge's exploration cannot answer that
//! directly: it commits to one option per event and undoes the commitment by
//! re-executing, which a search over *insertion orders* cannot use.
//!
//! Probe mode answers it instead. A probe execution runs the program against a
//! partial graph; every thread that reaches a fresh **choice point** — a send,
//! a receive, or a nondeterministic choice — has its would-be label recorded as
//! an [`Offer`] and is then **parked**: the label is not installed, the
//! thread's position is given back, and the thread is never rescheduled during
//! that probe. Deterministic bookkeeping (thread creation, `Begin`/`End`,
//! channel creation, blocking) installs normally, because it is forced. When
//! no thread can run, the probe ends and the collected offers are exactly the
//! events the program could perform next.
//!
//! The program is therefore only ever run *forwards*, against a graph that
//! already exists. Backtracking is done by the caller, on graphs, by discarding
//! one and keeping another — never by rewinding the program.

use std::collections::BTreeSet;

use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::thread::ThreadId;

/// An event the program could perform next, recorded without being installed.
///
/// The label is the one the handler was about to add to the graph, so
/// installing an offer later is just adding this label (plus, for a receive or
/// a nondeterministic choice, the decision of *which* option to take).
#[derive(Debug, Clone)]
pub(crate) struct Offer {
    label: LabelEnum,
    /// For a receive: the sends it could read, in the checker's order. Empty
    /// for every other kind of offer.
    sources: Vec<Event>,
    /// For a receive: whether it may also read nothing. Only a non-blocking
    /// receive may, and a blocking receive with no sources is not offered at
    /// all — it is not enabled.
    may_read_nothing: bool,
}

impl Offer {
    pub(crate) fn new(label: LabelEnum) -> Self {
        Self {
            label,
            sources: Vec::new(),
            may_read_nothing: false,
        }
    }

    /// A receive offer, carrying what it could read.
    pub(crate) fn recv(label: LabelEnum, sources: Vec<Event>, may_read_nothing: bool) -> Self {
        Self {
            label,
            sources,
            may_read_nothing,
        }
    }

    /// The sends this receive could read.
    pub(crate) fn sources(&self) -> &[Event] {
        &self.sources
    }

    /// Whether this receive may read nothing (`rf = ⊥`).
    pub(crate) fn may_read_nothing(&self) -> bool {
        self.may_read_nothing
    }

    /// Position the event would occupy: its thread, and its index in that
    /// thread's row.
    pub(crate) fn pos(&self) -> Event {
        self.label.pos()
    }

    pub(crate) fn label(&self) -> &LabelEnum {
        &self.label
    }

    /// A short description, for test assertions and diagnostics.
    pub(crate) fn kind(&self) -> &'static str {
        match self.label {
            LabelEnum::SendMsg(_) => "send",
            LabelEnum::RecvMsg(_) => "recv",
            LabelEnum::CToss(_) => "nondet",
            LabelEnum::Choice(_) => "choice",
            _ => "other",
        }
    }
}

/// State of one probe execution.
///
/// What the `just_parked` tripwire does and does not catch, stated because an
/// earlier version of this file overclaimed it. It catches **a handler that
/// records an offer whose API path then fails to suspend the thread**: the
/// next `record` on any thread trips the assertion below, and
/// `prober::probe_from` asserts at the end of every probe that no park was
/// left unconsumed — which is what covers the case where no second choice
/// point follows, including a single-threaded program.
///
/// It cannot catch a handler with *no* probe branch at all, because such a
/// handler never sets the flag. That class is addressed by rejecting
/// out-of-scope operations and by re-running the call-site enumeration per
/// feature flag, not by this assertion.
///
/// Lives on `Must` behind an `Option`, so a `None` probe context leaves every
/// hook in the engine inert and ordinary verification unchanged.
#[derive(Debug, Default)]
pub(crate) struct ProbeCtx {
    /// Choice points reached, in the order the probe reached them.
    offers: Vec<Offer>,
    /// Threads parked at a choice point; never rescheduled in this probe.
    parked: BTreeSet<ThreadId>,
    /// Set by a handler that has just recorded an offer, and consumed by the
    /// API layer, which must then suspend the thread *before returning any
    /// value to user code*.
    ///
    /// Every consumer uses this as a boolean; the thread is carried for
    /// diagnostics, and so that a call site which needs to assert it is
    /// suspending the thread that actually parked can do so without a
    /// signature change.
    just_parked: Option<ThreadId>,
}

impl ProbeCtx {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record a choice point and park the thread that reached it.
    ///
    /// Panics if the previous park was never consumed. That can only happen
    /// if some public API path reached a choice-point handler without the
    /// API layer then suspending the thread — in which case the program has
    /// been handed a fabricated value and is running on it. Failing loudly
    /// here turns that silent corruption into an immediate, locatable error;
    /// it is the tripwire for exactly the class of gap that an
    /// enumerate-the-call-sites approach is prone to.
    pub(crate) fn record(&mut self, offer: Offer) {
        assert!(
            self.just_parked.is_none(),
            "probe: a choice point was recorded while an earlier park was still \
             unconsumed, so some API path reached a handler without parking its \
             thread. Previous offer at {:?}, new offer at {:?}.",
            self.offers.last().map(Offer::pos),
            offer.pos()
        );
        self.parked.insert(offer.pos().thread);
        self.just_parked = Some(offer.pos().thread);
        self.offers.push(offer);
    }

    /// Consume the "a handler just parked" flag.
    ///
    /// The API layer calls this immediately after a handler returns; a `true`
    /// answer means the handler's return value is a placeholder that must
    /// never reach the program.
    pub(crate) fn take_just_parked(&mut self) -> Option<ThreadId> {
        self.just_parked.take()
    }

    /// True iff a park is still waiting to be consumed by the API layer.
    pub(crate) fn park_pending(&self) -> bool {
        self.just_parked.is_some()
    }

    pub(crate) fn is_parked(&self, t: &ThreadId) -> bool {
        self.parked.contains(t)
    }

    pub(crate) fn take_offers(&mut self) -> Vec<Offer> {
        std::mem::take(&mut self.offers)
    }
}
