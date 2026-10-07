//! The canonical form of a graph: what two engines, or two installation orders,
//! must agree on, and nothing they may differ on.
//!
//! Two consumers, one form. The enumerator's memoisation (`alg.tex` lem:memo)
//! keys its visited set on the inner graph — events with values and
//! reads-from, "insertion order and engine stamps excluded"
//! (`IMPL-PLAN-algorithms.md` §4.4) — and the differential harness compares
//! report sets across engines by "the set of its events as (thread, index,
//! label with values; receive labels without source), plus the rf map from
//! receive position to send position or ⊥. Nothing else: no insertion order,
//! no engine stamps, no engine ids" (§6). Those are the same object, so it is
//! built once here.
//!
//! # What is kept, what is dropped, and why
//!
//! TraceForge's labels carry more than `⟨E, po, rf, labels⟩`. The projection,
//! field by field (criteria `P4-APPARATUS` 11):
//!
//! - **Every `ThreadId` in a label field is mapped through [`ThreadKey`]** —
//!   the `TCreate`/`TJoin` child, a `Block(Join)` target, a send's destination
//!   `Loc` when it names a thread, and the thread half of an `Event`-valued
//!   `Loc` (an unnamed channel, whose `Loc` is the position of its `Unique`).
//!   A `ThreadId` is a per-run spawn-order id and is an engine id in the
//!   plan's sense.
//! - **Determined by history, hence excluded**: `RecvLoc.tag` (a closure),
//!   `RecvLoc.locs`, `SendLoc.tag`, and `Block{Value}`'s `RecvLoc` and index.
//!   By `ref2.tex` ¶`par:lg` a thread's saturated command and store are a
//!   function of its own events in index order and the values it received;
//!   by induction on the index, the label of event `i` — predicate included —
//!   is fixed by events `0..i-1` and the values they received, all of which the
//!   form already carries (received values through rf → the source's `val`,
//!   nondet results, join results through `End.result`). Excluding them loses
//!   no distinction. (The paper's `lem:memo` has `V` as a set; this is the
//!   engine transport of it, `P4-DISCUSS.md` D6.)
//! - **Determined by history under F79's premise, excluded** (`P4-MIXED` M8):
//!   `SendMsg.annotation` / `RecvMsg.annotation`, the issuing command's
//!   visibility annotation, fixed by the thread's history like every label
//!   field above — a program choosing its annotation from a `ThreadId` order
//!   breaks it exactly as it breaks this key (F79).
//! - **Engine bookkeeping, excluded**: `SendLoc.sender_tid` (the event's own
//!   thread, already the position), `SendMsg.reader`, `monitor_readers`,
//!   `cancelled_recv_readers`, `sb`, `RecvMsg.revisitable`.
//! - **Out of scope by guard, excluded**: `SendMsg.lossy`, `dropped`,
//!   `monitor_sends` (the lossy and monitor guards in `config.rs`).
//! - **Program metadata, excluded**: `CToss.predetermined`, `maximal`, `name`;
//!   `TCreate.name`, `is_daemon`, `sym_cid`, `filtered_origination_vec`;
//!   `Begin.parent`, `sym_id` — fixed by the program text, or already carried
//!   by the thread identity.
//! - **Engine artefacts, excluded**: stamps, insertion order, cached clocks
//!   (`lem:memo`).
//! - **Every value is kept** and compared by the engine's own equality: a
//!   send's value, a thread's return value, a `CToss` and a `Choice` result.
//!   `Val` is `Box<dyn Message>` with no `Hash`, so [`CanonicalGraph`] carries
//!   the values and compares them exactly, while [`CanonKey`] is the hashable
//!   projection — values replaced by their type names — with the single
//!   guarantee `equal ⟹ equal key`. A set of graphs is a map from key to
//!   bucket resolved by full equality ([`CanonSet`]).
//!
//! # Values must be present
//!
//! Every execution begins with `initialize_for_execution`, which blanks every
//! send value and every `End` result, and two blanked values compare *equal*.
//! A form built mid-replay would therefore equal any other blanked graph of
//! the same shape — a false memo hit, or two witnesses merged.
//! [`CanonicalGraph::of`] **asserts** that no such value is pending; it is
//! called only on fully replayed graphs (criteria E3).
//!
//! # Thread identity
//!
//! A thread whose declared name is in `Tvis` is [`ThreadKey::Declared`] by that
//! name — resolved through `obs::resolve_visible`, which refuses an ambiguous
//! name, and the error is propagated. Every other thread is
//! [`ThreadKey::Origination`] by its `TCreate` **origination vector**,
//! `parent's ++ [TCreate index]`, never by an undeclared name, which two
//! threads may share. The vector is a property of the program's structure, so
//! it is the same across runs and engines, and a thread a revisit deletes and
//! re-creates at the same parent index gets the same vector back.
//!
//! # What the form cannot promise
//!
//! **A `ThreadId` inside a message value or a return value is opaque** — a
//! `Val` cannot be mapped — so two installation orders of one graph whose
//! spawns come from different parents can produce two keys when a value
//! carries a thread id (backlog F41, F44). The stability claim is: *stable
//! when no `ThreadId` reaches a message value, a return value, or a user-named
//! `Loc`.* Part 6 labels or excludes pairs that break it.
//!
//! **The memo's soundness assumes `ThreadId`s are used only through spawn,
//! send, join and equality** (backlog F79). `tid_for_spawn` numbers threads by
//! insertion order, so a program that uses ids by *order* — a leader chosen as
//! the minimum id, iteration over a `BTreeMap<ThreadId, _>` — can take
//! different continuations from two installation orders of one canonical
//! graph, and `lem:memo`'s "every test is a function of the graph" fails for
//! it.
//!
//! **A9**: a value whose equality is not reflexive (a `NaN`) makes a graph
//! unequal to itself; [`CanonSet`] then never deduplicates it and a memo keyed
//! on it never hits, which is safe. Witness-cache deduplication and
//! cross-engine report-set equality are not, and Part 6 excludes such pairs.
//!
//! # Placeholders
//!
//! A blocked thread rests on a `Block{Value}` or `Block{Join}` label the engine
//! removes when the thread unblocks, installing the receive or `TJoin` at the
//! same index. The paper has no event there. The form **records** them: on a
//! complete graph they are the status evidence, and in the memo they cost
//! only missed hits. The certificate's validity test ignores them
//! (`cert.rs`). `Block{ConfPrune}` never reaches a form.

use std::collections::{BTreeMap, HashMap};

use crate::conformance::obs::{resolve_visible, ObsError};
use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::loc::CommunicationModel;
use crate::msg::Val;
use crate::thread::ThreadId;

/// A run-independent thread identity: the declared visible name, or the
/// origination vector. A tagged sum, so a declared thread and an undeclared
/// one can never collide.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ThreadKey {
    Declared(String),
    Origination(Vec<u32>),
}

/// The declared visible names of a graph, resolved once through the one
/// resolver; `AmbiguousName` is propagated.
pub(crate) struct Declared {
    by_tid: BTreeMap<ThreadId, String>,
}

impl Declared {
    pub(crate) fn of(graph: &ExecutionGraph, visible: &[String]) -> Result<Self, ObsError> {
        let mut by_tid = BTreeMap::new();
        for name in visible {
            if let Some(tid) = resolve_visible(graph, name)? {
                by_tid.insert(tid, name.clone());
            }
        }
        Ok(Self { by_tid })
    }

    /// The [`ThreadKey`] of `tid`: its declared name, else its origination
    /// vector.
    ///
    /// `at` is the event whose label names `tid` (its own `Begin` when the
    /// thread is being keyed for itself); the panic below reports that
    /// position, as criterion 11 asks.
    pub(crate) fn key(&self, graph: &ExecutionGraph, tid: ThreadId, at: Event) -> ThreadKey {
        match self.by_tid.get(&tid) {
            Some(n) => ThreadKey::Declared(n.clone()),
            None => {
                // A thread with no `TCreate` in the graph has no identity. It is
                // reachable only through the public `thread::construct_thread_id`,
                // outside F79's assumption that ids flow from spawns; under that
                // assumption the lookup is total, the graph being porf-prefix-closed.
                let tclab = graph.get_thr_opt(&tid).map(|_| graph.get_thread_tclab(tid));
                let tclab = tclab.unwrap_or_else(|| {
                    panic!(
                        "conformance: the label at {at} names thread {tid:?}, which no TCreate \
                         in the graph spawned; the canonical form cannot identify it \
                         (P4-APPARATUS E4)"
                    )
                });
                ThreadKey::Origination(tclab.origination_vec())
            }
        }
    }
}

/// A send's destination.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Dest {
    /// A thread, by stable identity.
    Thread(ThreadKey),
    /// An unnamed channel: the position of its `Unique`, by stable identity.
    Channel(ThreadKey, u32),
    /// Any other identifier, by its `Debug` form. The corpus produces none.
    Other(String),
}

/// One label in canonical form. A receive carries **no source** — the rf map
/// holds that — and nothing here carries a stamp.
///
/// `Inbox`, `Sample` and the symbolic labels are out of conformance scope
/// (`conf-plan.md` §9) and are refused at handler entry; reaching one here is
/// a bug, and the match is exhaustive so a new variant is a compile error.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum CanonLabel {
    Begin,
    End {
        result: Val,
    },
    TCreate {
        child: ThreadKey,
    },
    TJoin {
        child: ThreadKey,
    },
    Send {
        dst: Dest,
        val: Val,
        comm: CommunicationModel,
    },
    Recv {
        comm: CommunicationModel,
        blocking: bool,
    },
    /// A channel-uniqueness marker. Fieldless: the label exposes no accessor,
    /// and its communication model is replay-validation metadata determined by
    /// the program.
    Unique,
    CToss {
        result: bool,
    },
    Choice {
        result: usize,
        range: (usize, usize),
    },
    Block {
        kind: BlockKind,
    },
}

impl CanonLabel {
    /// A transient placeholder the engine replaces when the thread unblocks.
    pub(crate) fn is_placeholder(&self) -> bool {
        matches!(
            self,
            CanonLabel::Block {
                kind: BlockKind::Value | BlockKind::Join(_)
            }
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BlockKind {
    Assume,
    Assert,
    Value,
    Join(ThreadKey),
}

/// The position of an event in canonical form.
pub(crate) type CanonPos = (ThreadKey, u32);

/// A graph with every engine artefact stripped.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct CanonicalGraph {
    /// Sorted by position.
    events: Vec<(CanonPos, CanonLabel)>,
    /// Every receive, to the position of the send it reads or `None` for ⊥.
    rf: BTreeMap<CanonPos, Option<CanonPos>>,
}

impl CanonicalGraph {
    /// Build the form. Errors on an ambiguous declared visible name; panics on a
    /// pending value, which means the caller is mid-replay (criteria E3).
    pub(crate) fn of(graph: &ExecutionGraph, visible: &[String]) -> Result<Self, ObsError> {
        let declared = Declared::of(graph, visible)?;
        let key_of = |tid: ThreadId, at: Event| declared.key(graph, tid, at);
        let pos_of = |e: Event| (key_of(e.thread, e), e.index);

        let mut events = Vec::new();
        let mut rf = BTreeMap::new();
        for tid in graph.thread_ids() {
            let tk = key_of(tid, Event::new(tid, 0));
            for index in 0..graph.thread_size(tid) as u32 {
                let e = Event::new(tid, index);
                let label = match graph.label(e) {
                    LabelEnum::Begin(_) => CanonLabel::Begin,
                    LabelEnum::End(l) => {
                        assert!(
                            !l.result().is_pending(),
                            "conformance: the thread result at {e} is still pending; the \
                             canonical form was built mid-replay (P4-APPARATUS E3)"
                        );
                        CanonLabel::End {
                            result: l.result().clone(),
                        }
                    }
                    LabelEnum::TCreate(l) => CanonLabel::TCreate {
                        child: key_of(l.cid(), e),
                    },
                    LabelEnum::TJoin(l) => CanonLabel::TJoin {
                        child: key_of(l.cid(), e),
                    },
                    LabelEnum::SendMsg(l) => {
                        assert!(
                            !l.val().is_pending(),
                            "conformance: the send value at {e} is still pending; the \
                             canonical form was built mid-replay (P4-APPARATUS E3)"
                        );
                        CanonLabel::Send {
                            dst: if let Some(t) = l.loc().as_thread_id() {
                                Dest::Thread(key_of(t, e))
                            } else if let Some(ev) = l.loc().as_event() {
                                Dest::Channel(key_of(ev.thread, e), ev.index)
                            } else {
                                Dest::Other(format!("{:?}", l.loc()))
                            },
                            val: l.val().clone(),
                            comm: l.comm(),
                        }
                    }
                    LabelEnum::RecvMsg(l) => {
                        rf.insert((tk.clone(), index), l.rf().map(pos_of));
                        CanonLabel::Recv {
                            comm: l.comm(),
                            blocking: !l.is_non_blocking(),
                        }
                    }
                    LabelEnum::Unique(_) => CanonLabel::Unique,
                    LabelEnum::CToss(l) => CanonLabel::CToss { result: l.result() },
                    LabelEnum::Choice(l) => CanonLabel::Choice {
                        result: l.result(),
                        range: (*l.range().start(), *l.range().end()),
                    },
                    LabelEnum::Block(l) => CanonLabel::Block {
                        kind: match l.btype() {
                            BlockType::Assume => BlockKind::Assume,
                            BlockType::Assert => BlockKind::Assert,
                            BlockType::Value(_, _) => BlockKind::Value,
                            BlockType::Join(t) => BlockKind::Join(key_of(*t, e)),
                            BlockType::ConfPrune => unreachable!(
                                "conformance: a pruned graph reached the canonical form at \
                                 {e}; the gate fired on an execution it had already pruned"
                            ),
                        },
                    },
                    LabelEnum::Inbox(_) | LabelEnum::Sample(_) => unreachable!(
                        "conformance: {} at {e} is outside conformance scope \
                         (conf-plan.md §9) and is rejected at handler entry",
                        graph.label(e)
                    ),
                    #[cfg(feature = "symbolic")]
                    LabelEnum::SymbolicVar(_) | LabelEnum::ConstraintEval(_) => unreachable!(
                        "conformance: symbolic execution at {e} is outside conformance \
                         scope (conf-plan.md §9) and is rejected at handler entry"
                    ),
                };
                events.push(((tk.clone(), index), label));
            }
        }
        events.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(Self { events, rf })
    }

    pub(crate) fn key(&self) -> CanonKey {
        CanonKey {
            events: self
                .events
                .iter()
                .map(|(p, l)| (p.clone(), LabelShape::of(l)))
                .collect(),
            rf: self
                .rf
                .iter()
                .map(|(r, s)| (r.clone(), s.clone()))
                .collect(),
        }
    }

    pub(crate) fn events(&self) -> &[(CanonPos, CanonLabel)] {
        &self.events
    }

    pub(crate) fn label_at(&self, p: &CanonPos) -> Option<&CanonLabel> {
        self.events
            .binary_search_by(|(q, _)| q.cmp(p))
            .ok()
            .map(|i| &self.events[i].1)
    }

    pub(crate) fn rf(&self) -> &BTreeMap<CanonPos, Option<CanonPos>> {
        &self.rf
    }
}

/// A label with its values replaced by their type names: the hashable shape.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum LabelShape {
    Begin,
    End {
        type_name: String,
    },
    TCreate {
        child: ThreadKey,
    },
    TJoin {
        child: ThreadKey,
    },
    Send {
        dst: Dest,
        type_name: String,
        comm: CommunicationModel,
    },
    Recv {
        comm: CommunicationModel,
        blocking: bool,
    },
    Unique,
    CToss {
        result: bool,
    },
    Choice {
        result: usize,
        range: (usize, usize),
    },
    Block {
        kind: BlockKind,
    },
}

impl LabelShape {
    fn of(l: &CanonLabel) -> Self {
        match l {
            CanonLabel::Begin => LabelShape::Begin,
            CanonLabel::End { result } => LabelShape::End {
                type_name: result.type_name.clone(),
            },
            CanonLabel::TCreate { child } => LabelShape::TCreate {
                child: child.clone(),
            },
            CanonLabel::TJoin { child } => LabelShape::TJoin {
                child: child.clone(),
            },
            CanonLabel::Send { dst, val, comm } => LabelShape::Send {
                dst: dst.clone(),
                type_name: val.type_name.clone(),
                comm: *comm,
            },
            CanonLabel::Recv { comm, blocking } => LabelShape::Recv {
                comm: *comm,
                blocking: *blocking,
            },
            CanonLabel::Unique => LabelShape::Unique,
            CanonLabel::CToss { result } => LabelShape::CToss { result: *result },
            CanonLabel::Choice { result, range } => LabelShape::Choice {
                result: *result,
                range: *range,
            },
            CanonLabel::Block { kind } => LabelShape::Block { kind: kind.clone() },
        }
    }
}

/// The hashable projection of a [`CanonicalGraph`]. `a == b` implies
/// `a.key() == b.key()`; nothing is claimed the other way.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CanonKey {
    events: Vec<(CanonPos, LabelShape)>,
    rf: Vec<(CanonPos, Option<CanonPos>)>,
}

/// A set of canonical graphs: buckets by key, resolved by full equality.
#[derive(Clone, Debug, Default)]
pub(crate) struct CanonSet {
    buckets: HashMap<CanonKey, Vec<CanonicalGraph>>,
    len: usize,
}

impl CanonSet {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Insert; `false` if an equal graph was already present.
    pub(crate) fn insert(&mut self, g: CanonicalGraph) -> bool {
        let bucket = self.buckets.entry(g.key()).or_default();
        if bucket.contains(&g) {
            return false;
        }
        bucket.push(g);
        self.len += 1;
        true
    }

    pub(crate) fn contains(&self, g: &CanonicalGraph) -> bool {
        self.buckets.get(&g.key()).is_some_and(|b| b.contains(g))
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Set equality, for the differential harness: same graphs on both sides.
    pub(crate) fn same_as(&self, other: &CanonSet) -> bool {
        self.len == other.len && self.buckets.values().flatten().all(|g| other.contains(g))
    }
}
