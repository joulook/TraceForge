//! Signatures, visible positions, transported orders, coverage, and the
//! witness test — the apparatus every checker of `alg.tex` §8 shares.
//!
//! The draft splits the morphism of `ref2.tex` Def. morph into an equality
//! and a containment (`alg.tex` §8.2):
//!
//! > `sig(G) ≝ ⟨(w_t(G))_{t∈Tvis}, status_G|_{Tvis}⟩`. For a signature `s` write
//! > `w_t(s)` for its word component at `t`. The *visible positions* of `s` are
//! > `vpos(s) ≝ {⟨t,i⟩ | t ∈ Tvis, i < |w_t(s)|}`, and its universe is the set of
//! > pairs of distinct positions, `U(s) ≝ {⟨p,q⟩ ∈ vpos(s) × vpos(s) | p ≠ q}`.
//! > For a visible event `e` of a graph, its visible position is
//! > `vpos(e) ≝ ⟨tid(e), i⟩`, where `i` is the number of visible events of
//! > `tid(e)` that are po-before `e`; it counts visible events only, and it is
//! > not the position `pos(e)` … Any graph, complete or not, determines
//! > `ord(G) ≝ {⟨vpos(e), vpos(e')⟩ | ⟨e,e'⟩ ∈ vo_G}`.
//!
//! > **lem:sig.** For `G₁ ∈ Graphs(Impl)` and `G₂ ∈ Graphs(Spec)`,
//! > `G₁ ⊑ G₂ ⟺ sig(G₁) = sig(G₂) ∧ ord(G₂) ⊆ ord(G₁)`.
//!
//! And for a *partial* implementation graph against a *complete* specification
//! graph, the witness test of §8.4 (Def. cone), reproduced at [`cone`].
//!
//! Everything here is a pure function of graphs and their `Wobs` rows. Nothing
//! runs a search, and nothing consults engine stamps or insertion order: by
//! `lem:memo` those are not part of what the algorithms compare.
//!
//! # Two engine facts the definitions meet
//!
//! **`vo` is the engine's.** `vo_G` is computed by [`morphism::vo`], which is
//! `in_porf` with the diagonal excluded, and `in_porf` follows thread-creation
//! and join edges the paper's `porf ≝ (po ∪ rf)⁺` has no events for (backlog
//! A7, open). So an `ord` computed here can contain pairs the paper's `vo`
//! lacks on a fixture with a visible `main` that joins, or a late-spawned
//! thread. The criteria's fixture rule E1 (`P4-APPARATUS.md`, binding on every
//! paper-derived expected value: an invisible `main` is the only thread that
//! spawns or joins, and the rest of E1's clauses) is where the two agree.
//!
//! **A sourceless receive.** `RecvMsg.rf` is `None` both for "read ⊥" and for
//! "no source yet". The paper's convention (§8.5) is that no predicate is
//! applied to a receive in the latter state, and that is this module's
//! precondition: every function here is called only on graphs on which every
//! receive has had `SetRF` applied and the consistency guard has passed, and
//! never mid-replay (where `wobs` panics on a pending value). The
//! `debug_assert!`s check the half that is checkable: a *blocking* receive of a
//! declared visible thread never has `rf = None`.
//!
//! **`Val` cannot be hashed.** It is `Box<dyn Message>`, equal only through
//! `msg_equals`, so a signature cannot key a hash map directly. [`SigKey`] is a
//! *projection* — the hashable shape of a signature — with the single guarantee
//! `sig(a) == sig(b)` ⟹ `key(a) == key(b)`, which holds because `msg_equals`
//! downcasts to one concrete `T` and equal values therefore share
//! `type_name::<T>()`. The converse is not claimed; [`SigBuckets`] resolves a
//! bucket by full [`Sig`] equality.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::conformance::morphism::{self, statuses, CompleteExecution, Status};
use crate::conformance::obs::{is_visible, Obs, ObsError, Wobs};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;

/// `vpos(e)`: a declared visible thread and the number of visible events of
/// that thread that are po-before `e`.
///
/// It is **not** `e.index`. A nondet, `Begin`, `TCreate`, `TJoin` or `Block`
/// on a visible thread does not advance it — plan §5.5's mutation is exactly
/// "use the raw event index", and it produces a false report.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct VPos {
    pub(crate) thread: String,
    pub(crate) index: usize,
}

/// The visible positions of every visible event of a graph, read off its
/// `Wobs` rows: the i-th observation of thread `t` sits at `⟨t, i⟩`.
#[derive(Clone, Debug, Default)]
pub(crate) struct VPosMap {
    by_event: BTreeMap<Event, VPos>,
}

impl VPosMap {
    pub(crate) fn of(graph: &ExecutionGraph, wobs: &Wobs, visible: &[String]) -> Self {
        debug_assert_sourced(graph, wobs, visible);
        let mut by_event = BTreeMap::new();
        for name in visible {
            for (i, (e, _)) in wobs.of(name).iter().enumerate() {
                debug_assert!(
                    is_visible(graph, *e, visible),
                    "conformance: a Wobs row holds an event the visibility predicate rejects"
                );
                by_event.insert(
                    *e,
                    VPos {
                        thread: name.clone(),
                        index: i,
                    },
                );
            }
        }
        // The converse direction of the cross-check (gate-4 round 01, M1;
        // under `P4-MIXED` both sides read `is_visible`, so this checks row
        // construction only):
        // every event of the graph the predicate accepts is in a row. Together
        // the two directions pin the rows to the predicate, so a Part 7 that
        // changes one and not the other fails here in debug builds.
        debug_assert!(
            graph.thread_ids().into_iter().all(|t| {
                (0..graph.thread_size(t) as u32)
                    .map(|i| Event::new(t, i))
                    .filter(|&e| is_visible(graph, e, visible))
                    .all(|e| by_event.contains_key(&e))
            }),
            "conformance: the visibility predicate accepts an event no Wobs row holds"
        );
        Self { by_event }
    }

    pub(crate) fn get(&self, e: Event) -> Option<&VPos> {
        self.by_event.get(&e)
    }

    /// Every visible event, in engine `Event` order (`ThreadId`, then raw
    /// index) — not in `(thread name, vpos)` order.
    pub(crate) fn events(&self) -> impl Iterator<Item = (Event, &VPos)> {
        self.by_event.iter().map(|(e, p)| (*e, p))
    }
}

/// The checkable half of the sourceless-receive precondition: a blocking
/// receive of a declared visible thread has a source.
fn debug_assert_sourced(graph: &ExecutionGraph, wobs: &Wobs, visible: &[String]) {
    if cfg!(debug_assertions) {
        for name in visible {
            for (e, _) in wobs.of(name) {
                if let LabelEnum::RecvMsg(r) = graph.label(*e) {
                    debug_assert!(
                        r.is_non_blocking() || r.rf().is_some(),
                        "conformance: the blocking receive at {e} has no source; the \
                         apparatus was called before SetRF (alg.tex §8.5's convention)"
                    );
                }
            }
        }
    }
}

/// `sig(G)` of a complete graph: per-thread words and the status vector,
/// compared exactly as the morphism compares them — words by `Obs::eq`, which
/// is the engine's `msg_equals`, and statuses by `Status::eq`.
///
/// Takes a [`CompleteExecution`] because `status_G` is defined only on a
/// complete graph (§6.3). A probe-derived graph must obtain its
/// `CompleteExecution` through [`crate::conformance::prober::Probed::complete`];
/// the type states that obligation and does not enforce it
/// (`morphism.rs`, `assume_finished_at_gate`).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Sig {
    words: BTreeMap<String, Vec<Obs>>,
    statuses: BTreeMap<String, Status>,
}

impl Sig {
    pub(crate) fn of(
        exec: CompleteExecution<'_>,
        wobs: &Wobs,
        visible: &[String],
    ) -> Result<Self, ObsError> {
        // Statuses first: it is the call that refuses an unspawned declared
        // thread, which on a complete graph is a §8 violation rather than an
        // empty row.
        let statuses = statuses(exec, wobs, visible)?;
        let mut words = BTreeMap::new();
        for name in visible {
            let row = wobs.row(name).unwrap_or_else(|| {
                panic!(
                    "conformance: `{name}` is not in this wobs; the declared-visible \
                     list does not match what was extracted"
                )
            });
            words.insert(
                name.clone(),
                row.observations().iter().map(|(_, o)| o.clone()).collect(),
            );
        }
        Ok(Self { words, statuses })
    }

    pub(crate) fn word(&self, name: &str) -> &[Obs] {
        self.words.get(name).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(crate) fn status(&self, name: &str) -> Option<Status> {
        self.statuses.get(name).copied()
    }

    /// The hashable projection. `sig(a) == sig(b)` implies `a.key() == b.key()`;
    /// nothing is claimed the other way.
    pub(crate) fn key(&self) -> SigKey {
        SigKey {
            words: self
                .words
                .iter()
                .map(|(t, w)| (t.clone(), w.iter().map(ObsShape::of).collect()))
                .collect(),
            statuses: self
                .statuses
                .iter()
                .map(|(t, s)| (t.clone(), StatusKey::of(*s)))
                .collect(),
        }
    }
}

/// The shape of one observation: its kind, its Rust type name, and whether a
/// receive read ⊥. Two observations with equal shape may still differ in value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ObsShape {
    Send {
        type_name: String,
    },
    /// `None` is ⊥.
    Recv {
        type_name: Option<String>,
    },
}

impl ObsShape {
    fn of(o: &Obs) -> Self {
        match o {
            Obs::Send(v) => ObsShape::Send {
                type_name: v.type_name.clone(),
            },
            Obs::Recv(v) => ObsShape::Recv {
                type_name: v.as_ref().map(|v| v.type_name.clone()),
            },
        }
    }
}

/// The hashable projection of a [`Sig`]. See the module doc for what it does
/// and does not guarantee.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SigKey {
    words: Vec<(String, Vec<ObsShape>)>,
    statuses: Vec<(String, StatusKey)>,
}

/// `Status` as a hash key; `morphism::Status` itself derives no `Hash`, and
/// this module does not widen that type's derives.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum StatusKey {
    Errored,
    Done,
    Blocked,
}

impl StatusKey {
    fn of(s: Status) -> Self {
        match s {
            Status::Errored => StatusKey::Errored,
            Status::Done => StatusKey::Done,
            Status::Blocked => StatusKey::Blocked,
        }
    }
}

/// A map keyed by signature, resolved exactly: `SigKey → [(Sig, T)]`, grouped
/// by **full** `Sig` inside a bucket.
///
/// This is what makes §8.3's cost claim survive the projection: on `ex:naive`
/// a lookup costs one signature comparison per bucket member and no
/// containment test, because every graph with the same signature shares one
/// slot. The stateful index of Part 3 is `SigBuckets<BTreeSet<VisOrder>>`.
#[derive(Clone, Debug)]
pub(crate) struct SigBuckets<T> {
    buckets: HashMap<SigKey, Vec<(Sig, T)>>,
    len: usize,
}

impl<T> Default for SigBuckets<T> {
    fn default() -> Self {
        Self {
            buckets: HashMap::new(),
            len: 0,
        }
    }
}

impl<T> SigBuckets<T> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// The slot whose `Sig` equals `sig`, created with `make()` if absent.
    pub(crate) fn entry(&mut self, sig: Sig, make: impl FnOnce() -> T) -> &mut T {
        let bucket = self.buckets.entry(sig.key()).or_default();
        let at = match bucket.iter().position(|(s, _)| *s == sig) {
            Some(i) => i,
            None => {
                bucket.push((sig, make()));
                self.len += 1;
                bucket.len() - 1
            }
        };
        &mut bucket[at].1
    }

    /// The slot whose `Sig` equals `sig`, if any.
    pub(crate) fn get(&self, sig: &Sig) -> Option<&T> {
        self.buckets
            .get(&sig.key())
            .and_then(|b| b.iter().find(|(s, _)| s == sig))
            .map(|(_, t)| t)
    }

    /// Distinct signatures held.
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// The number of `SigKey` hash buckets — coarser than [`SigBuckets::len`],
    /// which counts full-`Sig` slots (`P4-STATEFUL` criterion 8).
    pub(crate) fn key_buckets(&self) -> usize {
        self.buckets.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// `ord(G)`: the visible order transported to positions. Defined on partial
/// graphs too.
pub(crate) type VisOrder = BTreeSet<(VPos, VPos)>;

/// `ord(G) ≝ {⟨vpos(e), vpos(e')⟩ | ⟨e,e'⟩ ∈ vo_G}`, with `vo_G` computed
/// through invisible events by [`morphism::vo`].
pub(crate) fn ord(graph: &ExecutionGraph, wobs: &Wobs, visible: &[String]) -> VisOrder {
    let vpos = VPosMap::of(graph, wobs, visible);
    let mut out = BTreeSet::new();
    for (e, pe) in vpos.events() {
        for (f, pf) in vpos.events() {
            if morphism::vo(graph, e, f) {
                out.insert((pe.clone(), pf.clone()));
            }
        }
    }
    out
}

/// What the complete-graph tests read of a graph: its signature and its
/// transported order. Built once, probed many times.
#[derive(Clone, Debug)]
pub(crate) struct Summary {
    pub(crate) sig: Sig,
    pub(crate) ord: VisOrder,
}

impl Summary {
    pub(crate) fn of(
        exec: CompleteExecution<'_>,
        wobs: &Wobs,
        visible: &[String],
    ) -> Result<Self, ObsError> {
        Ok(Self {
            sig: Sig::of(exec, wobs, visible)?,
            ord: ord(exec.graph(), wobs, visible),
        })
    }
}

/// `covered(G₁, G₂)` ≝ `sig(G₁) = sig(G₂) ∧ ord(G₂) ⊆ ord(G₁)` — the right-hand
/// side of `lem:sig`, and by that lemma exactly `G₁ ⊑ G₂`.
///
/// `imp` is the implementation graph, `spec` the specification graph; the
/// containment runs from the specification **back** to the implementation,
/// as (M2) does.
pub(crate) fn covered(imp: &Summary, spec: &Summary) -> bool {
    imp.sig == spec.sig && spec.ord.is_subset(&imp.ord)
}

/// `C₁(G₁, M)`, the witness test of `alg.tex` Def. cone, for a partial
/// implementation graph `G₁` against a complete specification graph `M`:
///
/// > `C₁(G₁,M)` holds when (1) `w_t(G₁)` is a prefix of `w_t(M)` for every
/// > `t ∈ Tvis`; (2) `⟨vpos(e),vpos(e')⟩ ∈ ord(G₁)` for all matched events `e,e'`
/// > of `M` with `⟨e,e'⟩ ∈ vo_M`; and (3) every visible event of `M` that is
/// > `porf_M`-before a matched event is itself matched.
///
/// where a visible event `e` of `M` is *matched* when `vpos(e) = ⟨t,i⟩` with
/// `i < |w_t(G₁)|`.
///
/// Clause (2) pulls back from `M` to `G₁` and in that direction only: a
/// too-strict clause makes the gated sweep find no witness and set a false
/// certificate, which is unsound. Clause (3) is not redundant — `ex:cone` is
/// its regression test. A pass here is a **partial-match** verdict, never a
/// coverage one (ruling 2): on a complete `G₁` the Blocking pair passes `cone`
/// and fails [`covered`].
///
/// **Departure from the paper, recorded.** Clauses (2) and (3) use the
/// engine's `porf` — [`morphism::vo`], which follows thread-creation and join
/// edges the paper's `porf ≝ (po ∪ rf)⁺` has no events for (backlog A7). E1 of
/// `P4-APPARATUS.md` is where the two agree.
///
/// This is the reference form, from graphs. [`cone_from`] is the same
/// predicate from summaries, which the gate probe uses so that `ord(G₁)` is
/// computed once per probe rather than once per witness (gate-4 round 01,
/// m1); the tester's corpus test holds the two to agreement.
pub(crate) fn cone(
    g1: &ExecutionGraph,
    g1_wobs: &Wobs,
    m: &ExecutionGraph,
    m_wobs: &Wobs,
    visible: &[String],
) -> bool {
    // (1) word prefixes, by Obs::eq.
    for name in visible {
        let w1 = g1_wobs.of(name);
        let wm = m_wobs.of(name);
        if w1.len() > wm.len() || !w1.iter().zip(wm).all(|((_, a), (_, b))| a == b) {
            return false;
        }
    }

    // Matched events of M: the first |w_t(G₁)| visible events of each thread.
    let m_vpos = VPosMap::of(m, m_wobs, visible);
    let matched: BTreeSet<Event> = visible
        .iter()
        .flat_map(|name| {
            let k = g1_wobs.of(name).len();
            m_wobs.of(name).iter().take(k).map(|(e, _)| *e)
        })
        .collect();

    // (2) every vo_M pair between matched events lands in ord(G₁), at the
    // same positions (the positional map).
    let ord1 = ord(g1, g1_wobs, visible);
    for &e in &matched {
        for &f in &matched {
            if morphism::vo(m, e, f) {
                let (pe, pf) = (
                    m_vpos
                        .get(e)
                        .expect("conformance: a matched event of M has no visible position"),
                    m_vpos
                        .get(f)
                        .expect("conformance: a matched event of M has no visible position"),
                );
                if !ord1.contains(&(pe.clone(), pf.clone())) {
                    return false;
                }
            }
        }
    }

    // (3) downward closure: a visible porf_M-predecessor of a matched event is
    // matched. `u` ranges over every visible event of M, matched or not, and
    // `vo` is computed through invisible events, so a predecessor reached only
    // through a relay is found.
    for (u, _) in m_vpos.events() {
        if matched.contains(&u) {
            continue;
        }
        if matched.iter().any(|&e| morphism::vo(m, u, e)) {
            return false;
        }
    }
    true
}

/// `C₁(G₁, M)` from what `W` already holds of `M` and what one probe computes
/// of `G₁` once: the words of `G₁`, `ord(G₁)`, and `M`'s [`Summary`].
///
/// Equivalent to [`cone`] because `vpos` is injective on visible events, so
/// for visible `u ≠ e` of `M`, `⟨u,e⟩ ∈ vo_M ⟺ ⟨vpos(u),vpos(e)⟩ ∈ ord(M)`
/// (plan §3: "`C₁` and `covered` read only words, statuses and `ord(M)`"). A
/// position `⟨t,i⟩` of `M` is *matched* iff `i < |w_t(G₁)|`:
///
/// - (1) `w_t(G₁)` is a prefix of `w_t(M)` for every `t`;
/// - (2) every `ord(M)` pair of matched positions is in `ord(G₁)`;
/// - (3) no `ord(M)` pair runs from an unmatched position to a matched one.
pub(crate) fn cone_from(g1_wobs: &Wobs, ord1: &VisOrder, m: &Summary, visible: &[String]) -> bool {
    for name in visible {
        let w1 = g1_wobs.of(name);
        let wm = m.sig.word(name);
        if w1.len() > wm.len() || !w1.iter().zip(wm).all(|((_, a), b)| a == b) {
            return false;
        }
    }
    let matched = |p: &VPos| p.index < g1_wobs.of(&p.thread).len();
    m.ord.iter().all(|(p, q)| {
        if matched(p) && matched(q) {
            ord1.contains(&(p.clone(), q.clone()))
        } else {
            // (3): an unmatched predecessor of a matched position fails.
            !(matched(q) && !matched(p))
        }
    })
}
