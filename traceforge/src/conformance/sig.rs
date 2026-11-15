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
//! `msg_equals`, so a signature cannot key a hash map directly. [`Sig::hash128`]
//! is a one-pass 128-bit hash of the signature's *shape* — per name the word's
//! length and each observation's kind, ⊥ and concrete message type, and the
//! statuses — with the single guarantee `sig(a) == sig(b)` ⟹ `hash(a) == hash(b)`,
//! which holds because `msg_equals` downcasts to one concrete `T` and equal values
//! therefore share `T`'s `TypeId`. The hash reads that `TypeId`, never the public
//! `Val::type_name` string, which a caller may change without changing equality
//! (`MIN-ENGINES-E4-CODE` round 01 M1). The converse is not claimed; [`SigBuckets`] resolves
//! a bucket by full [`Sig`] equality. (`MIN-ENGINES` E4; before it a projection
//! of the shape was built from cloned strings and hashed twice.)

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{Hash, Hasher};

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
        wobs: Wobs,
        visible: &[String],
    ) -> Result<Self, ObsError> {
        // Statuses first: it is the call that refuses an unspawned declared
        // thread, which on a complete graph is a §8 violation rather than an
        // empty row.
        let statuses = statuses(exec, &wobs, visible)?;
        Ok(Self::from_rows(statuses, wobs, visible))
    }

    /// `MIN-ENGINES` E4: the signature from its statuses and the rows, which it
    /// **takes** — the names and the observations `observe` built move in, the
    /// one clone per value — after every borrowing use of the `Wobs` has run.
    pub(crate) fn from_rows(
        statuses: BTreeMap<String, Status>,
        wobs: Wobs,
        visible: &[String],
    ) -> Self {
        for name in visible {
            assert!(
                wobs.row(name).is_some(),
                "conformance: `{name}` is not in this wobs; the declared-visible \
                 list does not match what was extracted"
            );
        }
        let words = wobs
            .into_rows()
            .into_iter()
            .map(|(name, row)| {
                let word: Vec<Obs> = row.into_observations().into_iter().map(|(_, o)| o).collect();
                (name, word)
            })
            .collect();
        Self { words, statuses }
    }

    /// `J3` (the reader of `interchange`): the signature from decoded words and
    /// statuses, with no graph; the caller gives one word and one status per
    /// declared name.
    pub(crate) fn from_words(
        statuses: BTreeMap<String, Status>,
        words: BTreeMap<String, Vec<Obs>>,
    ) -> Self {
        Self { words, statuses }
    }

    pub(crate) fn word(&self, name: &str) -> &[Obs] {
        self.words.get(name).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(crate) fn status(&self, name: &str) -> Option<Status> {
        self.statuses.get(name).copied()
    }

    /// `MIN-ENGINES` E4: the 128-bit hash of the signature's shape in one pass —
    /// per name (in `BTreeMap` order) its length and bytes, the word's length,
    /// and per observation a kind tag (0 send, 1 receive, 2 receive of ⊥) and
    /// the concrete message type's `TypeId`; then per status name its bytes and
    /// a tag — fed to two seeded `DefaultHasher`s (the seeds of the former
    /// `hash128`), no string built. `sig(a) == sig(b)` implies equal hashes:
    /// the hash reads only kind, ⊥, the `TypeId` and the status; `msg_equals`
    /// downcasts to one concrete type, so equal values share the `TypeId` — the
    /// public `Val::type_name` string, which equality ignores and a caller may
    /// change, is deliberately not read (`MIN-ENGINES-E4-CODE` round 01 M1).
    /// Nothing is claimed the other way.
    pub(crate) fn hash128(&self) -> u128 {
        fn put(a: &mut DefaultHasher, b: &mut DefaultHasher, bytes: &[u8]) {
            a.write(bytes);
            b.write(bytes);
        }
        let mut a = DefaultHasher::new();
        let mut b = DefaultHasher::new();
        a.write_u64(0x5f3759df);
        b.write_u64(0x9e3779b97f4a7c15);
        for (name, word) in &self.words {
            put(&mut a, &mut b, &(name.len() as u64).to_le_bytes());
            put(&mut a, &mut b, name.as_bytes());
            put(&mut a, &mut b, &(word.len() as u64).to_le_bytes());
            for o in word {
                let (tag, ty) = match o {
                    Obs::Send(v) => (0u8, Some(v.as_any_ref().type_id())),
                    Obs::Recv(Some(v)) => (1, Some(v.as_any_ref().type_id())),
                    Obs::Recv(None) => (2, None),
                };
                put(&mut a, &mut b, &[tag]);
                if let Some(ty) = ty {
                    ty.hash(&mut a);
                    ty.hash(&mut b);
                }
            }
        }
        for (name, s) in &self.statuses {
            put(&mut a, &mut b, &(name.len() as u64).to_le_bytes());
            put(&mut a, &mut b, name.as_bytes());
            put(&mut a, &mut b, &[match s {
                Status::Errored => 0,
                Status::Done => 1,
                Status::Blocked => 2,
            }]);
        }
        ((a.finish() as u128) << 64) | b.finish() as u128
    }
}

#[cfg(test)]
thread_local! {
    static TEST_KEY: std::cell::Cell<Option<fn(&Sig) -> u64>> = const {
        std::cell::Cell::new(None)
    };
}

#[cfg(test)]
pub(crate) fn with_test_key(key: fn(&Sig) -> u64, run: impl FnOnce()) {
    struct Reset(Option<fn(&Sig) -> u64>);
    impl Drop for Reset {
        fn drop(&mut self) {
            TEST_KEY.with(|key| key.set(self.0));
        }
    }
    let _reset = Reset(TEST_KEY.with(|slot| slot.replace(Some(key))));
    run();
}

// The fixed EI-0.2 set: i8–i128, u8–u128, isize, usize, bool, char, String,
// and Option<T>, Vec<T>, (T, U), (T, U, V) of those scalars, without nesting.
// Floats, &str, (), DecVal and every other user type are deliberately excluded.
// TypeId selects a concrete downcast; neither rendering nor type_name is read.
type ValueHash = fn(&dyn std::any::Any, &mut DefaultHasher);

fn value_hashers() -> &'static HashMap<std::any::TypeId, ValueHash> {
    use std::any::{Any, TypeId};
    static HASHERS: std::sync::OnceLock<HashMap<TypeId, ValueHash>> =
        std::sync::OnceLock::new();
    fn add<T: Hash + 'static>(map: &mut HashMap<TypeId, ValueHash>) {
        fn hash<T: Hash + 'static>(value: &dyn Any, h: &mut DefaultHasher) {
            value.downcast_ref::<T>().expect("conformance: typed value hash").hash(h);
        }
        map.insert(TypeId::of::<T>(), hash::<T>);
    }
    macro_rules! scalars {
        ($m:ident, $($arg:tt)*) => {
            $m!($($arg)*; i8, i16, i32, i64, i128, isize,
                u8, u16, u32, u64, u128, usize, bool, char, String);
        };
    }
    macro_rules! thirds {
        ($map:ident, $t:ty, $u:ty; $($v:ty),*) => {
            $(add::<($t, $u, $v)>(&mut $map);)*
        };
    }
    macro_rules! seconds {
        ($map:ident, $t:ty; $($u:ty),*) => {
            $(add::<($t, $u)>(&mut $map);
              scalars!(thirds, $map, $t, $u);)*
        };
    }
    macro_rules! firsts {
        ($map:ident; $($t:ty),*) => {
            $(add::<$t>(&mut $map);
              add::<Option<$t>>(&mut $map);
              add::<Vec<$t>>(&mut $map);
              scalars!(seconds, $map, $t);)*
        };
    }
    HASHERS.get_or_init(|| {
        let mut map = HashMap::new();
        scalars!(firsts, map);
        map
    })
}

impl Sig {
    /// Equality-compatible second-level key, using fixed-key DefaultHasher.
    /// Hashes i8–i128, u8–u128, isize, usize, bool, char, String, and Option<T>,
    /// Vec<T>, (T, U), (T, U, V) of those scalars only (no nested containers).
    /// Floats, &str, (), DecVal and all other types are outside this fixed set.
    /// Unsupported values contribute only a constant. The shape hash and all
    /// slot/order identities remain unchanged; byte estimates exclude the maps.
    pub(crate) fn value_key(&self) -> u64 {
        #[cfg(test)]
        if let Some(key) = TEST_KEY.with(|key| key.get()) {
            return key(self);
        }
        let mut h = DefaultHasher::new();
        self.hash128().hash(&mut h);
        for word in self.words.values() {
            for obs in word {
                let (kind, value) = match obs {
                    Obs::Send(v) => (0u8, Some(v)),
                    Obs::Recv(Some(v)) => (1, Some(v)),
                    Obs::Recv(None) => (2, None),
                };
                kind.hash(&mut h);
                if let Some(value) = value {
                    let any = value.as_any_ref();
                    any.type_id().hash(&mut h);
                    if let Some(hash) = value_hashers().get(&any.type_id()) {
                        hash(any, &mut h);
                    } else {
                        0u8.hash(&mut h);
                    }
                }
            }
        }
        h.finish()
    }
}

/// Slot indices in creation order, without an allocation for a singleton.
#[derive(Clone, Debug, Default)]
pub(crate) enum SlotChain {
    #[default]
    Empty,
    One(usize),
    Many(Vec<usize>),
}

impl SlotChain {
    pub(crate) fn push(&mut self, slot: usize) {
        match self {
            Self::Empty => *self = Self::One(slot),
            Self::One(first) => *self = Self::Many(vec![*first, slot]),
            Self::Many(slots) => slots.push(slot),
        }
    }

    fn as_slice(&self) -> &[usize] {
        match self {
            Self::Empty => &[],
            Self::One(slot) => std::slice::from_ref(slot),
            Self::Many(slots) => slots,
        }
    }

    pub(crate) fn iter(&self) -> std::slice::Iter<'_, usize> {
        self.as_slice().iter()
    }
}

impl<'a> IntoIterator for &'a SlotChain {
    type Item = &'a usize;
    type IntoIter = std::slice::Iter<'a, usize>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A map keyed by shape, then value key, resolved by full `Sig` equality.
/// Chains contain slot indices in creation order; unsupported values retain
/// the linear scan. The auxiliary maps do not change payload byte estimates.
/// The stateful index of Part 3 is `SigBuckets<BTreeSet<VisOrder>>`.
#[derive(Clone, Debug)]
pub(crate) struct SigBuckets<T> {
    buckets: HashMap<u128, Vec<(Sig, T)>>,
    chains: HashMap<u128, HashMap<u64, SlotChain>>,
    len: usize,
}

impl<T> Default for SigBuckets<T> {
    fn default() -> Self {
        Self {
            buckets: HashMap::new(),
            chains: HashMap::new(),
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
        let chain = self.chains.entry(sig.hash128()).or_default()
            .entry(sig.value_key()).or_default();
        let bucket = self.buckets.entry(sig.hash128()).or_default();
        let at = match chain.iter().copied().find(|&i| bucket[i].0 == sig) {
            Some(i) => i,
            None => {
                chain.push(bucket.len());
                bucket.push((sig, make()));
                self.len += 1;
                bucket.len() - 1
            }
        };
        &mut bucket[at].1
    }

    /// The slot whose `Sig` equals `sig`, if any.
    pub(crate) fn get(&self, sig: &Sig) -> Option<&T> {
        let bucket = self.buckets.get(&sig.hash128())?;
        self.chains.get(&sig.hash128())?.get(&sig.value_key())?.iter()
            .map(|&i| &bucket[i]).find(|(s, _)| s == sig).map(|(_, t)| t)
    }

    /// Distinct signatures held.
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// The number of hash buckets — coarser than [`SigBuckets::len`],
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

// `MIN-ENGINES` E7a-6 (a), test builds only: how many pair-set summaries this
// thread built — the tester's evidence that the compact path builds none.
#[cfg(test)]
thread_local! {
    static SUMMARIES_BUILT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `MIN-ENGINES` E7a-6 (a), test builds only: the thread's pair-set summaries.
#[cfg(test)]
pub(crate) fn summaries_built_for_test() -> usize {
    SUMMARIES_BUILT.with(|c| c.get())
}

/// `MIN-ENGINES` E7a-6 (a), test builds only: reset the count.
#[cfg(test)]
pub(crate) fn reset_summaries_built_for_test() {
    SUMMARIES_BUILT.with(|c| c.set(0));
}

impl Summary {
    pub(crate) fn of(
        exec: CompleteExecution<'_>,
        wobs: Wobs,
        visible: &[String],
    ) -> Result<Self, ObsError> {
        #[cfg(test)]
        SUMMARIES_BUILT.with(|c| c.set(c.get() + 1));
        // `MIN-ENGINES` E4: the statuses (the §8 refusal first, as before) and
        // the order borrow the rows; the signature then takes them.
        let statuses = statuses(exec, &wobs, visible)?;
        let ord = ord(exec.graph(), &wobs, visible);
        Ok(Self {
            sig: Sig::from_rows(statuses, wobs, visible),
            ord,
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

#[cfg(test)]
#[path = "index_key_tests.rs"]
mod index_key_tests;
