//! §11.6's oracle: `vis(Impl) ⊆ vis(Spec)`, computed the expensive way.
//!
//! This is the *ground truth* the differential harness measures the tool
//! against, and it is deliberately **not** the tool's algorithm. `conf-plan.md`
//! §7.3's `--naive-oracle` flag cannot serve: it asks a per-report,
//! specification-side coverability question, and §11.6 asks a whole-program
//! set-inclusion one (F-9, night-run Poll 1, unanimous).
//!
//! # Why it must materialise word sets
//!
//! By Thm. morph, `G₁ ⊑ G₂ ⟺ vis(G₁) ⊆ vis(G₂)`. So an oracle built out of
//! `morphism::refines` / `Search::cover` / `Recompute` would not merely be a
//! third transcription of one algorithm (F-17) — it would measure
//! single-cover-versus-inclusion **against itself** and report zero, which is
//! precisely the number §11.6 exists to produce. The expensive route is the
//! only honest one.
//!
//! # The object
//!
//! `ref2.tex`'s Def. visg, quoted because getting this wrong is the failure
//! this module exists to avoid:
//!
//! > For `G` with `next_P(G) = ∅`, so that every linearisation of `G` is a
//! > trace, `vis(G) ≝ { vis(σ) | σ ∈ lin_P(G) }`, so that
//! > `vis(P) = ⋃_{G ∈ Graphs(P)} vis(G)`.
//!
//! and, settling it (`ref2.tex:382-383`):
//!
//! > `vo_G` need not order two visible events of different threads, and
//! > **distinct linear extensions of it give distinct words, so a graph has a
//! > set of visible traces and not one.**
//!
//! So `vis(G)` is the set of **linear extensions** of `vo(G)`. A canonical
//! representative is not `vis(G)`: `diagnose::canonical_vis` returns one
//! linearisation, and an oracle built on it answers "inclusion holds" on the
//! draft's own pure-(M2) failing pair, because the two representatives
//! coincide (S6 criteria round 1, B1).
//!
//! # The alphabet
//!
//! A word element is a **`(declared thread name, Obs)`** pair, compared with
//! `Obs`'s own `PartialEq`. Both halves are load-bearing:
//!
//! - **The thread component is required here** even though `Obs` drops it.
//!   `obs.rs`'s rustdoc scopes its own justification precisely — the component
//!   "would be equal on both sides of every comparison *the algorithm
//!   performs* … if the matching ever stops being thread-preserving, this
//!   reasoning lapses with it". The oracle is **not** the matching: a `vis`
//!   word interleaves threads, so the thread is not recoverable from position,
//!   and without it `⟨snd,A,1⟩·⟨snd,C,1⟩` and `⟨snd,C,1⟩·⟨snd,A,1⟩` collapse
//!   to one word. The **declared name** is used rather than `ThreadId`,
//!   because ids are handed out per program in spawn order (F41).
//! - **Comparison is `Obs::eq`, never rendered text.** `report::obs_text` is
//!   `{:?}` of the user's message type; `Debug` is not injective and is
//!   type-blind, so `1u32` and `1i64` would compare equal as text while `Obs`
//!   compares them unequal via `msg_equals`. That conflation is in the
//!   permissive direction.
//!
//! # Cost
//!
//! Two multiplicative factors, not one: `|Graphs(P)|`, which is `k!` for the
//! draft's `ex:naive` family, and the number of linear extensions of `vo(G)`
//! per graph, which is factorial in the visible events when `vo` is sparse —
//! up to `(Σₜnₜ)!/Πₜnₜ!`, so two visible threads of three events each is 20
//! per graph and three of four is 34,650. This is tractable only on the
//! micro-programs §11.6's generator emits, and it is what the paper's
//! algorithm exists to avoid. It is **not** a second implementation of the
//! product.
//!
//! # What this cannot falsify
//!
//! The oracle shares `obs::wobs`, `ExecutionGraph::in_porf` and
//! `msg::Val::eq` with the tool, so an error in any of them appears
//! identically on both sides and cancels. F41 is a live instance: a `ThreadId`
//! inside a message value makes an observation depend on invisible spawn
//! count, the tool reports, and **the oracle agrees** — so the pair scores as
//! a correct report and never enters the false-alarm numerator. See
//! `criteria/P3-S6-harness.md` criterion 14.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::ctx::{ConfCtx, ConfMode};
use crate::conformance::morphism::{statuses, CompleteExecution, Status};
use crate::conformance::obs::{wobs, Obs, ObsError};
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::Config;

/// One element of a `vis` word: which declared visible thread observed it, and
/// what was observed.
#[derive(Clone, Debug)]
pub(crate) struct Elem {
    pub(crate) thread: String,
    pub(crate) obs: Obs,
}

impl PartialEq for Elem {
    fn eq(&self, other: &Self) -> bool {
        // `Obs::eq` is the engine's own `msg_equals` on the value; the thread
        // is the declared name. Written out rather than derived so that the
        // value comparison is visibly not a text comparison.
        self.thread == other.thread && self.obs == other.obs
    }
}

/// One visible trace: `vis(σ) ≝ ⟨w, status|_Tvis⟩` — a **pair**, not a word.
///
/// The statuses are as load-bearing as the word: the draft's own status-only
/// variation of `ex:morph` differs in nothing else, and dropping them would
/// make that pair compare equal.
#[derive(Clone, Debug)]
pub(crate) struct VisWord {
    pub(crate) word: Vec<Elem>,
    pub(crate) statuses: BTreeMap<String, Status>,
}

impl PartialEq for VisWord {
    fn eq(&self, other: &Self) -> bool {
        self.statuses == other.statuses && self.word == other.word
    }
}

/// A set of visible traces.
///
/// A `Vec` with membership by `PartialEq`, **not** a `HashSet`: `Obs` has
/// `PartialEq` but no `Eq`/`Hash`, and a rendered key would be a *second,
/// different* equality relation — exactly the text comparison the alphabet
/// exists to avoid. Membership is O(n·m); the generator's size cap is what
/// keeps that affordable.
#[derive(Clone, Debug, Default)]
pub(crate) struct VisSet {
    words: Vec<VisWord>,
}

impl VisSet {
    pub(crate) fn len(&self) -> usize {
        self.words.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    pub(crate) fn contains(&self, w: &VisWord) -> bool {
        self.words.iter().any(|x| x == w)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &VisWord> {
        self.words.iter()
    }

    /// Insert if absent. This is where `vis(P) = ⋃_G vis(G)` becomes a set
    /// rather than a multiset — two *different* graphs can yield the same
    /// word, and a `Vec` without this would over-count the union.
    pub(crate) fn insert(&mut self, w: VisWord) {
        if !self.contains(&w) {
            self.words.push(w);
        }
    }

    /// `self ⊆ other`, and the first witness when it is not.
    ///
    /// The witness is returned rather than a bare `bool` because a failing
    /// inclusion with no exhibit is not evidence anyone can act on.
    pub(crate) fn subset_of(&self, other: &VisSet) -> Result<(), VisWord> {
        match self.words.iter().find(|w| !other.contains(w)) {
            None => Ok(()),
            Some(w) => Err(w.clone()),
        }
    }
}

/// `vis(G)` for one **complete** graph: every linear extension of `vo(G)`.
///
/// Returns `None` when the graph still admits an event — Def. visg is defined
/// only for `next_P(G) = ∅`, and the draft says so again immediately after:
/// "a graph that still admits an event has neither a status nor a set of
/// visible traces". `CompleteExecution::try_finished` is the crate's own
/// recognition of the same precondition.
pub(crate) fn vis_of_graph(
    graph: &ExecutionGraph,
    visible: &[String],
) -> Result<Option<VisSet>, ObsError> {
    let Some(exec) = CompleteExecution::try_finished(graph) else {
        return Ok(None);
    };
    let w = wobs(graph, visible)?;
    let st = statuses(exec, &w, visible)?;

    // The visible events, flattened out of the per-thread rows. Position in
    // this vector is the identity used by the extension enumerator below.
    let mut items: Vec<(String, crate::event::Event, Obs)> = Vec::new();
    for name in visible {
        for (ev, obs) in w.of(name) {
            items.push((name.clone(), *ev, obs.clone()));
        }
    }

    // `vo` is `porf` restricted to visible events, minus the reflexive
    // diagonal. `in_porf` is the engine's own query and is what §6.2 equates
    // the `vo` edge with — note A7: TraceForge's `porf` is
    // `(po ∪ rf ∪ create ∪ join)⁺` where the draft's is `(po ∪ rf)⁺`, a
    // difference the tool and this oracle both inherit and which therefore
    // cancels in the differential.
    let n = items.len();
    let mut before = vec![vec![false; n]; n];
    for i in 0..n {
        for j in 0..n {
            if i != j && graph.in_porf(items[i].1, items[j].1) {
                before[i][j] = true;
            }
        }
    }

    let mut set = VisSet::default();
    let mut chosen: Vec<usize> = Vec::with_capacity(n);
    let mut used = vec![false; n];
    extend(&items, &before, &mut used, &mut chosen, &st, &mut set);
    Ok(Some(set))
}

/// Depth-first enumeration of the linear extensions of `before`.
///
/// At each step every not-yet-used item all of whose `vo`-predecessors are
/// already placed is a legal next element. That is exactly "linear extension
/// of `vo`", and when `vo` is empty on a pair it yields **both** orders —
/// which is the property a canonical representative loses.
fn extend(
    items: &[(String, crate::event::Event, Obs)],
    before: &[Vec<bool>],
    used: &mut [bool],
    chosen: &mut Vec<usize>,
    st: &BTreeMap<String, Status>,
    out: &mut VisSet,
) {
    if chosen.len() == items.len() {
        out.insert(VisWord {
            word: chosen
                .iter()
                .map(|&i| Elem {
                    thread: items[i].0.clone(),
                    obs: items[i].2.clone(),
                })
                .collect(),
            statuses: st.clone(),
        });
        return;
    }
    for i in 0..items.len() {
        if used[i] {
            continue;
        }
        // Every predecessor placed?
        if (0..items.len()).any(|j| !used[j] && j != i && before[j][i]) {
            continue;
        }
        used[i] = true;
        chosen.push(i);
        extend(items, before, used, chosen, st, out);
        chosen.pop();
        used[i] = false;
    }
}

/// Why an enumeration could not be trusted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OracleError {
    /// The exploration did not exhaust the state space, so `vis(P)` is an
    /// under-approximation and `⊆` is weakened in the **permissive**
    /// direction. A hard error, not a warning: prose candour is not a control.
    Truncated { reason: String },
    /// A captured graph still admitted an event, so Def. visg does not apply
    /// to it. Indicates the capture hook fired somewhere other than the
    /// completion gate.
    PartialGraph,
    /// A declared visible thread failed an assertion during the enumeration.
    ///
    /// **No longer returned by `vis_of_program`** (gate 4, M1): such runs are
    /// now *enumerated*, because `Collect` keeps their rows untruncated and
    /// `Status::Errored` is a value `vis` is defined on. Kept so a caller that
    /// wants to refuse the class rather than score it has the variant to
    /// return; `ConfCtx::collect_errors()` is where the failures are observed.
    VisibleError { thread: String },
    Obs(String),
}

/// Enumerate `Graphs(P)` and build `vis(P)`.
///
/// Runs the program under [`ConfMode::Collect`]: gate off, §9's guards **on**,
/// `keep_going_after_error` forced, §8's `check_spawn_order` running, and
/// visible assertion failures recorded without pruning.
///
/// Building through `Must::enable_conformance` is an obligation, not a
/// convenience (S6 criteria round 3): it is what runs `assert_config_in_scope`
/// and arms the handler guards, and it is the reason the oracle's notion of
/// "the executions of `P`" is *structurally* the tool's rather than a
/// hand-maintained invariant. An oracle built on a plain `Must` with
/// `conf = None` would enumerate graphs for programs the tool refuses outright,
/// stop at the first error where the tool keeps going, and never run §8.
pub(crate) fn vis_of_program<F>(
    config: Config,
    visible: &[String],
    program: F,
) -> Result<VisSet, OracleError>
where
    F: Fn() + Send + Sync + 'static,
{
    if config.max_iterations.is_some() {
        return Err(OracleError::Truncated {
            reason: "max_iterations is set, so the exploration is bounded and vis(P) would \
                     be an under-approximation"
                .to_owned(),
        });
    }

    let program = Arc::new(program);
    let program = Arc::new(move || program());
    let must = Rc::new(RefCell::new(Must::new(config.clone(), false)));
    {
        let mut ctx =
            ConfCtx::gate_disabled(config.clone(), visible.to_vec(), ConfMode::Collect);
        ctx.collect_graphs();
        must.borrow_mut().enable_conformance(ctx);
    }

    // `explore` sets `Must::set_current(Some(..))` and never clears it, and a
    // corpus run puts a panicking program next to a clean one as an ordinary
    // case, so the guard is not optional here.
    {
        let _guard = crate::conformance::testing::CurrentMustGuard;
        crate::explore(&must, &program);
    }

    let must = must.borrow();
    let ctx = must
        .conf_ctx()
        .expect("oracle: the collect context was taken and not put back");

    // **No exhaustions check here, deliberately** (F-D9, gate 3). An earlier
    // version of this function checked `ctx.exhaustions().is_empty()` for F43.
    // That guard **cannot fire on this path**: the only `exhaustions.push` is
    // inside the `Cover::BudgetExhausted` arm (`ctx.rs:990`), which sits below
    // `ctx.rs:948`'s `if self.worker.is_none() { return }`, and this function
    // builds its context with `gate_disabled` — the only constructor setting
    // `worker: None`. A guard that cannot fire is reassurance, not a control,
    // and refusing one is why the `search_budget` refusal was declined in the
    // same breath; applying that reasoning to one guard and not the other was
    // the inconsistency gate 3 caught.
    //
    // **Where the obligation actually lives**: on the *tool* side, discharged
    // by the certificate machinery rather than by a check here.
    // `ConfVerdict::of` routes any run whose `not_a_certificate()` is
    // non-empty — `SearchExhausted` among them — to `Inconclusive`, and
    // `differential::Agreement` excludes `Inconclusive` from every ratio and
    // gates its count. An exhausted run therefore can never be scored as a
    // certificate, which is what F43 asks for.

    // **A visible thread's failed assertion is enumerated, not refused** —
    // and this is what makes `ConfMode::Collect`'s branch load-bearing
    // (gate 4, M1).
    //
    // An earlier version returned `Err(OracleError::VisibleError)` here, on
    // `collect_errors().first()`, *before* reading `collected()`. That threw
    // away the very graphs the `Collect` branch exists to keep untruncated, so
    // the branch changed no oracle answer and the poll's edit to a sealed file
    // bought nothing. The fix is not to revert the branch — it is to use it.
    //
    // Enumerating is also what criterion 2(a) asks for ("collect a graph at
    // **every** execution ending — all-threads-completed, deadlock, **and
    // failed assertion**"), and it is semantically right: `Status::Errored` is
    // a value `vis(σ) ≝ ⟨w, status|_Tvis⟩` is defined on, `status_of` extracts
    // it by scanning every index for a `Block(Assert)`, and the draft's own
    // `ex:morph` variation turns on statuses alone.
    //
    // What it yields on a pair is the right answer rather than a refusal: an
    // implementation whose visible thread errors has `vis` words carrying
    // `Errored`; a specification is err-free by §5.4's precheck, so has none;
    // so inclusion **fails**, and the tool also reports (§4.4). Oracle and
    // tool agree, and the pair scores as a correct report instead of
    // collapsing into `DiffError`. That also dissolves gate 4's M4 — §11.5's
    // visible-error shape was un-emittable by the generator only because the
    // oracle refused to answer on it.

    let mut set = VisSet::default();
    for g in ctx.collected() {
        match vis_of_graph(g, visible) {
            Err(e) => return Err(OracleError::Obs(format!("{e}"))),
            Ok(None) => return Err(OracleError::PartialGraph),
            Ok(Some(s)) => {
                for w in s.iter() {
                    set.insert(w.clone());
                }
            }
        }
    }
    Ok(set)
}

/// The oracle's verdict on one pair.
#[derive(Clone, Debug)]
pub(crate) enum Inclusion {
    /// `vis(Impl) ⊆ vis(Spec)`.
    Holds,
    /// It does not, and here is a word of the implementation that no
    /// specification execution produces.
    Fails { witness: VisWord },
}

/// `vis(Impl) ⊆ vis(Spec)`, by Thm. morph the same question as
/// `Impl ⊑ Spec` — and answered without consulting the morphism.
pub(crate) fn includes<I, S>(
    config: Config,
    visible: &[String],
    implementation: I,
    specification: S,
) -> Result<Inclusion, OracleError>
where
    I: Fn() + Send + Sync + 'static,
    S: Fn() + Send + Sync + 'static,
{
    let vi = vis_of_program(config.clone(), visible, implementation)?;
    let vs = vis_of_program(config, visible, specification)?;
    Ok(match vi.subset_of(&vs) {
        Ok(()) => Inclusion::Holds,
        Err(witness) => Inclusion::Fails { witness },
    })
}
