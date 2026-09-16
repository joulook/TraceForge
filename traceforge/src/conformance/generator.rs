//! §11.6's fragment program generator.
//!
//! Emits **pairs**, because the tool takes a pair. Each pair comes with its
//! expected outcome *pinned by construction* — the mode determines the answer,
//! so the acceptance suite is evidence rather than a transcript of whatever
//! the tool happened to do.
//!
//! # This is a template family, not a grammar
//!
//! Stated plainly because criterion 9's rule is that an unstated gap reads as
//! a tested region. This module does **not** implement a general program
//! grammar with a random body. It emits a fixed set of parameterised shapes,
//! one per pairing mode, with the seed choosing parameters within a shape and
//! the sequence of shapes. That is narrower than "the fragment", and it means:
//!
//! - **the false-alarm rate is measured over these shapes**, not over §9's
//!   fragment, and
//! - a phenomenon no shape here can express is **not measured at all**, which
//!   is the failure mode criterion 7's fifth mode exists to prevent.
//!
//! The upside is the one that matters for an oracle-backed harness: the
//! expected answer for each shape is *derived*, not observed.
//!
//! # F-6, satisfied by construction
//!
//! Every shape spawns **every** named thread, visible and invisible, in a
//! fixed prologue before the program communicates, on every path. There is no
//! conditional spawn anywhere in this module and no shape takes a branch
//! before its prologue completes. That is what makes F-6's deferral safe:
//! a conditionally spawned *visible* thread is currently reported as a
//! conformance violation rather than refused as invalid input, so a generator
//! that could emit one would manufacture false violations — and in a
//! differential harness those surface as *disagreements*, the worst possible
//! place for a known false positive.
//!
//! **Coverage gap, recorded**: the generated population therefore cannot
//! exercise conditional spawning at all, so the false-alarm rate is measured
//! over a strictly smaller fragment than §9 admits and must be re-run when
//! F-6's route (i) lands.
//!
//! # What this never emits, in two lists
//!
//! **Refused by §9** — the tool itself rejects these, so no shape could emit
//! them even if one tried: symbolic, mailbox/`TotalOrder`, parallel
//! exploration, lossy sends, predetermined named choices, monitors,
//! symmetric spawning.
//!
//! **Not reached by this generator** — a property of these shapes, derived by
//! reading them:
//!
//! - **values whose equality depends on spawn order** — `ThreadId`, and
//!   anything containing one (**F41**). Every payload here is an `i32`. This
//!   is not a nicety: a `ThreadId` in an observed value makes an observation a
//!   function of invisible spawn count, and **the oracle inherits `msg_equals`
//!   and agrees with the tool**, so such a pair scores as a correct report and
//!   never enters the false-alarm numerator. It is a class this method cannot
//!   measure, not one it under-samples — see criterion 14.
//! - **conditional spawning of invisible threads** (**F44**), which renumbers
//!   later threads so one program yields two visible words for one behaviour.
//!   F-6 covers the visible case only.
//! - `join` between visible threads, `nondet()` branches in a body, tagged and
//!   vector-tagged sends, non-blocking receives, and any program exceeding
//!   [`MAX_VISIBLE_THREADS`] or [`MAX_VISIBLE_EVENTS_PER_THREAD`].
//! - **cross-model sends within {asyn, p2p, cd}** (§11.5's third shape). A
//!   `Pair` carries one `Config`, and `pair()` picks a *single global*
//!   `ConsType` from [`models`] per pair — the shapes have no per-channel
//!   model to vary, so no pair here mixes two. Criterion 9 names the global
//!   pick as the "obvious wrong discharge" of the per-model obligation, and
//!   this is that gap stated rather than left to be inferred from the absence
//!   of a shape.
//! - **visible-error pairs** (§11.5's fourth shape). No shape here has a
//!   visible thread that fails an assertion. This is a **generator** gap and
//!   nothing more. It was until recently a *joint* limit of generator and
//!   oracle — `vis_of_program` returned `Err(OracleError::VisibleError)` above
//!   its enumeration loop, so `compare()` yielded `DiffError::Oracle` and the
//!   harness could not score such a pair at all — but S6 gate 4's M1 removed
//!   that refusal (`oracle.rs:365`): `Status::Errored` is a value `vis` is
//!   defined on, so the oracle now *enumerates* these programs. The obstacle
//!   to emitting the shape is therefore no longer structural; it is that no
//!   shape was written.
//!
//! Both absences are listed because criterion 9's rule is that an unstated gap
//! in the generator reads as a tested region. §11.5's obligation itself is met
//! — the hand-written `refinement_suite.rs` covers all five shapes — so what
//! was missing was the *declaration*, not the coverage.
//!
//! # The size cap, and what enforces it
//!
//! Membership in `VisSet` is O(n·m), and the number of orderings to enumerate
//! grows with two independent parameters — faster than exponentially in the
//! number of visible threads, exponentially in the observations per thread (see
//! the two constants) — so "affordable" is a claim about bounds. Criterion
//! 13 requires these to be **hard grammar bounds, not conventions**, and to say
//! which of "cap it" / "bound the run" was chosen. **Both bounds are capped at
//! construction**, and the event bound has a runtime backstop as well:
//!
//! - [`MAX_VISIBLE_THREADS`] is **asserted in [`pair()`]** on every emitted
//!   pair. It is a property of the `visible` list, which is data this module
//!   holds.
//! - [`MAX_VISIBLE_EVENTS_PER_THREAD`] is **asserted in [`pair()`] against each
//!   shape's declaration**, [`Mode::declared_observations`], so a pair whose
//!   declared per-thread count is over the bound cannot be built. A shape's
//!   closure is opaque, so the count has to be *declared*; a declaration can be
//!   wrong, and two things stand behind it:
//!   - a **test** measures every shape's per-thread count from the oracle's
//!     words and requires it to **equal** the declaration;
//!   - a **runtime cap**: [`Pair::compare`] passes the bound to the oracle, which
//!     checks every visible thread of each collected graph **before** that
//!     graph's linear-extension enumeration. It compares observed counts with
//!     the **bound**, not with the declaration, so it catches a shape that
//!     actually exceeds the bound whatever it declared — but not an
//!     under-declaration that stays within it (declared 1, real 2), which only
//!     the test above catches. It acts only after the engine has explored
//!     `Graphs(P)`, and only per
//!     graph: graphs scored before the first over-cap one, and the whole
//!     implementation when only the specification is over, have already been
//!     enumerated. It binds only pairs run through `Pair::compare`; the uncapped
//!     `differential::compare`, `differential::compare_with_budget`,
//!     `oracle::includes` and `oracle::vis_of_program` bypass it.
//!
//! History: round 1 of `P3-gate4-fixes` (M1) rejected a corpus test alone as a
//! check of today's shapes; round 2 (M1) rejected the runtime cap alone because
//! it runs after exploration. The construction-time declaration is the bound.
//! The equality test checks that each declaration is true; the runtime cap
//! checks only that no run exceeds the bound. Declarations are tested for the
//! modes in `Mode::all()`. A mode missing from that list still has its
//! declaration checked against the bound in `pair()`, but nothing checks that
//! the declaration is true, and the runtime cap is then the only check on its
//! real count. `Mode::all()` is a hand-written list while
//! `declared_observations` is an exhaustive `match`, so a new variant can be
//! declared and still be left out of the list.
//!
//! **F-18 on a corpus that reports.** F-18 is the report sink retaining a
//! serialized graph per report, unbounded across reports. It does not
//! accumulate across a corpus: `compare()` scores each pair's `ConfVerdict`
//! into an [`Agreement`](super::differential::Agreement) — which retains a
//! witness word or a count, never a graph — and drops the outcome before the
//! next pair runs. So the retention bound is *one pair's* report count, and
//! `corpus()`'s size does not enter it.

use std::sync::Arc;

use crate::{recv_msg_block, send_msg, thread, ConsType, Config};

/// **Hard bound on visible threads per emitted pair** (criterion 13).
///
/// Every shape in this module declares exactly two visible threads, so this is
/// the bound the shapes already respect rather than a ceiling chosen to leave
/// room. Raising it is a deliberate act that must be accompanied by a re-run
/// of the corpus cost, because `vis` enumeration grows faster than
/// exponentially in this parameter: the linear extensions of `vo` over `t` visible threads of `k`
/// events each number `(t·k)! / (k!)^t` in the worst case, which at `k = 2`
/// runs 6, 90, 2 520, 113 400 for `t = 2..=5` — each step multiplying by more
/// than the last.
///
/// Asserted in [`pair()`], which is the single construction point.
pub(crate) const MAX_VISIBLE_THREADS: usize = 2;

/// **Hard bound on visible *observations* per visible thread** (criterion 13).
///
/// **The quantity is elements of a `vis` word**, not attempted communications.
/// That is the definition the bound needs: enumeration cost is exponential in the per-thread count of
/// visible events that actually appear in a word (two threads of `k` give
/// `C(2k, k)`: 2, 6, 20, 70, 252 for `k = 1..=5`), and an attempt that
/// contributes no observation costs nothing to enumerate. It is also the only
/// one the check can measure, since a blocked receive is invisible to `vis`.
///
/// **Enforced when a pair is built, on its shape's declaration.** [`pair()`]
/// asserts every entry of [`Mode::declared_observations`] against this
/// constant. Because the count is declared rather than read off the closure, a
/// test checks each declaration against the measured count, and
/// [`Pair::compare`] also passes this constant to the oracle as a per-graph
/// runtime cap. See the module doc for what each layer covers and what it does
/// not.
///
/// **The bound is slack by a factor of two, and that is recorded rather than
/// tightened.** Measured over every mode and both sides, the worst case is
/// **1**, not 2 (developer, `P3-S6-gate4-fixes`, finding 2). An earlier version
/// of this rustdoc claimed `Mode::SpecBlocks` reached the bound "because its
/// specification has `c` receive twice" — **false under the definition this
/// same rustdoc prescribes for the check**: `c`'s second `recv_msg_block()` can
/// never be satisfied, so it contributes no observation, which is exactly what
/// makes `SpecBlocks` an (M3) test rather than an (M1) one. The sentence used
/// one definition for the claim and the other for the check, which is the
/// defect shape the gate-4 fixes existed to remove.
///
/// The bound stays at 2 rather than dropping to the measured 1, so that a shape
/// with a genuinely two-observation visible thread is not rejected on arrival.
/// The cost of the slack is that a corpus check alone would also pass on a
/// generator that had silently lost half its events;
/// `the_events_per_thread_bound_is_not_attained_by_any_shape` is what notices
/// that, and it is why the measured 1 is pinned as a fact rather than left as a
/// margin.
pub(crate) const MAX_VISIBLE_EVENTS_PER_THREAD: usize = 2;

/// A pair, with the answer the mode fixes.
pub(crate) struct Pair {
    pub(crate) mode: Mode,
    pub(crate) seed: u64,
    pub(crate) visible: Vec<String>,
    pub(crate) config: Config,
    pub(crate) implementation: Arc<dyn Fn() + Send + Sync>,
    pub(crate) specification: Arc<dyn Fn() + Send + Sync>,
    /// What the **oracle** must say. Derived from the mode, never observed.
    pub(crate) expect_inclusion: bool,
}

impl Pair {
    /// Run this pair through the differential harness, **with criterion 13's
    /// event cap enforced**.
    ///
    /// This is the entry point for generated pairs. It calls
    /// `differential::compare_capped` with
    /// `Some(MAX_VISIBLE_EVENTS_PER_THREAD)`, so a shape whose visible thread
    /// produces more observations than the bound has that graph refused before
    /// the oracle enumerates its orderings, not after. The check is per graph;
    /// see the module doc for what that leaves unbounded. `search_budget` is passed
    /// through to the tool as for `differential::compare_with_budget`.
    pub(crate) fn compare(
        &self,
        search_budget: Option<usize>,
    ) -> Result<crate::conformance::differential::Agreement, crate::conformance::differential::DiffError>
    {
        let implementation = {
            let f = self.implementation.clone();
            move || f()
        };
        let specification = {
            let f = self.specification.clone();
            move || f()
        };
        crate::conformance::differential::compare_capped(
            self.config.clone(),
            &self.visible,
            implementation,
            specification,
            search_budget,
            Some(MAX_VISIBLE_EVENTS_PER_THREAD),
        )
    }
}

/// The pairing modes of criterion 7's stratification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mode {
    /// `Spec = Impl` up to a cosmetic difference. The floor: inclusion holds
    /// reflexively and the tool must certify.
    Identity,
    /// An **invisible refactor**: a relay inserted on one side. Inclusion
    /// holds in *both* directions, because `ex:relay` publishes
    /// `vis(P₁) = vis(P₂)` — the direct form already orders the send before
    /// the receive through its own `rf` edge, so a relay adds no `vo` edge.
    /// This is the mode that stresses Φ without changing the answer.
    InvisibleRefactor,
    /// A **visible mutation**: a changed observed value. Inclusion fails on
    /// (M1) and the tool must report.
    VisibleMutation,
    /// **(M2) coupling, decoupling the implementation.** The Spec orders a
    /// visible pair the Impl leaves incomparable, so a Spec `vo` edge has no
    /// Impl counterpart: (M2) fails, inclusion fails, the tool must report.
    DecoupleImpl,
    /// **(M2) coupling, decoupling the specification.** The Impl is *more*
    /// ordered, which (M2) allows — `order_is_reflected(spec, impl, ..)` is
    /// one-directional, asserted at `morphism.rs:648-651`. Inclusion holds
    /// non-reflexively and the tool must certify.
    DecoupleSpec,
    /// **(M3): the specification blocks where the implementation completes.**
    ///
    /// `ex:morph`'s published (M3) variation, in the draft's own orientation —
    /// "let `C` in `P₁` perform a second blocking receive that nothing can
    /// satisfy … `C` is blocked in the **specification** and done in the
    /// implementation, so (M3) fails". `P₁` is the specification.
    ///
    /// This mode exists because gate 3 measured that criterion 6's
    /// non-emptiness gates **cannot see a lost mode**: removing
    /// `VisibleMutation` from the corpus left the gates green, because
    /// `DecoupleImpl` kept the same classes non-empty. So "each
    /// morphism-failure class appears in the generated population" has to be
    /// supplied by construction rather than trusted to the gates — and before
    /// this, (M3) appeared in the hand-written suite only.
    ///
    /// The words agree on both sides and **only the statuses differ**, which
    /// is what makes it an (M3) test rather than an (M1) one.
    SpecBlocks,
    /// **Union-covered positive** — the only mode that *could* produce a false
    /// alarm, and **NOT YET CONSTRUCTED**. See the note on the variant's
    /// construction below before relying on anything it produces.
    ///
    /// A false alarm needs an implementation graph covered by the **union** of
    /// specification graphs and by **no single one**: that is exactly the gap
    /// `cor:sound` leaves open ("The premise asks that one graph of Spec cover
    /// `G₁` on its own, where `Impl ⊑ Spec` asks only that
    /// `vis(G₁) ⊆ ⋃ vis(G₂)`"). Minimally it needs a `G₁` with two
    /// `vo`-incomparable matched visible events — words `{ef, fe}` — against
    /// two specification graphs ordering that pair in **opposite** directions,
    /// so each contributes one word and neither contributes both.
    ///
    /// Inclusion **holds**; whether the tool reports is what would be
    /// measured — if the mode existed. **It does not.** The current
    /// construction is `decoupled` against itself, so it is an `Identity` pair
    /// and contributes nothing to the numerator. Anything derived from this
    /// mode must be published as *"0 by construction under this generator, not
    /// measured"*, which is a different and much weaker claim than a measured
    /// rate. A15.
    UnionCovered,
}

impl Mode {
    pub(crate) fn all() -> &'static [Mode] {
        &[
            Mode::Identity,
            Mode::InvisibleRefactor,
            Mode::VisibleMutation,
            Mode::DecoupleImpl,
            Mode::DecoupleSpec,
            Mode::SpecBlocks,
            Mode::UnionCovered,
        ]
    }

    /// Whether this mode's *construction* could produce a false alarm at all —
    /// i.e. an implementation graph covered by the **union** of specification
    /// graphs and by no single one. Only `UnionCovered` is designed to, and it
    /// is not built (A15), so this is currently `false` everywhere.
    ///
    /// Kept separate from [`Mode::is_constructed`] deliberately: if the hub
    /// shape is ever built, `is_constructed` becomes true for `UnionCovered`
    /// and this stays the statement of *what it is for*.
    pub(crate) fn can_false_alarm(self) -> bool {
        matches!(self, Mode::UnionCovered)
    }

    /// Whether this mode is actually built. `UnionCovered` is declared and
    /// **not** constructed; a harness that reports a false-alarm rate must say
    /// so beside the figure rather than let the zero speak for itself.
    pub(crate) fn is_constructed(self) -> bool {
        !matches!(self, Mode::UnionCovered)
    }

    /// What the oracle must answer. **Derived from the mode's construction**,
    /// which is what makes the acceptance suite evidence rather than a
    /// transcript.
    fn expect_inclusion(self) -> bool {
        match self {
            Mode::Identity
            | Mode::InvisibleRefactor
            | Mode::DecoupleSpec
            | Mode::UnionCovered => true,
            Mode::VisibleMutation | Mode::DecoupleImpl | Mode::SpecBlocks => false,
        }
    }

    /// **Criterion 13's event bound, declared per shape** — for each side, the
    /// most visible observations each declared visible thread produces in any
    /// `vis` word of that program.
    ///
    /// Written by hand, because a shape is an opaque closure and the count
    /// cannot be read off it. [`pair()`] asserts every entry against
    /// [`MAX_VISIBLE_EVENTS_PER_THREAD`], so **a pair whose declaration is over
    /// the bound cannot be built** — that is the construction-time grammar bound
    /// (`P3-gate4-fixes` round 2, M1). What a declaration cannot guarantee is its
    /// own truth. A test compares every entry with the count measured from the
    /// oracle's words and requires them to be **equal** — that is the only check
    /// of a declaration's truth. [`Pair::compare`] also passes the bound to the
    /// oracle as a runtime cap, which refuses any graph that actually exceeds the
    /// bound, whatever was declared; it does not detect an under-declaration
    /// that stays within the bound.
    ///
    /// Derived by reading each shape below, not by running it. Every count is 1:
    /// each visible thread sends or receives once. `SpecBlocks`' specification
    /// has `c` *attempt* a second receive that can never complete, which adds no
    /// observation.
    pub(crate) fn declared_observations(self) -> DeclaredObservations {
        const MAIN_C: &[(&str, usize)] = &[("main", 1), ("c", 1)];
        const P_C: &[(&str, usize)] = &[("p", 1), ("c", 1)];
        let both = |t: &'static [(&'static str, usize)]| DeclaredObservations {
            implementation: t,
            specification: t,
        };
        match self {
            Mode::Identity
            | Mode::InvisibleRefactor
            | Mode::VisibleMutation
            | Mode::SpecBlocks => both(MAIN_C),
            Mode::DecoupleImpl | Mode::DecoupleSpec | Mode::UnionCovered => both(P_C),
        }
    }
}

/// Per-side declared maxima of visible observations per visible thread. See
/// [`Mode::declared_observations`].
#[derive(Clone, Copy, Debug)]
pub(crate) struct DeclaredObservations {
    pub(crate) implementation: &'static [(&'static str, usize)],
    pub(crate) specification: &'static [(&'static str, usize)],
}

/// A tiny deterministic PRNG. Reproducibility is criterion 10's obligation and
/// a counterexample nobody can re-run has found nothing, so the seed is
/// carried on every `Pair` and this is the only source of choice.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // SplitMix64.
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[(self.next() % xs.len() as u64) as usize]
    }

    fn val(&mut self) -> i32 {
        (self.next() % 5) as i32 + 1
    }
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

fn names(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

/// The models in scope. Mailbox/`TotalOrder` is refused by §9 and is absent
/// here by construction rather than by filtering.
fn models() -> &'static [ConsType] {
    &[ConsType::FIFO, ConsType::Bag, ConsType::Causal]
}

/// One pair for `mode`, from `seed`.
pub(crate) fn pair(mode: Mode, seed: u64) -> Pair {
    let mut rng = Rng(seed);
    let ct = rng.pick(models());
    let config = Config::builder().with_cons_type(ct).build();
    let v = rng.val();

    // Every shape below spawns its whole prologue first, unconditionally.
    let (implementation, specification, visible): (
        Arc<dyn Fn() + Send + Sync>,
        Arc<dyn Fn() + Send + Sync>,
        Vec<String>,
    ) = match mode {
        Mode::Identity => {
            let p = move || {
                let c = named("c", || {
                    let _x: i32 = recv_msg_block();
                });
                send_msg(c.thread().id(), v);
            };
            (Arc::new(p), Arc::new(p), names(&["main", "c"]))
        }

        Mode::InvisibleRefactor => {
            // Impl relays through an invisible thread; Spec sends directly.
            // `vis` is equal, so inclusion holds both ways.
            let imp = move || {
                let c = named("c", || {
                    let _x: i32 = recv_msg_block();
                });
                let cid = c.thread().id();
                let r = named("r", move || {
                    let x: i32 = recv_msg_block();
                    send_msg(cid, x);
                });
                send_msg(r.thread().id(), v);
            };
            let spec = move || {
                let c = named("c", || {
                    let _x: i32 = recv_msg_block();
                });
                send_msg(c.thread().id(), v);
            };
            (Arc::new(imp), Arc::new(spec), names(&["main", "c"]))
        }

        Mode::VisibleMutation => {
            let w = v + 1;
            let imp = move || {
                let c = named("c", || {
                    let _x: i32 = recv_msg_block();
                });
                send_msg(c.thread().id(), v);
            };
            let spec = move || {
                let c = named("c", || {
                    let _x: i32 = recv_msg_block();
                });
                send_msg(c.thread().id(), w);
            };
            (Arc::new(imp), Arc::new(spec), names(&["main", "c"]))
        }

        // The couple/decouple primitive. `p` is a visible sender, `c` a
        // visible receiver, and the observations are identical on both forms:
        // a send does not observe its destination, and the relay forwards the
        // value unmodified.
        //
        //   coupled   — one invisible relay carries p's message to c, so
        //               `porf` runs p -> relay.recv -> relay.snd -> c and
        //               `vo` orders the visible pair.
        //   decoupled — p sends to an invisible sink and a separate invisible
        //               source feeds c, so no `porf` path joins them.
        Mode::DecoupleImpl => {
            let (imp, spec) = (decoupled(v), coupled(v));
            (imp, spec, names(&["p", "c"]))
        }
        Mode::DecoupleSpec => {
            let (imp, spec) = (coupled(v), decoupled(v));
            (imp, spec, names(&["p", "c"]))
        }

        // **NOT CONSTRUCTED — this is `decoupled` against itself, i.e. an
        // `Identity` pair, and it therefore measures nothing.**
        //
        // It is left here, honestly labelled, rather than deleted, because
        // criterion 7 requires either the mode or a record of what was
        // attempted, and because the obstacle is structural rather than a
        // matter of effort. Recorded as **A15**.
        //
        // What the mode needs: some `G₁ ∈ Graphs(Impl)` whose `vis` is
        // contained in `⋃ vis(G₂)` and in **no single** `vis(G₂)`. Within one
        // graph the values are fixed by the `rf` choice, so `vis(G₁)`'s
        // members differ only in **order**. With the minimal two visible
        // events that means `vis(G₁) = {ef, fe}`, and the specification needs
        // two graphs, one containing only `ef` and the other only `fe` — i.e.
        // two graphs ordering the same visible pair in **opposite**
        // directions.
        //
        // The obstacle: `vo` is `porf` restricted to visible events, so
        // ordering `f` before `e` requires a `porf` path from the visible
        // *receive* to the visible *send*. Every event of a visible thread is
        // itself visible, so such a path can only leave the receiver through a
        // send **of the receiver**, which adds a third visible event and
        // changes the word. The flip is therefore not available at two visible
        // events, and at three or more it has not been attempted here.
        //
        // A first attempt at a hub shape — two visible threads each doing
        // `send; recv`, with one invisible hub whose single receive may read
        // either send — is the identified route and is **unbuilt**.
        Mode::SpecBlocks => {
            // Impl: `c` receives once and is done.
            let imp = Arc::new(move || {
                let c = named("c", || {
                    let _x: i32 = recv_msg_block();
                });
                send_msg(c.thread().id(), v);
            }) as Arc<dyn Fn() + Send + Sync>;
            // Spec: `c` receives twice; nothing can satisfy the second, so it
            // is left `Blocked` where the implementation is `Done`.
            let spec = Arc::new(move || {
                let c = named("c", || {
                    let _x: i32 = recv_msg_block();
                    let _y: i32 = recv_msg_block();
                });
                send_msg(c.thread().id(), v);
            }) as Arc<dyn Fn() + Send + Sync>;
            (imp, spec, names(&["main", "c"]))
        }

        Mode::UnionCovered => (decoupled(v), decoupled(v), names(&["p", "c"])),
    };

    // Criterion 13's bound, **checked rather than conventional**. This is the
    // single construction point, so no pair escapes it. It fires on a shape
    // added later that declares a third visible thread — which is exactly the
    // reader the prose version of this sentence would have misled.
    assert!(
        visible.len() <= MAX_VISIBLE_THREADS,
        "generator: {mode:?} declares {} visible threads, over MAX_VISIBLE_THREADS ({}). \
         `vis` enumeration grows faster than exponentially in this parameter; raising \
         the bound means re-running the corpus cost, not editing the constant",
        visible.len(),
        MAX_VISIBLE_THREADS
    );

    check_declaration(mode, &visible, mode.declared_observations());

    Pair {
        mode,
        seed,
        visible,
        config,
        implementation,
        specification,
        expect_inclusion: mode.expect_inclusion(),
    }
}

/// **Criterion 13's event bound at construction**, on a shape's declaration.
///
/// Panics unless the declaration names exactly the pair's visible threads (so
/// an added thread cannot go undeclared) and every entry is within
/// [`MAX_VISIBLE_EVENTS_PER_THREAD`]. [`pair()`] calls it on every pair it
/// builds.
///
/// A separate function only so a test can pass it a *bad* declaration:
/// [`Mode::declared_observations`] is a fixed `match`, so from `pair()` alone
/// no test could make either assertion fire (developer, `P3-gate4-fixes`
/// round-2 response, finding 1). Behaviour is unchanged.
pub(crate) fn check_declaration(mode: Mode, visible: &[String], declared: DeclaredObservations) {
    for (side, entries) in [
        ("implementation", declared.implementation),
        ("specification", declared.specification),
    ] {
        let mut names: Vec<&str> = entries.iter().map(|(n, _)| *n).collect();
        let mut want: Vec<&str> = visible.iter().map(String::as_str).collect();
        names.sort_unstable();
        want.sort_unstable();
        assert_eq!(
            names, want,
            "generator: {mode:?}'s {side} declaration names {names:?} but the pair's \
             visible threads are {want:?}; every visible thread needs a declared count"
        );
        for (thread, count) in entries {
            assert!(
                *count <= MAX_VISIBLE_EVENTS_PER_THREAD,
                "generator: {mode:?} declares {count} visible observations for `{thread}` \
                 in its {side}, over MAX_VISIBLE_EVENTS_PER_THREAD ({}); an over-bound pair \
                 must not be constructible",
                MAX_VISIBLE_EVENTS_PER_THREAD
            );
        }
    }
}

/// `p`'s message reaches `c` through one invisible relay, so `vo` orders the
/// visible send before the visible receive.
fn coupled(v: i32) -> Arc<dyn Fn() + Send + Sync> {
    Arc::new(move || {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let relay = named("relay", move || {
            let x: i32 = recv_msg_block();
            send_msg(cid, x);
        });
        let rid = relay.thread().id();
        let _p = named("p", move || send_msg(rid, v));
    })
}

/// `p` sends to an invisible **sink** and a *separate* invisible **source**
/// feeds `c`, so no `porf` path joins the two visible events and they are
/// `vo`-incomparable.
///
/// This is **not** "the program before relay insertion": the direct form is
/// already coupled through its own `rf` edge, which is why relay insertion
/// alone changes nothing.
fn decoupled(v: i32) -> Arc<dyn Fn() + Send + Sync> {
    Arc::new(move || {
        let c = named("c", || {
            let _x: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let sink = named("sink", || {
            let _x: i32 = recv_msg_block();
        });
        let sid = sink.thread().id();
        let _src = named("src", move || send_msg(cid, v));
        let _p = named("p", move || send_msg(sid, v));
    })
}

/// A corpus: `per_mode` pairs of each mode, from one seed.
///
/// Every mode is represented, which is criterion 7's per-mode minimum, and the
/// whole corpus is regenerable from `seed` alone.
pub(crate) fn corpus(seed: u64, per_mode: usize) -> Vec<Pair> {
    let mut out = Vec::new();
    for (i, m) in Mode::all().iter().enumerate() {
        for k in 0..per_mode {
            out.push(pair(*m, seed ^ ((i as u64) << 32) ^ k as u64));
        }
    }
    out
}
