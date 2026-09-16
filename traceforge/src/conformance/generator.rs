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
//!   vector-tagged sends, non-blocking receives, and any program with more than
//!   the cap's visible events.

use std::sync::Arc;

use crate::{recv_msg_block, send_msg, thread, ConsType, Config};

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
