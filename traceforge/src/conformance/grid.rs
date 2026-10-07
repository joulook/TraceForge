//! P4-DIFF (plan §6) gate 2, the **lead's** half: the grid's fixture
//! registry, the per-configuration runner and the table writer. **Test-only.**
//!
//! Criteria `P4-DIFF.md` revision 5.2, X1 and criterion 13: this file carries
//! programs, encodings, visible sets and the settings each 2PC table's own
//! code states — **no expected value, ceiling, cap or label**. The judgement
//! functions (the plan-key projection, the certification oracle, the §8.8
//! expectation checks, the per-bin maxima, the wall-clock caps and the
//! exclusion labels) live in the tester's `grid_oracle.rs` and
//! `grid_tests.rs`, which also own every assertion (criterion 14).
//!
//! # What a run is
//!
//! One [`GridConfig`] — engine, selector, first-report mode, gated mode and
//! policy, memo, budget, precheck and instrumentation — applied to one
//! [`Fixture`] by [`run_grid`], **on its own thread** with a 32 MiB stack (64
//! MiB for the `ndk` pairs and every unlimited enumerator run — `bench.rs`'s
//! finding, X1), joined through a channel. The run thread wraps the engine
//! call in `catch_unwind`, so an engine panic comes back as
//! [`GridEnd::Panicked`] with its payload — a failure, never "out of reach".
//! Only a `recv_timeout` elapse is a cap ([`GridEnd::Capped`]): the thread is
//! abandoned, [`GRID_TAINTED`] is set for the rest of the process, and the
//! tester runs capped configurations one per process (X1). A `cap` of `None`
//! joins without a timeout — the default subset runs uncapped.
//!
//! The raw engine outcome travels back whole ([`GridRaw`]) so the tester reads
//! `spec_error`/`spec_errors` first (X3) and derives verdicts by
//! `ConfVerdict::of`'s rule written out; nothing here interprets it.
//!
//! # Fixture sourcing (X1, criterion 13)
//!
//! `bench.rs`'s `ndk` family and 2PC pair, `demo.rs`'s leader and ring pairs
//! and `paper_examples.rs`'s relay pair are **reused** through `pub(super)`.
//! Every fixture that lives in a tester-owned file is **copied** here with its
//! source named on the item, and the tester cross-checks each copy against the
//! source test's pinned figures. `ex:sched` is built here as the paper states
//! it (`search.rs`'s `sched_prog` is not it).

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::conformance::cfirst::{self, CFirstOutcome, SweepEnd};
use crate::conformance::config::{CompletionCover, ConfConfig, Engine, GatePolicy, GatedMode};
use crate::conformance::gated::{self, GatedOutcome, ReportSite};
use crate::conformance::search::SearchOpts;
use crate::conformance::selector::{paper_events, InnerOrder, Selector};
use crate::conformance::stateful::{self, StatefulOutcome};
use crate::conformance::{
    bench, demo, generator, paper_examples, verify, verify_conformance_with_opts, ConfBuilder,
    ConfError, ConfVerdict, Outcome, DEFAULT_SEARCH_BUDGET,
};
use crate::exec_graph::ExecutionGraph;
use crate::{send_msg, thread, CommunicationModel, Config, ConsType, Nondet};

pub(super) type Prog = Arc<dyn Fn() + Send + Sync>;

pub(super) fn prog<F: Fn() + Send + Sync + 'static>(f: F) -> Prog {
    Arc::new(f)
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
}

/// An unnamed `asyn` channel of `i32`, created by the calling thread (the
/// tester files' `chan`).
fn chan() -> (crate::channel::Sender<i32>, crate::channel::Receiver<i32>) {
    crate::channel::Builder::<i32>::new()
        .with_comm(CommunicationModel::NoOrder)
        .build()
}

pub(super) fn vis(ns: &[&str]) -> Vec<String> {
    ns.iter().map(|s| (*s).to_string()).collect()
}

/// Every grid run is seeded `with_seed(0)` (F61, X3) unless a 2PC table row
/// names the seed it was recorded under.
pub(super) fn cfg(model: ConsType) -> Config {
    Config::builder().with_cons_type(model).with_seed(0).build()
}

fn seeded(model: ConsType, seed: Option<u64>) -> Config {
    match seed {
        Some(s) => Config::builder().with_cons_type(model).with_seed(s).build(),
        None => cfg(model),
    }
}

// =========================================================================
// The registry
// =========================================================================

/// Which family a fixture belongs to; the tester groups rows and ceilings by it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Group {
    /// The paper's examples and the closed parts' fixtures (X6).
    Paper,
    /// Plan §6's oracle regressions R1 and R2 (X4).
    Regression,
    /// `bench.rs`'s `ndk` family (F63).
    Ndk,
    /// The two-phase-commit pairs (`bench.rs`, `demo.rs`).
    TwoPc,
    /// `generator::corpus`.
    Corpus,
}

/// The entry point a DEMO-2PC table's own code uses (criterion 7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TableEntry {
    /// `verify_conformance(cfg, impl, spec, visible, budget)`: engine-only,
    /// no precheck, no triage, report-and-continue.
    EngineOnly,
    /// `verify(ConfBuilder …stop_at_first_report(true).triage(true)…)`.
    VerifyStopTriage,
}

/// The settings a DEMO-2PC table row was measured under, quoted from the
/// table's own code (criterion 7, round 04 M1). The recorded outer-graph
/// counts are expected values and live with the tester.
#[derive(Clone, Debug)]
pub(super) struct TableRow {
    /// The document the row is in.
    pub(super) document: &'static str,
    /// The test whose loop prints the row.
    pub(super) test: &'static str,
    pub(super) n: usize,
    pub(super) budget: usize,
    pub(super) entry: TableEntry,
    /// The seed the row records, when the table prints one; the other rows
    /// are reproduced under seed 0.
    pub(super) recorded_seed: Option<u64>,
}

#[derive(Clone)]
pub(super) struct Fixture {
    pub(super) name: String,
    /// Where the programs come from, as a citation.
    pub(super) source: &'static str,
    pub(super) group: Group,
    pub(super) implementation: Prog,
    pub(super) specification: Prog,
    pub(super) visible: Vec<String>,
    /// Seeded `0` except for a 2PC row with a recorded seed.
    pub(super) config: Config,
    /// `ex:naive`'s `k`, where the fixture is one.
    pub(super) k: Option<usize>,
    /// `ex:naive`'s encoding (1: `C`'s send first; 2: last), where the
    /// fixture is one.
    pub(super) encoding: Option<u8>,
    /// Runs on a 64 MiB stack on every engine (`bench.rs`'s `ndk_run`).
    pub(super) big_stack: bool,
    /// The DEMO-2PC row this fixture reproduces, if any.
    pub(super) table: Option<TableRow>,
}

impl std::fmt::Debug for Fixture {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Fixture")
            .field("name", &self.name)
            .field("source", &self.source)
            .field("group", &self.group)
            .field("visible", &self.visible)
            .field("seed", &self.config.seed)
            .field("cons_type", &self.config.cons_type)
            .field("k", &self.k)
            .field("encoding", &self.encoding)
            .field("big_stack", &self.big_stack)
            .field("table", &self.table)
            .finish()
    }
}

fn fixture(
    name: impl Into<String>,
    source: &'static str,
    group: Group,
    config: Config,
    visible: Vec<String>,
    implementation: Prog,
    specification: Prog,
) -> Fixture {
    Fixture {
        name: name.into(),
        source,
        group,
        implementation,
        specification,
        visible,
        config,
        k: None,
        encoding: None,
        big_stack: false,
        table: None,
    }
}

// --- copies of tester-owned fixtures, each cited -------------------------

/// **Copy of `enumerator_tests.rs::naive_d`** (also `gated_tests.rs::naive_enc`
/// without `d`): `ex:naive`'s `Impl_k` (`v = 0`) or `Spec_k` (`v = 1`), every
/// mailbox a channel `main` creates before any spawn. Encoding 1 (`c_first`)
/// spawns `c, b1..bk, a`; encoding 2 spawns `b1..bk, a, c`. With `d_asserts`,
/// a visible `d` spawned last fails an assertion (Impl side only).
pub(super) fn naive_d(k: usize, v: i32, c_first: bool, d_asserts: Option<bool>) -> Prog {
    prog(move || {
        let (tx_a, _rx_a) = chan();
        let (tx_c, rx_c) = chan();
        let spawn_c = |tx_a: crate::channel::Sender<i32>, rx_c: crate::channel::Receiver<i32>| {
            named("c", move || {
                tx_a.send_msg(v);
                for _ in 0..k {
                    let _x: i32 = rx_c.recv_msg_block();
                }
            })
        };
        let spawn_bs = |tx_c: &crate::channel::Sender<i32>| {
            for i in 1..=k {
                let t = tx_c.clone();
                let _b = named(&format!("b{i}"), move || t.send_msg(1));
            }
        };
        if c_first {
            let _c = spawn_c(tx_a, rx_c);
            spawn_bs(&tx_c);
            let _a = named("a", || {});
        } else {
            spawn_bs(&tx_c);
            let _a = named("a", || {});
            let _c = spawn_c(tx_a, rx_c);
        }
        if let Some(fails) = d_asserts {
            let _d = named("d", move || {
                if fails {
                    crate::assert(false);
                }
            });
        }
    })
}

/// **Copy of `gated_tests.rs::naive_e2`** (`P4-GATED` criterion 5's revisit
/// fixture, E2): encoding 2's threads, `main` spawning `b1, c, b2..bk, a`.
pub(super) fn naive_e2(k: usize, v: i32) -> Prog {
    prog(move || {
        let (tx_a, _rx_a) = chan();
        let (tx_c, rx_c) = chan();
        let t1 = tx_c.clone();
        let _b1 = named("b1", move || t1.send_msg(1));
        let _c = named("c", move || {
            tx_a.send_msg(v);
            for _ in 0..k {
                let _x: i32 = rx_c.recv_msg_block();
            }
        });
        for i in 2..=k {
            let t = tx_c.clone();
            let _b = named(&format!("b{i}"), move || t.send_msg(1));
        }
        let _a = named("a", || {});
    })
}

/// `ex:naive`'s visible set: `a`, `c`, `b1..bk` (`enumerator_tests.rs`).
pub(super) fn naive_visible(k: usize) -> Vec<String> {
    let mut v = vec!["a".to_string(), "c".to_string()];
    v.extend((1..=k).map(|i| format!("b{i}")));
    v
}

/// **`ex:sched` as the paper states it** (`alg.tex`; X1, round 02 m6):
/// `B₁: send(C,7) ‖ B₂: send(C,7) ‖ C: x := recv(); send(D,8) ‖ D: skip`.
/// `C`'s and `D`'s mailboxes are channels `main` creates before any spawn;
/// `main` spawns `b1, b2, c, d`. Impl = Spec, every thread visible.
pub(super) fn ex_sched() -> Prog {
    prog(|| {
        let (tx_c, rx_c) = chan();
        let (tx_d, _rx_d) = chan();
        let t1 = tx_c.clone();
        let _b1 = named("b1", move || t1.send_msg(7));
        let _b2 = named("b2", move || tx_c.send_msg(7));
        let _c = named("c", move || {
            let _x: i32 = rx_c.recv_msg_block();
            tx_d.send_msg(8);
        });
        let _d = named("d", || {});
    })
}

/// **Copy of `apparatus_tests.rs::ex_cone_spec`**: `A: send(C,9) ‖ C: x := recv^b()`.
fn ex_cone_spec() {
    let c = named("c", || {
        let _x: i32 = crate::recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 9i32));
}

/// **Copy of `apparatus_tests.rs::ex_cone_impl`**: `A: skip ‖ D: send(C,9) ‖
/// C: x := recv^b()`.
fn ex_cone_impl() {
    let c = named("c", || {
        let _x: i32 = crate::recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", || {});
    let _d = named("d", move || send_msg(cid, 9i32));
}

/// **Copy of `apparatus_tests.rs::relay_spec`**: `A: send(R,9) ‖ R(inv): y :=
/// recv(); send(C,y) ‖ C: recv()`.
fn relay_spec() {
    let c = named("c", || {
        let _x: i32 = crate::recv_msg_block();
    });
    let cid = c.thread().id();
    let r = named("r", move || {
        let y: i32 = crate::recv_msg_block();
        send_msg(cid, y);
    });
    let rid = r.thread().id();
    let _a = named("a", move || send_msg(rid, 9i32));
}

/// **Copy of `apparatus_tests.rs::blocking_impl`**: `A: send(C,1) ‖ C: recv();
/// recv()`.
fn blocking_impl() {
    let c = named("c", || {
        let _x: i32 = crate::recv_msg_block();
        let _y: i32 = crate::recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 1i32));
}

/// **Copy of `apparatus_tests.rs::direct_of`** at `i32`: `A: send(C,v) ‖ C: recv()`.
fn direct_of(v: i32) -> Prog {
    prog(move || {
        let c = named("c", || {
            let _x: i32 = crate::recv_msg_block();
        });
        let cid = c.thread().id();
        let _a = named("a", move || send_msg(cid, v));
    })
}

/// **Copy of `cfirst_tests.rs::blocking`** (the Blocking pair in `main`/`c`
/// form): `c` receives twice (Impl) or once (Spec); `main` sends 1.
fn blocking_mc(twice: bool) -> Prog {
    prog(move || {
        let c = named("c", move || {
            let _v: i32 = crate::recv_msg_block();
            if twice {
                let _w: i32 = crate::recv_msg_block();
            }
        });
        send_msg(c.thread().id(), 1i32);
    })
}

/// **Copy of `cfirst_tests.rs::nogate`** (`ex:nogate`; also
/// `gated_tests.rs::nogate`): every mailbox a channel `main` creates before
/// any spawn; `main` spawns `u, w, i, a, b, c`. `u: send(a,9) ‖ w: send(b,7)
/// ‖ i: x := recv^nb(); if x = 1 then send(c,8) ‖ a: recv^nb() ‖ b: recv^b();
/// send(i,1) ‖ c: recv^b()`. Visible: `a, b, c`.
pub(super) fn nogate() -> Prog {
    prog(|| {
        let (tx_a, rx_a) = chan();
        let (tx_b, rx_b) = chan();
        let (tx_c, rx_c) = chan();
        let (tx_i, rx_i) = chan();
        let _u = named("u", move || tx_a.send_msg(9));
        let _w = named("w", move || tx_b.send_msg(7));
        let _i = named("i", move || {
            let x: Option<i32> = rx_i.recv_msg();
            if x == Some(1) {
                tx_c.send_msg(8);
            }
        });
        let _a = named("a", move || {
            let _x: Option<i32> = rx_a.recv_msg();
        });
        let _b = named("b", move || {
            let _y: i32 = rx_b.recv_msg_block();
            tx_i.send_msg(1);
        });
        let _c = named("c", move || {
            let _z: i32 = rx_c.recv_msg_block();
        });
    })
}

/// **Copy of `cfirst_tests.rs::restart`** (`ex:restart`, p2p; also in
/// `enumerator_tests.rs`): `main` spawns `c` (skip) then `a`; Impl `a:
/// send(c,1); send(c,6)`; Spec draws `n` from `5..=6`.
pub(super) fn restart(spec: bool) -> Prog {
    prog(move || {
        let c = named("c", || {});
        let cid = c.thread().id();
        let _a = named("a", move || {
            if spec {
                let n = (5..=6usize).nondet();
                send_msg(cid, 1i32);
                send_msg(cid, n as i32);
            } else {
                send_msg(cid, 1i32);
                send_msg(cid, 6i32);
            }
        });
    })
}

/// What `c` does in the `ex:traces` family (**copy of
/// `enumerator_tests.rs::CRecv`**).
#[derive(Clone, Copy, Debug)]
pub(super) enum CRecv {
    /// `x := recv()`.
    Plain,
    /// The paper's `recv(λy. y = 1)`: a tag filter — `a` tags its message `1`
    /// and `b` tags its `2` on both sides.
    OnlyFromA,
    /// `x := recv(); if x == 2 { assert(false) }`.
    AssertOnTwo,
    /// `x := recv(); assume(x == 1)`.
    AssumeOne,
}

/// **Copy of `enumerator_tests.rs::traces`** (`ex:traces` / `ex:rebuild` /
/// §5.1): `main` creates one channel and spawns `a, c, b`; `a` sends `1`
/// (tag 1), `b` sends `2` (tag 2). `ex:rebuild` is Impl `Plain` against Spec
/// `OnlyFromA` under `Bag`, `Tvis = {a, b, c}` (`enumerator_tests.rs`
/// criterion 10).
pub(super) fn traces(c: CRecv) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let ta = tx.clone();
        let _a = named("a", move || ta.send_tagged_msg(1, 1));
        let _c = named("c", move || match c {
            CRecv::Plain => {
                let _x: i32 = rx.recv_msg_block();
            }
            CRecv::OnlyFromA => {
                let _x: i32 = rx.recv_tagged_msg_block(|t| t == Some(1));
            }
            CRecv::AssertOnTwo => {
                let x: i32 = rx.recv_msg_block();
                if x == 2 {
                    crate::assert(false);
                }
            }
            CRecv::AssumeOne => {
                let x: i32 = rx.recv_msg_block();
                crate::assume!(x == 1);
            }
        });
        let _b = named("b", move || tx.send_tagged_msg(2, 2));
    })
}

/// **Copy of `gated_tests.rs::abc`** (plan §5.3 / §5.1's three-thread
/// program; `P4-GATED` criterion 4's certificate-reset pair is `abc("acb",
/// None)` against `abc("acb", Some(2))`): `a` sends 1 (tag 1), `b` sends 2
/// (tag 2), both to one channel `main` creates; `c` receives once — any
/// message, or (`only = Some(t)`) only tag `t`.
pub(super) fn abc(order: &'static str, only: Option<u32>) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let mut rx = Some(rx);
        for ch in order.chars() {
            match ch {
                'a' => {
                    let t = tx.clone();
                    let _a = named("a", move || t.send_tagged_msg(1, 1));
                }
                'b' => {
                    let t = tx.clone();
                    let _b = named("b", move || t.send_tagged_msg(2, 2));
                }
                'c' => {
                    let r = rx.take().expect("conformance: one receiver");
                    let _c = named("c", move || {
                        let _x: i32 = match only {
                            Some(tag) => r.recv_tagged_msg_block(move |t| t == Some(tag)),
                            None => r.recv_msg_block(),
                        };
                    });
                }
                _ => unreachable!("conformance: a spawn order names a, b, c only"),
            }
        }
    })
}

/// **Copy of `gated_tests.rs::forward_pair`** (`P4-GATED` criterion 12's
/// forward-pop pair): `a: send(c,1) ‖ b: send(c,2) ‖ c: x := recv(); send(d,
/// 2 | x)` — Impl sends 2, Spec forwards `x`; `d` is an undeclared thread
/// that never receives, its mailbox a channel. `main` spawns `a, b, c, d`.
pub(super) fn forward_pair(spec: bool) -> Prog {
    prog(move || {
        let (tx, rx) = chan();
        let (tx_d, _rx_d) = chan();
        let ta = tx.clone();
        let _a = named("a", move || ta.send_tagged_msg(1, 1));
        let _b = named("b", move || tx.send_tagged_msg(2, 2));
        let _c = named("c", move || {
            let x: i32 = rx.recv_msg_block();
            tx_d.send_msg(if spec { x } else { 2 });
        });
        let _d = named("d", || {});
    })
}

/// **Copy of `cfirst_tests.rs::a27`** (A27's witness 1): `b: x := recv_msg()
/// ‖ a: assert(false) ‖ c: send(b,1)`, all visible, spawned `b, a, c`; the
/// Spec has `a: skip`.
pub(super) fn a27(fails: bool) -> Prog {
    prog(move || {
        let b = named("b", || {
            let _x: Option<i32> = crate::recv_msg();
        });
        let bid = b.thread().id();
        let _a = named("a", move || {
            if fails {
                crate::assert(false);
            }
        });
        let _c = named("c", move || send_msg(bid, 1i32));
    })
}

/// Plan §6's oracle regression R1 as X4 states it: Impl `A: assert(false)`,
/// Spec `A: skip`, `Tvis = {a}` (`cfirst_tests.rs::visible_error` is the same
/// program with the thread named `w`).
pub(super) fn r1(fails: bool) -> Prog {
    prog(move || {
        let _a = named("a", move || {
            if fails {
                crate::assert(false);
            }
        });
    })
}

/// **Copy of `cfirst_tests.rs::growing`** (plan §6's regression R2): `a:
/// assert(false) ‖ b: send(B,0)` (Impl) vs `a: skip ‖ b: send(B,0)`; `a`
/// spawned first; `b`'s mailbox a channel nobody reads.
pub(super) fn r2(fails: bool) -> Prog {
    prog(move || {
        let (tx, _rx) = chan();
        let _a = named("a", move || {
            if fails {
                crate::assert(false);
            }
        });
        let _b = named("b", move || tx.send_msg(0));
    })
}

// --- Part 7's fixtures (`P4-MIXED` criterion 10; lead-owned, cited to the
// criteria that define them; the tester cross-checks each against its
// criterion's expected values) -------------------------------------------

/// A channel of `i32` under the p2p model (`ConsType::FIFO`'s communication
/// model), created by the calling thread — the server pairs' mailboxes.
fn fifo_chan() -> (crate::channel::Sender<i32>, crate::channel::Receiver<i32>) {
    crate::channel::Builder::<i32>::new()
        .with_comm(crate::channel::cons_to_model(ConsType::FIFO))
        .build()
}

/// `ex:server` (`mixed.tex`; `P4-MIXED` criterion 1), the Impl with `rounds`
/// storage round-trips: `K: send(S,1); x := recv^b() ‖ S: y := recv^b();
/// (send(D,1); z := recv^b()) × rounds; send(K, reply) ‖ D: (w := recv^b();
/// send(S,1)) × rounds`; every mailbox a channel `main` creates; spawned
/// `d, s, k`. With `annotated`, exactly `S`'s storage operations carry
/// `Visibility::Invisible`; `reply = 3` is criterion 7's violating variant.
pub(super) fn server_impl(rounds: usize, annotated: bool, reply: i32) -> Prog {
    prog(move || {
        let (tx_k, rx_k) = fifo_chan();
        let (tx_s, rx_s) = fifo_chan();
        let (tx_d, rx_d) = fifo_chan();
        let ts = tx_s.clone();
        let _d = named("d", move || {
            for _ in 0..rounds {
                let _w: i32 = rx_d.recv_msg_block();
                ts.send_msg(1);
            }
        });
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            for _ in 0..rounds {
                if annotated {
                    tx_d.send_msg_as(crate::Visibility::Invisible, 1);
                    let _z: i32 = rx_s.recv_msg_block_as(crate::Visibility::Invisible);
                } else {
                    tx_d.send_msg(1);
                    let _z: i32 = rx_s.recv_msg_block();
                }
            }
            tx_k.send_msg(reply);
        });
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
    })
}

/// `ex:server`'s Spec: `K: send(S,1); x := recv^b() ‖ S: y := recv^b();
/// send(K,2)`; spawned `s, k`.
pub(super) fn server_spec() -> Prog {
    prog(|| {
        let (tx_k, rx_k) = fifo_chan();
        let (tx_s, rx_s) = fifo_chan();
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            tx_k.send_msg(2);
        });
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
    })
}

/// `ex:serverblock` (`P4-MIXED` criterion 2): `S` replies, then
/// `send^i(D,1); z := recv^{b,i}()`; `D: w := recv^b()` never answers;
/// spawned `d, s, k`.
pub(super) fn serverblock_impl() -> Prog {
    prog(|| {
        let (tx_k, rx_k) = fifo_chan();
        let (tx_s, rx_s) = fifo_chan();
        let (tx_d, rx_d) = fifo_chan();
        let _d = named("d", move || {
            let _w: i32 = rx_d.recv_msg_block();
        });
        let _s = named("s", move || {
            let _y: i32 = rx_s.recv_msg_block();
            tx_k.send_msg(2);
            tx_d.send_msg_as(crate::Visibility::Invisible, 1);
            let _z: i32 = rx_s.recv_msg_block_as(crate::Visibility::Invisible);
        });
        let _k = named("k", move || {
            tx_s.send_msg(1);
            let _x: i32 = rx_k.recv_msg_block();
        });
    })
}

/// Branch-dependent visibility (`P4-MIXED` criterion 5): `A: n := nondet();
/// if n then send^v(C,1) else send^i(C,1) ‖ C: x := recv_msg()` (non-blocking);
/// `C`'s mailbox a channel `main` creates; spawned `a, c`.
pub(super) fn branch_dependent() -> Prog {
    prog(|| {
        let (tx_c, rx_c) = chan();
        let _a = named("a", move || {
            if crate::nondet() {
                tx_c.send_msg_as(crate::Visibility::Visible, 1);
            } else {
                tx_c.send_msg_as(crate::Visibility::Invisible, 1);
            }
        });
        let _c = named("c", move || {
            let _x: Option<i32> = rx_c.recv_msg();
        });
    })
}

/// The early-error-cut pair (`P4-MIXED` criterion 7′): `main` creates `X`'s
/// mailbox (read by nobody) and spawns `x: skip` (invisible) then `v`; Impl
/// `V: send^i(X,1); assert(false)`, Spec `V: send^i(X,1)`.
pub(super) fn cut_pair(fails: bool) -> Prog {
    prog(move || {
        let (tx_x, _rx_x) = fifo_chan();
        let _x = named("x", || {});
        let _v = named("v", move || {
            tx_x.send_msg_as(crate::Visibility::Invisible, 1);
            if fails {
                crate::assert(false);
            }
        });
    })
}

/// **Copy of `mixed_tests.rs::corpus_mixed`** (the Part 7 tester's two corpus
/// picks, `P4-MIXED` criterion 10): mixed variants of the generator's
/// `InvisibleRefactor` shape (conforming, `spec_value = None`) and
/// `VisibleMutation` shape (violating, `Some(2)`). `main` — visible — performs
/// a storage round-trip `send^i(R, 1); y := recv^{b,i}()` through an invisible
/// relay `r` before its visible `send(C, y)`; the Spec sends directly (`1`, or
/// the mutation's `2`) and spawns an idle `r` so both sides share the spawn
/// prologue. FIFO, `Tvis = {main, c}`.
pub(super) fn corpus_mixed(spec_value: Option<i32>) -> (Prog, Prog) {
    let imp = prog(|| {
        let c = named("c", || {
            let _x: i32 = crate::recv_msg_block();
        });
        let cid = c.thread().id();
        let me = thread::current().id();
        let r = named("r", move || {
            let x: i32 = crate::recv_msg_block();
            crate::send_msg(me, x);
        });
        crate::send_msg_as(r.thread().id(), crate::Visibility::Invisible, 1);
        let y: i32 = crate::recv_msg_block_as(crate::Visibility::Invisible);
        crate::send_msg(cid, y);
    });
    let w = spec_value.unwrap_or(1);
    let spec = prog(move || {
        let c = named("c", || {
            let _x: i32 = crate::recv_msg_block();
        });
        let _r = named("r", || {});
        crate::send_msg(c.thread().id(), w);
    });
    (imp, spec)
}

/// A registry entry built by a tester (`P4-MIXED` criterion 10's mixed
/// variants of two corpus pairs, which the tester picks and states).
pub(super) fn mixed_fixture(
    name: impl Into<String>,
    source: &'static str,
    config: Config,
    visible: Vec<String>,
    implementation: Prog,
    specification: Prog,
) -> Fixture {
    fixture(
        name,
        source,
        Group::Paper,
        config,
        visible,
        implementation,
        specification,
    )
}

/// `P4-MIXED` criterion 10's benchmarks, kept apart from [`registry`] (Part 6's
/// pinned pair counts): the server family `rounds = 1..=3` in three variants,
/// the serverblock pair, the branch-dependent pair, criterion 7′'s pair and the
/// tester's two corpus picks — 14 entries.
pub(super) fn mixed_fixtures() -> Vec<Fixture> {
    let ks = vis(&["k", "s"]);
    let mut out = Vec::new();
    for rounds in 1..=3usize {
        out.push(fixture(
            format!("mixed/server/r{rounds}/annotated"),
            "grid.rs::server_impl (P4-MIXED criterion 1(b)); FIFO channels, {k,s}",
            Group::Paper,
            cfg(ConsType::FIFO),
            ks.clone(),
            server_impl(rounds, true, 2),
            server_spec(),
        ));
        out.push(fixture(
            format!("mixed/server/r{rounds}/unannotated"),
            "grid.rs::server_impl (P4-MIXED criterion 1(a)); FIFO channels, {k,s}",
            Group::Paper,
            cfg(ConsType::FIFO),
            ks.clone(),
            server_impl(rounds, false, 2),
            server_spec(),
        ));
        out.push(fixture(
            format!("mixed/server/r{rounds}/reply3"),
            "grid.rs::server_impl (P4-MIXED criterion 7, annotated, S replies 3); FIFO, {k,s}",
            Group::Paper,
            cfg(ConsType::FIFO),
            ks.clone(),
            server_impl(rounds, true, 3),
            server_spec(),
        ));
    }
    out.push(fixture(
        "mixed/serverblock",
        "grid.rs::serverblock_impl (P4-MIXED criterion 2); FIFO channels, {k,s}",
        Group::Paper,
        cfg(ConsType::FIFO),
        ks,
        serverblock_impl(),
        server_spec(),
    ));
    out.push(fixture(
        "mixed/branch",
        "grid.rs::branch_dependent (P4-MIXED criterion 5); self-conformance, Bag, {a,c}",
        Group::Paper,
        cfg(ConsType::Bag),
        vis(&["a", "c"]),
        branch_dependent(),
        branch_dependent(),
    ));
    out.push(fixture(
        "mixed/cut",
        "grid.rs::cut_pair (P4-MIXED criterion 7′); FIFO, {v}",
        Group::Paper,
        cfg(ConsType::FIFO),
        vis(&["v"]),
        cut_pair(true),
        cut_pair(false),
    ));
    // The tester's two corpus picks (criterion 10), registered by the lead.
    let (ci, cs) = corpus_mixed(None);
    let (vi, vs) = corpus_mixed(Some(2));
    out.push(fixture(
        "mixed/corpus/InvisibleRefactor",
        "grid.rs::corpus_mixed (copy of mixed_tests.rs::corpus_mixed); FIFO, {main,c}",
        Group::Paper,
        cfg(ConsType::FIFO),
        vis(&["main", "c"]),
        ci,
        cs,
    ));
    out.push(fixture(
        "mixed/corpus/VisibleMutation",
        "grid.rs::corpus_mixed (copy; the Spec sends 2); FIFO, {main,c}",
        Group::Paper,
        cfg(ConsType::FIFO),
        vis(&["main", "c"]),
        vi,
        vs,
    ));
    out
}

// --- the registry ----------------------------------------------------------

/// `ex:naive` at `k` in encoding `1` or `2` (X6; D-6).
pub(super) fn naive_fixture(k: usize, encoding: u8) -> Fixture {
    let c_first = match encoding {
        1 => true,
        2 => false,
        _ => panic!("conformance: ex:naive has encodings 1 and 2"),
    };
    let mut f = fixture(
        format!("ex:naive/k{k}/enc{encoding}"),
        "enumerator_tests.rs::naive_d (copy; gated_tests.rs::naive_enc)",
        Group::Paper,
        cfg(ConsType::Bag),
        naive_visible(k),
        naive_d(k, 0, c_first, None),
        naive_d(k, 1, c_first, None),
    );
    f.k = Some(k);
    f.encoding = Some(encoding);
    f
}

/// `P4-GATED` criterion 5's E2 revisit fixture at `k` (X7's attribution site).
pub(super) fn naive_e2_fixture(k: usize) -> Fixture {
    let mut f = fixture(
        format!("ex:naive/e2/k{k}"),
        "gated_tests.rs::naive_e2 (copy)",
        Group::Paper,
        cfg(ConsType::Bag),
        naive_visible(k),
        naive_e2(k, 0),
        naive_e2(k, 1),
    );
    f.k = Some(k);
    f.encoding = Some(2);
    f
}

/// The paper and closed-part pairs of X6 other than `ex:naive`, each with the
/// model and visible set its source test runs it under.
pub(super) fn paper_fixtures() -> Vec<Fixture> {
    let bag = || cfg(ConsType::Bag);
    let fifo = || cfg(ConsType::FIFO);
    let ac = vis(&["a", "c"]);
    let abc_v = vis(&["a", "b", "c"]);
    let mc = vis(&["main", "c"]);
    vec![
        fixture(
            "ex:cone",
            "apparatus_tests.rs::{ex_cone_impl, ex_cone_spec} (copies); t:ex_cone, asyn, {a,c}",
            Group::Paper,
            bag(),
            ac.clone(),
            prog(ex_cone_impl),
            prog(ex_cone_spec),
        ),
        fixture(
            "relay/apparatus",
            "apparatus_tests.rs::{ex_cone_impl, relay_spec} (copies); t:relay, asyn, {a,c}",
            Group::Paper,
            bag(),
            ac.clone(),
            prog(ex_cone_impl),
            prog(relay_spec),
        ),
        fixture(
            "relay/paper",
            "paper_examples.rs::{p2_relay, p1_direct} (reused); ex:relay, FIFO, {main,c}",
            Group::Paper,
            fifo(),
            mc.clone(),
            prog(paper_examples::p2_relay),
            prog(paper_examples::p1_direct),
        ),
        fixture(
            "relay/paper/rev",
            "paper_examples.rs::{p1_direct, p2_relay} (reused); ex:relay's other orientation",
            Group::Paper,
            fifo(),
            mc.clone(),
            prog(paper_examples::p1_direct),
            prog(paper_examples::p2_relay),
        ),
        fixture(
            "ex:nogate",
            "cfirst_tests.rs::nogate (copy); self-conformance, Bag, {a,b,c}",
            Group::Paper,
            bag(),
            abc_v.clone(),
            nogate(),
            nogate(),
        ),
        fixture(
            "ex:sched",
            "grid.rs::ex_sched (the paper's program, X1); Impl = Spec, Bag, every thread visible",
            Group::Paper,
            bag(),
            vis(&["b1", "b2", "c", "d"]),
            ex_sched(),
            ex_sched(),
        ),
        fixture(
            "ex:restart",
            "cfirst_tests.rs::restart (copy); FIFO, {a,c}",
            Group::Paper,
            fifo(),
            ac.clone(),
            restart(false),
            restart(true),
        ),
        fixture(
            "ex:rebuild",
            "enumerator_tests.rs::traces (copy); Plain vs OnlyFromA, Bag, {a,b,c}",
            Group::Paper,
            bag(),
            abc_v.clone(),
            traces(CRecv::Plain),
            traces(CRecv::OnlyFromA),
        ),
        fixture(
            "traces/self",
            "enumerator_tests.rs::traces (copy); Plain vs Plain, Bag, {a,b,c}",
            Group::Paper,
            bag(),
            abc_v.clone(),
            traces(CRecv::Plain),
            traces(CRecv::Plain),
        ),
        fixture(
            "blocking/apparatus",
            "apparatus_tests.rs::{blocking_impl, direct_of(1)} (copies); t:blocking, asyn, {a,c}",
            Group::Paper,
            bag(),
            ac.clone(),
            prog(blocking_impl),
            direct_of(1),
        ),
        fixture(
            "blocking/cfirst",
            "cfirst_tests.rs::blocking (copy); twice vs once, Bag, {main,c}",
            Group::Paper,
            bag(),
            mc.clone(),
            blocking_mc(true),
            blocking_mc(false),
        ),
        fixture(
            "reset-pair",
            "gated_tests.rs::abc (copy); P4-GATED criterion 4: acb/None vs acb/Some(2), Bag, {a,b,c}",
            Group::Paper,
            bag(),
            abc_v.clone(),
            abc("acb", None),
            abc("acb", Some(2)),
        ),
        fixture(
            "forward-pop",
            "gated_tests.rs::forward_pair (copy); P4-GATED criterion 12, Bag, {a,b,c}",
            Group::Paper,
            bag(),
            abc_v.clone(),
            forward_pair(false),
            forward_pair(true),
        ),
        fixture(
            "a27",
            "cfirst_tests.rs::a27 (copy); A27's witness pair, Bag, {a,b,c}",
            Group::Paper,
            bag(),
            abc_v,
            a27(true),
            a27(false),
        ),
        fixture(
            "R1",
            "grid.rs::r1 (X4's statement; cfirst_tests.rs::visible_error with `w`); Bag, {a}",
            Group::Regression,
            bag(),
            vis(&["a"]),
            r1(true),
            r1(false),
        ),
        fixture(
            "R2",
            "cfirst_tests.rs::growing (copy); Bag, {a,b}",
            Group::Regression,
            bag(),
            vis(&["a", "b"]),
            r2(true),
            r2(false),
        ),
    ]
}

/// `bench.rs`'s `ndk` family (reused): `ndk2` conforming, `ndk3` conforming
/// and `ndk3 bad_A`, under `ndk_run`'s settings (FIFO, seed 0, `Tvis = {c}`;
/// the budget is the run's). Every member runs on a 64 MiB stack.
pub(super) fn ndk_fixtures() -> Vec<Fixture> {
    let mk = |name: &str, imp: Vec<(u64, u64)>, spec: Vec<(u64, u64)>| {
        let mut f = fixture(
            name,
            "bench.rs::{ndk, ndk_conf, ndk3_bad_a} (reused); FIFO, seed 0, {c}",
            Group::Ndk,
            cfg(ConsType::FIFO),
            vis(&["c"]),
            prog(bench::ndk(imp)),
            prog(bench::ndk(spec)),
        );
        f.big_stack = true;
        f
    };
    vec![
        mk("ndk2/conf", bench::ndk_conf(2), bench::ndk_conf(2)),
        mk("ndk3/conf", bench::ndk_conf(3), bench::ndk_conf(3)),
        mk("ndk3/bad_A", bench::ndk_conf(3), bench::ndk3_bad_a()),
    ]
}

/// The DEMO-2PC rows (criterion 7): seventeen, each with the settings its
/// table's code states — the coordinator pair (`bench.rs`), the leader pair
/// and the ring pair (`demo.rs`). `n_max` bounds `N` (the tester's choice per
/// run kind: `N ≤ 3` on the exhaustive sweeping runs, `N ≤ 4` elsewhere).
pub(super) fn two_pc_fixtures(n_max: usize) -> Vec<Fixture> {
    let fifo = ConsType::FIFO;
    let mut out = Vec::new();
    // Coordinator, conforming: `demo_2pc_correct_at_2_3_4`, seeds recorded.
    for (n, seed) in [
        (2usize, 11_267_641_651_409_304_418u64),
        (3, 7_492_669_099_539_880_903),
        (4, 1_784_307_368_278_839_636),
    ] {
        if n > n_max {
            break;
        }
        let mut f = fixture(
            format!("2pc/coord/conf/n{n}"),
            "bench.rs::{two_pc(n,false), two_pc_spec} (reused); DEMO-2PC.md, {p0,p1}",
            Group::TwoPc,
            seeded(fifo, Some(seed)),
            vis(&["p0", "p1"]),
            prog(bench::two_pc(n, false)),
            prog(bench::two_pc_spec()),
        );
        f.table = Some(TableRow {
            document: "DEMO-2PC.md",
            test: "bench::demo_2pc_correct_at_2_3_4",
            n,
            budget: 10_000,
            entry: TableEntry::EngineOnly,
            recorded_seed: Some(seed),
        });
        out.push(f);
    }
    // Coordinator, eager: `demo_2pc_eager_violation_traces`, no seed printed.
    for n in 2..=n_max.min(4) {
        let mut f = fixture(
            format!("2pc/coord/eager/n{n}"),
            "bench.rs::{two_pc(n,true), two_pc_spec} (reused); DEMO-2PC.md, {p0,p1}",
            Group::TwoPc,
            seeded(fifo, None),
            vis(&["p0", "p1"]),
            prog(bench::two_pc(n, true)),
            prog(bench::two_pc_spec()),
        );
        f.table = Some(TableRow {
            document: "DEMO-2PC.md",
            test: "bench::demo_2pc_eager_violation_traces",
            n,
            budget: 10_000,
            entry: TableEntry::VerifyStopTriage,
            recorded_seed: None,
        });
        out.push(f);
    }
    // Leader, conforming: `demo_leader_2pc_conforms`, `n = 2..=3`, no seed
    // recorded in DEMO-2PC-LEADER.md.
    for n in 2..=n_max.min(3) {
        let mut f = fixture(
            format!("2pc/leader/conf/n{n}"),
            "demo.rs::{le_impl(n,false), le_spec(n)} (reused); DEMO-2PC-LEADER.md, le_visible(n)",
            Group::TwoPc,
            seeded(fifo, None),
            demo::le_visible(n),
            prog(demo::le_impl(n, false)),
            prog(demo::le_spec(n)),
        );
        f.table = Some(TableRow {
            document: "DEMO-2PC-LEADER.md",
            test: "demo::demo_leader_2pc_conforms",
            n,
            budget: 10_000,
            entry: TableEntry::EngineOnly,
            recorded_seed: None,
        });
        out.push(f);
    }
    // Leader, split-brain: `demo_leader_2pc_split_brain`, budget 100 000.
    for n in 2..=n_max.min(4) {
        let mut f = fixture(
            format!("2pc/leader/split/n{n}"),
            "demo.rs::{le_impl(n,true), le_spec(n)} (reused); DEMO-2PC-LEADER.md, le_visible(n)",
            Group::TwoPc,
            seeded(fifo, None),
            demo::le_visible(n),
            prog(demo::le_impl(n, true)),
            prog(demo::le_spec(n)),
        );
        f.table = Some(TableRow {
            document: "DEMO-2PC-LEADER.md",
            test: "demo::demo_leader_2pc_split_brain",
            n,
            budget: 100_000,
            entry: TableEntry::VerifyStopTriage,
            recorded_seed: None,
        });
        out.push(f);
    }
    // Ring, conforming: `demo_ring_2pc_conforms`, seeds recorded.
    for (n, seed) in [
        (2usize, 8_694_399_807_746_060_002u64),
        (3, 1_992_948_037_369_921_880),
        (4, 13_733_943_097_982_699_720),
    ] {
        if n > n_max {
            break;
        }
        let mut f = fixture(
            format!("2pc/ring/conf/n{n}"),
            "demo.rs::{ring_impl(n,false), le_spec(n)} (reused); DEMO-2PC-RING.md, le_visible(n)",
            Group::TwoPc,
            seeded(fifo, Some(seed)),
            demo::le_visible(n),
            prog(demo::ring_impl(n, false)),
            prog(demo::le_spec(n)),
        );
        f.table = Some(TableRow {
            document: "DEMO-2PC-RING.md",
            test: "demo::demo_ring_2pc_conforms",
            n,
            budget: 10_000,
            entry: TableEntry::EngineOnly,
            recorded_seed: Some(seed),
        });
        out.push(f);
    }
    // Ring, split-brain: `demo_ring_2pc_split_brain`, budget 10 000.
    for n in 2..=n_max.min(4) {
        let mut f = fixture(
            format!("2pc/ring/split/n{n}"),
            "demo.rs::{ring_impl(n,true), le_spec(n)} (reused); DEMO-2PC-RING.md, le_visible(n)",
            Group::TwoPc,
            seeded(fifo, None),
            demo::le_visible(n),
            prog(demo::ring_impl(n, true)),
            prog(demo::le_spec(n)),
        );
        f.table = Some(TableRow {
            document: "DEMO-2PC-RING.md",
            test: "demo::demo_ring_2pc_split_brain",
            n,
            budget: 10_000,
            entry: TableEntry::VerifyStopTriage,
            recorded_seed: None,
        });
        out.push(f);
    }
    out
}

/// The generator corpus as fixtures: `corpus(seed, per_mode)` (X6: seed 7;
/// 10 per mode for the full grid, 3 in the default subset). The pair's own
/// `Config` is kept except that the seed is pinned to 0 (F61; the
/// generator's `Config` draws a fresh seed).
pub(super) fn corpus_fixtures(seed: u64, per_mode: usize) -> Vec<Fixture> {
    generator::corpus(seed, per_mode)
        .into_iter()
        .map(|p| {
            let mut config = p.config.clone();
            config.seed = 0;
            fixture(
                format!("corpus/{:?}/{:#x}", p.mode, p.seed),
                "generator::corpus (reused); the pair's model, seed pinned to 0",
                Group::Corpus,
                config,
                p.visible.clone(),
                p.implementation.clone(),
                p.specification.clone(),
            )
        })
        .collect()
}

/// The whole registry (X6) for `ex:naive` at `k_naive`, 2PC at `n_max` and
/// the corpus at `per_mode`; the tester picks the subsets per run kind.
pub(super) fn registry(
    k_naive: std::ops::RangeInclusive<usize>,
    n_max: usize,
    per_mode: usize,
) -> Vec<Fixture> {
    let mut out = Vec::new();
    for k in k_naive {
        out.push(naive_fixture(k, 1));
        out.push(naive_fixture(k, 2));
        out.push(naive_e2_fixture(k));
    }
    out.extend(paper_fixtures());
    out.extend(ndk_fixtures());
    out.extend(two_pc_fixtures(n_max));
    out.extend(corpus_fixtures(7, per_mode));
    out
}

// =========================================================================
// The runner
// =========================================================================

/// Which engine a configuration runs (`GridEngine` rather than
/// `config::Engine` so that the enumerator's two arms and the precheck arm are
/// explicit).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum GridEngine {
    /// `verify_conformance_with_opts`, raw `Outcome` (X3).
    Enumerator,
    /// `stateful::run_with(cc, impl, spec, true)`.
    Stateful,
    /// `cfirst::run_with(.., true)`, or `cfirst::run` with `precheck`.
    CompleteFirst,
    /// `gated::run_with(.., true)`, or `gated::run` with `precheck`.
    Gated,
    /// `verify(cc, impl, spec)` as a DEMO-2PC violating table calls it
    /// (`stop_at_first_report(true)`, `triage(true)`; criterion 7).
    Verify,
}

/// The enumerator's search budget (X3: the default-budget arm and the
/// unlimited arm; a 2PC row's own budget).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Budget {
    Default,
    Unlimited,
    Exact(usize),
}

impl Budget {
    pub(super) fn value(self) -> usize {
        match self {
            Budget::Default => DEFAULT_SEARCH_BUDGET,
            Budget::Unlimited => usize::MAX,
            Budget::Exact(n) => n,
        }
    }
}

/// One grid configuration (X3). Fields that an engine does not read are
/// carried unchanged into the row so a table can say what was set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct GridConfig {
    pub(super) engine: GridEngine,
    pub(super) selector: Selector,
    /// `stop_at_first_report` on every engine (plan §6's "stopped at first
    /// report"; on the enumerator, the stop flag of
    /// `verify_conformance_with_opts`).
    pub(super) stop_at_first_report: bool,
    pub(super) gated_mode: GatedMode,
    pub(super) gate_policy: GatePolicy,
    /// The enumerator's memo (`SearchOpts::memo`).
    pub(super) memo: bool,
    /// The enumerator's budget; the sweeping engines take the same figure as
    /// `search_budget` (their sweeps are unbounded under Parts 4–5).
    pub(super) budget: Budget,
    /// Complete-first and gated: `run` (precheck on) instead of `run_with`.
    pub(super) precheck: bool,
    /// The enumerator's `SearchOpts::instrument`.
    pub(super) instrumented: bool,
    /// Complete-first's early-error cut (plan §6 runs it off).
    pub(super) early_error_cut: bool,
    /// `P4-FLAT`: the completion-question engine of the complete-first and
    /// gated checkers; `Flat` runs only with `precheck` and on those engines
    /// (refused by `run_grid` otherwise).
    pub(super) completion_cover: CompletionCover,
}

impl GridConfig {
    /// `engine` with every other knob at plan §6's defaults: `Ltr`,
    /// report-and-continue, `Exhaustive`/`Always`, memo off, the default
    /// budget, no precheck, uninstrumented, the cut off.
    pub(super) fn new(engine: GridEngine) -> Self {
        Self {
            engine,
            selector: Selector::Ltr,
            stop_at_first_report: false,
            gated_mode: GatedMode::Exhaustive,
            gate_policy: GatePolicy::Always,
            memo: false,
            budget: Budget::Default,
            precheck: false,
            instrumented: false,
            early_error_cut: false,
            completion_cover: CompletionCover::Sweep,
        }
    }

    pub(super) fn cover(mut self, c: CompletionCover) -> Self {
        self.completion_cover = c;
        self
    }

    pub(super) fn selector(mut self, s: Selector) -> Self {
        self.selector = s;
        self
    }

    pub(super) fn stop(mut self, b: bool) -> Self {
        self.stop_at_first_report = b;
        self
    }

    pub(super) fn gated(mut self, m: GatedMode, p: GatePolicy) -> Self {
        self.gated_mode = m;
        self.gate_policy = p;
        self
    }

    pub(super) fn memo(mut self, b: bool) -> Self {
        self.memo = b;
        self
    }

    pub(super) fn budget(mut self, b: Budget) -> Self {
        self.budget = b;
        self
    }

    pub(super) fn precheck(mut self, b: bool) -> Self {
        self.precheck = b;
        self
    }

    pub(super) fn instrumented(mut self, b: bool) -> Self {
        self.instrumented = b;
        self
    }

    /// The `ConfConfig` this configuration builds for `fixture` (every engine
    /// but the enumerator's raw route reads it; the precheck is skipped unless
    /// `precheck`, in which case `run` performs it).
    pub(super) fn conf_config(&self, fixture: &Fixture) -> ConfConfig {
        let engine = match self.engine {
            GridEngine::Enumerator | GridEngine::Verify => Engine::Enumerator,
            GridEngine::Stateful => Engine::Stateful,
            GridEngine::CompleteFirst => Engine::CompleteFirst,
            GridEngine::Gated => Engine::Gated,
        };
        let b = ConfBuilder::new()
            .config(fixture.config.clone())
            .visible_threads(fixture.visible.clone())
            .engine(engine)
            .selector(self.selector)
            .inner_order(InnerOrder::Recorded)
            .memo(self.memo)
            .search_budget(self.budget.value())
            .stop_at_first_report(self.stop_at_first_report)
            .gated_mode(self.gated_mode)
            .gate_policy(self.gate_policy)
            .early_error_cut(self.early_error_cut)
            .completion_cover(self.completion_cover)
            .skip_spec_errfree_check(!self.precheck)
            .triage(self.engine == GridEngine::Verify);
        b.build()
            .expect("conformance: a grid configuration is in scope")
    }

    /// One line naming every knob, for a table row.
    pub(super) fn label(&self) -> String {
        format!(
            "{:?}/{:?}/stop={}/{:?}/{:?}/memo={}/{:?}/precheck={}/instr={}/cut={}/cover={:?}",
            self.engine,
            self.selector,
            self.stop_at_first_report,
            self.gated_mode,
            self.gate_policy,
            self.memo,
            self.budget,
            self.precheck,
            self.instrumented,
            self.early_error_cut,
            self.completion_cover
        )
    }
}

/// The raw engine outcome, whole (X3: the tester reads `spec_error` /
/// `spec_errors` first).
#[allow(clippy::large_enum_variant)]
pub(super) enum GridRaw {
    Enumerator(Outcome),
    Stateful(StatefulOutcome),
    CompleteFirst(CFirstOutcome),
    Gated(GatedOutcome),
    /// `cfirst::run` / `gated::run` (the precheck arm) and the `Verify`
    /// engine: the rendered route's verdict.
    Verdict(Result<ConfVerdict, ConfError>),
}

impl std::fmt::Debug for GridRaw {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GridRaw::Enumerator(o) => f
                .debug_struct("Enumerator")
                .field("reports", &o.reports.len())
                .field("exhaustions", &o.exhaustions.len())
                .field("end", &o.end)
                .field("spec_error", &o.spec_error.is_some())
                .finish(),
            GridRaw::Stateful(o) => f
                .debug_struct("Stateful")
                .field("reports", &o.reports.len())
                .field("impl_end", &o.impl_end)
                .field("spec_end", &o.spec_end)
                .field("spec_errors", &o.spec_errors.len())
                .finish(),
            GridRaw::CompleteFirst(o) => f
                .debug_struct("CompleteFirst")
                .field("reports", &o.reports.len())
                .field("impl_end", &o.impl_end)
                .field("aborted", &o.aborted)
                .field("spec_errors", &o.spec_errors.len())
                .finish(),
            GridRaw::Gated(o) => f
                .debug_struct("Gated")
                .field("reports", &o.reports.len())
                .field("impl_end", &o.impl_end)
                .field("aborted", &o.aborted)
                .field("spec_errors", &o.spec_errors.len())
                .finish(),
            GridRaw::Verdict(v) => f.debug_tuple("Verdict").field(v).finish(),
        }
    }
}

/// One completed run.
#[derive(Debug)]
pub(super) struct GridResult {
    pub(super) fixture: String,
    pub(super) config: GridConfig,
    pub(super) raw: GridRaw,
    /// Wall time of the engine call alone, on the run thread.
    pub(super) wall: Duration,
    /// The process's `VmHWM` (kB) before and after the run, when
    /// `/proc/self/status` is readable — a process figure that includes every
    /// thread's stack (X7).
    pub(super) vm_hwm_kb: (Option<u64>, Option<u64>),
    /// [`GRID_TAINTED`] was already set when this run started: the tester
    /// drops its timing and memory rows (X1).
    pub(super) tainted_at_start: bool,
    /// The stack the run thread was given, in MiB.
    pub(super) stack_mib: usize,
}

/// How a run ended.
#[allow(clippy::large_enum_variant)]
#[derive(Debug)]
pub(super) enum GridEnd {
    Ok(GridResult),
    /// The engine panicked; the payload rendered (X1: a failure, never "out of
    /// reach").
    Panicked {
        fixture: String,
        config: GridConfig,
        payload: String,
    },
    /// `recv_timeout` elapsed: the run thread was abandoned and the process
    /// marked tainted.
    Capped {
        fixture: String,
        config: GridConfig,
        after: Duration,
    },
}

/// Set once a run has been abandoned (X1); every later timing or memory row
/// of this process is suspect and the tester drops it.
pub(super) static GRID_TAINTED: AtomicBool = AtomicBool::new(false);

pub(super) fn tainted() -> bool {
    GRID_TAINTED.load(Ordering::SeqCst)
}

/// `VmHWM` from `/proc/self/status`, in kB (Linux only; `None` elsewhere).
pub(super) fn vm_hwm_kb() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    line.split_whitespace().nth(1)?.parse().ok()
}

/// The sum over threads of `selector::paper_events` (X7: complete-first's
/// `paper_events_at_first_report` is computed in the grid from its first
/// report graph; the gated engine sums the same way).
pub(super) fn paper_events_total(g: &ExecutionGraph) -> usize {
    g.thread_ids().into_iter().map(|t| paper_events(g, t)).sum()
}

fn panic_text(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_owned()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_owned()
    }
}

/// The engine call itself, on the run thread.
fn call(fixture: &Fixture, config: &GridConfig) -> GridRaw {
    let imp = fixture.implementation.clone();
    let spec = fixture.specification.clone();
    match config.engine {
        GridEngine::Enumerator => {
            // Knob A travels on the engine `Config` (`P4-SELECTOR` S4); the raw
            // route bypasses `ConfBuilder::build`, so it is set here.
            let mut engine_config = fixture.config.clone();
            engine_config.selector = config.selector;
            GridRaw::Enumerator(verify_conformance_with_opts(
                engine_config,
                imp,
                spec,
                fixture.visible.clone(),
                config.budget.value(),
                config.stop_at_first_report,
                SearchOpts {
                    inner_order: InnerOrder::Recorded,
                    memo: config.memo,
                    instrument: config.instrumented,
                },
            ))
        }
        GridEngine::Stateful => {
            let cc = config.conf_config(fixture);
            GridRaw::Stateful(stateful::run_with(&cc, &imp, &spec, true))
        }
        GridEngine::CompleteFirst => {
            let cc = config.conf_config(fixture);
            if config.precheck {
                GridRaw::Verdict(cfirst::run(cc, imp, spec))
            } else {
                GridRaw::CompleteFirst(cfirst::run_with(&cc, &imp, &spec, true))
            }
        }
        GridEngine::Gated => {
            let cc = config.conf_config(fixture);
            if config.precheck {
                GridRaw::Verdict(gated::run(cc, imp, spec))
            } else {
                GridRaw::Gated(gated::run_with(&cc, &imp, &spec, true))
            }
        }
        GridEngine::Verify => {
            let cc = config.conf_config(fixture);
            GridRaw::Verdict(verify(cc, move || imp(), move || spec()))
        }
    }
}

/// The run thread's stack: 32 MiB, or 64 MiB for an `ndk` pair or an
/// unlimited enumerator run (X1).
pub(super) fn stack_mib_for(fixture: &Fixture, config: &GridConfig) -> usize {
    if fixture.big_stack
        || (config.engine == GridEngine::Enumerator && config.budget == Budget::Unlimited)
    {
        64
    } else {
        32
    }
}

/// Run `config` on `fixture` on its own thread, joined through a channel.
/// `cap = None` joins without a timeout.
pub(super) fn run_grid(fixture: &Fixture, config: &GridConfig, cap: Option<Duration>) -> GridEnd {
    // `P4-FLAT` criterion 9: `Flat` runs with the precheck on and on the two
    // sweeping engines only; anything else is refused before a thread exists.
    if config.completion_cover == CompletionCover::Flat {
        let bad_engine = !matches!(config.engine, GridEngine::CompleteFirst | GridEngine::Gated);
        if bad_engine || !config.precheck {
            return GridEnd::Panicked {
                fixture: fixture.name.clone(),
                config: config.clone(),
                payload: format!(
                    "refused: completion_cover(Flat) needs precheck = true and engine in \
                     {{CompleteFirst, Gated}} (got precheck = {}, engine = {:?})",
                    config.precheck, config.engine
                ),
            };
        }
    }
    let tainted_at_start = tainted();
    let stack_mib = stack_mib_for(fixture, config);
    let (tx, rx) = mpsc::channel();
    let f = fixture.clone();
    let c = config.clone();
    let name = format!("grid:{}", fixture.name);
    let handle = std::thread::Builder::new()
        .name(name)
        .stack_size(stack_mib * 1024 * 1024)
        .spawn(move || {
            let before = vm_hwm_kb();
            let started = Instant::now();
            let outcome = catch_unwind(AssertUnwindSafe(|| call(&f, &c)));
            let wall = started.elapsed();
            let after = vm_hwm_kb();
            // A receiver that has given up (a cap) is gone; nothing to do.
            let _ = tx.send((outcome, wall, before, after));
        })
        .expect("conformance: could not spawn the grid run thread");
    // Only a `recv_timeout` elapse is a cap (X1). A disconnected channel
    // means the run thread vanished without sending — unreachable while the
    // thread's closure always sends, but a failure if it ever happens, never
    // "out of reach" (gate 4 round 01, m1).
    let received = match cap {
        None => rx.recv().map_err(|_| None),
        Some(d) => rx.recv_timeout(d).map_err(|e| match e {
            mpsc::RecvTimeoutError::Timeout => Some(d),
            mpsc::RecvTimeoutError::Disconnected => None,
        }),
    };
    match received {
        Err(Some(after)) => {
            GRID_TAINTED.store(true, Ordering::SeqCst);
            drop(handle);
            GridEnd::Capped {
                fixture: fixture.name.clone(),
                config: config.clone(),
                after,
            }
        }
        Err(None) => {
            let _ = handle.join();
            GridEnd::Panicked {
                fixture: fixture.name.clone(),
                config: config.clone(),
                payload: "run thread vanished without sending its outcome".to_owned(),
            }
        }
        Ok((outcome, wall, before, after)) => {
            // The thread has sent, so it is finishing; joining it is cheap
            // and keeps the stack accounting honest.
            let _ = handle.join();
            match outcome {
                Ok(raw) => GridEnd::Ok(GridResult {
                    fixture: fixture.name.clone(),
                    config: config.clone(),
                    raw,
                    wall,
                    vm_hwm_kb: (before, after),
                    tainted_at_start,
                    stack_mib,
                }),
                Err(payload) => GridEnd::Panicked {
                    fixture: fixture.name.clone(),
                    config: config.clone(),
                    payload: panic_text(payload),
                },
            }
        }
    }
}

// The raw outcomes cross the channel whole; this fails to compile if one of
// them stops being `Send`.
#[allow(dead_code)]
fn outcomes_are_send() {
    fn is_send<T: Send>() {}
    is_send::<GridRaw>();
    is_send::<GridResult>();
}

// =========================================================================
// The table writer
// =========================================================================

/// One row: column name and rendered value, in column order.
pub(super) type Row = Vec<(&'static str, String)>;

/// Where the tables go (criterion 8): the path in `P4_DIFF_TABLES`, appended
/// to, else the process's stdout — written through `io::Write`, which bypasses
/// libtest's capture, so it prints with or without `--nocapture` (see `emit`).
pub(super) struct Tables {
    file: Option<std::fs::File>,
}

impl Tables {
    pub(super) fn open() -> Tables {
        let file = std::env::var_os("P4_DIFF_TABLES").map(|p| {
            std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&p)
                .unwrap_or_else(|e| panic!("conformance: P4_DIFF_TABLES={p:?}: {e}"))
        });
        Tables { file }
    }

    fn emit(&mut self, s: &str) {
        use std::io::Write;
        match self.file.as_mut() {
            Some(f) => f
                .write_all(s.as_bytes())
                .expect("conformance: writing the tables"),
            // Not a `print!`: the closed `s5_tests` emission scan matches the
            // macro names literally and `grid.rs` is not on its test-only
            // allowlist (P4-DIFF gate 3, T1). Unlike `print!`, this write
            // bypasses libtest's output capture, so it prints with or without
            // `--nocapture`; only `#[ignore]`d tests call `Tables`, so the
            // difference is limited to them (gate 4 round 01, n1). The
            // scan's intent (no user-facing emission outside `report.rs`) is
            // a production rule and this module is `#[cfg(test)]`; when
            // `s5_tests.rs` next opens, add `grid.rs` to `TEST_ONLY_FILES`
            // and restore the macro.
            None => {
                let mut out = std::io::stdout().lock();
                out.write_all(s.as_bytes())
                    .expect("conformance: writing the tables");
            }
        }
    }

    /// A Markdown table: `title`, then `rows` under the union of their
    /// columns in first-seen order (a missing cell is blank).
    pub(super) fn table(&mut self, title: &str, rows: &[Row]) {
        let mut cols: Vec<&'static str> = Vec::new();
        for r in rows {
            for (c, _) in r {
                if !cols.contains(c) {
                    cols.push(*c);
                }
            }
        }
        let mut s = format!("\n### {title}\n\n");
        if cols.is_empty() {
            s.push_str("(no rows)\n");
            self.emit(&s);
            return;
        }
        s.push_str(&format!("| {} |\n", cols.join(" | ")));
        s.push_str(&format!("|{}\n", "---|".repeat(cols.len())));
        for r in rows {
            let cells: Vec<String> = cols
                .iter()
                .map(|c| {
                    r.iter()
                        .find(|(k, _)| k == c)
                        .map(|(_, v)| v.replace('|', "\\|").replace('\n', " "))
                        .unwrap_or_default()
                })
                .collect();
            s.push_str(&format!("| {} |\n", cells.join(" | ")));
        }
        self.emit(&s);
    }

    /// A paragraph (a note under a table, a listing of excluded runs).
    pub(super) fn note(&mut self, text: &str) {
        self.emit(&format!("\n{text}\n"));
    }
}

fn push<T: std::fmt::Debug>(row: &mut Row, k: &'static str, v: T) {
    row.push((k, format!("{v:?}")));
}

fn push_d<T: std::fmt::Display>(row: &mut Row, k: &'static str, v: T) {
    row.push((k, v.to_string()));
}

/// The settings columns every row starts with.
fn settings_columns(fixture: &str, config: &GridConfig, row: &mut Row) {
    push_d(row, "fixture", fixture);
    push(row, "engine", config.engine);
    push(row, "selector", config.selector);
    push_d(row, "stop", config.stop_at_first_report);
    push(row, "gated_mode", config.gated_mode);
    push(row, "policy", config.gate_policy);
    push_d(row, "memo", config.memo);
    push(row, "budget", config.budget);
    push_d(row, "precheck", config.precheck);
    push_d(row, "instrumented", config.instrumented);
    push(row, "cover", config.completion_cover);
}

/// `P4-FLAT` criterion 9: `FlatCounters`' columns, absent under `Sweep`.
fn flat_columns(row: &mut Row, fc: Option<&crate::conformance::FlatCounters>) {
    let Some(fc) = fc else {
        return;
    };
    push_d(row, "flat_calls", fc.calls);
    push_d(row, "flat_visits", fc.visits);
    push_d(row, "flat_nd_branches", fc.nd_branches);
    push_d(row, "flat_source_branches", fc.source_branches);
    push_d(row, "flat_source_recursions", fc.source_recursions);
    push_d(row, "flat_send_kills", fc.send_kills);
    push_d(row, "flat_slot_kills", fc.slot_kills);
    push_d(row, "flat_source_kills", fc.source_kills);
    push_d(row, "flat_done_kills", fc.done_kills);
    push_d(row, "flat_witnesses", fc.witnesses);
    push_d(row, "flat_max_depth", fc.max_depth);
    push_d(row, "flat_wall_time_ms", fc.wall_time_ms);
}

fn sweep_split(ends: &[SweepEnd]) -> String {
    let n = |e: SweepEnd| ends.iter().filter(|x| **x == e).count();
    format!(
        "witness={} exhausted={} aborted={} budgeted={}",
        n(SweepEnd::Witness),
        n(SweepEnd::Exhausted),
        n(SweepEnd::Aborted),
        n(SweepEnd::Budgeted)
    )
}

/// Every field of the engine's own record, flattened into one row (X7: "the
/// engine's own record is kept whole"), with the run's wall time and memory
/// figures. No derived ratio is computed here.
pub(super) fn row_of(r: &GridResult) -> Row {
    let mut row = Row::new();
    settings_columns(&r.fixture, &r.config, &mut row);
    push_d(&mut row, "wall_ms", r.wall.as_millis());
    push(&mut row, "vm_hwm_kb_before", r.vm_hwm_kb.0);
    push(&mut row, "vm_hwm_kb_after", r.vm_hwm_kb.1);
    push_d(&mut row, "tainted_at_start", r.tainted_at_start);
    push_d(&mut row, "stack_mib", r.stack_mib);
    match &r.raw {
        GridRaw::Enumerator(o) => {
            push_d(&mut row, "reports", o.reports.len());
            push_d(&mut row, "exhaustions", o.exhaustions.len());
            push_d(&mut row, "diagnostics", o.diagnostics.len());
            push(&mut row, "end", o.end);
            push_d(&mut row, "skipped_gates", o.skipped_gates);
            push_d(&mut row, "inert_gates", o.inert_gates);
            push_d(&mut row, "seed", o.seed);
            push_d(&mut row, "spec_error", o.spec_error.is_some());
            push(
                &mut row,
                "outer_graphs(execs+block)",
                o.stats.as_ref().map(|s| s.execs + s.block),
            );
            let c = &o.counters;
            push_d(&mut row, "gate_invocations", c.gate_invocations);
            push_d(&mut row, "gate_skipped_inert", c.gate_skipped_inert);
            push_d(&mut row, "gate_skipped_replay", c.gate_skipped_replay);
            push_d(&mut row, "gate_skipped_pruned", c.gate_skipped_pruned);
            push_d(&mut row, "gate_skipped_disabled", c.gate_skipped_disabled);
            push_d(&mut row, "gate_skipped_aborted", c.gate_skipped_aborted);
            push_d(&mut row, "cover_calls", c.cover_calls);
            push_d(&mut row, "cover_exhaustions", c.cover_exhaustions);
            push_d(&mut row, "rebuilds_taken", c.rebuilds_taken);
            push_d(
                &mut row,
                "rebuilds_skipped_initial_seed",
                c.rebuilds_skipped_initial_seed,
            );
            push_d(
                &mut row,
                "rebuilds_skipped_exhausted_seed",
                c.rebuilds_skipped_exhausted_seed,
            );
            push_d(&mut row, "spec_visit_calls", c.spec_visit_calls);
            push_d(
                &mut row,
                "spec_visit_calls_extend",
                c.spec_visit_calls_extend,
            );
            push_d(
                &mut row,
                "spec_visit_calls_rebuild",
                c.spec_visit_calls_rebuild,
            );
            push_d(&mut row, "memo_hits", c.memo_hits);
            push_d(&mut row, "per_cover", c.per_cover.len());
            push_d(&mut row, "distinct_keys_run_wide", c.distinct_keys_run_wide);
            push_d(&mut row, "f63_distinct_run_wide", c.f63_distinct_run_wide);
            push_d(
                &mut row,
                "explored_complete_keys",
                c.explored_complete_keys.len(),
            );
            push_d(&mut row, "report_keys", c.report_keys.len());
            push_d(
                &mut row,
                "max_paper_events_per_execution",
                c.max_paper_events_per_execution,
            );
            push(
                &mut row,
                "paper_events_at_first_report",
                c.paper_events_at_first_report,
            );
            push_d(&mut row, "executions", c.executions);
            push_d(&mut row, "engine_wall_time_ms", c.wall_time_ms);
            let per: Vec<String> = c
                .per_cover
                .iter()
                .map(|p| {
                    format!(
                        "calls={}/{}/{} hits={} rebuild={}/{}/{} distinct={} per_attempt={:?} f63={:?} so_far={} f63_so_far={}",
                        p.spec_visit_calls,
                        p.spec_visit_calls_extend,
                        p.spec_visit_calls_rebuild,
                        p.memo_hits,
                        p.rebuild_taken,
                        p.rebuild_skipped_initial_seed,
                        p.rebuild_skipped_exhausted_seed,
                        p.distinct_keys,
                        p.per_attempt_distinct,
                        p.f63_per_attempt_distinct,
                        p.run_wide_distinct_so_far,
                        p.f63_run_wide_distinct_so_far
                    )
                })
                .collect();
            push_d(&mut row, "per_cover_detail", per.join("; "));
        }
        GridRaw::Stateful(o) => {
            push_d(&mut row, "reports", o.reports.len());
            push(&mut row, "impl_end", o.impl_end);
            push(&mut row, "spec_end", o.spec_end);
            push_d(&mut row, "spec_errors", o.spec_errors.len());
            push_d(&mut row, "impl_notes", o.impl_notes.len());
            push_d(&mut row, "executions", o.executions);
            push_d(&mut row, "max_paper_events", o.max_paper_events);
            push_d(&mut row, "kept_impl_graphs", o.kept_impl_graphs.len());
            push_d(&mut row, "kept_spec_graphs", o.kept_spec_graphs.len());
            let c = &o.counters;
            push_d(&mut row, "spec_graphs", c.spec_graphs);
            push_d(&mut row, "impl_graphs", c.impl_graphs);
            push_d(&mut row, "sig_key_buckets", c.sig_key_buckets);
            push_d(&mut row, "signatures", c.signatures);
            push_d(&mut row, "orders_held", c.orders_held);
            push_d(&mut row, "lookups", c.lookups);
            push_d(&mut row, "lookups_signature_miss", c.lookups_signature_miss);
            push_d(
                &mut row,
                "lookups_containment_tested",
                c.lookups_containment_tested,
            );
            push_d(&mut row, "lookups_succeeded", c.lookups_succeeded);
            push_d(
                &mut row,
                "lookups_failed_after_tests",
                c.lookups_failed_after_tests,
            );
            push_d(&mut row, "containment_tests", c.containment_tests);
            push_d(&mut row, "counter_reports", c.reports);
            push_d(&mut row, "spec_wall_time_ms", c.spec_wall_time_ms);
            push_d(&mut row, "impl_wall_time_ms", c.impl_wall_time_ms);
        }
        GridRaw::CompleteFirst(o) => {
            push_d(&mut row, "reports", o.reports.len());
            push_d(&mut row, "cut_reports_list", o.cut_reports.len());
            push(&mut row, "impl_end", o.impl_end);
            push_d(&mut row, "spec_errors", o.spec_errors.len());
            push_d(&mut row, "aborted", o.aborted);
            push_d(&mut row, "impl_notes", o.impl_notes.len());
            push_d(&mut row, "executions", o.executions);
            push_d(&mut row, "max_paper_events", o.max_paper_events);
            push_d(&mut row, "kept_impl_graphs", o.kept_impl_graphs.len());
            push_d(
                &mut row,
                "kept_spec_graphs",
                o.kept_spec_graphs.iter().map(Vec::len).sum::<usize>(),
            );
            push_d(&mut row, "witness_cache_len", o.witnesses.len());
            push_d(&mut row, "sweep_ends", sweep_split(&o.sweep_ends));
            push(
                &mut row,
                "paper_events_at_first_report(grid)",
                o.reports.first().map(|(g, _)| paper_events_total(g)),
            );
            let c = &o.counters;
            push_d(&mut row, "impl_graphs", c.impl_graphs);
            push_d(&mut row, "cache_probes", c.cache_probes);
            push_d(&mut row, "cache_hits", c.cache_hits);
            push_d(&mut row, "cache_tests", c.cache_tests);
            push_d(&mut row, "sweeps", c.sweeps);
            push_d(&mut row, "sweeps_successful", c.sweeps_successful);
            push_d(&mut row, "sweeps_failing", c.sweeps_failing);
            push_d(&mut row, "sweeps_aborted", c.sweeps_aborted);
            push(&mut row, "sweep_sizes", &c.sweep_sizes);
            push_d(&mut row, "sweep_graphs", c.sweep_graphs);
            push_d(&mut row, "sweep_graphs_max", c.sweep_graphs_max);
            push_d(&mut row, "witnesses", c.witnesses);
            push_d(&mut row, "witness_duplicates", c.witness_duplicates);
            push_d(&mut row, "counter_reports", c.reports);
            push_d(&mut row, "cut_reports", c.cut_reports);
            push_d(&mut row, "precheck_ran", c.precheck_ran);
            push_d(&mut row, "precheck_wall_time_ms", c.precheck_wall_time_ms);
            push_d(&mut row, "outer_wall_time_ms", c.outer_wall_time_ms);
            push_d(&mut row, "sweep_wall_time_ms", c.sweep_wall_time_ms);
            flat_columns(&mut row, c.flat.as_ref());
        }
        GridRaw::Gated(o) => {
            push_d(&mut row, "reports", o.reports.len());
            let gate_reports = o
                .reports
                .iter()
                .filter(|(_, _, s)| matches!(s, ReportSite::Gate(_)))
                .count();
            push_d(&mut row, "reports_at_gates", gate_reports);
            push_d(
                &mut row,
                "reports_at_completion",
                o.reports.len() - gate_reports,
            );
            push(&mut row, "impl_end", o.impl_end);
            push_d(&mut row, "spec_errors", o.spec_errors.len());
            push_d(&mut row, "aborted", o.aborted);
            push(&mut row, "abort_gate_at", o.abort_gate_at.is_some());
            push_d(&mut row, "impl_notes", o.impl_notes.len());
            push_d(&mut row, "executions", o.executions);
            push_d(&mut row, "max_paper_events", o.max_paper_events);
            push_d(&mut row, "kept_impl_graphs", o.kept_impl_graphs.len());
            push_d(
                &mut row,
                "kept_spec_graphs",
                o.kept_spec_graphs.iter().map(Vec::len).sum::<usize>(),
            );
            push_d(&mut row, "witness_cache_len", o.witnesses.len());
            push_d(&mut row, "sweep_ends", sweep_split(&o.sweep_ends));
            let c = &o.counters;
            push_d(&mut row, "first_failure_mode", c.first_failure_mode);
            push_d(&mut row, "gates", c.gates);
            push_d(&mut row, "gates_inert", c.gates_inert);
            push_d(&mut row, "gates_skipped_replay", c.gates_skipped_replay);
            push_d(
                &mut row,
                "gates_skipped_certified",
                c.gates_skipped_certified,
            );
            push_d(&mut row, "gates_declined", c.gates_declined);
            push_d(&mut row, "c1_tests_carried", c.c1_tests_carried);
            push_d(&mut row, "carried_hits", c.carried_hits);
            push_d(&mut row, "c1_tests_cache", c.c1_tests_cache);
            push_d(&mut row, "gate_cache_hits", c.gate_cache_hits);
            push_d(&mut row, "c1_tests_sweep", c.c1_tests_sweep);
            push_d(&mut row, "gate_sweeps", c.gate_sweeps);
            push_d(&mut row, "gate_sweeps_successful", c.gate_sweeps_successful);
            push_d(&mut row, "gate_sweeps_failing", c.gate_sweeps_failing);
            push_d(&mut row, "gate_sweeps_budgeted", c.gate_sweeps_budgeted);
            push_d(&mut row, "gate_sweeps_aborted", c.gate_sweeps_aborted);
            push(&mut row, "gate_sweep_sizes", &c.gate_sweep_sizes);
            push_d(&mut row, "certificates_set", c.certificates_set);
            push_d(&mut row, "certificate_resets", c.certificate_resets);
            push_d(&mut row, "states_pushed", c.states_pushed);
            push_d(
                &mut row,
                "certified_states_revisited",
                c.certified_states_revisited,
            );
            push_d(&mut row, "reports_certified", c.reports_certified);
            push_d(
                &mut row,
                "reports_by_completion_test",
                c.reports_by_completion_test,
            );
            push(
                &mut row,
                "paper_events_at_first_report",
                c.paper_events_at_first_report,
            );
            push_d(&mut row, "impl_graphs", c.impl_graphs);
            push_d(&mut row, "completion_probes", c.completion_probes);
            push_d(&mut row, "completion_cache_hits", c.completion_cache_hits);
            push_d(&mut row, "completion_cache_tests", c.completion_cache_tests);
            push_d(&mut row, "completion_sweeps", c.completion_sweeps);
            push_d(
                &mut row,
                "completion_sweeps_successful",
                c.completion_sweeps_successful,
            );
            push_d(
                &mut row,
                "completion_sweeps_failing",
                c.completion_sweeps_failing,
            );
            push_d(
                &mut row,
                "completion_sweeps_aborted",
                c.completion_sweeps_aborted,
            );
            push(
                &mut row,
                "completion_sweep_sizes",
                &c.completion_sweep_sizes,
            );
            push_d(&mut row, "witnesses", c.witnesses);
            push_d(&mut row, "witness_duplicates", c.witness_duplicates);
            push_d(&mut row, "counter_reports", c.reports);
            push_d(&mut row, "precheck_ran", c.precheck_ran);
            push_d(&mut row, "precheck_wall_time_ms", c.precheck_wall_time_ms);
            push_d(&mut row, "outer_wall_time_ms", c.outer_wall_time_ms);
            push_d(&mut row, "sweep_wall_time_ms", c.sweep_wall_time_ms);
            flat_columns(&mut row, c.flat.as_ref());
        }
        GridRaw::Verdict(v) => {
            let class = match v {
                Ok(ConfVerdict::Conforms(_)) => "Conforms",
                Ok(ConfVerdict::Reported(_)) => "Reported",
                Ok(ConfVerdict::Inconclusive(_)) => "Inconclusive",
                Err(_) => "Err",
            };
            push_d(&mut row, "verdict", class);
            if let Ok(verdict) = v {
                let o = verdict.outcome();
                push_d(&mut row, "reports", o.reports.len());
                push_d(&mut row, "exhaustions", o.exhaustions.len());
                push_d(&mut row, "notes", o.notes.len());
                push(&mut row, "end", o.end);
                push_d(&mut row, "seed", o.seed);
                push(&mut row, "rendered_engine", o.engine);
                push(&mut row, "spec_errfree", o.spec_errfree);
                push_d(&mut row, "executions", o.counters.executions);
                push_d(&mut row, "engine_wall_time_ms", o.counters.wall_time_ms);
                let precheck_ms = o
                    .cfirst_counters
                    .as_ref()
                    .map(|c| c.precheck_wall_time_ms)
                    .or_else(|| o.gated_counters.as_ref().map(|c| c.precheck_wall_time_ms));
                push(&mut row, "precheck_wall_time_ms", precheck_ms);
                push(
                    &mut row,
                    "precheck_ran",
                    o.cfirst_counters
                        .as_ref()
                        .map(|c| c.precheck_ran)
                        .or_else(|| o.gated_counters.as_ref().map(|c| c.precheck_ran)),
                );
                if let Some(e) = o.flat_eligibility() {
                    push_d(&mut row, "communication_flat", e.communication_flat);
                    push_d(&mut row, "thread_flat", e.thread_flat);
                    push_d(&mut row, "spec_graphs_scanned", e.spec_graphs_scanned);
                    push(&mut row, "first_invisible", &e.first_invisible);
                }
                flat_columns(&mut row, o.flat_counters());
            } else if let Err(crate::conformance::ConfError::SpecNotCommunicationFlat { thread, pos }) = v {
                push_d(&mut row, "communication_flat", false);
                push_d(&mut row, "refused_at", format!("{thread} @ {pos}"));
            }
        }
    }
    row
}

/// A row for a run that did not complete (a panic or a cap), with the
/// settings columns and the reason.
pub(super) fn row_of_end(end: &GridEnd) -> Row {
    let mut row = Row::new();
    match end {
        GridEnd::Ok(r) => return row_of(r),
        GridEnd::Panicked {
            fixture,
            config,
            payload,
        } => {
            settings_columns(fixture, config, &mut row);
            push_d(&mut row, "ended", "panicked");
            push_d(&mut row, "payload", payload);
        }
        GridEnd::Capped {
            fixture,
            config,
            after,
        } => {
            settings_columns(fixture, config, &mut row);
            push_d(&mut row, "ended", "capped");
            push_d(&mut row, "cap_ms", after.as_millis());
        }
    }
    row
}
