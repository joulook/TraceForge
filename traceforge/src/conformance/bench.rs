//! S7's realistic benchmark: two-phase commit, and what conformance costs.
//!
//! **Test-only**, and in-crate deliberately. The numbers need `Stats`, which
//! `ConfOutcome` does not expose; the alternative was growing the public
//! surface for a benchmark's convenience, in the same step that shrank it by
//! deleting `--naive-oracle`. `verify_conformance` is `pub(crate)` and returns
//! `Outcome`, which carries `stats`, so nothing public changes.
//!
//! # Why 2PC, and not something from the corpus
//!
//! §6.1 matches a visible thread's own send/recv labels **positionally, by
//! value**, so a specification may abstract only the *invisible* part of a
//! system. That disqualifies most of TraceForge's test corpus outright: the
//! locked-bank clients' visible word *is* the lock protocol; `bank.rs` is
//! already its own specification; `job_queue`'s three designs are peers rather
//! than a pair; and `rupaxos` — the most recognisable protocol available —
//! has all-peer nodes, so a specification would have to reproduce each node's
//! full `Prepare/Ack/Propose/Promise` round and would *be* the implementation.
//!
//! 2PC survives because a participant's interface is **three events**:
//! `recv Prepare`, `send Yes|No`, `recv Commit|Abort`. Everything interesting
//! lives in the coordinator, which is invisible.
//!
//! # What the specification abstracts, and what it keeps
//!
//! The oracle **drops the decision rule** — its choice is a free `nondet()`,
//! so it admits `Abort` after two `Yes`, which real 2PC also does under
//! timeouts — and **drops the other `N-2` participants**. Its event count is
//! constant in `N`.
//!
//! It keeps exactly one thing: **both visible participants receive the same
//! decision.** That is *agreement*, the safety property 2PC exists to provide.
//! It is not a restatement of the implementation, since it says nothing about
//! *which* decision, and it is not vacuous.
//!
//! # F41, and why the coordinator is spawned first
//!
//! `ParticipantMsg::Prepare(ThreadId)` puts the coordinator's id into a value a
//! **visible** participant observes, and `ThreadId` is an opaque `u32` handed
//! out in spawn order. If the two programs differed in invisible spawn count
//! before that point, every `Prepare` observation would mismatch and the tool
//! would report a violation that does not exist (**F41**).
//!
//! The workaround is structural: the coordinator is spawned **first** on both
//! sides, so it is `t1` in each, and the visible participants are `t2`/`t3` in
//! each. Because the coordinator cannot capture ids of threads spawned after
//! it, it is told them by an `Init` message — which main sends, and main is
//! invisible, so the message is not observed.
//!
//! **This workaround covers unconditional spawns only** (F44). It is sound
//! here because every spawn below is unconditional.

use std::time::Instant;

use crate::conformance::{verify_conformance, Outcome};
use crate::thread::ThreadId;
use crate::{recv_msg_block, send_msg, thread, ConsType, Config};

#[derive(Clone, PartialEq, Debug)]
enum ToCoordinator {
    Init(Vec<ThreadId>),
    Yes,
    No,
}

#[derive(Clone, PartialEq, Debug)]
enum ToParticipant {
    Prepare(ThreadId),
    Commit,
    Abort,
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

/// Three events, and the whole of what a visible participant observes.
fn participant() {
    let cid = match recv_msg_block::<ToParticipant>() {
        ToParticipant::Prepare(id) => id,
        _ => return,
    };
    let vote = crate::nondet();
    send_msg(
        cid,
        if vote {
            ToCoordinator::Yes
        } else {
            ToCoordinator::No
        },
    );
    let _decision: ToParticipant = recv_msg_block();
}

/// Real 2PC: commit iff every participant voted yes, and tell everyone the
/// same thing.
fn coordinator_correct() {
    let ps = match recv_msg_block::<ToCoordinator>() {
        ToCoordinator::Init(ps) => ps,
        _ => return,
    };
    let me = thread::current().id();
    for p in &ps {
        send_msg(*p, ToParticipant::Prepare(me));
    }
    let mut yes = 0usize;
    for _ in 0..ps.len() {
        match recv_msg_block::<ToCoordinator>() {
            ToCoordinator::Yes => yes += 1,
            _ => {}
        }
    }
    let d = if yes == ps.len() {
        ToParticipant::Commit
    } else {
        ToParticipant::Abort
    };
    for p in &ps {
        send_msg(*p, d.clone());
    }
}

/// **The perturbation, and it is a real bug rather than a synthetic one.**
///
/// The coordinator decides *as it learns*: it answers each vote immediately,
/// committing to those who said yes and aborting the rest once a `No` has
/// arrived. Two participants can then receive **different** decisions, which
/// is exactly the loss of agreement 2PC exists to prevent.
fn coordinator_eager() {
    let ps = match recv_msg_block::<ToCoordinator>() {
        ToCoordinator::Init(ps) => ps,
        _ => return,
    };
    let me = thread::current().id();
    for p in &ps {
        send_msg(*p, ToParticipant::Prepare(me));
    }
    let mut seen_no = false;
    for p in &ps {
        match recv_msg_block::<ToCoordinator>() {
            ToCoordinator::No => seen_no = true,
            _ => {}
        }
        send_msg(
            *p,
            if seen_no {
                ToParticipant::Abort
            } else {
                ToParticipant::Commit
            },
        );
    }
}

/// The implementation, with `n` participants of which the first **two** are
/// declared visible.
///
/// Spawn order is load-bearing (F41): coordinator first, then `p0`, `p1`, then
/// the rest. All unconditional, all before the program communicates — so §8's
/// `check_spawn_order` is satisfied and F-6 does not arise.
fn two_pc(n: usize, eager: bool) -> impl Fn() + Send + Sync + Clone + 'static {
    move || {
        let coord = if eager {
            named("coord", coordinator_eager)
        } else {
            named("coord", coordinator_correct)
        };
        let mut ids = Vec::with_capacity(n);
        for i in 0..n {
            ids.push(named(&format!("p{i}"), participant).thread().id());
        }
        send_msg(coord.thread().id(), ToCoordinator::Init(ids));
    }
}

/// The specification: one invisible oracle and exactly two participants.
///
/// The oracle consumes both votes and **ignores** them, then makes a free
/// choice and sends the *same* decision to both. So the specification admits
/// strictly more behaviour than the implementation — including `Abort` after
/// two `Yes` — while still forbidding disagreement.
fn two_pc_spec() -> impl Fn() + Send + Sync + Clone + 'static {
    || {
        let coord = named("coord", || {
            let ps = match recv_msg_block::<ToCoordinator>() {
                ToCoordinator::Init(ps) => ps,
                _ => return,
            };
            let me = thread::current().id();
            for p in &ps {
                send_msg(*p, ToParticipant::Prepare(me));
            }
            for _ in 0..ps.len() {
                let _vote: ToCoordinator = recv_msg_block();
            }
            // The abstraction: a free choice, not the decision rule.
            let d = if crate::nondet() {
                ToParticipant::Commit
            } else {
                ToParticipant::Abort
            };
            // Agreement: the same `d` to both.
            for p in &ps {
                send_msg(*p, d.clone());
            }
        });
        let mut ids = Vec::with_capacity(2);
        for i in 0..2 {
            ids.push(named(&format!("p{i}"), participant).thread().id());
        }
        send_msg(coord.thread().id(), ToCoordinator::Init(ids));
    }
}

fn visible() -> Vec<String> {
    vec!["p0".to_string(), "p1".to_string()]
}

fn cfg() -> Config {
    Config::builder().with_cons_type(ConsType::FIFO).build()
}

/// Plain model checking of the implementation alone — the baseline the
/// overhead ratio is against. It must use the **same** `Config` the
/// conformance run does, or the comparison is not like-for-like.
/// Time `f` properly: repeat it until at least `MIN_SECS` of work has
/// happened, then divide. Returns seconds **per iteration**.
///
/// **F54.** The first version of this benchmark timed a single un-repeated run.
/// At `N <= 4` the plain baseline takes 1-16 ms, which is far too short to
/// divide by: three clean runs gave ratios spanning 32.8x-96.7x and a "flat
/// 80-87x" claim was published from one sample of that. A ratio is only as
/// stable as its denominator.
fn timed<T>(mut f: impl FnMut() -> T) -> (T, f64) {
    const MIN_SECS: f64 = 0.2;
    const ROUNDS: usize = 3;

    // One un-timed pass, so page faults and lazy initialisation land outside
    // every measurement.
    let mut last = f();

    // **The minimum across rounds, not the mean.** This machine is shared, and
    // interference only ever makes a run *slower* — so the minimum is the
    // cleanest estimate of the true cost, and the mean mostly measures what
    // else was running. Three rounds, each averaged over as many iterations as
    // fit in `MIN_SECS`.
    let mut best = f64::INFINITY;
    for _ in 0..ROUNDS {
        let start = Instant::now();
        let mut iters = 0u32;
        loop {
            last = f();
            iters += 1;
            if start.elapsed().as_secs_f64() >= MIN_SECS {
                break;
            }
        }
        let per = start.elapsed().as_secs_f64() / iters as f64;
        if per < best {
            best = per;
        }
    }
    (last, best)
}

fn baseline(n: usize, eager: bool) -> (crate::Stats, f64) {
    let p = two_pc(n, eager);
    timed(move || crate::verify(cfg(), p.clone()))
}

fn conformance(n: usize, eager: bool) -> (Outcome, f64) {
    let imp = two_pc(n, eager);
    let spec = two_pc_spec();
    timed(move || verify_conformance(cfg(), imp.clone(), spec.clone(), visible(), 10_000))
}

/// **The benchmark.** Conforming direction, scaling in `N`.
///
/// Reports executions and wall time for plain model checking and for
/// conformance, and the **ratio**, which is the number S7 should carry — the
/// absolute seconds are a property of this machine.
///
/// **`skipped` is the number of mid-run checks F49's repair suppressed.** It is
/// not zero on this pair and is not expected to be: `reports = 0` therefore
/// establishes "no check that ran found a violation". Every *end-of-execution*
/// check did run — that is guaranteed by `ConfCtx::gate`'s discrimination and
/// its assertion, not by this table.
///
/// `#[ignore]` because it is a measurement, not an assertion: it takes far
/// longer than a unit test and its output is a table for a human. Run it with
/// `cargo test -j 2 -p traceforge --lib conformance::bench -- --ignored --nocapture`.
#[test]
#[ignore]
fn two_pc_scaling() {
    // F61: the specification makes a `nondet()` choice, so the report, skip and
    // inert columns can depend on the run's seed. `cfg()` draws a fresh seed on
    // every call, and `timed` calls the run several times: the printed counts
    // and seed come from the **last** of those calls, which is the `Outcome`
    // `timed` returns, while `conf s` is the fastest of three rounds' average
    // per-call time, over calls that each drew their own seed.
    println!("\n  N | plain execs |  plain s  | reports | skipped |   inert | conf s | ratio | seed");
    println!("----+-------------+-----------+---------+---------+---------+--------+-------+------");
    for n in 2..=5usize {
        let (bs, bt) = baseline(n, false);
        let (out, ct) = conformance(n, false);
        let ratio = if bt > 0.0 { ct / bt } else { f64::NAN };
        println!(
            " {n:2} | {:11} | {bt:9.5} | {:7} | {:7} | {:7} | {ct:6.3} | {ratio:5.1}x | {}",
            bs.execs,
            out.reports.len(),
            out.skipped_gates,
            out.inert_gates,
            out.seed
        );
        // F43: a run that exhausted its inner budget established less than it
        // appears to, and reads as clean to anyone looking at reports alone.
        assert!(
            out.exhaustions.is_empty(),
            "N={n}: {} inner-search exhaustion(s) — this measurement is not sound",
            out.exhaustions.len()
        );
        // **Review `P3-A16`, M4 — reported, not asserted away.** This pair is
        // exactly F49's skip-triggering shape, so mid-run skips are expected
        // and a `skipped == 0` assertion would simply fail. What must never
        // happen is a skipped **completion** gate, and that is guaranteed by
        // construction: `ConfCtx::gate` discriminates on the variant and
        // asserts the precondition. So the count is printed in the table
        // instead, because a reader of `reports = 0` is entitled to know how
        // many checks did not run.
    }
}

/// **The non-conforming direction**: time to first report, which is a
/// different number from time to exhaustion and the one a user experiences
/// when the tool finds something.
#[test]
#[ignore]
fn two_pc_eager_coordinator_is_reported() {
    println!("\n  N | conf s | reports | seed");
    println!("----+--------+---------+------");
    for n in 2..=4usize {
        let (out, ct) = conformance(n, true);
        println!(" {n:2} | {ct:6.3} | {:7} | {}", out.reports.len(), out.seed);
        assert!(
            !out.reports.is_empty(),
            "N={n}: the eager coordinator loses agreement and must be reported"
        );
    }
}

/// The pair is **correct as a pair** — a fast assertion, not a measurement, so
/// it runs in the ordinary suite and guards the benchmark's premise.
///
/// Two claims, and both matter: the correct coordinator conforms (so the
/// specification is not vacuously permissive), and the eager one does not (so
/// it is not vacuously strict). A benchmark whose pair conformed either way
/// would be timing a tautology.
///
/// **Mutation, MEASURED**: replace `coordinator_eager`'s per-vote reply with
/// the correct two-phase reply — the second assertion then fails, because the
/// pair conforms in both directions and the benchmark measures nothing.
///
/// # It was F49's reproduction, and it is not `#[ignore]`d any more
///
/// This test used to panic on the probe thread at `obs.rs:304`
/// (*"observed a send at (t2, 3) whose value is still pending"*), which is
/// what F49 records. The `#[ignore]` said it "should start passing the day
/// F49 is fixed"; `ctx.rs`'s replay-frontier skip is that fix, and the
/// developer's gate-3 pass measured the day: it passes.
///
/// The trigger recorded on the `#[ignore]` — "`nondet()` in a declared visible
/// thread" — was the **first** hypothesis and it is wrong; one visible
/// branching thread is fine. It takes **two**, and the corrected table is in
/// `backlog/flaws.md` F49. The minimal shape is
/// `gate_tests::two_visible_threads_that_both_branch_survive_the_replay_frontier`,
/// which is where the F49 regression lives now; this one keeps the realistic
/// shape.
///
/// **Mutation, MEASURED (F49)**: delete `ctx.rs`'s
/// `if !g1.unreplayed_events.is_empty() { return GateOutcome::Continue; }` —
/// this test fails with the `obs.rs:304` panic above, as do all three other
/// tests in this module.
#[test]
fn the_two_pc_pair_conforms_and_its_perturbation_does_not() {
    let (clean, _) = conformance(2, false);
    assert!(
        clean.reports.is_empty(),
        "the correct 2PC must conform to the agreement specification; got {} report(s)",
        clean.reports.len()
    );
    let (broken, _) = conformance(2, true);
    assert!(
        !broken.reports.is_empty(),
        "the eager coordinator loses agreement and must be reported"
    );
}

/// **A violation this pair commits is still caught at a *fresh-add* gate, not
/// only at completion** — which is the measurable half of A16.
///
/// F49's fix skips any gate whose graph still has unreplayed events, and the
/// argument offered for its soundness is that the completion gate always runs
/// fully replayed, so a violation is reported "later, not never". That
/// argument would be cold comfort if the skip had in practice moved *every*
/// report to the completion gate, because the early gates would then be
/// decorative and the flat overhead ratio would be measuring a search that
/// never prunes.
///
/// It has not. This pair is exactly F49's shape — two declared visible threads
/// that both branch — so the skip fires all through the run, and the reports
/// it produces still come predominantly from fresh-add gates.
///
/// **Measured**, `--lib`, this tree, 2026-09-16 (developer's P3-skips pass):
///
/// | | reports | `FreshSend` | `FreshRecv` | `RevisitApply` | `Completion` |
/// |---|---|---|---|---|---|
/// | `N = 2` | 5 | 2 | 3 | 0 | 0 |
/// | `N = 3` | 28 | 10 | 16 | 0 | **2** |
///
/// **The previous figures in this doc were wrong and are corrected here.** They
/// read "`N = 3`: 15 `FreshRecv` and 13 `FreshSend`" with no completion
/// reports, and they were taken on a **pre-F42** build: F42's inertness skip
/// defers some fresh-add gates, which moves both the split between the two
/// fresh gates and — at `N = 3` — two reports onto the completion gate. The
/// assertion below was always the weaker "at least one fresh-add report",
/// which is why it did not notice; the numbers in the prose did not survive
/// the change and a reader would have trusted them.
///
/// The accompanying claim that the skip fired "1379 times across 59,925 gate
/// calls over the whole benchmark, of which none was a completion gate" is
/// **not re-verified** and is removed rather than restated: a total gate-call
/// count cannot be obtained from outside `ConfCtx::gate`, because both skips
/// return above `cover` and so record no `Exhaustion`. What *is* measured is
/// `Outcome::skipped_gates`, printed per `N` by [`two_pc_scaling`] (840 at
/// `N = 5`). That no skip is ever a completion gate holds by construction —
/// `ConfCtx::gate` discriminates on the variant — not by measurement.
///
/// **Mutation, MEASURED**: delete `ctx.rs`'s replay-frontier skip and this
/// test does not merely fail its assertion — it panics at `obs.rs:304`, which
/// is F49. There is no mutation that keeps the run alive and moves the reports
/// to the completion gate, because the skip is the only thing standing between
/// this program and the pending-value guard; that limit is stated rather than
/// worked around.
#[test]
fn the_eager_pairs_reports_come_from_fresh_add_gates() {
    use crate::conformance::ctx::Gate;

    let (out, _) = conformance(2, true);
    assert!(
        !out.reports.is_empty(),
        "the eager coordinator loses agreement and must be reported"
    );
    let fresh = out
        .reports
        .iter()
        .filter(|r| matches!(r.gate, Some(Gate::FreshSend) | Some(Gate::FreshRecv)))
        .count();
    assert!(
        fresh > 0,
        "every report arrived at a non-fresh gate, so the replay-frontier skip \
         has pushed all detection to completion: {:?}",
        out.reports.iter().map(|r| r.gate).collect::<Vec<_>>()
    );
}

