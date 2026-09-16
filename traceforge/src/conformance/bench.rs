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
fn baseline(n: usize, eager: bool) -> (crate::Stats, f64) {
    let p = two_pc(n, eager);
    let t = Instant::now();
    let stats = crate::verify(cfg(), p);
    (stats, t.elapsed().as_secs_f64())
}

fn conformance(n: usize, eager: bool) -> (Outcome, f64) {
    let imp = two_pc(n, eager);
    let spec = two_pc_spec();
    let t = Instant::now();
    let out = verify_conformance(cfg(), imp, spec, visible(), 10_000);
    (out, t.elapsed().as_secs_f64())
}

/// **The benchmark.** Conforming direction, scaling in `N`.
///
/// Reports executions and wall time for plain model checking and for
/// conformance, and the **ratio**, which is the number S7 should carry — the
/// absolute seconds are a property of this machine.
///
/// `#[ignore]` because it is a measurement, not an assertion: it takes far
/// longer than a unit test and its output is a table for a human. Run it with
/// `cargo test -j 2 -p traceforge --lib conformance::bench -- --ignored --nocapture`.
#[test]
#[ignore]
fn two_pc_scaling() {
    println!("\n  N | plain execs | plain s | conf reports | conf s | ratio");
    println!("----+-------------+---------+--------------+--------+-------");
    for n in 2..=5usize {
        let (bs, bt) = baseline(n, false);
        let (out, ct) = conformance(n, false);
        let ratio = if bt > 0.0 { ct / bt } else { f64::NAN };
        println!(
            " {n:2} | {:11} | {bt:7.3} | {:12} | {ct:6.3} | {ratio:5.1}x",
            bs.execs,
            out.reports.len()
        );
        // F43: a run that exhausted its inner budget established less than it
        // appears to, and reads as clean to anyone looking at reports alone.
        assert!(
            out.exhaustions.is_empty(),
            "N={n}: {} inner-search exhaustion(s) — this measurement is not sound",
            out.exhaustions.len()
        );
    }
}

/// **The non-conforming direction**: time to first report, which is a
/// different number from time to exhaustion and the one a user experiences
/// when the tool finds something.
#[test]
#[ignore]
fn two_pc_eager_coordinator_is_reported() {
    println!("\n  N | conf s | reports");
    println!("----+--------+--------");
    for n in 2..=4usize {
        let (out, ct) = conformance(n, true);
        println!(" {n:2} | {ct:6.3} | {}", out.reports.len());
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
/// # `#[ignore]`d: this is F49's reproduction, not a passing test
///
/// **It panics**, on the probe thread, at `obs.rs:304`:
///
/// ```text
/// conformance: observed a send at (t2, 3) whose value is still pending.
/// `wobs` was called before this send was re-executed; its value was blanked
/// by initialize_for_execution and has not come back yet (conf-plan.md §6.1)
/// ```
///
/// The trigger is **`nondet()` in a declared visible thread**, isolated by
/// bisection: with `participant`'s vote a constant this passes; with
/// `crate::nondet()` restored it panics every run, nothing else changed.
///
/// It is kept, ignored and named, rather than deleted or worked around,
/// because it is the only reproduction of F49 in the tree and it should start
/// passing the day F49 is fixed. Run it with
/// `cargo test -j 2 -p traceforge --lib conformance::bench -- --ignored`.
///
/// **§9 admits `nondet()`** — `probe_park` is installed at `nondet` and
/// `named_nondet` precisely so the probe handles it — so the assertion that
/// fires is a working guard on a precondition a legitimate program violates.
#[test]
#[ignore = "F49: nondet() in a visible thread panics the probe; this is the reproduction"]
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
