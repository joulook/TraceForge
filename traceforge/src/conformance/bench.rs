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
//!
//! # A second corpus in this module: the `ndk` family
//!
//! 2PC answers "what does conformance cost on a realistic protocol". It does not
//! exhibit the three *cost defects* the backlog records, because its
//! specification's event count is constant in `N` and its search never gets
//! large enough. The `ndk` family does, and it is the only corpus in the tree
//! where F63, F69 and F70 are all visible at once. It is a synthetic
//! one-parameter family rather than a protocol, which is the point: its minimum
//! budgets are predictable and two of them are pinned to figures P3-F61
//! published independently. See [`ndk`].

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
        if let ToCoordinator::Yes = recv_msg_block::<ToCoordinator>() {
            yes += 1;
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
        if let ToCoordinator::No = recv_msg_block::<ToCoordinator>() {
            seen_no = true;
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

// ===========================================================================
// The `ndk` family --- the cost corpus F63, F69 and F70 are all visible in.
// ===========================================================================

/// One member of the `ndk` family: `senders.len()` **invisible** senders, each
/// choosing by `nondet()` between the two values it is given, and one
/// **visible** receiver `c` that takes one value per sender.
///
/// `Tvis = {c}`, `ConsType::FIFO`. Nothing else is declared, so `main` and every
/// sender are invisible and a pair differs observably only in the multiset of
/// values `c` receives and the order it receives them in.
///
/// **The conforming member is the one where every sender draws from the *same*
/// two-element set.** That is the family P3-F61 published budget figures for and
/// P3-F63 recovered from prose, and the recovery is what identifies it: the
/// minimum budget at which the pair runs without exhausting is **33** for two
/// senders and **981** for three, both matching P3-F61's `ndk2_conf` and
/// `ndk3_conf` exactly. Those two numbers are pinned by the tests below, and
/// they are the reason this family is worth keeping rather than re-deriving: two
/// independent exact hits on a one-parameter family.
///
/// **Why it is in the tree.** Three backlog entries are visible here and
/// nowhere else in the corpus:
///
/// - **F63** — the cost asymmetry between a conforming and a non-conforming pair
///   is redundant re-derivation, not a larger search space: 488 against 649
///   distinct specification graphs, but 981 against 12 082 nodes.
/// - **F69** — the empty-seed rebuild. `ndk3 bad_A` through `verify` spends
///   65 410 duplicate nodes, 17.6% of the run, and the guard in
///   `conformance::search::cover` removes exactly that.
/// - **F70** — the budget's cost curve is not monotone: `bad_A` is *slower* at
///   the default 10 000, where it exhausts eleven times, than at 12 082, where
///   it does not exhaust at all.
///
/// Two earlier tasks rebuilt this family from P3-F61's prose and deleted it
/// again; a third rebuild would have been a third chance to build it
/// differently, which is why it is permanent now.
///
/// **F41.** Both sides of a pair spawn the same threads in the same order — `c`
/// first, then the senders — so `c` is `t1` on both and no `ThreadId` reaches an
/// observed value. The spawns are unconditional, which is what F44 requires of
/// that workaround.
fn ndk(senders: Vec<(u64, u64)>) -> impl Fn() + Send + Sync + Clone + 'static {
    move || {
        let takes = senders.len();
        let c = named("c", move || {
            for _ in 0..takes {
                let _: u64 = recv_msg_block();
            }
        })
        .thread()
        .id();
        for (i, (a, b)) in senders.iter().copied().enumerate() {
            let _ = named(&format!("s{}", i + 1), move || {
                send_msg(c, if crate::nondet() { a } else { b })
            });
        }
    }
}

/// `ndk`'s conforming member at `n` senders: every sender draws from `{1, 2}`.
fn ndk_conf(n: usize) -> Vec<(u64, u64)> {
    vec![(1, 2); n]
}

/// `ndk3`'s `bad_A`: the specification pins `s1` and `s2` to `1`, so it shares
/// every value with the implementation and Φ cuts almost nothing.
///
/// **This is not P3-F61's original `ndk3_bad`**, which no surviving artefact
/// records; it is the closest of ten candidates P3-F63 tried, matched on
/// character rather than on figures — reports and exhaustions of the same order,
/// exhaustions present at the default budget. Its own figures are pinned below
/// and every F63/F69/F70 number quoted for "`bad_A`" is this pair.
fn ndk3_bad_a() -> Vec<(u64, u64)> {
    vec![(1, 1), (1, 1), (1, 2)]
}

/// Run one `ndk` pair through the engine — no precheck, no diagnostics, no
/// triage — at `budget`.
///
/// **The seed is pinned to 0** (F61): every member calls `nondet()`, so the
/// report, exhaustion and skip counts depend on it and a figure taken at a
/// fresh seed is not reproducible.
///
/// **On its own 64 MiB thread.** The inner search recurses once per installed
/// specification event, and the default test-thread stack is not enough for
/// three senders at a budget in the thousands. `Search::cover` also requires a
/// thread that is not inside another execution, which this is.
fn ndk_run(
    implementation: Vec<(u64, u64)>,
    specification: Vec<(u64, u64)>,
    budget: usize,
) -> Outcome {
    let imp = ndk(implementation);
    let spec = ndk(specification);
    std::thread::Builder::new()
        .name("ndk".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            verify_conformance(
                Config::builder()
                    .with_cons_type(ConsType::FIFO)
                    .with_seed(0)
                    .build(),
                imp,
                spec,
                vec!["c".to_string()],
                budget,
            )
        })
        .expect("ndk: could not spawn the run thread")
        .join()
        .expect("ndk: the run thread panicked")
}

/// **`ndk2_conf`'s minimum budget is 33**, which is P3-F61's figure exactly.
///
/// Pinned as a minimum rather than as a bound: at 32 the pair exhausts, at 33 it
/// does not. One assertion without the other would pass at any budget above 33
/// and would identify nothing.
#[test]
fn ndk2_conf_needs_a_budget_of_exactly_33() {
    let tight = ndk_run(ndk_conf(2), ndk_conf(2), 32);
    assert!(
        !tight.exhaustions.is_empty(),
        "32 must not be enough, or 33 is not the minimum"
    );
    let clean = ndk_run(ndk_conf(2), ndk_conf(2), 33);
    assert!(
        clean.exhaustions.is_empty(),
        "33 is P3-F61's `ndk2_conf` and must exhaust nowhere, got {} exhaustions",
        clean.exhaustions.len()
    );
    assert!(
        clean.reports.is_empty(),
        "a program against itself conforms: {} reports",
        clean.reports.len()
    );
}

/// **`ndk3_conf`'s minimum budget is 981**, which is P3-F61's figure exactly,
/// and the second of the two independent hits that identify this family.
#[test]
fn ndk3_conf_needs_a_budget_of_exactly_981() {
    let tight = ndk_run(ndk_conf(3), ndk_conf(3), 980);
    assert!(
        !tight.exhaustions.is_empty(),
        "980 must not be enough, or 981 is not the minimum"
    );
    let clean = ndk_run(ndk_conf(3), ndk_conf(3), 981);
    assert!(
        clean.exhaustions.is_empty(),
        "981 is P3-F61's `ndk3_conf` and must exhaust nowhere, got {} exhaustions",
        clean.exhaustions.len()
    );
    assert!(
        clean.reports.is_empty(),
        "a program against itself conforms: {} reports",
        clean.reports.len()
    );
}

/// **`bad_A` at the default budget: 15 reports and 11 exhaustions** — the pair
/// every F63, F69 and F70 figure is quoted from.
///
/// It is the shape all three entries need: reports *and* exhaustions in the same
/// run, so that a verdict is neither silence nor a clean refutation.
///
/// `#[ignore]` because it takes ~15 s — a measurement's worth of time, for an
/// assertion the cheaper members already cover in character. Run it with
/// `cargo test -j 2 -p traceforge --lib conformance::bench -- --ignored --nocapture`.
#[test]
#[ignore]
fn ndk3_bad_a_reports_and_exhausts_at_the_default_budget() {
    let out = ndk_run(ndk_conf(3), ndk3_bad_a(), 10_000);
    println!(
        "[ndk3 bad_A b=10000] reports={} exhaustions={} skipped={} inert={} seed={}",
        out.reports.len(),
        out.exhaustions.len(),
        out.skipped_gates,
        out.inert_gates,
        out.seed
    );
    assert_eq!(
        (out.reports.len(), out.exhaustions.len()),
        (15, 11),
        "P3-F63 §1 measured 15 reports and 11 exhaustions at the default budget \
         with seed 0; a change here means the pair is not the one the F63, F69 \
         and F70 figures were taken on"
    );
}

/// **F70, pinned: a smaller budget is both non-exhaustive and slower.**
///
/// `bad_A` exhausts eleven times at the default 10 000 and not at all at 12 082,
/// its minimum exhaustive budget — and the exhaustive run is the *cheaper* one,
/// because `BudgetExhausted → Continue` withholds the prune a finished traversal
/// would have authorised. P3-F63 §6 measured 17.8 s against 13.2 s.
///
/// Only the non-monotonicity in *answers* is asserted; the wall clock is printed
/// and not asserted, because a timing assertion on a shared machine is a flaky
/// test rather than a measurement.
///
/// `#[ignore]`: two runs of ~15 s each. Run it with
/// `cargo test -j 2 -p traceforge --lib conformance::bench -- --ignored --nocapture`.
#[test]
#[ignore]
fn ndk3_bad_a_exhausts_at_the_default_budget_and_not_at_12082() {
    let (default, default_secs) = {
        let start = Instant::now();
        let out = ndk_run(ndk_conf(3), ndk3_bad_a(), 10_000);
        (out, start.elapsed().as_secs_f64())
    };
    let (raised, raised_secs) = {
        let start = Instant::now();
        let out = ndk_run(ndk_conf(3), ndk3_bad_a(), 12_082);
        (out, start.elapsed().as_secs_f64())
    };
    println!(
        "[F70] b=10000: reports={} exhaustions={} secs={:.2}",
        default.reports.len(),
        default.exhaustions.len(),
        default_secs
    );
    println!(
        "[F70] b=12082: reports={} exhaustions={} secs={:.2}",
        raised.reports.len(),
        raised.exhaustions.len(),
        raised_secs
    );
    assert!(
        !default.exhaustions.is_empty(),
        "the default budget must bind on this pair, or F70 has moved"
    );
    assert!(
        raised.exhaustions.is_empty(),
        "12 082 is P3-F63 §6.1's minimum exhaustive budget for `bad_A` and must \
         exhaust nowhere, got {}",
        raised.exhaustions.len()
    );
    assert!(
        raised.reports.len() > default.reports.len(),
        "the exhaustive run must find *more* reports than the truncated one \
         ({} against {}), which is what makes the default both non-exhaustive \
         and slower",
        raised.reports.len(),
        default.reports.len()
    );
}

// ---------------------------------------------------------------------------
// Demo harness (2026-09-29). Two `#[ignore]`d measurements written for a talk:
// the conforming pair at N = 2, 3, 4 with the **outer** search's explored-graph
// count, and the eager coordinator at the same sizes printing one concrete
// trace that witnesses the refinement violation.
//
// In `bench.rs` on purpose: this file is already on criterion 1's
// `TEST_ONLY_FILES`, so `println!` here needs no allowlist change (F68).
// ---------------------------------------------------------------------------

/// **Demo, conforming direction.** The correct 2PC refines the agreement
/// specification at N = 2, 3, 4, and the table says how much work that took.
///
/// `outer graphs` is the **outer** search's own count — complete plus blocked
/// executions of the implementation under conformance, from `Outcome::stats`.
/// That is the number a reader wants when asking "what did it explore?", and it
/// is not the same as `two_pc_scaling`'s `plain execs`, which is the *baseline*
/// engine with no gate attached.
///
/// Asserts what it prints: no reports, and **no inner-search exhaustion**, so
/// every gate's answer is exhaustive rather than truncated (F43, F70).
///
/// ```text
/// cargo test -j 2 -p traceforge --lib conformance::bench::demo_2pc_correct_at_2_3_4 -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn demo_2pc_correct_at_2_3_4() {
    println!("\n  2PC, correct coordinator — does it refine the agreement spec?\n");
    println!("   N | verdict  | outer graphs | reports | exhaustions | skipped | inert | seconds | seed");
    println!("  ---+----------+--------------+---------+-------------+---------+-------+---------+------");
    for n in 2..=4usize {
        let start = Instant::now();
        let out = verify_conformance(cfg(), two_pc(n, false), two_pc_spec(), visible(), 10_000);
        let secs = start.elapsed().as_secs_f64();
        let graphs = out
            .stats
            .as_ref()
            .map(|s| s.execs + s.block)
            .expect("the engine records stats");
        let verdict = if out.reports.is_empty() && out.exhaustions.is_empty() {
            "conforms"
        } else {
            "REPORTED"
        };
        println!(
            "  {n:2} | {verdict:8} | {graphs:12} | {:7} | {:11} | {:7} | {:5} | {secs:7.3} | {}",
            out.reports.len(),
            out.exhaustions.len(),
            out.skipped_gates,
            out.inert_gates,
            out.seed
        );
        assert!(
            out.reports.is_empty(),
            "N={n}: the correct 2PC must refine the agreement specification, got {} report(s)",
            out.reports.len()
        );
        assert!(
            out.exhaustions.is_empty(),
            "N={n}: {} inner-search exhaustion(s) — the answer is not exhaustive",
            out.exhaustions.len()
        );
    }
    println!("\n  Every row is exhaustive: zero exhaustions, so `conforms` means the search");
    println!("  finished rather than ran out of room.\n");
}

/// **Demo, violating direction.** The eager coordinator loses agreement, and
/// this prints a concrete trace witnessing it at N = 2, 3, 4.
///
/// Uses the public [`crate::conformance::verify`] rather than the engine half,
/// because the trace comes from **triage**: `ConfBuilder::triage(true)`
/// completes each reported graph into a concrete execution. `stop_at_first_report`
/// is on, so each size prints **one** minimal witness instead of every report —
/// `two_pc_eager_coordinator_is_reported` is the test that counts them all.
///
/// Everything printed below a size's heading is violation evidence: a conforming
/// run at the same size prints no trace at all.
///
/// ```text
/// cargo test -j 2 -p traceforge --lib conformance::bench::demo_2pc_eager_violation_traces -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn demo_2pc_eager_violation_traces() {
    use crate::conformance::{verify, ConfBuilder};
    println!("\n  2PC, EAGER coordinator — traces witnessing the refinement violation\n");
    for n in 2..=4usize {
        let cc = ConfBuilder::new()
            .config(cfg())
            .visible_threads(visible())
            .triage(true)
            .stop_at_first_report(true)
            .search_budget(10_000)
            .build()
            .expect("the demo config is in scope");
        let start = Instant::now();
        let verdict = verify(cc, two_pc(n, true), two_pc_spec()).expect("the run completes");
        let secs = start.elapsed().as_secs_f64();
        println!("  ===== N = {n} participants ({secs:.3} s) =====");
        println!("{verdict}");
    }
}

// ===========================================================================
// P3-DEMOS (developer, 2026-09-29): the demo pair's claims, pinned cheaply and
// checked against an independent ground truth.
//
// The two `demo_*` measurements above are `#[ignore]`d, so nothing in an
// ordinary suite run would notice if version 1 stopped demonstrating anything.
// The three tests below are un-`ignore`d and cost 0.19 s together (measured:
// 0.11 + 0.06 + 0.02, each run alone with `--exact`).
//
// **The ground truth is `conformance::oracle`, not the tool.** `oracle` builds
// `vis(P)` by materialising, for every graph, *every* linear extension of
// `vo(G)` — the draft's Def. visg literally — and answers set inclusion. It
// never consults the morphism, `Search::cover` or a canonical representative,
// so an agreement between it and the tool is evidence and not a tautology.
// What it cannot falsify is listed in that module: it shares `obs::wobs`,
// `in_porf` and `Val::eq` with the tool, so an error in any of those cancels.
// ===========================================================================

/// One oracle `vis` word rendered the way `diagnose::canonical_vis` renders
/// the tool's, so a word quoted in a document can be **located** in an
/// oracle-built set by text.
///
/// Location only. Every verdict below is decided by `VisSet::contains`, which
/// is `Obs`'s own `msg_equals` on a `Val`; this string is never the thing
/// compared. `obs.rs` says why that distinction matters — `Debug` is neither
/// injective nor type-aware, so `1u32` and `1i64` render alike and compare
/// unequal.
fn render_word(w: &crate::conformance::oracle::VisWord) -> String {
    let word = w
        .word
        .iter()
        .map(|e| {
            format!(
                "{}: {}",
                e.thread,
                crate::conformance::report::obs_text(&e.obs)
            )
        })
        .collect::<Vec<_>>()
        .join(" → ");
    let st = w
        .statuses
        .iter()
        .map(|(t, s)| format!("{t}: {}", crate::conformance::report::status_text(*s)))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{word} , [{st}]")
}

/// **The pair demonstrates what it claims to, and a second procedure says so.**
///
/// The correct coordinator refines the agreement specification at `N = 2, 3, 4`
/// and the eager one does not — established by set inclusion on materialised
/// `vis` sets rather than by the algorithm under test. So a change that made
/// the tool agree with itself would not move this test.
///
/// It also answers the question the demo document cannot answer by running:
/// the correct pair conforms *for the right reason*. `vis(Impl) ⊆ vis(Spec)`
/// holds exactly, with **0** of the implementation's words uncovered at every
/// size — not merely "the tool found nothing".
///
/// Measured on this tree: 0.11 s for all six runs.
///
/// **Mutation, MEASURED**: give `coordinator_eager` the correct two-phase
/// reply (collect all votes, then send one decision to each) and the
/// `Inclusion::Fails` arm below fails at every `N`, with the message naming the
/// size.
#[test]
fn the_2pc_pair_is_sound_by_the_naive_oracle() {
    use crate::conformance::oracle::{includes, Inclusion};
    for n in 2..=4usize {
        match includes(cfg(), &visible(), two_pc(n, false), two_pc_spec()) {
            Ok(Inclusion::Holds) => {}
            other => panic!(
                "N={n}: the correct 2PC must satisfy vis(Impl) ⊆ vis(Spec); the oracle said {other:?}"
            ),
        }
        match includes(cfg(), &visible(), two_pc(n, true), two_pc_spec()) {
            Ok(Inclusion::Fails { .. }) => {}
            other => panic!(
                "N={n}: the eager coordinator loses agreement, so inclusion must fail; \
                 the oracle said {other:?}"
            ),
        }
    }
}

/// **F71, refuted.** `DEMO-2PC-ALL.md` exhibits this word for version 1 at
/// `N = 4` and argues it is *inside* `vis(Spec)` — "both participants receive
/// `Abort`, so the oracle discards the votes, chooses `Abort`, and sends it to
/// both" — and concludes the report is an instance of the single-cover gap
/// rather than a caught bug.
///
/// It is not inside `vis(Spec)`, and the missing half of the argument is the
/// **order**. `vis(σ)` is a word: a linearisation of the whole trace with the
/// invisible events deleted, not a per-thread row. The specification's
/// coordinator runs `for _ in 0..ps.len() { recv }` **before** it chooses `d`,
/// so in every specification trace *both* vote-sends precede *both*
/// decision-receives. The document's word has `p0` receiving `Abort` at
/// position 2, before `p1` has voted at position 4 — which is precisely what
/// the eager coordinator does and precisely what the correct one cannot.
///
/// The two assertions are a matched pair, and the second is the load-bearing
/// one: the *content* the document reasons about (`p0` votes `No`, `p1` votes
/// `Yes`, both receive `Abort`) really is producible by the specification, so
/// the document's premise is right and its conclusion still does not follow.
/// Move the one observation and the same multiset of observations lands inside
/// `vis(Spec)`.
///
/// The third block pins the **other three** witnesses this demo has been
/// observed to print, for the reason F71 exists: the witness depends on the
/// run's seed, so a document that argues about one word is arguing about one
/// run. Two of the four show no loss of agreement at all.
///
/// Cost: 0.06 s.
///
/// **Mutation, MEASURED**: swap `DOCUMENTED` and `REORDERED` — the test fails
/// on both of the first two assertions at once.
#[test]
fn the_documented_n4_2pc_witness_is_outside_vis_of_the_specification() {
    use crate::conformance::oracle::vis_of_program;

    /// `DEMO-2PC-ALL.md`, "Version 1 — `n = 4`: reported, but **not** shown to
    /// be a non-conformer", transcribed into the tool's own rendering.
    const DOCUMENTED: &str = "p0: receive Prepare(ThreadId { opaque_id: 1 }) → p0: send No → \
p0: receive Abort → p1: receive Prepare(ThreadId { opaque_id: 1 }) → p1: send Yes → \
p1: receive Abort , [p0: done, p1: done]";
    /// The same observations, with `p0`'s decision-receive moved after `p1`'s
    /// vote — the only change, and it is the whole difference.
    const REORDERED: &str = "p0: receive Prepare(ThreadId { opaque_id: 1 }) → p0: send No → \
p1: receive Prepare(ThreadId { opaque_id: 1 }) → p1: send Yes → p0: receive Abort → \
p1: receive Abort , [p0: done, p1: done]";

    let spec =
        vis_of_program(cfg(), &visible(), two_pc_spec()).expect("the specification enumerates");
    let imp =
        vis_of_program(cfg(), &visible(), two_pc(4, true)).expect("the implementation enumerates");

    let documented = imp
        .iter()
        .find(|w| render_word(w) == DOCUMENTED)
        .unwrap_or_else(|| {
            panic!("the documented N=4 witness is not a word of the eager implementation at all")
        });
    assert!(
        !spec.contains(documented),
        "the documented N=4 witness IS in vis(Spec), so F71 stands and this test is wrong"
    );

    let reordered = imp
        .iter()
        .find(|w| render_word(w) == REORDERED)
        .expect("the reordering is also an implementation word");
    assert!(
        spec.contains(reordered),
        "the specification cannot produce these observations in any order, so the \
         discriminator is not the order after all and the argument above is wrong"
    );

    // **Every witness this demo has been observed to print is outside
    // `vis(Spec)`, including the two in which the decisions *agree*.**
    //
    // `demo_2pc_eager_violation_traces` draws a fresh seed per run (F61) and
    // the witness it prints is whichever report `stop_at_first_report` stopped
    // at. Four runs over `N = 2, 3, 4` — twelve witnesses — produced exactly
    // these four words, and **which size produces which is a seed artefact**:
    // the document's `N = 4` word came out at `N = 3` in two of the four runs.
    //
    // Two of the four show no loss of agreement at all: both participants
    // receive `Commit`, or both receive `Abort`, which is what *correct* 2PC
    // does. They are reported anyway, and correctly — so the document's
    // agreement argument is not what makes any of these witnesses a violation.
    // What makes all four violations is the same thing: `p0` has its decision
    // before `p1` has voted.
    const OBSERVED: [&str; 3] = [
        // p0 Yes → Commit, p1 No → Abort. Seven of the twelve.
        "p0: receive Prepare(ThreadId { opaque_id: 1 }) → p0: send Yes → p0: receive Commit → \
p1: receive Prepare(ThreadId { opaque_id: 1 }) → p1: send No → p1: receive Abort , \
[p0: done, p1: done]",
        // p0 Yes → Commit, p1 Yes → Commit — the decisions agree. Printed as the
        // `N = 2` witness on run seed 7989666650678556505.
        "p0: receive Prepare(ThreadId { opaque_id: 1 }) → p0: send Yes → p0: receive Commit → \
p1: receive Prepare(ThreadId { opaque_id: 1 }) → p1: send Yes → p1: receive Commit , \
[p0: done, p1: done]",
        // p0 No → Abort, p1 No → Abort — the decisions agree. Printed as the
        // `N = 4` witness on run seed 10860480359802314445.
        "p0: receive Prepare(ThreadId { opaque_id: 1 }) → p0: send No → p0: receive Abort → \
p1: receive Prepare(ThreadId { opaque_id: 1 }) → p1: send No → p1: receive Abort , \
[p0: done, p1: done]",
    ];
    for observed in OBSERVED {
        let w = imp
            .iter()
            .find(|w| render_word(w) == observed)
            .unwrap_or_else(|| {
                panic!("this demo printed a word the implementation cannot produce:\n  {observed}")
            });
        assert!(
            !spec.contains(w),
            "this witness IS in vis(Spec), so the demo printed a false alarm:\n  {observed}"
        );
    }

    // **Agreement really is lost, and this is where the document's claim is
    // right.** Everything above says the *printed* witnesses are ordering
    // witnesses; it does not say the eager coordinator keeps agreement. This
    // word does: both vote-sends precede both decision-receives, which is an
    // order the specification can produce, and the decisions still differ. So
    // `vis(Impl) ⊄ vis(Spec)` for the reason 2PC exists to rule out as well as
    // for the timing — the two are independent, and only the second is what any
    // witness observed so far exhibits.
    //
    // Note `p0` votes `No` and receives `Commit`. That is the eager
    // coordinator's second, undocumented facet: `for p in &ps { recv(); send(*p,
    // …) }` replies to `ps[i]` with the verdict standing after the *i*-th vote
    // **arrived**, whoever cast it, so a participant is told the decision for
    // someone else's vote.
    const DISAGREEING: &str = "p0: receive Prepare(ThreadId { opaque_id: 1 }) → p0: send No → \
p1: receive Prepare(ThreadId { opaque_id: 1 }) → p1: send Yes → p0: receive Commit → \
p1: receive Abort , [p0: done, p1: done]";
    let disagreeing = imp
        .iter()
        .find(|w| render_word(w) == DISAGREEING)
        .expect("the eager coordinator can give the two participants different decisions");
    assert!(
        !spec.contains(disagreeing),
        "the specification permits disagreement, so it is not an agreement specification"
    );
}

/// The `#[ignore]`d table's essential claim at the smallest size that shows it,
/// asserted the way the table asserts it — **including `exhaustions`**.
///
/// [`the_two_pc_pair_conforms_and_its_perturbation_does_not`] already pins the
/// reports half, but it does not look at `exhaustions`, and a run that
/// exhausted its inner budget establishes less than it appears to while reading
/// as clean to anyone looking at reports alone (F43). `conforms` is the
/// conjunction, so the test is too.
///
/// Cost: 0.03 s. It does not use [`timed`], so it is one run rather than the
/// several that function repeats.
///
/// **Mutation, MEASURED**: this call's own `search_budget` argument 10_000 → 1
/// and the `exhaustions` assertion fires while the `reports` one still passes —
/// which is the whole point of asserting both.
#[test]
fn the_correct_2pc_run_is_exhaustive_and_not_merely_silent() {
    let out = verify_conformance(cfg(), two_pc(2, false), two_pc_spec(), visible(), 10_000);
    assert!(
        out.reports.is_empty(),
        "N=2: the correct 2PC must refine the agreement specification, got {} report(s)",
        out.reports.len()
    );
    assert!(
        out.exhaustions.is_empty(),
        "N=2: {} inner-search exhaustion(s) — `conforms` would mean \
         \"nothing found in the part we looked at\"",
        out.exhaustions.len()
    );
}
