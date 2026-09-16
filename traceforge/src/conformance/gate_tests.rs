//! Adversarial tests for S4: the gate, the prune path, the scope guards and
//! the error split.
//!
//! Written by the developer agent under the owner's four-gate rule (gate 3).
//! The properties were derived from `criteria/P3-S4-gate.md`, `conf-plan.md`
//! §3/§4/§8/§9/§11.7-9 and the lead's record **before** any of S4's code or
//! tests were read, for the reason the method gives: reading the code first
//! anchors the test list to what the author already thought of.
//!
//! The aim is to break the code. A test that fails is reported as a finding,
//! not repaired into agreement.

#![cfg(test)]

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::conformance::ctx::{
    check_spawn_order, DiagnosticReason, Gate, ReportKind, VisibleThreadError,
};
use crate::conformance::testing::{names, run_once};
use crate::conformance::{verify_conformance, Outcome};
use crate::event::Event;
use crate::event_label::{AsEventLabel, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::thread::{self, main_thread_id, ThreadId};
use crate::{Config, ConsType, SchedulePolicy, Stats};

// ---------------------------------------------------------------------------
// Helpers. None of these reach into the implementation; one that had to would
// be a finding rather than a helper.
// ---------------------------------------------------------------------------

fn fifo() -> Config {
    Config::builder().with_cons_type(ConsType::FIFO).build()
}

/// Spawn a named thread, the way §8's pairing rule expects programs to.
fn named<F>(name: &str, f: F) -> ThreadId
where
    F: FnOnce() + Send + 'static,
{
    thread::Builder::new()
        .name(name.to_owned())
        .spawn(f)
        .unwrap()
        .thread()
        .id()
}

/// A conformance run with the default budget.
fn conf<I, S>(implementation: I, specification: S, visible: &[&str]) -> Outcome
where
    I: Fn() + Send + Sync + 'static,
    S: Fn() + Send + Sync + 'static,
{
    verify_conformance(
        fifo(),
        implementation,
        specification,
        names(visible),
        4096,
    )
}

/// A conformance run whose inner search can never answer: every `Cover` call
/// exhausts on its first node.
///
/// This is the **gate counter** the rest of the file leans on. With a budget of
/// zero, `Budget::spend` fails immediately, `cover` returns `BudgetExhausted`,
/// and `ConfCtx::gate` records one `Exhaustion` and continues. So
/// `outcome.exhaustions` is exactly the sequence of gate calls, in order, with
/// the gate that fired recorded on each — and nothing is ever pruned, so the
/// exploration is the one an ordinary run would do.
fn gates_fired<I>(implementation: I, visible: &[&str]) -> Vec<Gate>
where
    I: Fn() + Send + Sync + 'static,
{
    let out = verify_conformance(fifo(), implementation, || {}, names(visible), 0);
    assert!(
        out.reports.is_empty(),
        "a zero budget established nothing, so it must report nothing: {:?}",
        out.reports
    );
    assert_skips_did_not_blind_the_census(&out);
    out.exhaustions.iter().map(|e| e.gate).collect()
}

/// The census is `exhaustions`, and **both skips return above `cover`** — so a
/// skipped gate records no `Exhaustion` and is invisible to every caller of
/// [`gates_fired`]. That is not a nuance: the reviewer re-introduced the exact
/// defect [`c2_replayed_events_are_not_re_gated`] exists to catch — a
/// `conf_gate(FreshSend)` in `handle_send`'s **replay** branch — and the test
/// still passed, because the re-gated replayed sends were being skipped before
/// they could be counted. F49's replay-frontier skip is what blinded it; F42's
/// inertness skip blinds it the same way, and the note claiming "the property
/// under test is unchanged" was false.
///
/// The repair is not a new counter — a gate that returns before `cover` can
/// only be counted inside `ConfCtx::gate`, which is production code. It is to
/// make the existing instrument **self-checking**: `Outcome` already carries
/// both skip totals, so a census is sound exactly when both are zero, and this
/// turns a silent undercount into a loud failure. A program on which the skips
/// do fire simply cannot be measured this way, and must say so rather than
/// quietly report a short count.
fn assert_skips_did_not_blind_the_census(out: &Outcome) {
    assert_eq!(
        (out.skipped_gates, out.inert_gates),
        (0, 0),
        "the gate census is blind to {} replay-frontier skip(s) and {} inertness \
         skip(s): both return above `cover`, so they record no `Exhaustion` and \
         this program's `exhaustions` is a short count. Any assertion derived \
         from it is unsound — choose a program the skips do not fire on (declare \
         every thread visible to defeat F42; avoid a shape that gates behind the \
         replay frontier to defeat F49), or count something else.",
        out.skipped_gates,
        out.inert_gates
    );
}

fn count(gates: &[Gate], want: Gate) -> usize {
    gates.iter().filter(|g| **g == want).count()
}

fn stats(out: &Outcome) -> Stats {
    out.stats.clone().expect("verify_conformance always fills stats")
}

/// `Report::gate` is `Option<Gate>` since the F-E fix: `None` for a
/// `VisibleError`, which is not a gate firing at all.
fn report_gates(out: &Outcome) -> Vec<Option<Gate>> {
    out.reports.iter().map(|r| r.gate).collect()
}

fn is_no_cover(kind: &ReportKind) -> bool {
    matches!(kind, ReportKind::NoCover)
}

// ===========================================================================
// Criterion 1 --- zero behaviour change when `conf` is `None`.
//
// The criterion the step is judged on. Its own warning is the thing to attack:
// `reject_out_of_scope` is *called* unconditionally at handler entry and tests
// its flags inside, so the guard's widening from `probe.is_some()` to
// `probe.is_some() || conf.is_some()` sits on the ordinary path of every
// existing TraceForge user.
// ===========================================================================

/// A battery of exact execution counts on the ordinary path.
///
/// Criterion 12 names this instrument and says why it is the right one: the
/// counters are deterministic, so requiring exact values is flake-free, and it
/// catches a behaviour change that "the suite is green" would miss. The numbers
/// are derived from the programs, not copied from a run.
#[test]
fn c1_ordinary_execution_counts_are_exact() {
    // One send, one receive: the receive has exactly one source.
    let s = crate::verify(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });
    assert_eq!((s.execs, s.block), (1, 0), "one send, one blocking receive");

    // Two sends to one receiver, one blocking receive: two coherent sources,
    // so two complete executions; neither blocks.
    let s = crate::verify(fifo(), || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
    });
    assert_eq!((s.execs, s.block), (2, 0), "two sources, one receive");

    // A non-blocking receive with one possible source: read it, or read ⊥.
    let s = crate::verify(fifo(), || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        let _: Option<u64> = crate::recv_msg();
    });
    assert_eq!((s.execs, s.block), (2, 0), "one source or ⊥");

    // A blocking receive with nothing to read: one blocked execution.
    let s = crate::verify(fifo(), || {
        let _: u64 = crate::recv_msg_block();
    });
    assert_eq!((s.execs, s.block), (0, 1), "blocking receive, no sender");

    // One nondet: two executions.
    let s = crate::verify(fifo(), || {
        let _ = crate::nondet();
    });
    assert_eq!((s.execs, s.block), (2, 0), "one coin toss");
}

/// The widened handler-entry guards must reject **nothing** on an ordinary run.
///
/// This is criterion 1's blast radius. `reject_out_of_scope` is reached by
/// every send, every receive, every `sample`, every inbox read, every monitor
/// registration and every symmetric spawn in the crate. If its condition were
/// written `!self.probe.is_some()`, or if the `conf` disjunct were dropped into
/// an unconditional `panic!`, every one of these would abort — and none of the
/// existing conformance tests would notice, because none of them runs an
/// ordinary `verify`.
#[test]
fn c1_the_widened_scope_guards_reject_nothing_on_an_ordinary_run() {
    // A `TotalOrder` channel, send and receive halves.
    let s = crate::verify(Config::builder().build(), || {
        let (tx, rx) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::TotalOrder)
            .build();
        tx.send_msg(1);
        let _ = rx.recv_msg();
    });
    assert!(s.execs + s.block > 0, "a TotalOrder channel run explored nothing");

    // `Mailbox` consistency, which is the config-level half of the same
    // exclusion.
    let s = crate::verify(
        Config::builder().with_cons_type(ConsType::Mailbox).build(),
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
    );
    assert!(s.execs + s.block > 0, "a Mailbox run explored nothing");

    // `sample`.
    let s = crate::verify(fifo(), || {
        let _: i64 = crate::sample(rand::distr::Uniform::new(0i64, 3i64).unwrap(), 2);
    });
    assert!(s.execs + s.block > 0, "a sampling run explored nothing");

    // Symmetric spawning. (`with_symmetry(true)` is refused by `Config::build`
    // itself — "Symmetry reduction is currently not supported" — so the
    // spawn is made under the default config, which is what `spawn_symmetric`
    // needs to set the `sym_id` the guard keys on.)
    let s = crate::verify(Config::builder().build(), || {
        let m = main_thread_id();
        let a = thread::spawn(move || crate::send_msg(m, 1u64));
        let _ = crate::spawn_symmetric(move || crate::send_msg(m, 1u64), a.thread().id());
        let _: u64 = crate::recv_msg_block();
    });
    assert!(s.execs + s.block > 0, "a symmetric run explored nothing");

    // Predetermined named choices.
    let mut choices = HashMap::new();
    choices.insert("c".to_owned(), true);
    let s = crate::verify(
        Config::builder()
            .with_predetermined_global_choices(choices)
            .build(),
        || {
            let _ = crate::named_nondet("c");
        },
    );
    assert!(s.execs + s.block > 0, "a predetermined run explored nothing");
}

/// §9's config predicate must not fire on a run that never asked for
/// conformance.
///
/// `assert_config_in_scope` is called from `enable_conformance` and
/// `enable_probe`, never from `Must::new`. The placement is what makes this
/// pass; an assertion actually written at `Must::new` — which is how §3 item 8
/// words it — would reject these.
#[test]
fn c1_out_of_scope_configs_still_run_without_conformance() {
    for (what, config) in [
        (
            "Mailbox",
            Config::builder().with_cons_type(ConsType::Mailbox).build(),
        ),
        (
            "Arbitrary",
            Config::builder()
                .with_policy(SchedulePolicy::Arbitrary)
                .build(),
        ),
        ("lossy", Config::builder().with_lossy(2).build()),
    ] {
        let s = crate::verify(config, || {
            let w = named("w", || {
                let _: Option<u64> = crate::recv_msg();
            });
            crate::send_msg(w, 1u64);
        });
        assert!(
            s.execs + s.block > 0,
            "{what}: an ordinary run under an out-of-scope config explored nothing"
        );
    }
}

/// The gate must not perturb the implementation's own exploration.
///
/// Criterion 1's instrument is stated as "the counters must be identical with
/// conformance compiled in and `conf = None`". There is no pre-conformance tree
/// to compare against from inside the crate, so this asks the sharper question
/// the same counters can answer: with conformance *on* but nothing declared
/// visible, the gate fires at every site and always finds a cover (the empty
/// specification covers the empty observation sequence), so the exploration
/// must be exactly the one `verify` does.
///
/// A gate that pruned spuriously, blocked a thread, or consumed a revisit shows
/// up here as a changed count.
#[test]
fn c1_conformance_with_nothing_visible_explores_exactly_what_verify_does() {
    macro_rules! same {
        ($name:expr, $prog:expr) => {{
            let plain = crate::verify(fifo(), $prog);
            let out = conf($prog, || {}, &[]);
            let c = stats(&out);
            assert!(
                out.reports.is_empty(),
                "{}: nothing is visible, so nothing can fail to be covered: {:?}",
                $name,
                out.reports
            );
            assert_eq!(
                (plain.execs, plain.block),
                (c.execs, c.block),
                "{}: the gate changed the exploration",
                $name
            );
            assert!(
                plain.execs + plain.block > 1,
                "{}: a single-execution program cannot witness a perturbation",
                $name
            );
        }};
    }

    same!("two sources", || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
    });
    same!("non-blocking receive", || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        let _: Option<u64> = crate::recv_msg();
    });
    same!("coin toss and a send", || {
        let w = named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
        if crate::nondet() {
            crate::send_msg(w, 1u64);
        }
    });
}

// ===========================================================================
// Criterion 2 --- the gate fires where §4.1 says, and nowhere else.
// ===========================================================================

/// Bookkeeping labels are not gated, and the completion gate fires once per
/// execution.
///
/// §4.1's exemption list names `Block`/`TCreate`/`TJoin`/`Begin`/`End`/`Unique`
/// installs. A program made of nothing but those must therefore produce exactly
/// one gate call — the completion one — per execution.
#[test]
fn c2_a_program_with_no_communication_fires_only_the_completion_gate() {
    let gates = gates_fired(
        || {
            // `TCreate`, `Begin`, `End`, `TJoin`, and main's own bookkeeping:
            // every label §4.1's third exemption names, and no other.
            let h = thread::Builder::new()
                .name("w".to_owned())
                .spawn(|| {})
                .unwrap();
            h.join().unwrap();
        },
        &["main"],
    );
    assert_eq!(
        gates,
        vec![Gate::Completion],
        "spawning and joining fired something other than the completion gate"
    );
}

/// The ⊥ case and the blocked case are told apart by the installed label, not
/// by the returned `Option<Val>`.
///
/// Criterion 2 calls this a requirement rather than a hazard note, and names
/// the failure: both paths return `None` at the caller, so a gate keyed on
/// `val.is_some()` either fires on a blocked receive — a false alarm on the
/// ordinary path — or drops a real ⊥ report.
///
/// The two halves are run as one test so neither can pass for the other's
/// reason.
#[test]
fn c2_a_bottom_receive_is_gated_and_a_blocked_receive_is_not() {
    // ⊥: a non-blocking receive with nothing to read installs a `RecvMsg`
    // reading nothing, and that is a fresh add.
    let bottom = gates_fired(
        || {
            let _: Option<u64> = crate::recv_msg();
        },
        &["main"],
    );
    assert_eq!(
        count(&bottom, Gate::FreshRecv),
        1,
        "a ⊥ receive was not gated: {bottom:?}"
    );

    // Blocked: a blocking receive with nothing to read overwrites the
    // `RecvMsg` with `Block(Value)` and installs no receive at all.
    let blocked = gates_fired(
        || {
            let _: u64 = crate::recv_msg_block();
        },
        &["main"],
    );
    assert_eq!(
        count(&blocked, Gate::FreshRecv),
        0,
        "a blocked receive fired the fresh-add gate: {blocked:?}"
    );
    assert_eq!(
        count(&blocked, Gate::Completion),
        1,
        "the blocked execution never reached the completion gate: {blocked:?}"
    );
}

/// ND installs and ND flips are ungated (§4.1's second exemption).
///
/// A single `nondet()` produces two executions: the install and one flip. If
/// either were gated the trace would carry a gate call the send does not
/// account for.
#[test]
fn c2_nondet_installs_and_flips_are_not_gated() {
    let gates = gates_fired(
        || {
            let _ = crate::nondet();
        },
        &["main"],
    );
    assert_eq!(
        gates,
        vec![Gate::Completion, Gate::Completion],
        "a coin toss fired a gate of its own: {gates:?}"
    );

    // Not vacuous: with a send in the program the trace does grow, so the
    // counter really does see non-completion gates.
    //
    // **`w` is declared visible** so that F42's inertness skip cannot fire.
    // `w`'s ⊥ receive is a fresh-add gate on an *invisible* thread, so it was
    // being skipped above `cover` and recorded no `Exhaustion` — this call was
    // measuring a census one gate short, which `assert_skips_did_not_blind_the_census`
    // now refuses. Declaring `w` visible restores a complete census; the
    // property under test — that the coin toss fires no gate of its own — is
    // untouched by which threads are declared visible.
    let gates = gates_fired(
        || {
            let w = named("w", || {
                let _: Option<u64> = crate::recv_msg();
            });
            if crate::nondet() {
                crate::send_msg(w, 1u64);
            }
        },
        &["main", "w"],
    );
    assert!(
        count(&gates, Gate::FreshSend) >= 1,
        "the gate counter saw no sends at all: {gates:?}"
    );
}

/// A replayed event is not re-gated (§4.1's fourth exemption).
///
/// `handle_send`'s replay branch returns before the tail the gate sits in, and
/// `handle_recv`'s returns before `visit_rfs` is reached. The observable form:
/// across a whole exploration, the number of fresh-add gate calls equals the
/// number of *logical* events added, not the number of replayed ones — and the
/// second execution of a two-execution exploration replays the whole prefix.
#[test]
fn c2_replayed_events_are_not_re_gated() {
    // Two sources for one receive: two executions, the second replaying both
    // sends and re-deciding only the receive.
    let gates = gates_fired(
        || {
            let m = main_thread_id();
            named("a", move || crate::send_msg(m, 1u64));
            named("b", move || crate::send_msg(m, 2u64));
            let _: u64 = crate::recv_msg_block();
        },
        // **`a` and `b` are declared visible here deliberately** (F42). This
        // test counts `FreshSend` firings to detect re-gating, and F42 skips a
        // fresh gate whose event changed nothing observable — which is exactly
        // what an *invisible* thread's send does. With `&["main"]` the two
        // sends became inert and the count stopped measuring re-gating and
        // started measuring visibility. Making the senders visible restores
        // what the test is for: the property under test is that a **replayed**
        // send is not gated a second time, and that is unchanged.
        &["main", "a", "b"],
    );
    // Execution 1: two fresh sends, one fresh receive, one completion.
    // Execution 2: the revisit-apply gate for the re-pointed rf, then one
    // completion. The two sends are replayed and must not be gated again.
    assert_eq!(
        count(&gates, Gate::FreshSend),
        2,
        "the two sends were gated {} times; replayed sends are being re-gated: {gates:?}",
        count(&gates, Gate::FreshSend)
    );
    assert_eq!(
        count(&gates, Gate::Completion),
        2,
        "expected one completion gate per execution: {gates:?}"
    );
}

// ===========================================================================
// Criterion 11 --- the completion gate.
// ===========================================================================

/// A pruned execution is counted as **blocked**, never as complete.
///
/// This is the observable consequence of the gate running *before*
/// `check_blocked`. Move it after and `maybe_block` is already `None`, so
/// `record_ending_telemetry` increments `EXECS` instead of `BLOCKED` and this
/// assertion fails on both halves at once.
#[test]
fn c11_a_pruned_execution_is_counted_blocked_not_complete() {
    let out = conf(
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 2u64);
        },
        &["main"],
    );
    let s = stats(&out);
    assert_eq!(out.reports.len(), 1, "expected one report: {:?}", out.reports);
    assert!(is_no_cover(&out.reports[0].kind));
    assert_eq!(s.execs, 0, "a pruned execution was counted complete");
    assert_eq!(s.block, 1, "a pruned execution was not counted blocked");
}

/// Only the completion gate passes `outer_complete = true`, and it passes it
/// for a **blocked** ending as well as a completed one.
///
/// The lever is `done`: with `outer_complete` false it stops at "the
/// specification can follow this prefix", and only with it true does it compare
/// the statuses conjunct. This pair differs in **nothing but status** — neither
/// side's `main` ever observes an event — so it is reported if and only if the
/// completion gate passed `true`. And the implementation ends *blocked*, which
/// is the half of the owner's ruling that a test of a completed ending cannot
/// reach.
#[test]
fn c11_the_completion_gate_passes_complete_for_a_blocked_ending() {
    let out = conf(
        // `main` blocks forever: `Block(Value)`, no observation.
        || {
            let _: u64 = crate::recv_msg_block();
        },
        // `main` finishes: no observation either.
        || {},
        &["main"],
    );
    assert_eq!(
        out.reports.len(),
        1,
        "a status-only difference at a blocked ending was not reported: {:?}",
        out.reports
    );
    assert_eq!(
        out.reports[0].gate,
        Some(Gate::Completion),
        "the status-only difference was reported at the wrong gate"
    );

    // Not vacuous: the same shapes with matching statuses are silent, so the
    // report above is the statuses conjunct and not some other difference.
    let out = conf(|| {}, || {}, &["main"]);
    assert!(
        out.reports.is_empty(),
        "two programs that do nothing reported: {:?}",
        out.reports
    );
    let out = conf(
        || {
            let _: u64 = crate::recv_msg_block();
        },
        || {
            let _: u64 = crate::recv_msg_block();
        },
        &["main"],
    );
    assert!(
        out.reports.is_empty(),
        "two programs that both block reported: {:?}",
        out.reports
    );
}

/// The fresh-add gates pass `outer_complete = false`, and this is what keeps
/// them from panicking.
///
/// `done` calls `assume_finished_at_gate` only under the complete regime, and
/// that function panics if the graph has a running spawned thread. So a gate
/// firing while a spawned thread is mid-flight would abort with "a finished
/// execution has no running spawned thread". The program below fires a
/// fresh-send gate at a point where `w` has been created and has not finished.
#[test]
fn c11_a_fresh_gate_with_a_running_spawned_thread_does_not_assume_completeness() {
    let out = conf(
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
        &["main"],
    );
    assert!(out.reports.is_empty(), "an identical pair reported: {:?}", out.reports);
}

/// The completion gate must not fire on an execution the gate already pruned.
///
/// `complete_execution` runs for *every* ending, the pruned one included. With
/// no must-not-fire guard the gate would run `Cover` on a graph whose every
/// thread rests at `Block(ConfPrune)` — where (M3) is outside its domain and
/// `status_of` panics by design. Two things are asserted: exactly one report
/// per pruned execution, and no panic.
#[test]
fn c3_a_pruned_graph_never_reaches_status_extraction() {
    let out = conf(
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
            crate::send_msg(w, 2u64);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 9u64);
        },
        &["main"],
    );
    // One report per pruned execution, not two.
    let s = stats(&out);
    assert!(
        out.reports.len() <= s.execs + s.block,
        "more reports ({}) than executions ({}): the completion gate double-reported on a \
         pruned graph: {:?}",
        out.reports.len(),
        s.execs + s.block,
        out.reports
    );
    assert!(!out.reports.is_empty(), "the non-conforming pair reported nothing");
}

// ===========================================================================
// Criterion 4 / §11.7 --- the sibling-order test.
// ===========================================================================

/// **A pruned send's backward revisits survive the prune.**
///
/// This is §11.7, and criterion 4 says why it is the one test the rest of the
/// suite cannot substitute for: "a prune that drained the queue would pass
/// every other test". `handle_send` runs `calc_revisits` *before* the gate, so
/// the send's backward revisits are already in `rqueue` when the gate prunes;
/// §4.2's prune is `block_exec` + `stop`, which touch neither the queue nor the
/// saved states.
///
/// The program is shaped so that the backward revisit is the **only** way to
/// reach a second execution. `w`'s non-blocking receive reads ⊥ concurrently
/// with `main`'s later visible send to `w`, so that send's `calc_revisits`
/// queues a backward revisit at `w`'s shallower stamp. The specification cannot
/// match the send, so the gate prunes immediately after queueing it.
#[test]
fn o6_a_pruned_sends_backward_revisits_survive_the_prune() {
    let implementation = || {
        let m = main_thread_id();
        let w = named("w", || {
            // Concurrent with main's send below: nothing of `w` flows to
            // `main`, so this receive is not in that send's porf prefix and a
            // backward revisit is queued for it.
            let _: Option<u64> = crate::recv_msg();
        });
        named("x", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
        crate::send_msg(w, 7u64);
    };
    // The specification reproduces main's receive and stops: it can follow the
    // prefix but cannot match the send.
    let specification = || {
        let m = main_thread_id();
        named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
        named("x", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    };

    // The control: without the gate, the program really does have a second
    // execution reachable only through that backward revisit.
    let plain = crate::verify(fifo(), implementation);
    assert!(
        plain.execs + plain.block >= 2,
        "the program has no revisit to survive: {plain:?}"
    );

    // The gate trace with a zero budget (which never prunes) shows the
    // exploration this program has: the second execution is entered through
    // the revisit-apply gate, so a surviving revisit is what a second
    // execution means here.
    // **Every thread is declared visible for the census, and only for it.**
    // F42's inertness skip returns above `cover`, so an invisible thread's
    // fresh gate records no `Exhaustion`; with `&["main"]` this census was one
    // gate short and `assert_skips_did_not_blind_the_census` now refuses it.
    // The `conf` run below keeps `&["main"]` — *that* visible list is part of
    // the property, since it is what makes the specification fail to match.
    let unpruned = gates_fired(implementation, &["main", "w", "x"]);
    assert!(
        unpruned.contains(&Gate::RevisitApply),
        "the program reaches its second execution some other way than a revisit: {unpruned:?}"
    );

    let out = conf(implementation, specification, &["main"]);
    assert_eq!(
        report_gates(&out),
        vec![Some(Gate::FreshSend), Some(Gate::RevisitApply)],
        "the send's backward revisit did not survive its prune. Exactly two things must \
         appear: the prune of the send at `FreshSend`, and then the queued backward revisit \
         popped and gated at `RevisitApply`. A `conf_prune` that drained `rqueue` leaves \
         only the first."
    );
}

// *Instrument note, recorded rather than quietly corrected.* Until the
// revisit-apply departure landed, this test asserted `execs + block >= 2`:
// the surviving revisit used to be *launched* and then pruned at its own
// gate, so a second execution was a faithful proxy for "the revisit
// survived". Under the departure a revisit pruned before launch produces no
// execution at all, so the proxy went false while the property stayed true —
// the reports above show the revisit popped and gated. The proxy was
// replaced by the property; the test was not weakened to agree with the code,
// and `report_gates` is strictly the sharper instrument: draining `rqueue` in
// `conf_prune` removes the second entry under either design, whereas the old
// count could not have told a drained queue from a skipped launch.

/// The revisit-apply gate fires for the first revisit popped after a prune.
///
/// The latch that makes a prune stick must be cleared at the boundary
/// `try_revisit` sees. `try_revisit` — and with it `conf_revisit_gate` — runs
/// at the *end* of `complete_execution`, so a latch cleared only by
/// `begin_execution` is still set when the next revisit is applied, and
/// §4.1's stated purpose for this gate, "skips the doomed re-execution
/// entirely", does not happen for it.
///
/// The observable form: this pair must report at `RevisitApply`, not merely at
/// `FreshSend` and then `Completion`.
///
/// *(Found failing at gate 3 as finding F-B; `ConfCtx::end_execution` was
/// added for it. This is the regression test, not a description of current
/// behaviour.)*
#[test]
fn c2_the_revisit_apply_gate_after_a_prune() {
    let implementation = || {
        let m = main_thread_id();
        let w = named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
        named("x", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
        crate::send_msg(w, 7u64);
    };
    let specification = || {
        let m = main_thread_id();
        named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
        named("x", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    };
    let out = conf(implementation, specification, &["main"]);
    println!("reports fired at {:?}", report_gates(&out));
    assert!(
        report_gates(&out).contains(&Some(Gate::RevisitApply)),
        "the revisit applied after the prune was never gated: reports at {:?}. \
         `ConfCtx::pruned` is still set when `try_revisit` runs, because it is \
         cleared in `begin_execution`, which happens afterwards.",
        report_gates(&out)
    );
}

// ===========================================================================
// Criterion 5 / §4.4 --- the error split by visibility.
// ===========================================================================

/// A **visible** thread's failed assertion reports and prunes.
#[test]
fn c5_a_visible_threads_failed_assert_reports_and_prunes() {
    let out = conf(
        || {
            crate::assert(false);
        },
        || {},
        &["main"],
    );
    assert_eq!(out.reports.len(), 1, "expected one report: {:?}", out.reports);
    match &out.reports[0].kind {
        ReportKind::VisibleError { thread, .. } => {
            assert_eq!(thread, "main", "the report named the wrong thread")
        }
        other => panic!("a visible assertion failure was reported as {other:?}"),
    }
    // F-E, now checkable: a §4.4 error is not a gate firing, so it carries no
    // gate. The field used to be hard-coded `Gate::Completion`, which was
    // wrong for every `VisibleError` and had no test that could say so.
    assert_eq!(
        out.reports[0].gate, None,
        "a visible assertion failure was stamped with a gate it did not fire at"
    );
    assert!(
        out.diagnostics.is_empty(),
        "a visible error also landed in diagnostics: {:?}",
        out.diagnostics
    );
    let s = stats(&out);
    assert_eq!(s.execs, 0, "the pruned execution was counted complete");
    assert_eq!(s.block, 1, "the pruned execution was not counted blocked");
}

/// An **invisible** thread's failed assertion is neither a report nor a prune.
///
/// Criterion 5 and §4.4: the theorem does not speak about it, so reporting it
/// would claim a violation of something never promised, and pruning on it would
/// cut a subtree for a reason the morphism cannot see. The no-prune half is
/// what this test is really about, and it is checked by comparing the whole
/// exploration against the same program's ordinary run.
#[test]
fn c5_an_invisible_threads_failed_assert_neither_reports_nor_prunes() {
    let implementation = || {
        named("hidden", || {
            crate::assert(false);
        });
        // `main` is visible and does nothing the specification cannot do.
        let _ = crate::nondet();
    };
    let plain = crate::verify(
        Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_keep_going_after_error(true)
            .build(),
        implementation,
    );

    let out = conf(
        implementation,
        || {
            let _ = crate::nondet();
        },
        &["main"],
    );
    let s = stats(&out);
    assert!(
        out.reports.is_empty(),
        "an invisible assertion failure was reported: {:?}",
        out.reports
    );
    // One diagnostic per execution: the invisible thread fails in both
    // branches of the coin flip. Tied to the execution count rather than to a
    // literal, so the test says *why* it expects that many.
    assert_eq!(
        out.diagnostics.len(),
        s.execs + s.block,
        "expected one invisible-failure diagnostic per execution: {:?}",
        out.diagnostics
    );
    assert!(
        !out.diagnostics.is_empty(),
        "the invisible thread never failed, so nothing was under test"
    );
    // The reason field is what keeps this apart from the `AfterPrune`
    // diagnostic, which is also "not a report" but for an entirely different
    // cause. Before it existed the two were indistinguishable in the sink.
    assert!(
        out.diagnostics
            .iter()
            .all(|d| matches!(d.reason, DiagnosticReason::InvisibleThread)),
        "an invisible thread's failure was recorded with the wrong reason: {:?}",
        out.diagnostics
    );
    assert_eq!(
        (plain.execs, plain.block),
        (s.execs, s.block),
        "the invisible error changed the exploration, so something pruned"
    );
}

/// Conformance forces `keep_going_after_error`, so a visible error does not end
/// the run.
///
/// The config handed in has the flag *off*. If `enable_conformance` did not
/// force it, the first failed assertion would end the exploration and the
/// second branch would never be explored.
#[test]
fn c5_keep_going_after_error_is_forced_by_conformance() {
    let out = verify_conformance(
        Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_keep_going_after_error(false)
            .build(),
        || {
            if crate::nondet() {
                crate::assert(false);
            }
        },
        || {
            let _ = crate::nondet();
        },
        names(&["main"]),
        4096,
    );
    let s = stats(&out);
    assert_eq!(
        out.reports.len(),
        1,
        "expected exactly the one failing branch to report: {:?}",
        out.reports
    );
    assert_eq!(
        s.execs + s.block,
        2,
        "the run stopped at the first error instead of exploring both branches"
    );
}

/// A conformance report writes no counterexample file --- **and F30 makes this
/// undiscriminating, which is the finding, not the assertion.**
///
/// §4.4 replaces the persistence sink so reports do not become counterexample
/// files, and criterion 5 asks for that to be checked. The control below is the
/// same failure under an ordinary keep-going run, and it writes **no file
/// either**: `traceforge::assert` calls `persist_task_failure` while holding
/// `s.must.borrow_mut()` (lib.rs:1797), and `persist_task_failure`'s
/// `must.try_borrow_mut()` therefore fails and logs
/// "Couldn't generate a counterexample because Must::current is borrowed".
/// That is F30, observed rather than suspected.
///
/// So the assertion below is true and no mutation of S4's code makes it false:
/// deleting the conformance branch in `assert` would still write nothing. The
/// control is kept, and kept *failing-free*, precisely so the vacuity is on the
/// record instead of being presented as a passing check of a real property.
#[test]
fn c5_a_conformance_report_writes_no_counterexample_file() {
    let dir = std::env::temp_dir().join(format!(
        "traceforge-conf-gate-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let control = dir.join("control.trace");
    let under_conformance = dir.join("conf.trace");

    // Control: an ordinary keep-going run. F30 means it writes nothing.
    let _ = crate::verify(
        Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_keep_going_after_error(true)
            .with_error_trace(control.to_str().unwrap())
            .build(),
        || crate::assert(false),
    );
    assert!(
        !control.exists(),
        "the ordinary keep-going path wrote a counterexample file after all, so F30 does \
         not apply here and this test should be rewritten as a real discriminator"
    );

    let out = verify_conformance(
        Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_error_trace(under_conformance.to_str().unwrap())
            .build(),
        || crate::assert(false),
        || {},
        names(&["main"]),
        4096,
    );
    assert_eq!(out.reports.len(), 1, "the visible error was not reported");
    assert!(
        !under_conformance.exists(),
        "conformance persisted a counterexample file at {under_conformance:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// ===========================================================================
// Criteria 6 and 7 / §11.8 --- one test per §9 rejection, per engine.
//
// Criterion 7 is the reason these are written against `verify_conformance` and
// not only against a probe: the guards used to key off `probe.is_some()`, so
// §9's "primary" layer was inert on the **outer conformance run** — an
// implementation program could use an inbox, `sample`, a `TotalOrder` channel
// or a monitor and still receive a verdict. "One test per rejection" with no
// outer/probe split is satisfied by an S4 that arms zero guards on the outer
// run, which is exactly the hole review round 2 found.
// ===========================================================================

/// §9's requirement, stated as an assertion: the run "aborts with an 'outside
/// conformance scope' error **naming the event**".
///
/// The message is asserted rather than merely the abort. `catch_unwind(..)
/// .is_err()` is satisfied by any panic at all, and two lead-written tests were
/// killed by the vacuity audit in earlier steps for exactly that; here it would
/// be worse than vacuous, because the failure these guards actually have is
/// that *something else* panics first and destroys the diagnostic.
fn assert_outer_guard<F>(expected: &str, program: F)
where
    F: Fn() + Send + Sync + 'static,
{
    let message = panic_message(move || {
        let _ = conf(program, || {}, &["main"]);
    });
    let message = message.unwrap_or_else(|| {
        println!("FINDING: the outer conformance run accepted `{expected}` without rejecting it");
        panic!("the outer conformance run accepted `{expected}` without rejecting it")
    });
    if !message.contains(expected) {
        println!(
            "FINDING: the guard fired but did not name the event it rejected.\n\
             \x20 wanted: {expected}\n\x20 got:    {message}"
        );
    }
    assert!(
        message.contains(expected),
        "the guard did not name the event it rejected.\n  wanted: `{expected}`\n  got:    \
         `{message}`"
    );
}

macro_rules! outer_guard_test {
    ($name:ident, $expected:expr, $prog:expr) => {
        #[test]
        fn $name() {
            assert_outer_guard($expected, $prog);
        }
    };
}

outer_guard_test!(
    c7_outer_run_rejects_an_inbox,
    "`inbox` is outside conformance scope",
    || {
        let _ = crate::inbox();
    }
);

outer_guard_test!(
    c7_outer_run_rejects_sample,
    "`sample` is outside conformance scope",
    || {
        let _: i64 = crate::sample(rand::distr::Uniform::new(0i64, 3i64).unwrap(), 2);
    }
);

outer_guard_test!(
    c7_outer_run_rejects_a_total_order_send,
    "`a TotalOrder (mailbox) send` is outside conformance scope",
    || {
        let (tx, _rx) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::TotalOrder)
            .build();
        tx.send_msg(1);
    }
);

outer_guard_test!(
    c7_outer_run_rejects_a_total_order_receive,
    "`a TotalOrder (mailbox) receive` is outside conformance scope",
    || {
        let (_tx, rx) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::TotalOrder)
            .build();
        let _ = rx.recv_msg();
    }
);

outer_guard_test!(
    c7_outer_run_rejects_symmetric_spawning,
    "`symmetric thread spawning` is outside conformance scope",
    || {
        let m = main_thread_id();
        let a = thread::spawn(move || crate::send_msg(m, 1u64));
        let _ = crate::spawn_symmetric(move || crate::send_msg(m, 1u64), a.thread().id());
    }
);

/// The predetermined-named-choice guard (§3 item 13) is **unreachable** on the
/// outer conformance run, and that is the honest result rather than a missing
/// test.
///
/// `named_nondet` reaches `handle_ctoss_predetermined` only when the config
/// carries an entry for that name — and a config carrying one is refused by
/// `assert_config_in_scope` before any program runs. §3 item 13 says as much
/// ("with the config rejected this path is unreachable; the guard turns a miss
/// into a loud error"), so §11.8's "one test per rejection" lands on the config
/// half. Both halves are asserted here so the gap is visible rather than
/// implied.
#[test]
fn c7_a_predetermined_named_choice_is_refused_at_config_time_not_at_runtime() {
    let mut global = HashMap::new();
    global.insert("c".to_owned(), true);
    let message = panic_message(|| {
        let _ = verify_conformance(
            Config::builder()
                .with_predetermined_global_choices(global)
                .build(),
            || {
                let _ = crate::named_nondet("c");
            },
            || {},
            names(&["main"]),
            64,
        );
    });
    let message = message.expect("a predetermined config reached a conformance run");
    assert!(
        message.contains("predetermined choices"),
        "refused for the wrong reason: `{message}`"
    );

    // And with no predetermined entry the handler is never reached, so the
    // runtime guard cannot fire: the program runs to completion.
    let out = conf(
        || {
            let _ = crate::named_nondet("c");
        },
        || {
            let _ = crate::named_nondet("c");
        },
        &["main"],
    );
    assert_eq!(
        stats(&out).execs,
        2,
        "the ordinary `named_nondet` branch did not run both ways"
    );
}

#[test]
#[cfg(feature = "symbolic")]
fn c7_outer_run_rejects_a_symbolic_branch() {
    assert_outer_guard("`symbolic constraint evaluation` is outside conformance scope", || {
        let b = crate::symbolic::fresh_bool();
        let _ = crate::symbolic::eval(b);
    });
}

/// Monitor registration, the seventh runtime guard.
///
/// §9 names monitor registration among the four kinds the primary guard must
/// catch, and §3 item 7 puts the guard at `spawn_monitor` (lib.rs:790); it
/// actually landed inside `handle_register_mon`, which that funnel calls.
struct NoopMonitor;
impl crate::monitor_types::Monitor for NoopMonitor {}

fn no_create(_: ThreadId, _: ThreadId, _: crate::Val) -> Option<crate::Val> {
    None
}

fn no_accept(_: ThreadId, _: ThreadId, _: crate::Val) -> bool {
    false
}

#[test]
fn c7_outer_run_rejects_monitor_registration() {
    assert_outer_guard("`monitor registration` is outside conformance scope", || {
        let m: std::sync::Arc<std::sync::Mutex<dyn crate::monitor_types::Monitor>> =
            std::sync::Arc::new(std::sync::Mutex::new(NoopMonitor));
        let _: crate::thread::JoinHandle<u64> =
            crate::spawn_monitor(|| 0u64, no_create, no_accept, m);
    });
}

// ===========================================================================
// Criterion 10 / §9 --- the config predicate, on every engine.
// ===========================================================================

/// Every one of §9's seven config exclusions is refused by the outer
/// conformance run.
///
/// The list is taken from §9, not from the source: Mailbox, symbolic, both
/// parallel modes, estimation entry points, `Arbitrary`, `lossy_budget > 0`,
/// and the two predetermined maps.
#[test]
fn c10_the_outer_run_refuses_every_section_9_config_exclusion() {
    let mut predetermined = HashMap::new();
    predetermined.insert("c".to_owned(), vec![vec![true]]);
    let mut global = HashMap::new();
    global.insert("c".to_owned(), true);

    let cases: Vec<(&str, Config)> = vec![
        (
            "mailbox is out of scope",
            Config::builder().with_cons_type(ConsType::Mailbox).build(),
        ),
        (
            "LTR schedule policy",
            Config::builder()
                .with_policy(SchedulePolicy::Arbitrary)
                .build(),
        ),
        ("lossy sends", Config::builder().with_lossy(1).build()),
        (
            "both parallel modes",
            Config::builder().with_parallel(true).build(),
        ),
        (
            "both parallel modes",
            Config::builder()
                .with_partitioned_parallelization(true)
                .build(),
        ),
        (
            "predetermined choices",
            Config::builder()
                .with_predetermined_choices(predetermined)
                .build(),
        ),
        (
            "predetermined choices",
            Config::builder()
                .with_predetermined_global_choices(global)
                .build(),
        ),
    ];

    for (expected, config) in cases {
        let message = panic_message(|| {
            let _ = verify_conformance(config, || {}, || {}, names(&["main"]), 16);
        });
        let message = message.unwrap_or_else(|| {
            panic!("an out-of-scope config was accepted by the outer conformance run (wanted `{expected}`)")
        });
        assert!(
            message.contains(expected),
            "the outer run refused for the wrong reason: wanted `{expected}`, got `{message}`"
        );
        assert!(
            message.contains("conformance:"),
            "the refusal did not name the engine it came from: `{message}`"
        );
    }
}

/// The three exclusions the probe `Must` was missing until this step.
///
/// `enable_probe` wrote four of §9's seven out by hand; symbolic, both parallel
/// modes and the two predetermined maps were absent, and the gap survived three
/// review rounds. Criterion 10 requires one shared predicate so they cannot
/// drift, so the same list is asked of the probe engine.
#[test]
fn c10_the_probe_engine_refuses_the_same_list() {
    let mut predetermined = HashMap::new();
    predetermined.insert("c".to_owned(), vec![vec![true]]);
    let mut global = HashMap::new();
    global.insert("c".to_owned(), true);

    let cases: Vec<(&str, Config)> = vec![
        (
            "both parallel modes",
            Config::builder().with_parallel(true).build(),
        ),
        (
            "both parallel modes",
            Config::builder()
                .with_partitioned_parallelization(true)
                .build(),
        ),
        (
            "predetermined choices",
            Config::builder()
                .with_predetermined_choices(predetermined)
                .build(),
        ),
        (
            "predetermined choices",
            Config::builder()
                .with_predetermined_global_choices(global)
                .build(),
        ),
    ];

    for (expected, config) in cases {
        let message = panic_message(|| {
            let _ = crate::conformance::prober::probe_once(config, || {});
        });
        let message = message.unwrap_or_else(|| {
            panic!("an out-of-scope config was accepted by the probe engine (wanted `{expected}`)")
        });
        assert!(
            message.contains(expected),
            "the probe refused for the wrong reason: wanted `{expected}`, got `{message}`"
        );
        assert!(
            message.contains("probe:"),
            "the refusal did not name the engine it came from: `{message}`"
        );
    }
}

/// Run `f`, returning the panic message if it panicked.
///
/// The panic hook is deliberately **not** replaced. `std::panic::set_hook` is
/// process-global, and these tests run in parallel, so a test that silenced the
/// hook would silence every other test's failure message too — which is how the
/// first version of this file lost its own diagnostics.
fn panic_message<F: FnOnce()>(f: F) -> Option<String> {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    match result {
        Ok(()) => None,
        Err(payload) => Some(
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_else(|| "<non-string panic payload>".to_owned()),
        ),
    }
}

// ===========================================================================
// Criterion 9 / §8 --- the spawn-order guard.
// ===========================================================================

/// A declared visible thread spawned after its program has communicated is
/// rejected.
#[test]
fn c9_a_late_spawned_visible_thread_is_rejected() {
    let graph = run_once(fifo(), || {
        let a = named("a", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(a, 1u64);
        // `late` is created after `main` has already sent.
        named("late", || {});
    });

    // Not vacuous: with `late` undeclared the same graph passes.
    assert_eq!(
        check_spawn_order(&graph, &names(&["main"])),
        Ok(()),
        "the guard rejected a graph in which no late thread is declared visible"
    );

    match check_spawn_order(&graph, &names(&["main", "late"])) {
        Err(VisibleThreadError::SpawnedLate { name, .. }) => assert_eq!(name, "late"),
        other => panic!("a late-spawned visible thread was accepted: {other:?}"),
    }
}

/// A visible thread merely **unordered** with a communication event is not
/// rejected.
///
/// This is where the two readings of §8 differ, and the lead chose the weaker
/// one deliberately: the condition checked is "no communication event is
/// `porf`-before the `TCreate`", not "the `TCreate` is `porf`-before every
/// communication event". The two agree except on unordered pairs. The test
/// asserts the two events really are unordered, so it cannot pass by accident
/// on a graph where the stricter reading would agree.
#[test]
fn c9_an_unordered_spawn_is_not_rejected() {
    let graph = run_once(fifo(), || {
        let m = main_thread_id();
        // `x` communicates on its own; `w` is created afterwards in main's
        // program order, but nothing of `x` flows to main.
        named("x", move || crate::send_msg(m, 1u64));
        named("w", || {});
        let _: Option<u64> = crate::recv_msg();
    });

    let send = find_label(&graph, |l| matches!(l, LabelEnum::SendMsg(_)))
        .expect("the program contains a send");
    let w = crate::conformance::obs::resolve_visible(&graph, "w")
        .unwrap()
        .expect("`w` was spawned");
    let create = graph.get_thread_tclab(w).pos();

    // The premise of the test, stated rather than assumed.
    assert!(
        !graph.in_porf(send, create) && !graph.in_porf(create, send),
        "the send and the create are ordered, so this graph does not \
         distinguish the two readings of §8"
    );

    assert_eq!(
        check_spawn_order(&graph, &names(&["main", "w"])),
        Ok(()),
        "an unordered spawn was rejected; the guard is using the stricter reading"
    );
}

/// Main is exempt, and not vacuously so: main communicates in this graph.
#[test]
fn c9_main_is_exempt_from_the_spawn_order_guard() {
    let graph = run_once(fifo(), || {
        let a = named("a", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(a, 1u64);
    });
    assert!(
        find_label(&graph, |l| matches!(l, LabelEnum::SendMsg(_))).is_some(),
        "main never communicated, so the exemption is not under test"
    );
    assert_eq!(check_spawn_order(&graph, &names(&["main"])), Ok(()));
}

/// The guard runs on the real gate path, not only as a unit.
///
/// The specification is a copy of the implementation, so the run reaches the
/// gate that first sees the late `TCreate` instead of pruning before it. That
/// also demonstrates the deferral the lead recorded: the *specification's* own
/// late spawn is not guarded — `check_spawn_order` runs on the implementation
/// graph only — so the panic below can only be about the implementation.
#[test]
#[should_panic(expected = "§8 requires each declared visible thread to be spawned before")]
fn c9_the_gate_enforces_the_spawn_order_guard() {
    let late = || {
        let a = named("a", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(a, 1u64);
        named("late", || {});
    };
    let _ = conf(late, late, &["main", "late"]);
}

fn find_label<F>(graph: &ExecutionGraph, f: F) -> Option<Event>
where
    F: Fn(&LabelEnum) -> bool,
{
    for t in graph.thread_ids() {
        for i in 0..graph.thread_size(t) as u32 {
            let e = Event::new(t, i);
            if f(graph.label(e)) {
                return Some(e);
            }
        }
    }
    None
}

// ===========================================================================
// The entry point --- the false-alarm floor and the exhaustion/report split.
// ===========================================================================

/// **Identical programs must report nothing.**
///
/// The single most valuable test in the file: every other assertion here is
/// about the shape of a failure, and this one is about the absence of one. A
/// gate that reported on a program against itself would make conformance
/// useless while passing every "the report says X" test.
#[test]
fn l1_identical_programs_are_silent() {
    macro_rules! silent {
        ($name:expr, $vis:expr, $prog:expr) => {{
            let out = conf($prog, $prog, $vis);
            assert!(
                out.reports.is_empty(),
                "{}: a program did not refine itself: {:?}",
                $name,
                out.reports
            );
            assert!(
                out.exhaustions.is_empty(),
                "{}: the budget ran out, so silence proves nothing: {:?}",
                $name,
                out.exhaustions
            );
        }};
    }

    silent!("empty", &["main"], || {});
    silent!("one visible send", &["main"], || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });
    silent!("visible receive", &["main"], || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    });
    silent!("two visible threads", &["main", "w"], || {
        let m = main_thread_id();
        let w = named("w", move || {
            let _: u64 = crate::recv_msg_block();
            crate::send_msg(m, 2u64);
        });
        crate::send_msg(w, 1u64);
        let _: u64 = crate::recv_msg_block();
    });
    silent!("a blocked visible thread", &["main"], || {
        let _: u64 = crate::recv_msg_block();
    });
    silent!("⊥ receive", &["main"], || {
        let _: Option<u64> = crate::recv_msg();
    });
}

/// Exhaustion is not a report, and never prunes.
///
/// "⊥ is a claim about the program, exhaustion is a claim about the search."
/// This is the shape of defect the criteria call "seven defects of one shape":
/// a failure quietly turned into an answer. With a budget of zero the search
/// establishes nothing at every gate, so the run must report nothing, prune
/// nothing, and explore exactly what an ordinary run explores.
#[test]
fn l3_budget_exhaustion_is_neither_a_report_nor_a_prune() {
    let implementation = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
    };
    let plain = crate::verify(fifo(), implementation);

    // A specification that cannot possibly cover the implementation, so the
    // only thing keeping the run silent is the exhaustion rule.
    let out = verify_conformance(
        fifo(),
        implementation,
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 99u64);
        },
        names(&["main"]),
        0,
    );
    let s = stats(&out);
    assert!(
        out.reports.is_empty(),
        "exhaustion was reported as a conformance violation: {:?}",
        out.reports
    );
    assert!(
        !out.exhaustions.is_empty(),
        "a zero budget produced no exhaustions, so nothing was under test"
    );
    assert_eq!(
        (plain.execs, plain.block),
        (s.execs, s.block),
        "exhaustion pruned the exploration"
    );

    // The same pair with a real budget does report: the silence above is the
    // exhaustion rule and not an inability to see the difference.
    let out = conf(
        implementation,
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 99u64);
        },
        &["main"],
    );
    assert!(
        !out.reports.is_empty(),
        "the pair is not distinguishable at all, so the exhaustion test is vacuous"
    );
}

/// O2 --- a maximally stale `H` still gives the right answer.
///
/// §4.3 keeps one mutable `H` and never snapshots it into `MustState`, so at a
/// deep revisit pop the carried `H` is generally not the one the draft would
/// carry there. Soundness and completeness are supposed to be unaffected:
/// `Cover` re-verifies against the live outer graph, and rebuilds from empty on
/// extend-failure. Both directions are checked on a program whose revisits are
/// deep enough that the carried `H` is stale at most pops.
#[test]
fn c14_a_stale_carried_h_changes_no_verdict() {
    let busy = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
        let _: Option<u64> = crate::recv_msg();
    };
    let out = conf(busy, busy, &["main"]);
    assert!(
        out.reports.is_empty(),
        "a revisit-heavy program did not refine itself: {:?}",
        out.reports
    );
    assert!(out.exhaustions.is_empty(), "budget ran out: {:?}", out.exhaustions);
    let s = stats(&out);
    assert!(
        s.execs + s.block >= 3,
        "the program is not revisit-heavy enough to make `H` stale: {s:?}"
    );
}

/// A prune at the revisit-apply gate must not leave the engine stopped.
///
/// The smallest pair that reaches the hazard: the implementation's `main` may
/// read either of two sends; the specification can only produce the first. The
/// first execution is covered, the forward revisit to the second send is
/// popped, and the revisit-apply gate prunes it.
///
/// If that prune does `block_exec` + `stop()`, nothing undoes the `stop()` —
/// `unstop()` runs *before* `try_revisit` in `complete_execution`. The next
/// execution then runs zero events, no send is re-executed after
/// `initialize_for_execution` blanked every send value, the latch is cleared,
/// and the completion gate fires on a graph that is both pruned and
/// unreplayed. That reaches the morphism, which criterion 3 says must never
/// happen.
///
/// *(Found failing at gate 3 as finding F-A, where it crashed in `wobs` on a
/// blanked send value and surfaced as "the probe worker died mid-search". The
/// gate now abandons the alternative instead of blocking it — see
/// [`c3_a_revisit_apply_prune_skips_rather_than_blocking`], which pins that
/// choice.)*
#[test]
fn c3_a_revisit_apply_prune_does_not_leave_the_engine_stopped() {
    let implementation = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
    };
    let specification = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    };
    // The control: the implementation really does have the forward revisit.
    let plain = crate::verify(fifo(), implementation);
    assert_eq!((plain.execs, plain.block), (2, 0), "{plain:?}");

    let message = panic_message(move || {
        let out = conf(implementation, specification, &["main"]);
        assert!(
            !out.reports.is_empty(),
            "the unmatchable second source was never reported"
        );
    });
    if let Some(m) = &message {
        println!("FINDING: a prune at the revisit-apply gate crashed the run: {m}");
    }
    assert!(
        message.is_none(),
        "a prune at the revisit-apply gate crashed the run: `{}`",
        message.unwrap()
    );
}

/// A conformance report is observable without anything being rendered.
///
/// Criterion 13's boundary on "minimal": the sink exists so that a prune is
/// observable by a test and by S5, and it must not acquire formatting. This
/// test reads a report's three fields and never asks for a string.
#[test]
fn c13_a_report_is_observable_without_rendering() {
    let out = conf(
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 2u64);
        },
        &["main"],
    );
    assert_eq!(out.reports.len(), 1);
    let r = &out.reports[0];
    assert_eq!(
        r.gate,
        Some(Gate::FreshSend),
        "the send was gated at the wrong site"
    );
    assert!(is_no_cover(&r.kind));
    assert!(
        r.events > 0,
        "the report carries no graph identity, so two reports from one run \
         cannot be told apart"
    );
}

/// The side effects a pruned execution's deeper events would have had do not
/// happen.
///
/// §4.2: "deeper events never run, so their revisits are never queued". The
/// counter is bumped by user code placed after the send the gate prunes.
#[test]
fn c4_a_prune_stops_the_execution_it_prunes() {
    static AFTER: AtomicUsize = AtomicUsize::new(0);
    AFTER.store(0, Ordering::SeqCst);

    let out = conf(
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
            // Reached only if the execution carries on past the pruned send's
            // next scheduling point.
            let _: Option<u64> = crate::recv_msg();
            AFTER.fetch_add(1, Ordering::SeqCst);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 2u64);
        },
        &["main"],
    );
    assert_eq!(out.reports.len(), 1, "{:?}", out.reports);
    assert_eq!(
        AFTER.load(Ordering::SeqCst),
        0,
        "user code below the pruned send ran"
    );
}


// ---------------------------------------------------------------------------
// §11.8's other engine. `prober.rs` and `adversarial.rs` already cover the
// `TotalOrder` send and receive, symbolic evaluation and symmetric spawning on
// the probe `Must`; these are the three handler-entry guards that were covered
// on neither engine.
// ---------------------------------------------------------------------------

fn assert_probe_guard<F>(expected: &str, program: F)
where
    F: Fn() + Send + Sync + 'static,
{
    let message = panic_message(move || {
        let _ = crate::conformance::prober::probe_once(fifo(), program);
    });
    let message = message
        .unwrap_or_else(|| panic!("the probe engine accepted `{expected}` without rejecting it"));
    if !message.contains(expected) {
        println!(
            "FINDING: the probe guard fired but did not name the event it rejected.\n\
             \x20 wanted: {expected}\n\x20 got:    {message}"
        );
    }
    assert!(
        message.contains(expected),
        "the probe guard did not name the event it rejected.\n  wanted: `{expected}`\n  got:    \
         `{message}`"
    );
}

#[test]
fn c6_probe_engine_rejects_an_inbox() {
    assert_probe_guard("`inbox` is outside conformance scope", || {
        let _ = crate::inbox();
    });
}

#[test]
fn c6_probe_engine_rejects_sample() {
    assert_probe_guard("`sample` is outside conformance scope", || {
        let _: i64 = crate::sample(rand::distr::Uniform::new(0i64, 3i64).unwrap(), 2);
    });
}

#[test]
fn c6_probe_engine_rejects_monitor_registration() {
    assert_probe_guard("`monitor registration` is outside conformance scope", || {
        let m: std::sync::Arc<std::sync::Mutex<dyn crate::monitor_types::Monitor>> =
            std::sync::Arc::new(std::sync::Mutex::new(NoopMonitor));
        let _: crate::thread::JoinHandle<u64> =
            crate::spawn_monitor(|| 0u64, no_create, no_accept, m);
    });
}

/// A declared visible name the **implementation** never spawns must not be
/// blamed on the specification.
///
/// `statuses` raises `ObsError::NotSpawned` for the outer graph as readily as
/// for a probe's, and `ConfCtx::gate` funnels every `Err` into one message.
/// §8 makes this the *user's* error in whichever program committed it, and the
/// two programs here differ only in that the implementation is missing the
/// declared thread, so the message names the wrong one.
///
/// **`NotSpawned` reaches the classifier by only one route, and that is what
/// this test pins.** `wobs` cannot raise it: `resolve` returns `Ok(None)` and
/// `visible_events` turns that into `Row::Unspawned`, the empty sequence and a
/// perfectly good `Ok` (obs.rs:259; obs.rs:224's doc says so in as many words,
/// "Raised by `statuses`, not by `wobs`"). Only `statuses` raises it, so
/// `blame_for` must run a status extraction over `g1` and not just a `wobs`.
///
/// *(Found failing at gate 3 as finding F-D, and still failing after a first
/// fix that consulted `wobs` alone — which is why the sibling test
/// [`c9_an_ambiguous_name_in_the_implementation_is_blamed_on_the_implementation`]
/// is not a substitute: `AmbiguousName` *is* raised by `wobs`, so it passed
/// throughout and would have signed off a classifier that was wrong here.)*
#[test]
fn c9_a_never_spawned_visible_name_is_not_blamed_on_the_specification() {
    let message = panic_message(|| {
        let _ = conf(
            // No thread called `w` at all.
            || {},
            || {
                named("w", || {});
            },
            &["main", "w"],
        );
    });
    let message = message.expect("a declared visible name the implementation never spawned was accepted");
    println!("got: {message}");
    assert!(
        !message.contains("the specification program is not a valid input"),
        "an implementation-side §8 violation was reported against the specification: `{message}`"
    );
}

// ===========================================================================
// The revisit-apply departure from §4.2's uniform wording.
//
// §4.2 says a gate failure records the report, `block_exec`s and `stop`s. The
// revisit-apply gate now instead **abandons** the alternative and polls the
// worklist for the next one. The lead records it as a departure and asks for
// it to be attacked; these are that attack. The question that matters is
// whether the abandoned graph — already mutated in place by `forward_revisit`,
// or replaced wholesale by `backward_revisit` after a `push_state` — can reach
// anything before the next pop rebuilds or cuts.
// ===========================================================================

/// A **coverable** sibling alternative survives a revisit-apply prune and is
/// still explored.
///
/// The oracle is exact and derived from the program, not from a run. `main`
/// has one receive with three sources, 1, 2 and 3; the specification can
/// produce 1 and 3 but not 2. So:
///
/// - the canonical execution reads 1, is covered, and runs — one complete
///   execution;
/// - the alternative reading 2 is popped, gated at `RevisitApply`, and pruned;
/// - the alternative reading 3 is popped, gated, covered, and **must run** —
///   a second complete execution.
///
/// Exactly one report, at `RevisitApply`. If abandoning the middle alternative
/// corrupted `current.graph` or the worklist, the third is lost, mis-explored,
/// or crashes.
#[test]
fn o6_a_coverable_sibling_survives_a_revisit_apply_prune() {
    let implementation = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        named("c", move || crate::send_msg(m, 3u64));
        let _: u64 = crate::recv_msg_block();
    };
    let specification = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("c", move || crate::send_msg(m, 3u64));
        let _: u64 = crate::recv_msg_block();
    };

    // The control: three sources really are three executions.
    let plain = crate::verify(fifo(), implementation);
    assert_eq!((plain.execs, plain.block), (3, 0), "{plain:?}");

    let out = conf(implementation, specification, &["main"]);
    let s = stats(&out);
    assert_eq!(
        report_gates(&out),
        vec![Some(Gate::RevisitApply)],
        "expected exactly the middle alternative to be reported, at the revisit-apply gate"
    );
    assert_eq!(
        (s.execs, s.block),
        (2, 0),
        "the two coverable alternatives did not both run to completion; abandoning the \
         middle one disturbed the worklist or the graph"
    );
}

/// The departure's own signature: a revisit pruned **before launch** produces
/// no execution at all.
///
/// Under §4.2's uniform wording the same prune would `block_exec` + `stop`, and
/// the abandoned alternative would be counted as one more **blocked**
/// execution. Under the departure it is counted as nothing. The test pins the
/// departure rather than merely tolerating it: restore `block_exec` + `stop`
/// at the revisit-apply gate and `block` goes from 0 to 1.
///
/// This is also the shape that used to crash (developer's F-A): the same pair,
/// with the gate's prune leaving `stop` set and the next completion gate then
/// firing on a pruned, unreplayed graph.
#[test]
fn c3_a_revisit_apply_prune_skips_rather_than_blocking() {
    let implementation = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
    };
    let specification = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    };
    let plain = crate::verify(fifo(), implementation);
    assert_eq!((plain.execs, plain.block), (2, 0), "{plain:?}");

    let out = conf(implementation, specification, &["main"]);
    let s = stats(&out);
    assert_eq!(
        report_gates(&out),
        vec![Some(Gate::RevisitApply)],
        "the unmatchable second source was not reported at the revisit-apply gate"
    );
    assert_eq!(
        (s.execs, s.block),
        (1, 0),
        "a revisit pruned before launch was counted as an execution; §4.2's uniform \
         wording would make this (1, 1) and the departure makes it (1, 0)"
    );
}

/// An abandoned **backward** revisit leaves nothing behind for a shallower
/// alternative to trip over.
///
/// `backward_revisit` is the dangerous half of the departure: unlike
/// `forward_revisit` it does `push_state()` and then replaces
/// `self.current.graph` wholesale with a cut view. Abandoning it leaves that
/// state on the stack and the cut view installed as `current.graph`, with the
/// pruned alternative's labels in it, and the next pop inherits both.
///
/// The program puts a shallow, ungated `CToss` alternative behind exactly that
/// situation. The `true` branch sends, is pruned at `FreshSend`, and its
/// backward revisit is later popped and abandoned at `RevisitApply`; the
/// `false` branch sends nothing, is coverable, and is reached only by the coin
/// flip queued at a shallower stamp than either.
///
/// Oracle: one complete execution (the `false` branch), one blocked (the
/// `true` branch, pruned at its fresh-add gate), and the coin flip itself
/// ungated (§4.1's ND exemption), so no report names it.
#[test]
fn o6_an_abandoned_backward_revisit_leaves_a_shallower_alternative_intact() {
    let implementation = || {
        let m = main_thread_id();
        let w = named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
        named("x", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
        if crate::nondet() {
            crate::send_msg(w, 7u64);
        }
    };
    let specification = || {
        let m = main_thread_id();
        named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
        named("x", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    };

    let out = conf(implementation, specification, &["main"]);
    let s = stats(&out);
    assert!(
        report_gates(&out).contains(&Some(Gate::FreshSend)),
        "the sending branch was never pruned, so nothing was under test: {:?}",
        report_gates(&out)
    );
    assert_eq!(
        s.execs, 1,
        "the non-sending branch, reachable only through a coin flip queued at a shallower \
         stamp than both prunes, did not run to completion. Reports: {:?}",
        report_gates(&out)
    );
    assert_eq!(
        s.block, 1,
        "expected exactly the sending branch to end blocked. Reports: {:?}",
        report_gates(&out)
    );
}

/// O2's completeness half, which F-A made unwritable.
///
/// The gate-3 report recorded this as half-tested: every program shape that
/// forced a revisit-deep, maximally-stale `H` *and* a real difference to catch
/// hit the revisit-apply crash. With that fixed the half is writable, so here
/// it is.
///
/// §4.3 keeps one mutable `H` and never restores it on backtrack, so at these
/// pops the carried `H` is the one some unrelated branch left behind.
/// Completeness is supposed to be restored by `Cover`'s rebuild-from-empty on
/// extend-failure. If it were not, a difference reachable only after several
/// pops would be missed and the run would be silent.
#[test]
fn c14_a_stale_carried_h_still_catches_a_real_difference() {
    let implementation = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
        let _: Option<u64> = crate::recv_msg();
    };
    // Identical but for `b`'s value, so the difference is only visible on the
    // branches that read from `b` — several pops deep.
    let specification = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 5u64));
        let _: u64 = crate::recv_msg_block();
        let _: Option<u64> = crate::recv_msg();
    };

    // The program really is revisit-heavy: four executions, so most pops see
    // an `H` left by a different branch.
    let plain = crate::verify(fifo(), implementation);
    assert_eq!((plain.execs, plain.block), (4, 0), "{plain:?}");

    let out = conf(implementation, specification, &["main"]);
    assert!(
        !out.reports.is_empty(),
        "a real difference several revisit pops deep was missed; the carried `H` went \
         stale and `Cover`'s rebuild-from-empty did not restore completeness"
    );
    assert!(
        out.exhaustions.is_empty(),
        "the search ran out of room, so a report proves nothing about staleness: {:?}",
        out.exhaustions
    );

    // Not vacuous in the other direction: the same program against itself,
    // with the same pops and the same staleness, is silent.
    let out = conf(implementation, implementation, &["main"]);
    assert!(
        out.reports.is_empty(),
        "the identical pair reported, so the report above is not about the difference: {:?}",
        out.reports
    );
}

/// What the F-D fix *does* reach: an ambiguous name in the implementation is
/// now blamed on the implementation.
///
/// Kept next to the never-spawned case so the two halves of §8's error
/// attribution can be compared. `wobs` raises `AmbiguousName` itself, so
/// re-deriving blame by asking `wobs` about `g1` catches this one.
#[test]
fn c9_an_ambiguous_name_in_the_implementation_is_blamed_on_the_implementation() {
    let message = panic_message(|| {
        let _ = conf(
            || {
                named("w", || {});
                named("w", || {});
            },
            || {
                named("w", || {});
            },
            &["main", "w"],
        );
    });
    let message = message.expect("two threads sharing a declared visible name were accepted");
    println!("got: {message}");
    assert!(
        message.contains("the implementation program is not a valid input"),
        "an implementation-side ambiguous name was not blamed on the implementation: `{message}`"
    );
}

// ---------------------------------------------------------------------------
// §8 error attribution, as a 2x2 rather than a pair of examples.
//
// `ConfCtx::blame_for` is a two-way classifier, so one direction proves
// nothing: "always says implementation" passes every implementation-side test
// ever written, and "always says specification" was the original F-D. Both
// `ObsError` kinds are therefore asked in both directions. The four tests are
// exact mirrors — same program shape, the defect moved from one side to the
// other — so a classifier that ignores its argument fails two of the four
// whichever constant it returns.
//
// The two kinds are not redundant either: they reach `blame_for` through
// different limbs. `AmbiguousName` is raised by `wobs` and caught by the first
// match arm; `NotSpawned` is raised only by `statuses`, so it reaches the
// classifier solely through the `try_finished` limb — which is exactly the
// limb the first attempt at this fix lacked.
// ---------------------------------------------------------------------------

/// Converse of the never-spawned case: the **specification** is the one
/// missing the declared thread, and must be the one named.
#[test]
fn c9_a_never_spawned_visible_name_in_the_specification_is_blamed_on_the_specification() {
    let message = panic_message(|| {
        let _ = conf(
            || {
                named("w", || {});
            },
            // No thread called `w` at all.
            || {},
            &["main", "w"],
        );
    });
    let message = message.expect("a declared visible name the specification never spawned was accepted");
    println!("got: {message}");
    assert!(
        message.contains("the specification program is not a valid input"),
        "a specification-side §8 violation was not blamed on the specification: `{message}`"
    );
    assert!(
        message.contains("never spawned"),
        "the message does not say which §8 condition was broken: `{message}`"
    );
}

/// Converse of the ambiguous-name case.
///
/// This one also exercises `blame_for`'s `try_finished(g1) == None` limb: the
/// specification's `wobs` fails at the first gate, where the implementation
/// graph is not finished, so the classifier has to answer without a status
/// extraction to consult.
#[test]
fn c9_an_ambiguous_name_in_the_specification_is_blamed_on_the_specification() {
    let message = panic_message(|| {
        let _ = conf(
            || {
                let w = named("w", || {
                    let _: u64 = crate::recv_msg_block();
                });
                crate::send_msg(w, 1u64);
            },
            || {
                let w = named("w", || {
                    let _: u64 = crate::recv_msg_block();
                });
                named("w", || {});
                crate::send_msg(w, 1u64);
            },
            &["main", "w"],
        );
    });
    let message = message.expect("two specification threads sharing a declared visible name were accepted");
    println!("got: {message}");
    assert!(
        message.contains("the specification program is not a valid input"),
        "a specification-side ambiguous name was not blamed on the specification: `{message}`"
    );
    assert!(
        message.contains("two threads are named"),
        "the message does not say which §8 condition was broken: `{message}`"
    );
}

/// When **both** programs break the same §8 condition, the implementation is
/// named.
///
/// Recorded rather than asserted as a virtue: with both sides wrong either
/// answer is defensible, and what matters is that the choice is deterministic
/// and that the message still says which condition was broken. Naming the
/// implementation is the better default — it is the program the user ran — and
/// pinning it here stops the tie-break drifting silently, since neither of the
/// four directed tests above can see it.
#[test]
fn c9_when_both_programs_break_section_8_the_implementation_is_named() {
    let message = panic_message(|| {
        let _ = conf(|| {}, || {}, &["main", "w"]);
    });
    let message = message.expect("neither program spawned `w` and both were accepted");
    println!("got: {message}");
    assert!(
        message.contains("the implementation program is not a valid input"),
        "the tie-break changed: `{message}`"
    );
    assert!(
        message.contains("never spawned"),
        "the message does not say which §8 condition was broken: `{message}`"
    );
}

// ===========================================================================
// Gate-4 B1 --- a thread that keeps running past its own prune.
//
// This is derived property C4, which the gate-3 pass listed ("the three silent
// sites do something defensible with `ConfPrune`") and then never came back
// to. It should have been three tests then; it is three tests now.
//
// `conf_prune` writes `Block(ConfPrune)` at `thread_last(t).pos().next()` for
// every thread — including the one still running. That is exactly the position
// the pruning thread's next `next_pos()` hands out, and `traceforge::assert`
// installs its label without yielding first. So the thread walks straight into
// a position conformance has already written, `is_replay` is true,
// `validate_replay_event` compares `Block(ConfPrune)` against `Block(Assert)`,
// and `blocks_are_compatible` decides. Its catch-all answered `false`, and the
// caller turns `false` into "Incorrect TraceForge Program … must be
// deterministic" --- a conformance-internal defect billed to the user.
//
// The three reproducers reach it through different gates, which is the point:
// the pruning gate and the thread that runs past it are different mechanisms,
// and a fix that only handled one of them would pass the other two.
// ===========================================================================

/// One pruned `FreshSend` gate, then the same thread asserts.
#[test]
fn b1_an_assert_after_a_pruned_send_is_not_program_nondeterminism() {
    let out = conf(
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
            // The send's gate prunes here. `main` has not yielded, so this
            // lands on the position `conf_prune` just wrote.
            crate::assert(false);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 2u64);
        },
        &["main"],
    );
    assert_eq!(
        report_gates(&out),
        vec![Some(Gate::FreshSend)],
        "the send was not the thing pruned, so the reproducer is not set up"
    );
    assert_eq!(
        out.diagnostics.len(),
        1,
        "the assertion after the prune was dropped without trace: {:?}",
        out.diagnostics
    );
    assert!(
        matches!(out.diagnostics[0].reason, DiagnosticReason::AfterPrune),
        "recorded with the wrong reason: {:?}",
        out.diagnostics[0]
    );
}

/// The same, through the **receive** gate.
///
/// `FreshRecv` prunes from inside `visit_rfs`, several frames below the
/// handler `FreshSend` prunes from, so the position bookkeeping on the way
/// back out is not the same code.
#[test]
fn b1_an_assert_after_a_pruned_receive_is_not_program_nondeterminism() {
    let out = conf(
        || {
            let m = main_thread_id();
            named("a", move || crate::send_msg(m, 1u64));
            let _: u64 = crate::recv_msg_block();
            crate::assert(false);
        },
        || {
            let m = main_thread_id();
            named("a", move || crate::send_msg(m, 9u64));
            let _: u64 = crate::recv_msg_block();
        },
        &["main"],
    );
    assert_eq!(
        report_gates(&out),
        vec![Some(Gate::FreshRecv)],
        "the receive was not the thing pruned, so the reproducer is not set up"
    );
    assert_eq!(
        out.diagnostics.len(),
        1,
        "the assertion after the prune was dropped without trace: {:?}",
        out.diagnostics
    );
    assert!(
        matches!(out.diagnostics[0].reason, DiagnosticReason::AfterPrune),
        "recorded with the wrong reason: {:?}",
        out.diagnostics[0]
    );
}

/// **Two failing asserts on a visible thread**, which is the form the reviewer
/// hit: the first is the §4.4 report that prunes, the second walks into the
/// `Block(ConfPrune)` the prune just wrote.
///
/// Nothing about a gate is involved — `conf_assert_failure` prunes on its own
/// — so this is the third distinct route in.
#[test]
fn b1_two_failing_visible_asserts_are_not_program_nondeterminism() {
    let out = conf(
        || {
            crate::assert(false);
            crate::assert(false);
        },
        || {},
        &["main"],
    );
    assert_eq!(
        out.reports.len(),
        1,
        "the second failure became a second report; the first already names \
         the occasion: {:?}",
        out.reports
    );
    assert!(
        matches!(out.reports[0].kind, ReportKind::VisibleError { .. }),
        "{:?}",
        out.reports[0]
    );
    assert_eq!(
        out.diagnostics.len(),
        1,
        "the second failure was dropped silently: {:?}",
        out.diagnostics
    );
    assert!(
        matches!(out.diagnostics[0].reason, DiagnosticReason::AfterPrune),
        "recorded with the wrong reason: {:?}",
        out.diagnostics[0]
    );

    // **All three of `Diagnostic`'s fields, not just `reason`** (gate-4 round
    // 2, M1). The first version of this test asserted the count and the reason
    // and read neither `thread` nor `pos`, and two of the three fields were
    // wrong underneath it: the diagnostic carried the *runtime task name*
    // while the report carried the declared visible name, so the same thread
    // came out as `main` in one and `main-thread-ThreadId(N)` in the other —
    // breaking exactly the join S5 needs to pair a prune with what followed it.
    let ReportKind::VisibleError { thread: reported, pos: reported_pos } =
        &out.reports[0].kind
    else {
        unreachable!("checked just above")
    };
    assert_eq!(
        &out.diagnostics[0].thread, reported,
        "the diagnostic and the report name the same thread differently, so they \
         cannot be joined"
    );
    assert_eq!(
        out.diagnostics[0].pos.thread, reported_pos.thread,
        "the diagnostic is attributed to a different thread than the report"
    );
    assert_ne!(
        out.diagnostics[0].pos, *reported_pos,
        "the two failing statements were given the same position, so the \
         diagnostic cannot say which one it is about"
    );

    let s = stats(&out);
    assert_eq!(
        (s.execs, s.block),
        (0, 1),
        "the pruned execution was miscounted"
    );
}

/// A third failing assert adds a third diagnostic, not a third report.
///
/// Without this, "record exactly one `AfterPrune` and then stop recording"
/// would pass all three tests above.
#[test]
fn b1_every_failure_after_a_prune_is_recorded() {
    let out = conf(
        || {
            crate::assert(false);
            crate::assert(false);
            crate::assert(false);
        },
        || {},
        &["main"],
    );
    assert_eq!(out.reports.len(), 1, "{:?}", out.reports);
    assert_eq!(
        out.diagnostics.len(),
        2,
        "failures after a prune are being coalesced or dropped: {:?}",
        out.diagnostics
    );
    assert!(out
        .diagnostics
        .iter()
        .all(|d| matches!(d.reason, DiagnosticReason::AfterPrune)));

    // Every diagnostic joins to the report, and the three failing statements
    // stay distinguishable from one another.
    let ReportKind::VisibleError { thread: reported, pos: reported_pos } =
        &out.reports[0].kind
    else {
        panic!("{:?}", out.reports[0])
    };
    assert!(
        out.diagnostics.iter().all(|d| &d.thread == reported),
        "a diagnostic does not join to the report: {:?} vs `{reported}`",
        out.diagnostics
    );
    let mut positions: Vec<_> = out
        .diagnostics
        .iter()
        .map(|d| d.pos)
        .chain(std::iter::once(*reported_pos))
        .collect();
    positions.sort();
    positions.dedup();
    assert_eq!(
        positions.len(),
        3,
        "the three failing statements did not get three distinct positions: {:?}",
        out.diagnostics
    );
}

/// `"main"` may not be used as a `Builder` thread name under either engine,
/// and an ordinary `verify` is unaffected.
#[test]
fn c9_main_is_banned_as_a_builder_name_under_conformance() {
    let message = panic_message(|| {
        let _ = conf(
            || {
                named("main", || {});
            },
            || {},
            &["main"],
        );
    });
    let message = message.expect("`main` was accepted as a Builder thread name");
    assert!(
        message.contains("reserved for each program's own main thread"),
        "banned for the wrong reason, or caught late at extraction as an \
         ambiguous name instead of at the declaration: `{message}`"
    );

    // The ban is on the engine, not on TraceForge: an ordinary run is
    // untouched. Without this the guard could have been written unconditionally
    // and criterion 1 would have been broken by it.
    let s = crate::verify(fifo(), || {
        named("main", || {});
    });
    assert!(
        s.execs + s.block > 0,
        "an ordinary run was refused a thread named `main`"
    );
}

// ===========================================================================
// §9's handler-entry guards on the **specification**, reached the way a
// conformance run reaches them.
//
// The gate-4 reviewer's point, and it is a good one: `c6_probe_engine_rejects_*`
// and `c10_the_probe_engine_refuses_the_same_list` call `prober::probe_once`
// directly. That is not the path production takes. A conformance run reaches
// the specification through `ConfCtx` -> `ProbeWorker` -> a dedicated OS
// thread -> `Search::cover` -> `probe_from`, and the guard fires several
// frames and one thread boundary away from the caller. Criteria 6 and 12 were
// therefore satisfied on a path production never uses, which is the same class
// of gap as criterion 7's "the guards were watching the wrong engine".
//
// These drive each rejection through `verify_conformance` with the
// out-of-scope construct in the **specification** program, and assert the
// message survives the worker boundary — which it does only because the worker
// catches the panic and `resume_unwind`s it on the calling thread. A worker
// that let the payload turn into a channel error would fail every one of them.
// ===========================================================================

fn assert_spec_guard<F>(expected: &str, specification: F)
where
    F: Fn() + Send + Sync + 'static,
{
    let message = panic_message(move || {
        // The implementation is in scope and trivially coverable, so the only
        // thing that can refuse the run is the specification.
        let _ = conf(|| {}, specification, &["main"]);
    });
    let message = message.unwrap_or_else(|| {
        panic!("the specification was allowed to use `{expected}` and the run returned normally")
    });
    if !message.contains(expected) {
        println!(
            "FINDING: a specification-side scope rejection did not survive the probe worker \
             boundary.\n\x20 wanted: {expected}\n\x20 got:    {message}"
        );
    }
    assert!(
        message.contains(expected),
        "a specification-side scope rejection did not reach the caller intact.\n  wanted: \
         `{expected}`\n  got:    `{message}`"
    );
}

#[test]
fn c6_a_specification_using_an_inbox_is_refused_through_verify_conformance() {
    assert_spec_guard("`inbox` is outside conformance scope", || {
        let _ = crate::inbox();
    });
}

#[test]
fn c6_a_specification_using_sample_is_refused_through_verify_conformance() {
    assert_spec_guard("`sample` is outside conformance scope", || {
        let _: i64 = crate::sample(rand::distr::Uniform::new(0i64, 3i64).unwrap(), 2);
    });
}

#[test]
fn c6_a_specification_using_a_total_order_send_is_refused_through_verify_conformance() {
    assert_spec_guard("`a TotalOrder (mailbox) send` is outside conformance scope", || {
        let (tx, _rx) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::TotalOrder)
            .build();
        tx.send_msg(1);
    });
}

#[test]
fn c6_a_specification_using_a_total_order_receive_is_refused_through_verify_conformance() {
    assert_spec_guard(
        "`a TotalOrder (mailbox) receive` is outside conformance scope",
        || {
            let (_tx, rx) = crate::channel::Builder::<i32>::new()
                .with_comm(crate::CommunicationModel::TotalOrder)
                .build();
            let _ = rx.recv_msg();
        },
    );
}

#[test]
fn c6_a_specification_spawning_symmetrically_is_refused_through_verify_conformance() {
    assert_spec_guard("`symmetric thread spawning` is outside conformance scope", || {
        let m = main_thread_id();
        let a = thread::spawn(move || crate::send_msg(m, 1u64));
        let _ = crate::spawn_symmetric(move || crate::send_msg(m, 1u64), a.thread().id());
    });
}

#[test]
fn c6_a_specification_registering_a_monitor_is_refused_through_verify_conformance() {
    assert_spec_guard("`monitor registration` is outside conformance scope", || {
        let m: std::sync::Arc<std::sync::Mutex<dyn crate::monitor_types::Monitor>> =
            std::sync::Arc::new(std::sync::Mutex::new(NoopMonitor));
        let _: crate::thread::JoinHandle<u64> =
            crate::spawn_monitor(|| 0u64, no_create, no_accept, m);
    });
}

#[test]
#[cfg(feature = "symbolic")]
fn c6_a_specification_branching_symbolically_is_refused_through_verify_conformance() {
    assert_spec_guard(
        "`symbolic constraint evaluation` is outside conformance scope",
        || {
            let b = crate::symbolic::fresh_bool();
            let _ = crate::symbolic::eval(b);
        },
    );
}

/// `"main"` as a `Builder` name in the **specification** is refused too.
#[test]
fn c9_main_is_banned_as_a_builder_name_in_the_specification() {
    assert_spec_guard("reserved for each program's own main thread", || {
        named("main", || {});
    });
}

/// §5.4: the specification must be error-free, and a failed assertion in it
/// must reach the caller as itself.
///
/// Not a §9 rejection but the same boundary question, and the one the reviewer's
/// M1 was actually about: before the worker forwarded payloads this arrived as
/// "the probe worker died mid-search: RecvError".
#[test]
fn c6_a_specification_assertion_failure_reaches_the_caller_intact() {
    let message = panic_message(|| {
        let _ = conf(
            || {
                let w = named("w", || {
                    let _: u64 = crate::recv_msg_block();
                });
                crate::send_msg(w, 1u64);
            },
            || {
                let w = named("w", || {
                    let _: u64 = crate::recv_msg_block();
                });
                crate::send_msg(w, 1u64);
                crate::assert(false);
            },
            &["main"],
        );
    });
    let message = message.expect("a specification that fails an assertion was accepted");
    println!("got: {message}");
    assert!(
        !message.contains("the probe worker died"),
        "a specification-side failure was reported as a channel error: `{message}`"
    );
}

/// The probe worker is shut down where the run ends, not whenever the
/// thread-local happens to be replaced.
///
/// `Drop` is the backstop and cannot be the normal path: `explore` installs the
/// outer `Must` in `CURRENT_MUST` and never clears it, so when
/// `verify_conformance` drops its own `Rc` the refcount is still 1. The `Must`
/// is not dropped, `ConfCtx` is not dropped, and the worker stays parked in
/// `recv` **holding the specification closure** — and everything the user
/// captured in it — until some later run replaces the thread-local.
///
/// The gate-3 report claimed this was "covered by volume", and the gate-4
/// reviewer was right that the conclusion did not follow: 62 runs that do not
/// hang show only that nothing hangs, which `Drop` alone would also show. What
/// distinguishes "joined where the run ends" from "joined eventually" is
/// whether the closure is still alive *at the moment the call returns*, and
/// nothing in the suite looked.
///
/// So: give the specification closure sole ownership of an `Arc`, keep only a
/// `Weak` outside it, and look immediately. Delete the `conf_shutdown` call in
/// `verify_conformance` and `upgrade()` starts returning `Some`.
#[test]
fn m1_the_probe_worker_is_shut_down_where_the_run_ends() {
    use std::sync::{Arc, Weak};

    let sentinel = Arc::new(());
    let weak: Weak<()> = Arc::downgrade(&sentinel);

    let out = verify_conformance(
        fifo(),
        || {},
        move || {
            // The closure's only job is to own `sentinel`. Nothing else holds
            // a strong reference, so the `Arc` lives exactly as long as the
            // worker thread that holds the closure.
            let _owned = &sentinel;
        },
        names(&["main"]),
        64,
    );
    assert!(out.reports.is_empty(), "{:?}", out.reports);

    assert!(
        weak.upgrade().is_none(),
        "the specification closure is still alive after `verify_conformance` \
         returned, so the probe worker is still parked holding it — and \
         everything the user captured in it — until something else replaces \
         the `CURRENT_MUST` thread-local"
    );
}

/// The sentinel really would survive without the shutdown, so the test above
/// is not asserting something `Arc` gives for free.
///
/// Same shape, but the strong reference is kept here rather than handed to the
/// closure: `upgrade()` must succeed. If a bare `Weak` to a live `Arc` could
/// come back `None`, the test above would pass for a reason that has nothing
/// to do with the worker.
#[test]
fn m1_the_shutdown_sentinel_is_not_self_fulfilling() {
    use std::sync::Arc;

    let sentinel = Arc::new(());
    let weak = Arc::downgrade(&sentinel);
    let held = Arc::clone(&sentinel);

    let out = verify_conformance(
        fifo(),
        || {},
        move || {
            let _owned = &sentinel;
        },
        names(&["main"]),
        64,
    );
    assert!(out.reports.is_empty(), "{:?}", out.reports);
    assert!(
        weak.upgrade().is_some(),
        "a `Weak` to an `Arc` still held on the stack came back empty"
    );
    drop(held);
}

/// Is an **invisible** thread's failure after a prune reachable at all?
///
/// The gate-3 report raised it as a note for S5: the post-prune branch is taken
/// before the visible/invisible split, so such a failure would be recorded as
/// `AfterPrune` and would not appear under CA §7's "invisible assertion
/// failure" heading. Round 2's fix resolves the *name*, which was the M1
/// defect, but the reason is still `AfterPrune` for either kind of thread.
///
/// This test asks whether the case can be built. It documents the answer rather
/// than asserting a disposition, because the disposition only matters if the
/// case is reachable: `conf_prune` calls `stop()`, so after a prune the only
/// thread that runs on is the one that triggered it, and a gate on an invisible
/// thread's event sees the same visible observations the previous gate saw — so
/// it cannot newly fail. Both routes to a prune therefore end on a thread that
/// is either visible or the one that asserted.
#[test]
fn c5_an_invisible_failure_after_a_prune_is_not_reachable_by_this_construction() {
    let out = conf(
        || {
            let m = main_thread_id();
            named("hidden", move || {
                crate::send_msg(m, 5u64);
                // Would only be reached if this thread kept running past a
                // prune triggered by its own send.
                crate::assert(false);
            });
            let _: Option<u64> = crate::recv_msg();
        },
        || {
            let m = main_thread_id();
            named("hidden", move || crate::send_msg(m, 5u64));
            let _: Option<u64> = crate::recv_msg();
        },
        &["main"],
    );
    println!(
        "reports={:?} diagnostics={:?}",
        report_gates(&out),
        out.diagnostics
    );
    // Whatever the routing, an invisible thread's failure is never a report.
    assert!(
        out.reports
            .iter()
            .all(|r| !matches!(r.kind, ReportKind::VisibleError { .. })),
        "an invisible thread's failure was reported as a visible error: {:?}",
        out.reports
    );
    // And every diagnostic it produces is attributed to `hidden`, whichever
    // reason it carries — the field M1 was about.
    assert!(
        out.diagnostics.iter().all(|d| d.thread.contains("hidden")),
        "a diagnostic from the invisible thread is attributed elsewhere: {:?}",
        out.diagnostics
    );
    assert!(
        !out.diagnostics.is_empty(),
        "the invisible thread never failed, so nothing was under test"
    );
}

// ===========================================================================
// F49 --- the replay frontier.
//
// `ExecutionGraph::initialize_for_execution` blanks **every** send value at
// the start of each execution and the values come back only as each event is
// re-executed. A fresh-add gate can therefore fire while a *different* visible
// thread is still behind that frontier, and `wobs` walks every visible row —
// so it reaches a blanked send and trips `obs.rs`'s pending-value guard. The
// repair in `ConfCtx::gate` is to skip a gate whose graph still has unreplayed
// events.
//
// Two tests: the crash does not happen, and the skip does not reach the
// completion gate. Both are new in the developer's S7-fixes pass; F49 had no
// regression test at all, only `bench.rs`'s realistic pair.
// ===========================================================================

/// The **minimal** shape F49 needs, which is not the shape the flaw was first
/// filed under.
///
/// The lead's first hypothesis was "`nondet()` in a declared visible thread";
/// that is wrong, and the corrected table in `backlog/flaws.md` F49 is
/// measured one variable at a time:
///
/// | visible threads | of which branch | result |
/// |---|---|---|
/// | 1 | 1 | OK |
/// | 2 | 0 | OK |
/// | 2 | 1 | OK |
/// | 2 | **2** | **PANIC** |
///
/// So the program below is the smallest thing that reproduces it: one
/// invisible hub (`main`), and **two** declared visible threads that each
/// `recv` → `nondet()` → `send` → `recv`. One of them is adding a fresh event
/// while the other sits behind the replay frontier, which is the whole
/// mechanism.
///
/// The pair is the program against **itself**, so conformance is expected to
/// hold and any report would be a separate finding. That is deliberate: this
/// test is about the run surviving, and a violating pair would confound "the
/// guard did not fire" with "the search found something".
///
/// **Mutation, MEASURED**: delete
/// `if !g1.unreplayed_events.is_empty() { return GateOutcome::Continue; }`
/// from `ConfCtx::gate` and this test fails with
///
/// ```text
/// thread 'traceforge-conformance-probe' panicked at conformance/obs.rs:304:
/// conformance: observed a send at (t1, 3) whose value is still pending.
/// ```
#[test]
fn two_visible_threads_that_both_branch_survive_the_replay_frontier() {
    let out = conf(
        two_branching_visibles,
        two_branching_visibles,
        &["p0", "p1"],
    );
    assert!(
        out.reports.is_empty(),
        "the program conforms to itself; a report here is a separate finding: {:?}",
        report_gates(&out)
    );
    assert_eq!(
        stats(&out).execs,
        8,
        "the outer exploration must be the one an ordinary run does; a different \
         count means the skip changed *which* executions happen, not just when \
         the gate asks"
    );
}

/// One invisible hub and two declared visible threads that each branch.
///
/// No `ThreadId` crosses a *visible* thread's observation — the hub is
/// `main_thread_id()`, which is `t0` in both programs, and the participants'
/// ids are used only by the hub — so F41 does not arise and the pair's
/// conformance is not an artefact of spawn order.
fn two_branching_visibles() {
    let hub = main_thread_id();
    let branching = move || {
        let _: i32 = crate::recv_msg_block();
        let v = crate::nondet();
        crate::send_msg(hub, if v { 1i32 } else { 0i32 });
        let _: i32 = crate::recv_msg_block();
    };
    let p0 = named("p0", branching);
    let p1 = named("p1", branching);
    crate::send_msg(p0, 0i32);
    crate::send_msg(p1, 0i32);
    let _a: i32 = crate::recv_msg_block();
    let _b: i32 = crate::recv_msg_block();
    crate::send_msg(p0, 9i32);
    crate::send_msg(p1, 9i32);
}

/// **The completion gate is never the one that gets skipped**, on the program
/// that makes the skip fire hardest.
///
/// This is the load-bearing half of the argument offered for F49's fix (the
/// lead recorded the rest as **A16**, unproven): a fresh-add gate that cannot
/// observe the graph is skipped, and the answer is deferred to the completion
/// gate, which "always runs with every event replayed". Deferring to a gate
/// that is itself skipped would not be a deferral — it would be a silent loss,
/// and the difference is not visible in any verdict, because a skipped gate
/// leaves no trace in the outcome.
///
/// [`gates_fired`]'s instrument makes it visible. With a budget of zero every
/// gate that reaches `cover` records one `Exhaustion` carrying its `Gate`, and
/// a gate the replay guard skipped returns *above* `cover` and records
/// nothing. So the completion gates in `out.exhaustions` are exactly the
/// completion gates that were not skipped, and `execs + block` is how many
/// execution endings there were.
///
/// **Measured** on this program, this tree, 2026-09-16 (developer's P3-skips
/// pass): 8 executions, 0 blocked, and a census of 7 `FreshSend`, 23
/// `FreshRecv`, 4 `RevisitApply`, **8 `Completion`** — one per ending, none
/// missing.
///
/// **The previous figures were wrong and are corrected here.** They read
/// "24 `FreshSend`, 29 `FreshRecv`" and were taken on a **pre-F42** build.
/// The 53 fresh-add gates became 30, and the missing **23** are exactly this
/// run's `Outcome::inert_gates` — F42's skip returns above `cover`, so those
/// gates record no `Exhaustion` and drop out of the census. The completion
/// count is unaffected, which is the point: F42 skips only the two fresh
/// gates, so `Completion` is the one column this instrument still counts
/// completely, and the assertion below rests on that column alone.
///
/// The fresh-add counts are therefore **not** a complete gate census on this
/// program, and the "not vacuous" assertion below is worded accordingly.
///
/// **Mutation, MEASURED**: deleting the skip does not make this test fail with
/// a wrong count — it makes it **panic** at `obs.rs:304`, because a zero
/// budget does not short-circuit `wobs` (`cover` extracts the observation
/// before it spends). So this test's failing direction is F49's crash, and the
/// count assertion is what would catch a *future* skip that swallowed a
/// completion gate. Stated rather than claimed both ways.
#[test]
fn the_completion_gate_is_never_skipped_by_the_replay_guard() {
    let out = verify_conformance(fifo(), two_branching_visibles, || {}, names(&["p0", "p1"]), 0);
    assert!(
        out.reports.is_empty(),
        "a zero budget established nothing, so it must report nothing: {:?}",
        out.reports
    );
    let st = stats(&out);
    let completions = out
        .exhaustions
        .iter()
        .filter(|e| e.gate == Gate::Completion)
        .count();
    assert_eq!(
        completions,
        st.execs + st.block,
        "every execution ending must reach the completion gate: {} ending(s) but \
         {completions} completion gate(s) got as far as `cover`. The skipped ones \
         are where a violation would have been lost rather than deferred.",
        st.execs + st.block
    );
    // Not vacuous: fresh-add gates reach `cover` too, so the census is of a
    // real run rather than a run of nothing but completions.
    //
    // Deliberately **not** `assert_skips_did_not_blind_the_census`: this
    // program exists to make both skips fire, so its fresh-add census is
    // knowingly short. Only the `Completion` column above is complete, and it
    // is the only one asserted on.
    assert!(
        count(&out.exhaustions.iter().map(|e| e.gate).collect::<Vec<_>>(), Gate::FreshSend) > 0,
        "no fresh-add gate reached `cover`, so this program does not exercise the skip"
    );
    assert!(
        out.skipped_gates > 0 && out.inert_gates > 0,
        "both skips must fire on this program or it is not the hard case it \
         claims to be: skipped={} inert={}",
        out.skipped_gates,
        out.inert_gates
    );
}

// ===========================================================================
// F42 --- the inertness skip, and what the two skip counters are worth.
//
// Written in the developer's P3-skips pass. F42 shipped with no test of its
// own; `c2_replayed_events_are_not_re_gated` was *adjusted* for it, which is
// not the same thing.
// ===========================================================================

/// **The total number of gate calls**, which `exhaustions` alone cannot give.
///
/// This is the instrument the gate census was missing. At a budget of zero
/// every gate that reaches `cover` records exactly one `Exhaustion`, and every
/// gate that does not reach `cover` returns through one of the two skips,
/// each of which increments its own counter. Nothing else stands between the
/// top of `ConfCtx::gate` and `cover` on a budget-zero run: the `pruned` latch
/// is never set (a zero budget reports nothing, so nothing prunes) and
/// `worker.is_none()` is false for a `verify_conformance` context. So the sum
/// is the whole call count, and it is sound even on programs where
/// [`gates_fired`] is not.
///
/// What it deliberately does **not** give is the count *per `Gate` variant*.
/// `ConfCtx` carries the two skip totals but not a breakdown, so a skipped
/// gate's variant is unrecoverable from outside. That would need a
/// per-variant counter in `ConfCtx::gate`, which is production code and is
/// recorded rather than added here.
fn gates_called<I>(implementation: I, visible: &[&str]) -> usize
where
    I: Fn() + Send + Sync + 'static,
{
    let out = verify_conformance(fifo(), implementation, || {}, names(visible), 0);
    assert!(
        out.reports.is_empty(),
        "a zero budget established nothing, so it must report nothing: {:?}",
        out.reports
    );
    out.exhaustions.len() + out.skipped_gates + out.inert_gates
}

/// Two `u64` senders into `main`, all three threads nameable.
fn two_workers() {
    let m = main_thread_id();
    let _w1 = named("w1", move || {
        crate::send_msg(m, 1u64);
        crate::send_msg(m, 2u64);
    });
    let _w2 = named("w2", move || {
        crate::send_msg(m, 3u64);
        crate::send_msg(m, 4u64);
    });
    let _: u64 = crate::recv_msg_block();
    let _: u64 = crate::recv_msg_block();
}

/// **`inert_gates` counts gates that really were suppressed**, and the
/// predicate really does select the *invisible* thread's fresh events.
///
/// Declaring a thread visible or not cannot change the implementation's
/// exploration — at a budget of zero nothing prunes, and the visible list
/// reaches nothing but the observation extractor — so the **total** number of
/// gate calls is the same whichever threads are declared. What changes is how
/// many of them F42 suppresses. Both halves are asserted:
///
/// 1. `gates_called` is invariant across four visible lists. A counter that
///    over-counted (incrementing without returning) or under-counted (skipping
///    without incrementing) would break the sum, because `exhaustions` is an
///    independent count of the gates that *did* reach `cover`.
/// 2. `inert_gates` is **zero** when every thread is declared visible, and
///    rises as threads are hidden. This is the predicate's claim — "the count
///    moves iff the actor was visible" — in its testable direction.
///
/// **Measured**, this tree, 2026-09-16, on `two_workers`:
///
/// | visible | exhaustions | skipped | inert | total |
/// |---|---|---|---|---|
/// | `main, w1, w2` | 13 | 1 | **0** | 14 |
/// | `main, w1` | 11 | 1 | 2 | 14 |
/// | `main` | 10 | 1 | 3 | 14 |
/// | `w1` | 9 | 1 | 4 | 14 |
///
/// **Mutation, MEASURED** (one direction of two). Incrementing `inert_gates`
/// *without* taking the early return — the audit form the developer used to
/// attack F42 — makes this program's totals read `main, w1, w2` = 14 but
/// `main` = **17**, and the invariance assertion fails. The opposite
/// direction, returning without incrementing, is the symmetric argument and
/// was **not run**: `ctx.rs` was frozen at the lead's request while the
/// `last_visible_obs` fix was applied, so no further mutation of it was made.
///
/// **What it does not establish**: that the *skipped gate's answer* would have
/// been the same as the gate before it. That is F42's actual soundness claim,
/// it is not a property any counter can see, and the developer's report for
/// `P3-skips-dev` records that it is **false** as shipped — the stale
/// `last_visible_obs` defect. This test is about the counter, not the skip.
#[test]
fn the_inert_counter_conserves_the_gate_call_count() {
    let all = gates_called(two_workers, &["main", "w1", "w2"]);
    for narrower in [
        &["main", "w1"][..],
        &["main"][..],
        &["w1"][..],
    ] {
        assert_eq!(
            gates_called(two_workers, narrower),
            all,
            "declaring {narrower:?} visible instead of every thread changed the \
             total gate call count. Visibility cannot change the implementation's \
             exploration at a zero budget, so the two skip counters and \
             `exhaustions` are not accounting for the same set of gate calls."
        );
    }

    let out = verify_conformance(
        fifo(),
        two_workers,
        || {},
        names(&["main", "w1", "w2"]),
        0,
    );
    assert_eq!(
        out.inert_gates, 0,
        "every thread is declared visible, so every fresh event contributes an \
         observation and no gate can be inert — but {} were skipped as inert. \
         F42's predicate is selecting something other than invisibility.",
        out.inert_gates
    );

    let narrow = verify_conformance(fifo(), two_workers, || {}, names(&["main"]), 0);
    assert!(
        narrow.inert_gates > 0,
        "hiding both workers made no gate inert, so this test is vacuous"
    );
}

/// A **visible** thread's fresh event is never inert, on every shape the
/// developer could construct that might have made one.
///
/// F42's predicate is "the visible observation count did not move", and it
/// stands in for "the fresh event was invisible". The substitution is wrong if
/// a visible thread's fresh send or receive can leave the count where it was.
/// Four shapes were tried, each with **every** thread declared visible so that
/// no fresh event *can* be invisible; a non-zero `inert_gates` on any of them
/// is a counterexample.
///
/// - plain sends and blocking receives (`two_workers`);
/// - a visible thread whose blocking receive never has a candidate, so the
///   engine installs a `RecvMsg` and **overwrites it with `Block(Value)`** —
///   the one path in the engine that removes an observation from a row;
/// - a visible thread taking a non-blocking receive that reads ⊥ in some
///   executions and a real value in others;
/// - two visible threads that both branch on `nondet()`, which is F49's own
///   shape and the one that drives the replay frontier hardest.
///
/// **Measured**: `inert_gates == 0` on all four. No counterexample was found,
/// which is weaker than a proof and is the honest statement of what was done.
/// The mechanism agrees: the overwrite path installs and removes the
/// `RecvMsg` inside one `visit_rfs` call, with no gate between the two, so the
/// decrement is never observed by a gate.
#[test]
fn no_visible_threads_fresh_event_is_inert() {
    fn a_visible_thread_blocks_forever() {
        let m = main_thread_id();
        let _v = named("v", move || {
            crate::send_msg(m, 1u64);
            let _: u64 = crate::recv_msg_block(); // nobody ever sends to v
        });
        let _u = named("u", move || {
            crate::send_msg(m, 2u64);
        });
        let _: u64 = crate::recv_msg_block();
        let _: u64 = crate::recv_msg_block();
    }
    fn a_visible_thread_reads_bottom() {
        let m = main_thread_id();
        let _v = named("v", move || {
            let _: Option<u64> = crate::recv_msg();
            crate::send_msg(m, 1u64);
        });
        let v2 = named("v2", move || {
            let _: Option<u64> = crate::recv_msg();
            crate::send_msg(m, 2u64);
        });
        crate::send_msg(v2, 9u64);
        let _: u64 = crate::recv_msg_block();
        let _: u64 = crate::recv_msg_block();
    }

    for (name, p, vis) in [
        ("two_workers", two_workers as fn(), &["main", "w1", "w2"][..]),
        (
            "blocks_forever",
            a_visible_thread_blocks_forever as fn(),
            &["main", "v", "u"][..],
        ),
        (
            "reads_bottom",
            a_visible_thread_reads_bottom as fn(),
            &["main", "v", "v2"][..],
        ),
        (
            "branching",
            two_branching_visibles as fn(),
            &["main", "p0", "p1"][..],
        ),
    ] {
        let out = verify_conformance(fifo(), p, || {}, names(vis), 0);
        assert_eq!(
            out.inert_gates, 0,
            "{name}: every thread is declared visible, so a fresh event on any of \
             them contributes an observation — yet {} gate(s) were skipped as \
             inert. A visible thread's fresh event left the observation count \
             where it was, which is the case F42's predicate does not cover.",
            out.inert_gates
        );
    }
}
