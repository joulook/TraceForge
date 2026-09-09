//! Throwaway probe instrument for flaw candidate **F19** (`is_maximal` has no
//! `Sample` arm, so every sample branch passes the revisit condition). Task
//! P1-probes-3, probe P7.
//!
//! This file asserts nothing and fixes nothing. It records, for models in which
//! a *branching* event (`sample` / `Choice` / nothing) sits next to a receive
//! that a racing send may revisit, the number of executions TraceForge runs and
//! the full graph of every execution, so that the per-execution graph dumps can
//! be byte-compared for duplicates.
//!
//! The cases come in four groups, because the first three shapes turned out not
//! to generate a backward revisit at all (each group's doc comment says why):
//!
//! 1. `*_dup` / `*_control_*` — the task's shape: branching event, then a
//!    *blocking* receive, with the send in `main`;
//! 2. `*_racing` — the send moved into a thread spawned after `R`;
//! 3. `*_two_senders`, `*_after_recv` — two senders, branching event before
//!    resp. after the blocking receive;
//! 4. `*_nb` — a **non-blocking** receive, which is the only shape here in
//!    which a backward revisit is generated and `is_maximal` is consulted on
//!    the deleted set. These are the discriminating cases.
//!
//! Each group runs `Sample`, `Choice` (`(0..3).nondet()`, same branching factor,
//! canonical branch `range.end()` *is* gated) and a no-branching baseline.
//!
//! `traceforge::sample` is `#[doc(hidden)]` but publicly reachable at the crate
//! root, which is the import path used here.
//!
//! Run one at a time with:
//! `cargo test -p traceforge --test probe_f19_sample_dup -- --exact <name> --nocapture --test-threads=1`

use rand::distr::Uniform;
use traceforge::thread;
use traceforge::Config;

/// P7 main case: an unguarded `Sample` in front of the revisited receive.
///
/// The domain is `[0, 1_000_000)` so that two independent draws coinciding by
/// chance is unlikely; equal `SAMPLE` values in two graphs are therefore
/// evidence of a replayed value, not of a collision.
#[test]
fn probe_f19_sample_dup() {
    println!("=== PROBE probe_f19_sample_dup : sample(d, 3) before a revisited recv ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _s: u32 = traceforge::sample(Uniform::new(0u32, 1_000_000u32).unwrap(), 3);
                let _m: i32 = traceforge::recv_msg_block();
            });
            traceforge::send_msg(r.thread().id(), 1i32);
        },
    );
    println!(
        "=== RESULT probe_f19_sample_dup execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 control: the same program with the sample removed.
#[test]
fn probe_f19_control_nosample() {
    println!("=== PROBE probe_f19_control_nosample : no branching event ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
            });
            traceforge::send_msg(r.thread().id(), 1i32);
        },
    );
    println!(
        "=== RESULT probe_f19_control_nosample execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 racing variant: the send is moved into a thread `S` spawned *after* `R`.
///
/// The task's shape (send in `main`) turns out not to race at all: main's own
/// events are added first under this scheduler, so `R`'s receive already sees
/// the send and no backward revisit happens. Moving the send into a later
/// thread is what puts the receive in the graph before the send, which is the
/// situation the F19 design argument is about.
#[test]
fn probe_f19_sample_dup_racing() {
    println!("=== PROBE probe_f19_sample_dup_racing : sample(d, 3) + recv in R, send from S ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _s: u32 = traceforge::sample(Uniform::new(0u32, 1_000_000u32).unwrap(), 3);
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s = thread::spawn(move || traceforge::send_msg(rid, 1i32));
        },
    );
    println!(
        "=== RESULT probe_f19_sample_dup_racing execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 racing control: the racing shape with the sample removed.
#[test]
fn probe_f19_control_nosample_racing() {
    println!("=== PROBE probe_f19_control_nosample_racing : no branching event, send from S ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s = thread::spawn(move || traceforge::send_msg(rid, 1i32));
        },
    );
    println!(
        "=== RESULT probe_f19_control_nosample_racing execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 racing control: `Choice` in the racing shape.
#[test]
fn probe_f19_control_choice_racing() {
    use traceforge::Nondet;
    println!("=== PROBE probe_f19_control_choice_racing : (0..3).nondet() + recv in R, send from S ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _c: usize = (0usize..3).nondet();
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s = thread::spawn(move || traceforge::send_msg(rid, 1i32));
        },
    );
    println!(
        "=== RESULT probe_f19_control_choice_racing execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7, second correction: **two** senders, so that a backward revisit actually
/// happens.
///
/// With a single send, the blocking receive is only ever *added after* the send
/// (it blocks, the sender runs, the receive resumes and reads it), so no
/// backward revisit is generated at all — see the two `*_racing` cases above.
/// With two sends, the receive is added reading the first send and the second
/// send backward-revisits it; the `Sample` event then sits in the deleted set,
/// which is the F19 situation.
#[test]
fn probe_f19_sample_dup_two_senders() {
    println!("=== PROBE probe_f19_sample_dup_two_senders : sample(d,3) + recv in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _s: u32 = traceforge::sample(Uniform::new(0u32, 1_000_000u32).unwrap(), 3);
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_sample_dup_two_senders execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 two-sender control: no branching event (the pure rf baseline).
#[test]
fn probe_f19_control_nosample_two_senders() {
    println!("=== PROBE probe_f19_control_nosample_two_senders : recv in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_control_nosample_two_senders execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 two-sender control: `Choice` (canonical branch checked by `is_maximal`)
/// in the same shape, i.e. the comparison case for the `Sample` run.
#[test]
fn probe_f19_control_choice_two_senders() {
    use traceforge::Nondet;
    println!(
        "=== PROBE probe_f19_control_choice_two_senders : (0..3).nondet() + recv in R, S1/S2 send ==="
    );
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _c: usize = (0usize..3).nondet();
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_control_choice_two_senders execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7, third correction: the branching event is placed **after** the revisited
/// receive, which is the only position that puts it in the *deleted set*.
///
/// `is_maximal` is consulted on the events a backward revisit deletes. A
/// `Sample` that is program-order *before* the receive stays in the revisit
/// view and is never gated, so the shapes above cannot exercise F19 whatever
/// the scheduler does. Here `R` receives first and samples afterwards, so
/// `S2`'s send deletes the `SAMPLE` event and the gate applies.
#[test]
fn probe_f19_sample_after_recv() {
    println!("=== PROBE probe_f19_sample_after_recv : recv then sample(d,3) in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
                let _s: u32 = traceforge::sample(Uniform::new(0u32, 1_000_000u32).unwrap(), 3);
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_sample_after_recv execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 comparison for `probe_f19_sample_after_recv`: identical shape and
/// branching factor with `Choice`, whose canonical branch *is* gated.
#[test]
fn probe_f19_choice_after_recv() {
    use traceforge::Nondet;
    println!("=== PROBE probe_f19_choice_after_recv : recv then (0..3).nondet() in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
                let _c: usize = (0usize..3).nondet();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_choice_after_recv execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 baseline for the two cases above: the same shape with no branching event
/// after the receive.
#[test]
fn probe_f19_nothing_after_recv() {
    println!("=== PROBE probe_f19_nothing_after_recv : recv only in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_nothing_after_recv execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 control: `Choice` in place of `Sample` — same branching factor (3), but
/// `is_maximal` fixes the canonical branch at `range.end()`.
#[test]
fn probe_f19_control_choice() {
    use traceforge::Nondet;
    println!("=== PROBE probe_f19_control_choice : (0..3).nondet() before a revisited recv ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _c: usize = (0usize..3).nondet();
                let _m: i32 = traceforge::recv_msg_block();
            });
            traceforge::send_msg(r.thread().id(), 1i32);
        },
    );
    println!(
        "=== RESULT probe_f19_control_choice execs={} block={} ===",
        stats.execs, stats.block
    );
}

// ---------------------------------------------------------------------------
// P7, fourth correction: a *non-blocking* receive, which is the only shape in
// which a backward revisit is generated at all.
//
// `is_maximal_extension` (must.rs) is the gate F19 is about: for a candidate
// backward revisit `(r, s)` it scans every label with `stamp > stamp(r)` that
// is outside `porf(s)` — the deleted set — and requires `is_maximal` of each.
// A blocking receive is only ever *added* once some matching send is already in
// the graph, so it is never the `r` of a backward revisit in these programs
// (the alternative sends are reached by *forward* revisits instead, which do
// not consult `is_maximal`). A non-blocking receive is added immediately,
// reading ⊥, and the later sends backward-revisit it — with the branching event
// that follows it in the deleted set.
// ---------------------------------------------------------------------------

/// P7 discriminating case: `Sample` in the deleted set of a real backward
/// revisit.
#[test]
fn probe_f19_sample_nb() {
    println!("=== PROBE probe_f19_sample_nb : nonblocking recv then sample(d,3) in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
                let _s: u32 = traceforge::sample(Uniform::new(0u32, 1_000_000u32).unwrap(), 3);
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_sample_nb execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 discriminating comparison: the same shape with `Choice`, whose canonical
/// branch (`range.end()`) *is* checked by `is_maximal`.
#[test]
fn probe_f19_choice_nb() {
    use traceforge::Nondet;
    println!("=== PROBE probe_f19_choice_nb : nonblocking recv then (0..3).nondet() in R ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
                let _c: usize = (0usize..3).nondet();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_choice_nb execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 discriminating baseline: no branching event after the non-blocking
/// receive (the pure rf count for this shape).
#[test]
fn probe_f19_nothing_nb() {
    println!("=== PROBE probe_f19_nothing_nb : nonblocking recv only in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f19_nothing_nb execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 with a single sender, non-blocking: the minimal backward-revisit shape
/// the task's program description was aiming at.
#[test]
fn probe_f19_sample_nb_one_sender() {
    println!("=== PROBE probe_f19_sample_nb_one_sender : nonblocking recv + sample, one send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
                let _s: u32 = traceforge::sample(Uniform::new(0u32, 1_000_000u32).unwrap(), 3);
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
        },
    );
    println!(
        "=== RESULT probe_f19_sample_nb_one_sender execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P7 single-sender comparison with `Choice`.
#[test]
fn probe_f19_choice_nb_one_sender() {
    use traceforge::Nondet;
    println!("=== PROBE probe_f19_choice_nb_one_sender : nonblocking recv + choice, one send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF19).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
                let _c: usize = (0usize..3).nondet();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
        },
    );
    println!(
        "=== RESULT probe_f19_choice_nb_one_sender execs={} block={} ===",
        stats.execs, stats.block
    );
}
