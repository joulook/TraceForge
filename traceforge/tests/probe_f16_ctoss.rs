//! Throwaway probe instrument for flaw candidate **F16(b)** (`CToss`
//! cross-lineage canonicality: `is_maximal` compares against the per-instance
//! `maximal` draw, which re-execution after a cut re-draws from the evolving
//! seeded RNG stream). Task P1-probes-3, probe P8.
//!
//! This file asserts nothing and fixes nothing. It records the number of
//! executions and the full graph of every execution, so that the per-execution
//! graph dumps can be byte-compared for duplicates (same toss result + same rf).
//!
//! Base shape: `R` (spawned first) tosses and receives; `S1` and `S2` each send
//! `R` a distinct value.
//!
//! Variants:
//!
//! * `probe_f16_ctoss` — the task's shape: one `nondet()` *before* a blocking
//!   receive;
//! * `probe_f16_ctoss_two_seq` / `..._two_nested` — the harder variant under
//!   both readings of "two nested `nondet()`s" (back to back, and one inside
//!   each branch of the first), since the task's wording admits either;
//! * `..._after_recv`, `..._two_after_recv` — the toss moved after the receive;
//! * `..._nb`, `..._two_nb`, `..._two_seq_nb`, `..._two_recvs_nb` — with a
//!   **non-blocking** receive, which is the only shape here that produces a
//!   backward revisit, i.e. that puts the `CToss` in a deleted set and exposes
//!   it to `is_maximal_extension`. These are the discriminating cases.
//!
//! Run one at a time with:
//! `cargo test -p traceforge --test probe_f16_ctoss -- --exact <name> --nocapture --test-threads=1`

use traceforge::thread;
use traceforge::Config;

/// P8 main variant: a single `CToss` in front of a doubly-revisited receive.
#[test]
fn probe_f16_ctoss() {
    println!("=== PROBE probe_f16_ctoss : one nondet() before a doubly-revisited recv ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _t = traceforge::nondet();
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P8, correction: the toss placed **after** the revisited receive, so that it
/// lands in the *deleted set* where `is_maximal` is consulted (and where a cut
/// destroys the `CToss` instance and its `maximal` field, forcing a re-draw).
/// A toss program-order before the receive stays in the revisit view and is
/// never gated.
#[test]
fn probe_f16_ctoss_after_recv() {
    println!("=== PROBE probe_f16_ctoss_after_recv : recv then nondet() in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
                let _t = traceforge::nondet();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_after_recv execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P8 correction, harder: two tosses after the revisited receive.
#[test]
fn probe_f16_ctoss_two_after_recv() {
    println!("=== PROBE probe_f16_ctoss_two_after_recv : recv then two nondet()s in R ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
                let _t = if traceforge::nondet() {
                    traceforge::nondet()
                } else {
                    traceforge::nondet()
                };
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_two_after_recv execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P8 harder variant, sequential reading: two `CToss` events back to back.
#[test]
fn probe_f16_ctoss_two_seq() {
    println!("=== PROBE probe_f16_ctoss_two_seq : two sequential nondet()s ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _t1 = traceforge::nondet();
                let _t2 = traceforge::nondet();
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_two_seq execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P8 harder variant, nested reading: the second `CToss` is inside a branch of
/// the first, so the two program points are control-dependent.
#[test]
fn probe_f16_ctoss_two_nested() {
    println!("=== PROBE probe_f16_ctoss_two_nested : nondet() inside each branch ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _t = if traceforge::nondet() {
                    traceforge::nondet()
                } else {
                    traceforge::nondet()
                };
                let _m: i32 = traceforge::recv_msg_block();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_two_nested execs={} block={} ===",
        stats.execs, stats.block
    );
}

// ---------------------------------------------------------------------------
// P8, correction: as in P7, only a *non-blocking* receive is ever the target of
// a backward revisit in these programs, so only this shape puts the `CToss` in
// the deleted set that `is_maximal_extension` scans.
// ---------------------------------------------------------------------------

/// P8 discriminating case: one `CToss` in the deleted set of a real backward
/// revisit, with two senders (so two revisits, two lineages).
#[test]
fn probe_f16_ctoss_nb() {
    println!("=== PROBE probe_f16_ctoss_nb : nonblocking recv then nondet() in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
                let _t = traceforge::nondet();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_nb execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P8 discriminating case, harder: two nested `CToss`es in the deleted set.
#[test]
fn probe_f16_ctoss_two_nb() {
    println!("=== PROBE probe_f16_ctoss_two_nb : nonblocking recv then two nested nondet()s ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
                let _t = if traceforge::nondet() {
                    traceforge::nondet()
                } else {
                    traceforge::nondet()
                };
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_two_nb execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P8 discriminating case, sequential reading of the harder variant.
#[test]
fn probe_f16_ctoss_two_seq_nb() {
    println!("=== PROBE probe_f16_ctoss_two_seq_nb : nonblocking recv then two sequential nondet()s ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _m: Option<i32> = traceforge::recv_msg();
                let _t1 = traceforge::nondet();
                let _t2 = traceforge::nondet();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_two_seq_nb execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// P8 cross-lineage stress: a `CToss` *between* two non-blocking receives, so
/// that several distinct revisit lineages exist and cuts delete and re-draw the
/// toss repeatedly. If two lineages could enqueue the same restricted graph
/// through differently-drawn canonical branches, this is where it should show.
#[test]
fn probe_f16_ctoss_two_recvs_nb() {
    println!("=== PROBE probe_f16_ctoss_two_recvs_nb : recv, nondet(), recv in R, S1/S2 send ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF16).with_verbose(2).build(),
        || {
            let r = thread::spawn(|| {
                let _a: Option<i32> = traceforge::recv_msg();
                let _t = traceforge::nondet();
                let _b: Option<i32> = traceforge::recv_msg();
            });
            let rid = r.thread().id();
            let _s1 = thread::spawn(move || traceforge::send_msg(rid, 1i32));
            let _s2 = thread::spawn(move || traceforge::send_msg(rid, 2i32));
        },
    );
    println!(
        "=== RESULT probe_f16_ctoss_two_recvs_nb execs={} block={} ===",
        stats.execs, stats.block
    );
}
