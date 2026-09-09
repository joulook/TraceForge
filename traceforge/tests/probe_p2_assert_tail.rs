//! Throwaway probe instrument for task **P2-design-check**, items 4 and 7.
//!
//! This file asserts nothing and fixes nothing. It prints the graph of every
//! execution (`.with_verbose(2)`) so that the *last label of each thread* can be
//! read off directly.
//!
//! Question being probed: design `conf-plan.md` §6.3 claims that under
//! `keep_going_after_error`, "an Assert-blocked thread never reaches its `End`
//! label (the scheduler excludes Block-terminated threads)", so per-thread
//! status extraction can read the last graph label and get `Block(Assert)` for
//! an errored thread.
//!
//! Reading the source suggests otherwise: `traceforge::assert` (lib.rs:1732)
//! installs `Block(BlockType::Assert)` but — unlike `assume` (lib.rs:1723) —
//! does **not** call `switch()` afterwards, so the failing thread keeps running
//! its Rust code. `thread.rs:251` installs the `End` label with no `switch()`
//! either. So a thread body that ends right after a failed `assert` should
//! append `End` after `Block(Assert)`.
//!
//! Variants distinguish "nothing after the assert" from "an operation that
//! yields first".
//!
//! Run one at a time with:
//! `cargo test -p traceforge --test probe_p2_assert_tail -- --exact <name> --nocapture --test-threads=1`

use traceforge::thread;
use traceforge::Config;

fn cfg() -> traceforge::Config {
    Config::builder()
        .with_keep_going_after_error(true)
        .with_verbose(2)
        .build()
}

/// A spawned thread whose body ENDS with a failing `assert`.
/// Design §6.3 predicts last label = `Block(Assert)`.
#[test]
fn probe_p2_assert_then_thread_end() {
    println!("=== PROBE probe_p2_assert_then_thread_end : spawned thread body ends with assert(false) ===");
    let stats = traceforge::verify(cfg(), || {
        let h = thread::spawn(|| {
            traceforge::assert(false);
        });
        let _ = h.thread().id();
    });
    println!(
        "=== RESULT probe_p2_assert_then_thread_end execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// The MAIN thread's body ends with a failing `assert`.
#[test]
fn probe_p2_assert_then_main_end() {
    println!("=== PROBE probe_p2_assert_then_main_end : main body ends with assert(false) ===");
    let stats = traceforge::verify(cfg(), || {
        traceforge::assert(false);
    });
    println!(
        "=== RESULT probe_p2_assert_then_main_end execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// A failing `assert` followed by a SEND (which calls `switch()` before
/// `next_pos()`, lib.rs:1046), so the thread should never be rescheduled and
/// the send should never enter the graph.
#[test]
fn probe_p2_assert_then_send() {
    println!("=== PROBE probe_p2_assert_then_send : assert(false) then send_msg ===");
    let stats = traceforge::verify(cfg(), || {
        let main_id = traceforge::thread::current().id();
        let h = thread::spawn(move || {
            traceforge::assert(false);
            traceforge::send_msg(main_id, 1i32);
        });
        let _ = h.thread().id();
        let _v: Option<i32> = traceforge::recv_msg();
    });
    println!(
        "=== RESULT probe_p2_assert_then_send execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// A failing `assert` followed by a blocking RECEIVE that can never be
/// satisfied (`recv_msg_block` calls `switch()` first, lib.rs:1229).
#[test]
fn probe_p2_assert_then_blocking_recv() {
    println!("=== PROBE probe_p2_assert_then_blocking_recv : assert(false) then recv_msg_block ===");
    let stats = traceforge::verify(cfg(), || {
        let h = thread::spawn(|| {
            traceforge::assert(false);
            let _m: i32 = traceforge::recv_msg_block();
        });
        let _ = h.thread().id();
    });
    println!(
        "=== RESULT probe_p2_assert_then_blocking_recv execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// Control (item 4, Ex.-blocking shape): a blocking receive with no possible
/// send. Design §6.3 predicts last label = `Block(Value(..))`.
#[test]
fn probe_p2_never_satisfiable_recv() {
    println!("=== PROBE probe_p2_never_satisfiable_recv : blocking recv with no sender ===");
    let stats = traceforge::verify(cfg(), || {
        let h = thread::spawn(|| {
            let _m: i32 = traceforge::recv_msg_block();
        });
        let _ = h.thread().id();
    });
    println!(
        "=== RESULT probe_p2_never_satisfiable_recv execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// Control (item 5): does a `thread::Builder::name` reach the graph's `TCreate`
/// label and therefore the printed graph?
#[test]
fn probe_p2_thread_name_in_graph() {
    println!("=== PROBE probe_p2_thread_name_in_graph : named thread via Builder ===");
    let stats = traceforge::verify(cfg(), || {
        let h = thread::Builder::new()
            .name("visible-alice".to_string())
            .spawn(|| {
                let _m: i32 = traceforge::recv_msg_block();
            })
            .unwrap();
        let id = h.thread().id();
        traceforge::send_msg(id, 7i32);
    });
    println!(
        "=== RESULT probe_p2_thread_name_in_graph execs={} block={} ===",
        stats.execs, stats.block
    );
}
