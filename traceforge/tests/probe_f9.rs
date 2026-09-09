//! PROBE ONLY — throwaway instrument for task P1-probes (branch `probe/internals`).
//! Not a fix, not a contribution. Reproduces the disputed litmus programs verbatim
//! and runs them with `.with_verbose(2)` so every explored graph is printed.
//! No assertions: this file records evidence, it does not judge counts.

use traceforge::thread;
use traceforge::*;
use SchedulePolicy::*;

/// The program of `tests/litmus.rs::s_r_s` (assertion at litmus.rs:230,
/// `assert_eq!(stats.execs, 2 * 2 + 2 * 2); // + 1);`), verbatim, under its
/// original `ConsType::MO`. Single run instead of the `TEST_RUNS` loop.
#[test]
fn probe_s_r_s_mo() {
    println!("=== PROBE probe_s_r_s_mo : litmus.rs::s_r_s program, ConsType::MO ===");
    let stats = traceforge::verify(
        Config::builder()
            .with_policy(Arbitrary)
            .with_cons_type(ConsType::MO)
            .with_verbose(2)
            .build(),
        || {
            let sh1 = thread::spawn(move || {
                let r = traceforge::recv_msg();
                if r.is_some() {
                    traceforge::send_msg(r.unwrap(), 1);
                }
            });
            let rh = thread::spawn(move || {
                let _: Option<i32> = traceforge::recv_msg();
            });
            let sh2 = thread::spawn(move || {
                let r = traceforge::recv_msg();
                if r.is_some() {
                    traceforge::send_msg(r.unwrap(), 2);
                }
            });

            traceforge::send_msg(sh1.thread().id(), rh.thread().id());
            traceforge::send_msg(sh2.thread().id(), rh.thread().id());
        },
    );
    println!(
        "=== RESULT probe_s_r_s_mo: execs={} block={} max_graph_events={} ===",
        stats.execs, stats.block, stats.max_graph_events
    );
}

/// The program of `tests/litmus_cd.rs::s_r_s` (assertion at litmus_cd.rs:148,
/// `assert_eq!(stats.execs, 8); //2 * 2 + 2 * 2 + 1`), verbatim, under its
/// original `ConsType::Causal`. Single run instead of the `TEST_RUNS` loop.
/// This is the same program text as `probe_s_r_s_mo`; only `ConsType` differs.
#[test]
fn probe_s_r_s_causal() {
    println!("=== PROBE probe_s_r_s_causal : litmus_cd.rs::s_r_s program, ConsType::Causal ===");
    let stats = traceforge::verify(
        Config::builder()
            .with_policy(Arbitrary)
            .with_cons_type(ConsType::Causal)
            .with_verbose(2)
            .build(),
        || {
            let sh1 = thread::spawn(move || {
                let r = traceforge::recv_msg();
                if r.is_some() {
                    traceforge::send_msg(r.unwrap(), 1);
                }
            });
            let rh = thread::spawn(move || {
                let _: Option<i32> = traceforge::recv_msg();
            });
            let sh2 = thread::spawn(move || {
                let r = traceforge::recv_msg();
                if r.is_some() {
                    traceforge::send_msg(r.unwrap(), 2);
                }
            });

            traceforge::send_msg(sh1.thread().id(), rh.thread().id());
            traceforge::send_msg(sh2.thread().id(), rh.thread().id());
        },
    );
    println!(
        "=== RESULT probe_s_r_s_causal: execs={} block={} max_graph_events={} ===",
        stats.execs, stats.block, stats.max_graph_events
    );
}

/// Extra, beyond the literal P1 spec: the re-enabled `litmus_cd.rs::r_ns_assm`
/// program under `ConsType::Causal`, without assertions, so that the *blocked*
/// count is observable (in the re-enabled test the `execs` assertion fires first
/// and hides it). Verbose is left at the default: verbose(2) on this program
/// prints thousands of graphs.
#[test]
fn probe_r_ns_assm_causal_counts_only() {
    println!("=== PROBE probe_r_ns_assm_causal_counts_only : litmus_cd.rs::r_ns_assm program, ConsType::Causal ===");
    let stats = traceforge::verify(
        Config::builder()
            .with_policy(Arbitrary)
            .with_cons_type(ConsType::Causal)
            .build(),
        || {
            let n = 7;

            let rh = thread::spawn(move || {
                let r: Option<i32> = traceforge::recv_msg();
                traceforge::assume!(r.is_some());
            });
            for i in 0..n {
                let sh = thread::spawn(move || {
                    let r = traceforge::recv_msg();
                    traceforge::assume!(r.is_some());
                    traceforge::send_msg(r.unwrap(), i);
                });
                traceforge::send_msg(sh.thread().id(), rh.thread().id());
            }
        },
    );
    println!(
        "=== RESULT probe_r_ns_assm_causal_counts_only: execs={} block={} max_graph_events={} ===",
        stats.execs, stats.block, stats.max_graph_events
    );
}
