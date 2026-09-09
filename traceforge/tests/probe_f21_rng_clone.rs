//! Throwaway probe instrument for flaw candidate **F21** (`handle_sample` draws
//! from a *clone* of the RNG and never advances it, so two samples reached at
//! the same RNG state see the same value sequence). Task P1-probes-3, probe P9.
//!
//! This file asserts nothing and fixes nothing. It records both `SAMPLE` values
//! of a single thread that calls `sample(d, 1)` twice back to back, over a
//! domain of 10^6 so that an accidental collision is unlikely.
//!
//! Run with:
//! `cargo test -p traceforge --test probe_f21_rng_clone -- --nocapture --test-threads=1`

use rand::distr::Uniform;
use std::sync::Mutex;
use traceforge::Config;

/// Values observed by the model closure, in call order, one pair per execution.
static SEEN: Mutex<Vec<u32>> = Mutex::new(Vec::new());

/// Two back-to-back `sample(d, 1)` calls in one thread; `max_samples == 1` means
/// no forward revisit is queued, so the model is expected to run exactly once.
#[test]
fn probe_f21_rng_clone() {
    SEEN.lock().unwrap().clear();
    println!("=== PROBE probe_f21_rng_clone : sample(d,1); sample(d,1) ===");
    let stats = traceforge::verify(
        Config::builder().with_seed(0xF21).with_verbose(2).build(),
        || {
            let d = Uniform::new(0u32, 1_000_000u32).unwrap();
            let a: u32 = traceforge::sample(d, 1);
            let b: u32 = traceforge::sample(d, 1);
            let mut seen = SEEN.lock().unwrap();
            seen.push(a);
            seen.push(b);
        },
    );
    let seen = SEEN.lock().unwrap().clone();
    println!(
        "=== RESULT probe_f21_rng_clone execs={} block={} values={:?} ===",
        stats.execs, stats.block, seen
    );
}
