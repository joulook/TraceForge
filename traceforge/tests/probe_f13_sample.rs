//! Throwaway probe instrument for flaw candidate **F13** (`handle_sample`
//! off-by-one and duplicate execution). Task P1-probes-2, probe P5.
//!
//! This file asserts nothing and fixes nothing. It records, for a single-thread
//! model that calls `traceforge::sample(<uniform over a large domain>, N)` once,
//! the number of executions TraceForge runs and the sampled value seen by *each*
//! execution, for `N ∈ {1, 2, 3, 4}`.
//!
//! `traceforge::sample` is `#[doc(hidden)]` but publicly reachable at the crate
//! root (`src/lib.rs`), which is the import path used here — the same one
//! `tests/estimation.rs` uses.
//!
//! Run with:
//! `cargo test -p traceforge --test probe_f13_sample -- --nocapture --test-threads=1`

use rand::distr::Uniform;
use std::sync::Mutex;
use traceforge::Config;

/// Values observed by the model closure, one push per execution, in the order
/// the executions were run. A plain `static` is enough: `verify` runs the model
/// on the same OS process/thread the test does.
static SEEN: Mutex<Vec<u32>> = Mutex::new(Vec::new());

/// Records `execs`, `block` and the per-execution `SAMPLE` values for
/// `max_samples ∈ {1, 2, 3, 4}`.
///
/// The domain is `[0, 1_000_000)` so that two independent draws coinciding by
/// chance is unlikely; any repeated value in the recorded sequence is therefore
/// evidence of a replayed value rather than of a collision.
///
/// `.with_verbose(2)` makes TraceForge print the full execution graph of every
/// execution, so the `SAMPLE` label values are also visible verbatim in the
/// graph dumps, independently of this file's own bookkeeping.
#[test]
fn probe_f13_sample_off_by_one() {
    for n in 1usize..=4 {
        SEEN.lock().unwrap().clear();
        println!("=== PROBE probe_f13_sample_off_by_one : max_samples = {n} ===");

        let stats = traceforge::verify(
            Config::builder().with_seed(0xF13).with_verbose(2).build(),
            move || {
                let s: u32 = traceforge::sample(Uniform::new(0u32, 1_000_000u32).unwrap(), n);
                SEEN.lock().unwrap().push(s);
            },
        );

        let seen = SEEN.lock().unwrap().clone();
        let mut distinct = seen.clone();
        distinct.sort_unstable();
        distinct.dedup();

        println!(
            "=== RESULT max_samples={} execs={} block={} values={:?} distinct={} ===",
            n,
            stats.execs,
            stats.block,
            seen,
            distinct.len()
        );
    }
}
