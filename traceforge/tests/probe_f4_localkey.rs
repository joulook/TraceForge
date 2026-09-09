//! PROBE ONLY — throwaway instrument for task P1-probes (branch `probe/internals`).
//! Not a fix. Probes whether `traceforge::thread::LocalKey` is dead code (F4).

use std::marker::PhantomData;
use traceforge::thread::LocalKey;
use traceforge::*;

/// A `LocalKey` must be constructed by explicit struct literal: TraceForge exports
/// no `thread_local!` macro of its own, and the fields are `pub` (though
/// `#[doc(hidden)]`) precisely so that this is possible.
static COUNTER: LocalKey<u32> = LocalKey {
    init: || 42u32,
    _p: PhantomData,
};

/// `try_with` should hand back the initialised value; record what it actually does.
#[test]
fn probe_localkey_try_with() {
    println!("=== PROBE probe_localkey_try_with ===");
    let stats = traceforge::verify(Config::builder().build(), || {
        let r: Result<u32, _> = COUNTER.try_with(|v| *v);
        println!("try_with returned: {:?}", r);
    });
    println!(
        "=== RESULT probe_localkey_try_with: execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// `with` should hand back the initialised value 42; record what it actually does.
/// Expected to panic if `LocalKey` is dead; the panic text is the evidence.
#[test]
fn probe_localkey_with() {
    println!("=== PROBE probe_localkey_with ===");
    let stats = traceforge::verify(Config::builder().build(), || {
        let v: u32 = COUNTER.with(|v| *v);
        println!("with returned: {:?}", v);
    });
    println!(
        "=== RESULT probe_localkey_with: execs={} block={} ===",
        stats.execs, stats.block
    );
}
