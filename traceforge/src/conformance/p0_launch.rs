//! `SVERIFY-P` P0 (the owner's order of 2026-10-26): a launcher for one
//! measurement row — Must alone on one side of one fixture, sequential or in
//! the partitioned mode. Not a test: `p0_row` is `#[ignore]`d and a no-op
//! without `P0_KEY`, like `eval::eval_row`. Temporary: it goes when I4's
//! baseline row lands, or on the owner's word.
//!
//! Environment: `P0_KEY` the fixture's name; `P0_SIDE` `impl` or `spec`;
//! `P0_THREADS` `0` for the sequential `verify`, else the partitioned pool
//! size; `P0_SPLIT` `iterations_until_split` (default 100); `P0_WARMUP`
//! (default 100). The configuration is the `Explore` arm's (`P5-XBASE` F1):
//! the fixture's own `Config` with `keep_going_after_error`. One `p0:` line
//! on stdout carries the counts, the wall and the process's `VmHWM`.

use std::time::Instant;

/// `VmHWM` from `/proc/self/status`, in KiB; 0 if unreadable.
fn vm_hwm_kb() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|n| n.parse().ok())
        })
        .unwrap_or(0)
}

fn env_usize(name: &str, default: usize) -> usize {
    match std::env::var(name) {
        Ok(s) => s
            .parse()
            .unwrap_or_else(|_| panic!("conformance: p0 {name}={s} is not a number")),
        Err(_) => default,
    }
}

#[test]
#[ignore]
fn p0_row() {
    let Ok(key) = std::env::var("P0_KEY") else {
        return;
    };
    let side = std::env::var("P0_SIDE").expect("conformance: p0 P0_SIDE unset");
    let threads = env_usize("P0_THREADS", 0);
    let split = env_usize("P0_SPLIT", 100);
    let warmup = env_usize("P0_WARMUP", 100);
    let Ok(fixture) = super::eval::fixture_by_name(&key) else {
        panic!("conformance: p0 P0_KEY={key} names no fixture");
    };
    let prog = match side.as_str() {
        "impl" => fixture.implementation.clone(),
        "spec" => fixture.specification.clone(),
        other => panic!("conformance: p0 P0_SIDE is impl or spec, not {other}"),
    };
    let mut cfg = fixture.config.clone();
    cfg.keep_going_after_error = true;
    if threads > 0 {
        cfg.partitioned_parallelization = true;
        cfg.partitioned_num_threads = Some(threads);
        cfg.iterations_until_split = split;
        cfg.warmup = warmup;
    }
    // The driver's run thread (`grid::stack_mib_for`): 32 MiB, 64 for a
    // big-stack pair. The partitioned workers are rayon's, sized by
    // `RUST_MIN_STACK`, which the runner sets.
    let stack_mib = if fixture.big_stack { 64 } else { 32 };
    let start = Instant::now();
    let handle = std::thread::Builder::new()
        .name("p0".to_owned())
        .stack_size(stack_mib * 1024 * 1024)
        .spawn(move || crate::verify(cfg, move || prog()))
        .expect("conformance: p0 could not spawn the run thread");
    let stats = handle
        .join()
        .expect("conformance: p0 the run thread panicked");
    let wall_ms = start.elapsed().as_millis();
    // The row the runner parses, on stdout, through `writeln!` on the locked
    // handle rather than `println!`: the s5 emission scan names the print
    // macros and this test-only file is not on its list (owner's ruling on
    // `ISSUE-sverify-p-items.md` §1, option (b): no red test in the committed
    // tree). The line itself is unchanged.
    use std::io::Write as _;
    writeln!(
        std::io::stdout().lock(),
        "p0: key={key} side={side} threads={threads} split={split} warmup={warmup} \
         execs={} block={} max_graph_events={} wall_ms={wall_ms} vm_hwm_kb={}",
        stats.execs,
        stats.block,
        stats.max_graph_events,
        vm_hwm_kb()
    )
    .expect("conformance: p0 could not write the row");
}
