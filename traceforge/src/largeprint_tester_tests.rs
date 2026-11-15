//! `ENG-LARGEPRINT`'s tests, the tester's (`criteria/ENG-LARGEPRINT.md` EL-0.2, EL-1.1; the
//! derivation `log/dev/ENG-LARGEPRINT.derived.md` §1).
//!
//! **The crossing ends the run, with either flag value.** A thread that never ends adds labels
//! until something halts it. `elt1` runs an unbounded sender at threshold 16, with and without
//! `--dump-large-graph`, and checks that the run ends within a deadline and reports the
//! threshold (thread `main`, limit 16, no execution, no block). Its failing direction is the
//! loss of the threshold's detection or recording (GATE-CROSSING): a hang. Gating only the
//! explicit `stop()` by the flag is equivalent on this base: `add_to_graph` records the
//! threshold before `stop()`, and `Must::is_stopped` reads the recorded threshold, so the run
//! stops either way.
use crate::*;
use std::sync::mpsc;
use std::time::Duration;

#[test]
fn elt1_an_unbounded_thread_stops_at_the_crossing_with_and_without_the_flag() {
    for flag in [false, true] {
        let (done, wait) = mpsc::channel();
        std::thread::spawn(move || {
            let stats = verify(
                Config::builder()
                    .with_thread_threshold(16)
                    .with_dump_large_graph(flag)
                    .build(),
                || {
                    let (tx, _rx) = channel::Builder::<i32>::new().build();
                    let mut i = 0;
                    loop {
                        tx.send_msg(i);
                        i += 1;
                    }
                },
            );
            let _ = done.send(stats);
        });
        let stats = wait
            .recv_timeout(Duration::from_secs(60))
            .unwrap_or_else(|_| panic!("ENG-LARGEPRINT: flag {flag}: no end in 60 s"));
        let reason = stats.threshold.expect("ENG-LARGEPRINT: a threshold end");
        assert_eq!(
            (
                reason.thread.as_str(),
                reason.limit,
                stats.execs,
                stats.block
            ),
            ("main", 16, 0, 0),
            "ENG-LARGEPRINT: flag {flag}"
        );
    }
}
