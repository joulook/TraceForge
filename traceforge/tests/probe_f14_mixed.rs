//! Throwaway probe instrument for flaw candidate **F14** (`CausalOrder`
//! happens-before excludes `TotalOrder` rf edges). Task P1-probes-2, probe P6.
//!
//! This file asserts nothing and fixes nothing. It records the set of final
//! execution graphs of the smallest program in which two `CausalOrder` sends to
//! one receiver are causally related **only** through a rf edge of a second
//! channel:
//!
//! ```text
//!   data channel  d : CausalOrder
//!   relay channel t : <varied — TotalOrder in the probe, CausalOrder in the control>
//!
//!   thread A (main) : d.send(1)          "m1"
//!                     t.send(0)          "token"
//!   thread B        : t.recv_block()
//!                     d.send(2)          "m2"
//!   thread C        : d.recv_block()     one blocking cd-recv
//! ```
//!
//! `m1` reaches `m2` only along `po(A) ; rf(token) ; po(B)`. The probe varies
//! the relay channel's communication model and records which of `m1`/`m2`
//! thread C reads, plus `execs`/`block`.
//!
//! Run with:
//! `cargo test -p traceforge --test probe_f14_mixed -- --nocapture --test-threads=1`

use traceforge::channel::Builder;
use traceforge::loc::CommunicationModel;
use traceforge::thread;
use traceforge::Config;

/// Runs the mixed-model program once under `verify`, with the relay channel
/// built at `relay_comm` and the data channel always at `CausalOrder`.
///
/// Prints a banner, then (via `.with_verbose(2)`) every final execution graph,
/// then a result line with `execs`/`block`. The `C received` lines let each
/// graph be matched to the value thread C read without decoding the graph dump.
fn probe(label: &str, relay_comm: CommunicationModel) {
    println!(
        "=== PROBE probe_f14_mixed / {label} : data=CausalOrder relay={:?} ===",
        relay_comm
    );

    let stats = traceforge::verify(Config::builder().with_verbose(2).build(), move || {
        // Data channel: always CausalOrder ("cd").
        let (dsend, drecv) = Builder::<i32>::new()
            .with_comm(CommunicationModel::CausalOrder)
            .build();
        // Relay channel: the variable under probe.
        let (tsend, trecv) = Builder::<i32>::new().with_comm(relay_comm).build();

        let dsend_b = dsend.clone();

        // Thread C: one blocking cd-recv.
        let _c = thread::spawn(move || {
            let v: i32 = drecv.recv_msg_block();
            println!("C received {v}");
        });

        // Thread B: relay-recv the token, then cd-send m2.
        let _b = thread::spawn(move || {
            let _token: i32 = trecv.recv_msg_block();
            dsend_b.send_msg(2);
        });

        // Thread A is main: cd-send m1, then relay-send the token.
        dsend.send_msg(1);
        tsend.send_msg(0);
    });

    println!(
        "=== RESULT {label}: execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// The F14 case: the causal link between `m1` and `m2` runs through a
/// `TotalOrder` (mailbox) rf edge, which `cons.rs::calc_views` excludes from
/// `posw` — and `posw` is what becomes `sb` for `CausalOrder` sends.
#[test]
fn probe_f14_relay_total_order() {
    probe("relay=TotalOrder", CommunicationModel::TotalOrder);
}

/// The control: the identical program with the relay hop at `CausalOrder`, so
/// the rf edge *is* counted in `posw`.
#[test]
fn probe_f14_relay_causal_order_control() {
    probe("relay=CausalOrder", CommunicationModel::CausalOrder);
}

/// Second control. `calc_views` excludes the rf edge from `posw` for
/// `TotalOrder` only; `LocalOrder` falls in the catch-all `_` arm. If the
/// two-read result above is caused by that arm and not by some unrelated
/// difference between models, this must behave like the `CausalOrder` control.
#[test]
fn probe_f14_relay_local_order_control() {
    probe("relay=LocalOrder", CommunicationModel::LocalOrder);
}

/// Third control, same reasoning as `probe_f14_relay_local_order_control` but
/// for the weakest model, `NoOrder` — also in the catch-all arm.
#[test]
fn probe_f14_relay_no_order_control() {
    probe("relay=NoOrder", CommunicationModel::NoOrder);
}
