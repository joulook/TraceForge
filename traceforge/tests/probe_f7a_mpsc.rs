//! PROBE ONLY — throwaway instrument for task P1-probes (branch `probe/internals`).
//! Not a fix. Probes `sync::mpsc::Receiver::try_recv`'s `format!("{:?}", msg)
//! .contains("mpscClose")` string sniffing (F7a).

use traceforge::{sync::mpsc::*, *};

/// A perfectly ordinary user message type. `Status` carries a free-form string,
/// as application messages routinely do.
#[derive(Clone, Debug, PartialEq)]
enum UserMsg {
    /// Debug renders as `MpscCloseAck` — note the capital `M`, so this does NOT
    /// contain the literal lowercase substring `mpscClose` the library looks for.
    MpscCloseAck,
    /// Debug renders as `Status("mpscClose")` — this DOES contain it.
    Status(String),
}

/// Send `UserMsg::MpscCloseAck` and `try_recv` it. Records whether the
/// case-mismatched variant name is misclassified as `Empty`.
#[test]
fn probe_mpsc_close_ack_variant() {
    println!("=== PROBE probe_mpsc_close_ack_variant ===");
    println!(
        "Debug of the sent message = {:?}",
        UserMsg::MpscCloseAck
    );
    let stats = verify(
        Config::builder().with_keep_going_after_error(false).build(),
        || {
            let (tx, rx) = channel(100);
            let _t = thread::spawn(move || {
                traceforge::future::block_on(async {
                    let _ = tx.send(UserMsg::MpscCloseAck).await;
                })
            });
            let got = rx.try_recv();
            println!("try_recv returned: {:?}", got);
        },
    );
    println!(
        "=== RESULT probe_mpsc_close_ack_variant: execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// Send `UserMsg::Status("mpscClose".to_string())` — a legitimate user payload
/// that happens to contain the sniffed substring — and `try_recv` it.
#[test]
fn probe_mpsc_close_in_payload() {
    println!("=== PROBE probe_mpsc_close_in_payload ===");
    println!(
        "Debug of the sent message = {:?}",
        UserMsg::Status("mpscClose".to_string())
    );
    let stats = verify(
        Config::builder().with_keep_going_after_error(false).build(),
        || {
            let (tx, rx) = channel(100);
            let _t = thread::spawn(move || {
                traceforge::future::block_on(async {
                    let _ = tx.send(UserMsg::Status("mpscClose".to_string())).await;
                })
            });
            let got = rx.try_recv();
            println!("try_recv returned: {:?}", got);
        },
    );
    println!(
        "=== RESULT probe_mpsc_close_in_payload: execs={} block={} ===",
        stats.execs, stats.block
    );
}

/// Control: an ordinary payload with no such substring.
#[test]
fn probe_mpsc_control_plain_payload() {
    println!("=== PROBE probe_mpsc_control_plain_payload ===");
    let stats = verify(
        Config::builder().with_keep_going_after_error(false).build(),
        || {
            let (tx, rx) = channel(100);
            let _t = thread::spawn(move || {
                traceforge::future::block_on(async {
                    let _ = tx.send(UserMsg::Status("hello".to_string())).await;
                })
            });
            let got = rx.try_recv();
            println!("try_recv returned: {:?}", got);
        },
    );
    println!(
        "=== RESULT probe_mpsc_control_plain_payload: execs={} block={} ===",
        stats.execs, stats.block
    );
}
