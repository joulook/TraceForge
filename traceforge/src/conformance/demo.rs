//! **Conformance examples: one implementation, one specification, one verdict.**
//!
//! Every test here is a *pair*. Each prints both programs, runs
//! `verify(config, implementation, specification)`, and prints the answer.
//!
//! ```text
//! cargo test -j 2 -p traceforge --lib conformance::demo -- --nocapture --test-threads=1
//! ```
//!
//! or one at a time:
//!
//! ```text
//! cargo test -j 2 -p traceforge --lib conformance::demo::c3_wrong_value -- --nocapture
//! ```
//!
//! | # | test | implementation | specification | verdict |
//! |---|---|---|---|---|
//! | 1 | `c1_identical` | `send(c,1)` | the same program | **conforms** |
//! | 2 | `c2_relay_is_invisible` | sends via an invisible relay | sends directly | **conforms** |
//! | 3 | `c3_wrong_value` | sends `1` | sends `2` | **reports** |
//! | 4 | `c4_spec_blocks` | `c` receives once | `c` receives twice | **reports** |
//! | 5 | `c5_impl_blocks` | `c` receives twice | `c` receives once | **reports** |
//! | 6 | `c6_spec_orders_what_impl_leaves_free` | two unordered sends | the sends ordered | **reports** |
//! | 7 | `c7_impl_orders_what_spec_leaves_free` | the sends ordered | two unordered sends | **conforms** |
//! | 8 | `c8_visible_thread_fails_an_assertion` | visible `w` asserts false | `w` does nothing | **reports** |
//! | 9 | `c9_invisible_thread_fails_an_assertion` | invisible `x` asserts false | no `x` | **conforms** |
//! | 10 | `c10_spec_allows_more_than_impl_does` | always sends `1` | sends `1` **or** `2` | **conforms** |
//! | 11 | `c11_impl_does_more_than_spec_allows` | sends `1` **or** `2` | always sends `1` | **reports** |
//! | 12 | `c12_extra_invisible_work` | hidden workers, logging, extra messages | none of it | **conforms** |
//! | 13 | `c13_a_visible_threads_send_to_an_invisible_thread_is_still_observed` | visible `main` also logs | `main` does not | **reports** |
//!
//! Pairs 6/7 and 10/11 are the *same two programs with the roles swapped*, and
//! they answer differently. That is why both are here: refinement is a one-way
//! relation, and a demonstration that only ever shows it passing does not show
//! what it means.
//!
//! **12 and 13 are the pair to read together.** The same logging costs nothing
//! when an *invisible* thread does it (12) and reports when a *visible* thread
//! does it (13). Visibility is a property of the thread that acts, not of the
//! thread on the other end.

use crate::conformance::{verify, ConfBuilder, ConfVerdict};
use crate::{nondet, recv_msg_block, send_msg, thread, ConsType, Config};

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

fn conf(visible: &[&str]) -> crate::conformance::ConfConfig {
    ConfBuilder::new()
        .visible_threads(visible.iter().copied())
        // **Triage on.** It completes each reported graph into a concrete
        // trace, which is what these examples print instead of an explanation.
        // Off by default because it costs one extra engine run per report.
        .triage(true)
        .config(
            Config::builder()
                .with_cons_type(ConsType::FIFO)
                // Silence the engine's progress lines. With `0` it falls back
                // to a "report at 1, 2, 3, 10, 20..." rule, which is pure noise
                // on runs this small.
                .with_progress_report(1_000_000)
                .build(),
        )
        .build()
        .expect("in-scope configuration")
}

/// Run one pair and print it side by side. `imp_src`/`spec_src` are the two
/// programs written out, for the reader.
fn run(
    title: &str,
    visible: &[&str],
    imp_src: &str,
    spec_src: &str,
    implementation: fn(),
    specification: fn(),
) -> ConfVerdict {
    println!("\n{}", "=".repeat(74));
    println!("  {title}");
    println!("{}", "=".repeat(74));
    println!("\n  visible threads: {visible:?}\n");
    println!("  IMPLEMENTATION                        SPECIFICATION");
    println!("  {}   {}", "-".repeat(34), "-".repeat(34));
    let (mut a, mut b) = (imp_src.lines(), spec_src.lines());
    loop {
        match (a.next(), b.next()) {
            (None, None) => break,
            (x, y) => println!("  {:<36} {}", x.unwrap_or(""), y.unwrap_or("")),
        }
    }
    // **Both algorithms, on every example.**
    //
    // The naive procedure materialises every observable behaviour of both
    // programs and tests set inclusion directly — exponential, and exactly what
    // the paper's algorithm exists to avoid. The optimised one is the paper's
    // algorithm, which never enumerates. They are independent by construction:
    // the naive one does not consult the morphism at all.
    let vis: Vec<String> = visible.iter().map(|s| s.to_string()).collect();
    let naive = crate::conformance::oracle::includes(
        Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_progress_report(1_000_000)
            .build(),
        &vis,
        implementation,
        specification,
    );

    let v = verify(conf(visible), implementation, specification).expect("run");

    // Print the two answers side by side before the evidence.
    let naive_word = match &naive {
        Ok(crate::conformance::oracle::Inclusion::Holds) => "holds",
        Ok(crate::conformance::oracle::Inclusion::Fails { .. }) => "fails",
        Err(_) => "n/a",
    };
    let tool_word = match &v {
        ConfVerdict::Conforms(_) => "conforms",
        ConfVerdict::Reported(_) => "reports",
        ConfVerdict::Inconclusive(_) => "inconclusive",
    };
    println!("\n  naive procedure (enumerates everything):  {naive_word}");
    println!("  the paper's algorithm:                    {tool_word}");

    // The only combination that must never occur.
    if let (Ok(crate::conformance::oracle::Inclusion::Fails { .. }), ConfVerdict::Conforms(_)) =
        (&naive, &v)
    {
        panic!("UNSOUND: the algorithm certified a pair the naive procedure says does not refine");
    }

    match &v {
        ConfVerdict::Conforms(_) => {
            println!("\n  VERDICT:  CONFORMS");
            println!("  No implementation behaviour is outside the specification, the inner");
            println!("  search never ran out of budget, and the state space was exhausted.");
        }
        ConfVerdict::Reported(o) => {
            println!(
                "\n  VERDICT:  REPORTS  ({} candidate violation(s))",
                o.reports().len()
            );
            for (i, r) in o.reports().iter().enumerate() {
                println!("\n  --- violation #{i} ---");
                show_violation(r);
            }
        }
        ConfVerdict::Inconclusive(_) => {
            println!("\n  VERDICT:  INCONCLUSIVE  (established neither)")
        }
    }
    v
}

/// Print the **evidence**: the implementation behaviour that no specification
/// execution accounts for.
fn show_violation(r: &crate::conformance::ConfReport) {
    use crate::conformance::{ReportCause, TriageOutcome};

    match r.cause() {
        ReportCause::VisibleError { thread, pos } => {
            println!("  the visible thread `{thread}` failed an assertion at {pos}");
        }
        ReportCause::NoCover => {
            println!("  no specification execution accounts for this implementation run");
        }
    }

    // §7.3's triage completes the reported graph into a concrete trace. This is
    // the violating behaviour itself rather than a description of it.
    match r.triage() {
        Some(TriageOutcome::Completed {
            vis, spec_mismatch, ..
        }) => {
            println!("\n  the implementation produced this visible trace:");
            for (k, step) in vis.word().iter().enumerate() {
                println!("      {k}. {step}");
            }
            let st = vis
                .statuses()
                .iter()
                .map(|(t, s)| format!("{t}={s}"))
                .collect::<Vec<_>>()
                .join(", ");
            println!("      ends: {st}");
            println!("\n  and the specification, at its first point of difference:");
            for line in spec_mismatch.lines() {
                println!("      {line}");
            }
        }
        Some(other) => {
            println!("\n  triage could not complete this graph: {other}");
            println!("  falling back to the reported graph:");
            for line in r.graph_dump().lines() {
                println!("      {line}");
            }
        }
        None => {
            println!("\n  reported implementation graph:");
            for line in r.graph_dump().lines() {
                println!("      {line}");
            }
        }
    }
}

fn conforms(v: &ConfVerdict) -> bool {
    matches!(v, ConfVerdict::Conforms(_))
}
fn reports(v: &ConfVerdict) -> bool {
    matches!(v, ConfVerdict::Reported(_))
}

// --- the programs the examples reuse ---------------------------------------

fn direct_1() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 1i32);
}

fn direct_2() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 2i32);
}

fn via_relay() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let r = named("r", move || {
        let v: i32 = recv_msg_block();
        send_msg(cid, v);
    });
    send_msg(r.thread().id(), 1i32);
}

fn two_free_sends() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let _a = named("a", move || send_msg(cid, 1i32));
    let _b = named("b", move || send_msg(cid, 2i32));
}

fn two_ordered_sends() {
    let c = named("c", || {
        let _x: i32 = recv_msg_block();
    });
    let cid = c.thread().id();
    let a = named("a", move || send_msg(cid, 1i32));
    let _b = named("b", move || {
        a.join().unwrap();
        send_msg(cid, 2i32);
    });
}

// ===========================================================================

/// **1. The floor.** A program conforms to itself.
#[test]
fn c1_identical() {
    let v = run(
        "1. identical programs",
        &["main", "c"],
        "main: send(c, 1)\nc:    recv()",
        "main: send(c, 1)\nc:    recv()",
        direct_1,
        direct_1,
    );
    assert!(conforms(&v));
}

/// **2. An invisible relay changes nothing observable.**
#[test]
fn c2_relay_is_invisible() {
    let v = run(
        "2. implementation relays through an invisible thread",
        &["main", "c"],
        "main: send(r, 1)\nr:    recv(); send(c, v)    <- invisible\nc:    recv()",
        "main: send(c, 1)\n\nc:    recv()",
        via_relay,
        direct_1,
    );
    assert!(conforms(&v));
}

/// **3. A different observed value.**
#[test]
fn c3_wrong_value() {
    let v = run(
        "3. implementation sends 1, specification sends 2",
        &["main", "c"],
        "main: send(c, 1)\nc:    recv()",
        "main: send(c, 2)\nc:    recv()",
        direct_1,
        direct_2,
    );
    assert!(reports(&v));
}

/// **4. The specification blocks where the implementation finishes.**
#[test]
fn c4_spec_blocks() {
    fn spec() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
            let _w: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    }
    let v = run(
        "4. the specification's `c` waits for a second message",
        &["main", "c"],
        "main: send(c, 1)\nc:    recv()",
        "main: send(c, 1)\nc:    recv(); recv()   <- never satisfied",
        direct_1,
        spec,
    );
    assert!(reports(&v));
}

/// **5. The same thing, mirrored.**
#[test]
fn c5_impl_blocks() {
    fn imp() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
            let _w: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    }
    let v = run(
        "5. the implementation's `c` waits for a second message",
        &["main", "c"],
        "main: send(c, 1)\nc:    recv(); recv()   <- hangs",
        "main: send(c, 1)\nc:    recv()",
        imp,
        direct_1,
    );
    assert!(reports(&v));
}

/// **6. The specification imposes an order the implementation does not.**
#[test]
fn c6_spec_orders_what_impl_leaves_free() {
    let v = run(
        "6. specification orders two sends the implementation leaves free",
        &["main", "a", "b", "c"],
        "a: send(c, 1)\nb: send(c, 2)\nc: recv()",
        "a: send(c, 1)\nb: wait for a; send(c, 2)\nc: recv()",
        two_free_sends,
        two_ordered_sends,
    );
    assert!(reports(&v));
}

/// **7. The same two programs, swapped — and it conforms.**
#[test]
fn c7_impl_orders_what_spec_leaves_free() {
    let v = run(
        "7. implementation orders two sends the specification leaves free",
        &["main", "a", "b", "c"],
        "a: send(c, 1)\nb: wait for a; send(c, 2)\nc: recv()",
        "a: send(c, 1)\nb: send(c, 2)\nc: recv()",
        two_ordered_sends,
        two_free_sends,
    );
    assert!(conforms(&v));
}

/// **8. A visible thread fails an assertion.**
#[test]
fn c8_visible_thread_fails_an_assertion() {
    fn imp() {
        let _w = named("w", || crate::assert(false));
    }
    fn spec() {
        let _w = named("w", || {});
    }
    let v = run(
        "8. a VISIBLE thread fails an assertion",
        &["w"],
        "w: assert(false)",
        "w: (nothing)",
        imp,
        spec,
    );
    assert!(reports(&v));
}

/// **9. An invisible thread fails an assertion — and nothing happens.**
#[test]
fn c9_invisible_thread_fails_an_assertion() {
    fn imp() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        let _x = named("x", || crate::assert(false));
        send_msg(c.thread().id(), 1i32);
    }
    let v = run(
        "9. an INVISIBLE thread fails an assertion",
        &["main", "c"],
        "main: send(c, 1)\nx:    assert(false)    <- invisible\nc:    recv()",
        "main: send(c, 1)\n\nc:    recv()",
        imp,
        direct_1,
    );
    assert!(conforms(&v));
}

/// **10. The specification permits a choice the implementation never makes.**
#[test]
fn c10_spec_allows_more_than_impl_does() {
    fn spec() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), if nondet() { 1i32 } else { 2i32 });
    }
    let v = run(
        "10. specification may send 1 or 2; implementation always sends 1",
        &["main", "c"],
        "main: send(c, 1)\nc:    recv()",
        "main: send(c, nondet ? 1 : 2)\nc:    recv()",
        direct_1,
        spec,
    );
    assert!(conforms(&v));
}

/// **11. And the reverse reports.**
#[test]
fn c11_impl_does_more_than_spec_allows() {
    fn imp() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), if nondet() { 1i32 } else { 2i32 });
    }
    let v = run(
        "11. implementation may send 1 or 2; specification allows only 1",
        &["main", "c"],
        "main: send(c, nondet ? 1 : 2)\nc:    recv()",
        "main: send(c, 1)\nc:    recv()",
        imp,
        direct_1,
    );
    assert!(reports(&v));
}

/// **12. Arbitrary hidden machinery is free.**
#[test]
fn c12_extra_invisible_work() {
    fn imp() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        let cid = c.thread().id();
        let log = named("log", || {
            let _a: i32 = recv_msg_block();
            let _b: i32 = recv_msg_block();
        });
        let lid = log.thread().id();
        let worker = named("worker", move || {
            let v: i32 = recv_msg_block();
            send_msg(lid, v);
            send_msg(lid, v + 1);
            send_msg(cid, v);
        });
        send_msg(worker.thread().id(), 1i32);
    }
    let v = run(
        "12. implementation has hidden workers, logging and extra messages",
        &["main", "c"],
        "main:   send(worker, 1)\nworker: recv()              <- invisible\n        send(log,v); send(log,v+1)\n        send(c, v)\nlog:    recv(); recv()      <- invisible\nc:      recv()",
        "main:   send(c, 1)\n\n\n\n\nc:      recv()",
        imp,
        direct_1,
    );
    assert!(conforms(&v));
}

/// **13. The trap: a visible thread's send is observed even when it goes to an
/// invisible thread.**
#[test]
fn c13_a_visible_threads_send_to_an_invisible_thread_is_still_observed() {
    fn imp() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        let log = named("log", || {
            let _a: i32 = recv_msg_block();
        });
        send_msg(log.thread().id(), 99i32);
        send_msg(c.thread().id(), 1i32);
    }
    let v = run(
        "13. visible `main` also logs to an invisible thread",
        &["main", "c"],
        "main: send(log, 99)      <- log is invisible\n      send(c, 1)\nc:    recv()",
        "main: send(c, 1)\n\nc:    recv()",
        imp,
        direct_1,
    );
    assert!(reports(&v));
}

// ===========================================================================

/// **Cross-check: the same pairs through a second, independent procedure.**
///
/// The naive procedure materialises every observable behaviour of both programs
/// and tests set inclusion directly. The optimised one is the paper's
/// algorithm, which never enumerates. They were built independently on purpose:
/// a cross-check sharing the optimised one's machinery would agree with itself
/// by construction and mean nothing.
#[test]
fn cross_check_naive_against_optimised() {
    use crate::conformance::differential::{compare, Agreement};

    println!("\n{}", "=".repeat(74));
    println!("  cross-check: the naive procedure vs. the paper's algorithm");
    println!("{}", "=".repeat(74));

    let vis: Vec<String> = ["main", "c"].iter().map(|s| s.to_string()).collect();
    let vis4: Vec<String> = ["main", "a", "b", "c"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    let cfg = Config::builder().with_cons_type(ConsType::FIFO).build();

    println!("\n  implementation      specification        naive      tool");
    println!("  {}", "-".repeat(64));

    let rows = [
        ("via_relay", "direct_1", compare(cfg.clone(), &vis, via_relay, direct_1)),
        ("direct_1", "via_relay", compare(cfg.clone(), &vis, direct_1, via_relay)),
        ("direct_1", "direct_2", compare(cfg.clone(), &vis, direct_1, direct_2)),
        (
            "two_free_sends",
            "two_ordered_sends",
            compare(cfg.clone(), &vis4, two_free_sends, two_ordered_sends),
        ),
        (
            "two_ordered_sends",
            "two_free_sends",
            compare(cfg.clone(), &vis4, two_ordered_sends, two_free_sends),
        ),
    ];

    let mut unsound = 0;
    for (i, s, a) in rows {
        let a = a.expect("compare");
        let (n, t, note) = match a {
            Agreement::BothClean => ("holds", "conforms", "agree"),
            Agreement::BothFail { .. } => ("fails", "reports ", "agree"),
            Agreement::FalseAlarm { .. } => ("holds", "reports ", "FALSE ALARM"),
            Agreement::Unsound { .. } => {
                unsound += 1;
                ("fails", "conforms", "*** UNSOUND ***")
            }
            Agreement::Inconclusive { .. } => ("-", "inconcl.", "neither"),
        };
        println!("  {i:<19} {s:<20} {n:<10} {t:<9} {note}");
    }

    println!("\n  Both decide the same question by different means. They may");
    println!("  legitimately differ one way: the tool can report where the naive");
    println!("  answer is `holds`, because it is conservative by design. The");
    println!("  reverse is unsoundness, and it is the only thing asserted here.");
    assert_eq!(unsound, 0);
}
