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

    // F61: the run's seed decides the exploration order, so the violating
    // trace printed below can differ between runs of the same pair.
    println!("  run seed:                                 {}", v.outcome().seed());

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

// ===========================================================================
// Leader election + two-phase commit (2026-09-29, owner's design).
//
// **The abstraction is a whole sub-protocol.** Both sides run `n` participants
// and the *same* participant code. The only difference:
//
//   - the **specification** has one invisible oracle that picks the leader with
//     a free `nondet()` choice;
//   - the **implementation** has `n` invisible electors running a real
//     election — all-to-all exchange, highest index wins.
//
// The refinement question: *can the election produce an outcome the free choice
// could not?*
//
// **Why the election is on separate threads.** Visibility is declared **per
// thread** (`visible_threads`), not per event, so "the election is invisible"
// must be realised by running it on threads that are not declared visible. Were
// those messages exchanged between the participants, they would be visible
// observations and §6.1 would require the specification to reproduce them one
// for one — putting the election *into* the specification and abstracting
// nothing.
//
// **Why one message type.** `recv_msg_block::<T>()` type-checks the *next*
// message rather than filtering for `T`. A participant's inbound messages come
// from two sources — its invisible boss and its peers — so their arrival order
// is not fixed, and a first draft with separate `Role`/`Tpc` types panicked with
// "expecting Role but got Tpc" when a peer's message overtook the role. One
// enum makes every arrival order well typed, and the loop below tolerates them.
//
// **F41.** Participants are spawned **first** on both sides, so their
// `ThreadId`s agree. Every id travelling inside a message a participant
// observes is a *participant* id; no elector or oracle id is ever observed.
// ===========================================================================

/// Everything an **elector** can receive: its setup from main, and its peers'
/// election messages — in one type, for the same reason [`PIn`] is one type.
#[derive(Clone, Debug, PartialEq)]
enum EIn {
    Setup(Setup),
    Elect(usize),
}

/// Everything a participant can receive, in one type.
#[derive(Clone, Debug, PartialEq)]
enum PIn {
    /// You lead; coordinate these peers.
    BeLeader(Vec<crate::thread::ThreadId>),
    /// You follow; vote to this leader.
    BeFollower(crate::thread::ThreadId),
    Vote(bool),
    Decision(bool),
}

#[derive(Clone, Debug, PartialEq)]
struct Setup {
    me: usize,
    electors: Vec<crate::thread::ThreadId>,
    participants: Vec<crate::thread::ThreadId>,
}

/// **Shared by both sides, byte for byte.** Its visible word is the whole of
/// what conformance compares: a role, a vote or a tally, and one decision.
///
/// Written as a tolerant loop rather than a straight line because a peer's vote
/// may overtake this thread's own role message; the counting is unaffected.
fn le_participant(n: usize) {
    let mut peers: Option<Vec<crate::thread::ThreadId>> = None;
    let mut voted = false;
    let mut votes = 0usize;
    let mut all_yes = true;
    // **A hard bound rather than `loop`.** A leader needs its role plus `n-1`
    // votes; a follower needs its role plus one decision. `n` covers both.
    //
    // It is a clarity choice, and nothing more. An earlier comment here claimed
    // the bound was load-bearing for the specification search, on the theory
    // that the prober may offer a receive reading **⊥** so an unbounded loop
    // gives the specification an unbounded space. **That is false**:
    // `Offer::may_read_nothing` is set only for a *non-blocking* receive —
    // `prober.rs`'s own tests assert both directions — and `recv_msg_block`
    // simply blocks, contributing no offer at all. The claim was invented to
    // explain a slow run that, measured properly, was never slow: `n = 2`
    // completes in 0.025 s and `n = 3` in 1.633 s. The apparent hang was `n = 4`
    // throughout, whose cost is the election's own state space (1 839 744
    // executions under plain checking), and the missing output was a block-
    // buffered pipe losing a finished row when the process was killed.
    for _ in 0..n {
        match recv_msg_block::<PIn>() {
            PIn::BeLeader(ps) => peers = Some(ps),
            PIn::BeFollower(leader) => {
                if !voted {
                    voted = true;
                    // A fixed vote on purpose. This example exists to abstract
                    // the **election**, and a `nondet()` per participant
                    // multiplies the specification's space by 2^(n-1) for a
                    // dimension the abstraction does not touch — measured: with
                    // nondet votes, `n = 2` did not finish in ten minutes.
                    send_msg(leader, PIn::Vote(true));
                }
            }
            PIn::Vote(v) => {
                votes += 1;
                all_yes &= v;
            }
            PIn::Decision(_) => return,
        }
        if let Some(ps) = peers.as_ref() {
            if votes == ps.len() {
                for p in ps {
                    send_msg(*p, PIn::Decision(all_yes));
                }
                return;
            }
        }
    }
}

/// Announce participant `i`'s role.
fn le_announce(i: usize, leader: usize, ps: &[crate::thread::ThreadId]) {
    if i == leader {
        let peers = ps
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != leader)
            .map(|(_, t)| *t)
            .collect();
        send_msg(ps[i], PIn::BeLeader(peers));
    } else {
        send_msg(ps[i], PIn::BeFollower(ps[leader]));
    }
}

/// The implementation's election, on an **invisible** thread.
///
/// Correct: the leader is the highest index, *including my own*, so every
/// elector computes the same answer from the same set.
///
/// `buggy = true` omits its own index — a one-word omission of the kind that
/// survives review. Each elector then takes the maximum of what it *received*,
/// so at `n = 2` the two disagree at once (e0 elects 1, e1 elects 0).
fn le_elector(buggy: bool) {
    let mut setup: Option<Setup> = None;
    let mut heard: Vec<usize> = Vec::new();
    let mut announced = false;
    loop {
        match recv_msg_block::<EIn>() {
            EIn::Setup(s) => setup = Some(s),
            EIn::Elect(j) => heard.push(j),
        }
        let Some(s) = setup.as_ref() else { continue };
        if !announced {
            announced = true;
            for (i, e) in s.electors.iter().enumerate() {
                if i != s.me {
                    send_msg(*e, EIn::Elect(s.me));
                }
            }
        }
        if heard.len() == s.electors.len() - 1 {
            // Correct: seed with my own index. Buggy: start from nothing, so
            // the maximum is taken over what I *received* only.
            let mut best: Option<usize> = if buggy { None } else { Some(s.me) };
            for j in &heard {
                best = Some(match best {
                    Some(b) => b.max(*j),
                    None => *j,
                });
            }
            le_announce(s.me, best.unwrap_or(s.me), &s.participants);
            return;
        }
    }
}

/// The specification's oracle: a free choice among the `n` participants,
/// encoded as a ladder of boolean `nondet()`s — the only choice primitive
/// TraceForge offers.
fn le_oracle() {
    let s: Setup = recv_msg_block();
    let n = s.participants.len();
    let mut leader = n - 1;
    for i in 0..n - 1 {
        if nondet() {
            leader = i;
            break;
        }
    }
    for i in 0..n {
        le_announce(i, leader, &s.participants);
    }
}

fn le_impl(n: usize, buggy: bool) -> impl Fn() + Send + Sync + Clone + 'static {
    move || {
        // Participants first: this is what keeps their ids equal to the
        // specification's (F41).
        let ps: Vec<crate::thread::ThreadId> = (0..n)
            .map(|i| named(&format!("p{i}"), move || le_participant(n)).thread().id())
            .collect();
        let es: Vec<crate::thread::ThreadId> = (0..n)
            .map(|i| named(&format!("e{i}"), move || le_elector(buggy)).thread().id())
            .collect();
        for (i, e) in es.iter().enumerate() {
            send_msg(
                *e,
                EIn::Setup(Setup {
                    me: i,
                    electors: es.clone(),
                    participants: ps.clone(),
                }),
            );
        }
    }
}

fn le_spec(n: usize) -> impl Fn() + Send + Sync + Clone + 'static {
    move || {
        let ps: Vec<crate::thread::ThreadId> = (0..n)
            .map(|i| named(&format!("p{i}"), move || le_participant(n)).thread().id())
            .collect();
        let oracle = named("oracle", le_oracle).thread().id();
        send_msg(
            oracle,
            Setup {
                me: 0,
                electors: vec![],
                participants: ps.clone(),
            },
        );
    }
}

fn le_visible(n: usize) -> Vec<String> {
    (0..n).map(|i| format!("p{i}")).collect()
}

fn le_cfg() -> Config {
    Config::builder().with_cons_type(ConsType::FIFO).build()
}

/// **Conforming direction**: a real election refines a free choice, `n = 2,3,4`.
///
/// ```text
/// cargo test -j 2 -p traceforge --lib conformance::demo::demo_leader_2pc_conforms -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn demo_leader_2pc_conforms() {
    use crate::conformance::verify_conformance;
    println!("\n  Leader election + 2PC — does a real election refine a free choice?\n");
    println!("   N | verdict  | outer graphs | reports | exhaustions | seconds | seed");
    println!("  ---+----------+--------------+---------+-------------+---------+------");
    // **Stops at 3 on purpose.** All-to-all gives the implementation 1 839 744
    // executions at n = 4 under plain checking (84 s), and the conformance run
    // was still going after 6.5 minutes when it was stopped. The ring version
    // (`demo_ring_2pc_conforms`) does n = 4 in 1.1 s.
    for n in 2..=3usize {
        let t = std::time::Instant::now();
        let out = verify_conformance(le_cfg(), le_impl(n, false), le_spec(n), le_visible(n), 10_000);
        let secs = t.elapsed().as_secs_f64();
        let graphs = out.stats.as_ref().map(|s| s.execs + s.block).expect("stats");
        let verdict = if out.reports.is_empty() && out.exhaustions.is_empty() {
            "conforms"
        } else {
            "REPORTED"
        };
        println!(
            "  {n:2} | {verdict:8} | {graphs:12} | {:7} | {:11} | {secs:7.3} | {}",
            out.reports.len(),
            out.exhaustions.len(),
            out.seed
        );
        assert!(out.reports.is_empty(), "N={n}: expected refinement");
        assert!(out.exhaustions.is_empty(), "N={n}: not exhaustive");
    }
}

/// **Violating direction**: the elector that forgets its own index.
///
/// ```text
/// cargo test -j 2 -p traceforge --lib conformance::demo::demo_leader_2pc_split_brain -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn demo_leader_2pc_split_brain() {
    println!("\n  Leader election + 2PC — an elector that omits its own index\n");
    for n in 2..=4usize {
        let cc = ConfBuilder::new()
            .config(le_cfg())
            .visible_threads(le_visible(n))
            .triage(true)
            .stop_at_first_report(true)
            .search_budget(100_000)
            .build()
            .expect("in scope");
        let t = std::time::Instant::now();
        let verdict = verify(cc, le_impl(n, true), le_spec(n)).expect("completes");
        println!("  ===== N = {n} ({:.3} s) =====", t.elapsed().as_secs_f64());
        println!("{verdict}");
    }
}

/// Diagnostic: the two programs under **plain** model checking, no conformance.
/// Isolates "is the program explosive?" from "is the conformance search slow?".
#[test]
#[ignore]
fn diag_leader_plain_state_space() {
    for n in 2..=4usize {
        let t = std::time::Instant::now();
        let s = crate::verify(le_cfg(), le_impl(n, false));
        println!(
            "  impl n={n}: execs={} blocked={} max_events={} in {:.3}s",
            s.execs, s.block, s.max_graph_events, t.elapsed().as_secs_f64()
        );
        let t = std::time::Instant::now();
        let s = crate::verify(le_cfg(), le_spec(n));
        println!(
            "  spec n={n}: execs={} blocked={} max_events={} in {:.3}s",
            s.execs, s.block, s.max_graph_events, t.elapsed().as_secs_f64()
        );
    }
}

// ===========================================================================
// Ring leader election + 2PC (2026-09-29). A *separate* example from the
// all-to-all one above, written because that one does not scale: its election
// gives the implementation 1 839 744 executions at `n = 4` under plain checking,
// before conformance looks at anything.
//
// **The structural difference.** In a ring each elector has exactly **one**
// inbound channel — its predecessor — so its receive order is FIFO and fixed,
// and each message is *caused* by the previous one. The election is a chain
// rather than a cloud, so there is almost nothing to interleave.
//
// **The specification is unchanged**: `le_spec`, one invisible oracle making a
// free `nondet()` choice. Only the implementation's election differs, which is
// the whole point of the example.
//
// **Correct**: a token carrying the running maximum goes round once, `e0` reads
// the winner off the returning token, then an announcement goes round so every
// elector uses *the same* answer.
//
// **Buggy**: each elector decides alone, from the token value it happened to
// see, without considering its own index — "deciding on partial information",
// and it skips the announcement. Every elector then names a different leader, so
// nobody leads.
// ===========================================================================

/// What a **ring** elector can receive. One inbound channel, but three kinds of
/// message, so one type for the reason [`PIn`] is one type.
#[derive(Clone, Debug, PartialEq)]
enum RIn {
    Setup(Setup),
    /// The circulating token, carrying the running maximum index.
    Tok(usize),
    /// The winner, announced once the token has completed its loop.
    Ann(usize),
}

fn ring_elector(buggy: bool) {
    // **Order-tolerant, and this is not optional.** An elector's inbound
    // messages come from two senders — `main` (its `Setup`) and its predecessor
    // (the ring traffic) — so their arrival order is not fixed. A first draft
    // read `Setup` with `match … { RIn::Setup(s) => s, _ => return }` and `e1`
    // received `Tok(0)` first, took the `_` arm and **exited silently**; the
    // whole ring then blocked behind it, and conformance correctly reported the
    // resulting blocked execution as a violation. The lesson is the `_ => return`
    // as much as the race: it discarded a message and left no trace.
    let mut setup: Option<Setup> = None;
    let mut tok: Option<usize> = None;
    let mut ann: Option<usize> = None;
    let mut started = false;
    // At most three inbound messages: `Setup`, `Tok`, and (correct mode, i != 0)
    // `Ann`.
    for _ in 0..3 {
        match recv_msg_block::<RIn>() {
            RIn::Setup(s) => setup = Some(s),
            RIn::Tok(m) => tok = Some(m),
            RIn::Ann(l) => ann = Some(l),
        }
        let Some(s) = setup.as_ref() else { continue };
        let n = s.electors.len();
        let succ = s.electors[(s.me + 1) % n];

        if !started {
            started = true;
            if s.me == 0 {
                send_msg(succ, RIn::Tok(0));
            }
        }

        if let Some(m) = tok.take() {
            if buggy {
                // **The bug.** Decide alone, from the token value seen so far,
                // ignoring my own index, and never wait for an announcement.
                le_announce(s.me, m, &s.participants);
                if s.me != 0 {
                    send_msg(succ, RIn::Tok(m.max(s.me)));
                }
                return;
            }
            if s.me == 0 {
                // The token has been all the way round, so `m` is the maximum.
                le_announce(0, m, &s.participants);
                if n > 1 {
                    send_msg(succ, RIn::Ann(m));
                }
                return;
            }
            send_msg(succ, RIn::Tok(m.max(s.me)));
        }

        if let Some(l) = ann.take() {
            le_announce(s.me, l, &s.participants);
            if s.me + 1 < n {
                send_msg(succ, RIn::Ann(l));
            }
            return;
        }
    }
}

/// Implementation: `n` visible participants, `n` invisible electors in a ring.
fn ring_impl(n: usize, buggy: bool) -> impl Fn() + Send + Sync + Clone + 'static {
    move || {
        // Participants first, so their ids match the specification's (F41).
        let ps: Vec<crate::thread::ThreadId> = (0..n)
            .map(|i| named(&format!("p{i}"), move || le_participant(n)).thread().id())
            .collect();
        let es: Vec<crate::thread::ThreadId> = (0..n)
            .map(|i| named(&format!("e{i}"), move || ring_elector(buggy)).thread().id())
            .collect();
        for (i, e) in es.iter().enumerate() {
            send_msg(
                *e,
                RIn::Setup(Setup {
                    me: i,
                    electors: es.clone(),
                    participants: ps.clone(),
                }),
            );
        }
    }
}

/// Diagnostic: the ring implementation's own state space, no conformance.
#[test]
#[ignore]
fn diag_ring_plain_state_space() {
    for n in 2..=4usize {
        let t = std::time::Instant::now();
        let s = crate::verify(le_cfg(), ring_impl(n, false));
        println!(
            "  ring impl n={n}: execs={} blocked={} max_events={} in {:.3}s",
            s.execs,
            s.block,
            s.max_graph_events,
            t.elapsed().as_secs_f64()
        );
    }
}

/// **Conforming direction**: a ring election refines a free choice.
///
/// ```text
/// cargo test -j 2 -p traceforge --lib conformance::demo::demo_ring_2pc_conforms -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn demo_ring_2pc_conforms() {
    use crate::conformance::verify_conformance;
    println!("\n  Ring election + 2PC — does a ring election refine a free choice?\n");
    println!("   N | verdict  | outer graphs | reports | exhaustions | seconds | seed");
    println!("  ---+----------+--------------+---------+-------------+---------+------");
    for n in 2..=4usize {
        let t = std::time::Instant::now();
        let out =
            verify_conformance(le_cfg(), ring_impl(n, false), le_spec(n), le_visible(n), 10_000);
        let secs = t.elapsed().as_secs_f64();
        let graphs = out.stats.as_ref().map(|s| s.execs + s.block).expect("stats");
        let verdict = if out.reports.is_empty() && out.exhaustions.is_empty() {
            "conforms"
        } else {
            "REPORTED"
        };
        println!(
            "  {n:2} | {verdict:8} | {graphs:12} | {:7} | {:11} | {secs:7.3} | {}",
            out.reports.len(),
            out.exhaustions.len(),
            out.seed
        );
        assert!(out.reports.is_empty(), "N={n}: expected refinement");
        assert!(out.exhaustions.is_empty(), "N={n}: not exhaustive");
    }
}

/// **Violating direction**: electors deciding alone on partial information.
///
/// ```text
/// cargo test -j 2 -p traceforge --lib conformance::demo::demo_ring_2pc_split_brain -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn demo_ring_2pc_split_brain() {
    println!("\n  Ring election + 2PC — each elector decides alone\n");
    for n in 2..=4usize {
        let cc = ConfBuilder::new()
            .config(le_cfg())
            .visible_threads(le_visible(n))
            .triage(true)
            .stop_at_first_report(true)
            .search_budget(10_000)
            .build()
            .expect("in scope");
        let t = std::time::Instant::now();
        let verdict = verify(cc, ring_impl(n, true), le_spec(n)).expect("completes");
        println!("  ===== N = {n} ({:.3} s) =====", t.elapsed().as_secs_f64());
        println!("{verdict}");
    }
}

// ===========================================================================
// P3-DEMOS (developer, 2026-09-29): the leader-election pairs' claims, pinned
// cheaply and checked against an independent ground truth.
//
// Every `demo_*` and `diag_*` test above is `#[ignore]`d, so before these an
// ordinary suite run asserted **nothing** about versions 2 and 3: a change that
// made the buggy election conform, or the correct one report, would have gone
// unnoticed until someone ran a measurement by hand. The four tests below are
// un-`ignore`d and cost 0.22 s together (measured: 0.17 + 0.05 + under 0.01
// twice), dominated by the `n = 3` ring run.
//
// The ground truth is `conformance::oracle` — `vis(P)` materialised as every
// linear extension of every graph, compared by set inclusion, with no reference
// to the morphism. See `bench.rs`'s P3-DEMOS block for what it cannot falsify.
// ===========================================================================

/// **Both pairs demonstrate what they claim to, at the smallest size that shows
/// it.** The conforming direction asserts `exhaustions` as well as `reports`:
/// `conforms` is the conjunction (F43), and the `#[ignore]`d tables print both
/// columns for exactly that reason.
///
/// `n = 2` for the all-to-all pair and `n = 2, 3` for the ring — the ring's
/// `n = 3` run is 0.07 s and is worth keeping because it is the first size at
/// which the *correct* ring actually circulates a token and announces, rather
/// than degenerating into a two-element cycle.
///
/// Cost: 0.17 s.
///
/// **Mutations, MEASURED**, one each way:
///
/// - seed `le_elector`'s comparison with `Some(s.me)` unconditionally (delete
///   the `buggy` arm) — the all-to-all split-brain assertion fails;
/// - `ring_elector`'s inbound bound `for _ in 0..3` → `0..2`, so a correct
///   elector never reads its `Ann` — the ring *conformance* assertions fail,
///   because the ring then blocks. That is the same class as the `_ => return`
///   defect the module comment above records, reached by a different edit.
#[test]
fn the_election_demos_still_demonstrate_what_they_claim() {
    use crate::conformance::verify_conformance;

    let conforms = |tag: &str, n: usize, out: crate::conformance::Outcome| {
        assert!(
            out.reports.is_empty(),
            "{tag} n={n}: a real election must refine the free choice, got {} report(s)",
            out.reports.len()
        );
        assert!(
            out.exhaustions.is_empty(),
            "{tag} n={n}: {} inner-search exhaustion(s), so `conforms` would mean \
             \"nothing found in the part we looked at\"",
            out.exhaustions.len()
        );
    };
    let reports = |tag: &str, n: usize, out: crate::conformance::Outcome| {
        assert!(
            !out.reports.is_empty(),
            "{tag} n={n}: every elector names a different leader, so this must be reported"
        );
    };

    let run = |buggy: bool| {
        verify_conformance(
            le_cfg(),
            le_impl(2, buggy),
            le_spec(2),
            le_visible(2),
            10_000,
        )
    };
    conforms("all-to-all", 2, run(false));
    reports("all-to-all", 2, run(true));
    for n in 2..=3usize {
        let run = |buggy: bool| {
            verify_conformance(
                le_cfg(),
                ring_impl(n, buggy),
                le_spec(n),
                le_visible(n),
                10_000,
            )
        };
        conforms("ring", n, run(false));
        reports("ring", n, run(true));
    }
}

/// **Both pairs are sound, by a second procedure.** At `n = 2` the oracle
/// materialises `vis` for both sides and tests inclusion directly.
///
/// The conforming direction is the one worth having: the correct election
/// elects the maximum index **deterministically**, so it would conform to
/// anything that can guess a fixed leader, and "the tool found nothing" cannot
/// tell that apart from a specification that is vacuously permissive. The
/// oracle can: it exhibits `vis(Impl)` as a subset of `vis(Spec)` with nothing
/// left over, and `vis(Spec)` is strictly larger (the oracle's free choice
/// reaches leaders the ring never elects), so the abstraction is doing work in
/// the direction that matters.
///
/// `n = 2` only, and that is a cost limit rather than a choice: at `n = 3` the
/// leader's row is five observations and the followers' three, so one graph has
/// `11!/(5!·3!·3!) = 92 400` linear extensions and the specification alone has
/// 18 graphs. The tool exists because this is what it avoids.
///
/// Cost: under 0.01 s.
///
/// **Mutation, MEASURED**: seed `le_elector`'s comparison with `Some(s.me)`
/// unconditionally and the all-to-all `Fails` arm fails — the oracle answers
/// `Holds` for a pair the demo presents as split brain.
#[test]
fn the_election_pairs_are_sound_by_the_naive_oracle() {
    use crate::conformance::oracle::{includes, Inclusion};
    let vis = le_visible(2);
    for (tag, buggy) in [("all-to-all", false), ("all-to-all", true)] {
        let got = includes(le_cfg(), &vis, le_impl(2, buggy), le_spec(2));
        match (buggy, got) {
            (false, Ok(Inclusion::Holds)) | (true, Ok(Inclusion::Fails { .. })) => {}
            (_, other) => panic!("{tag} buggy={buggy}: the oracle said {other:?}"),
        }
    }
    for (tag, buggy) in [("ring", false), ("ring", true)] {
        let got = includes(le_cfg(), &vis, ring_impl(2, buggy), le_spec(2));
        match (buggy, got) {
            (false, Ok(Inclusion::Holds)) | (true, Ok(Inclusion::Fails { .. })) => {}
            (_, other) => panic!("{tag} buggy={buggy}: the oracle said {other:?}"),
        }
    }
}

/// **Why `n ≥ 3` has no completed trace to show, established as a fact about
/// the two programs rather than as a reading of a report.**
///
/// At `n ≥ 3` both buggy elections leave the implementation with **no**
/// complete execution at all: every one of its endings is a deadlock, because
/// every elector names a different leader, nobody collects a quorum and every
/// participant waits for a decision that is never sent. The specification, at
/// the same sizes, has no blocked ending at all. So every implementation
/// visible trace carries a blocked visible thread and no specification visible
/// trace does — the violation is in the **status** component of
/// `vis(σ) = ⟨w, status|_Tvis⟩`, and it is there for every trace rather than
/// for some.
///
/// **This is not what the report establishes, and the distinction is the point
/// of the test.** At `n ≥ 3` triage answers *"the completion ended blocked
/// instead of finishing"*, so no `⟨word, status⟩` pair is produced and the
/// first failing obligation the tool names is **(M1)**, an observation mismatch
/// on the last participant at position 0 — not (M3). The status argument is
/// sound and it is derived here, from `Stats`, not read off the report.
///
/// The counts are pinned rather than compared to zero because they are also the
/// figures the demo document quotes for the *correct* pair's blocked column
/// falling to zero, and a silent change in either direction is worth a failure.
///
/// Cost: 0.05 s. `n = 4` is left out: the all-to-all buggy election has
/// 2 759 616 blocked executions there (measured).
///
/// **Mutations, MEASURED**: seed `le_elector` with `Some(s.me)` unconditionally
/// and the `(0, 882)` assertion fails; `ring_elector`'s `for _ in 0..3` → `0..2`
/// and the correct ring's `blocked = 0` assertion fails.
#[test]
fn at_n3_every_buggy_execution_blocks_and_no_specification_execution_does() {
    let s = crate::verify(le_cfg(), le_spec(3));
    assert_eq!(
        (s.execs, s.block),
        (18, 0),
        "the specification must have no blocked ending: every visible thread ends `done`"
    );

    let s = crate::verify(le_cfg(), le_impl(3, true));
    assert_eq!(
        (s.execs, s.block),
        (0, 882),
        "the all-to-all split brain must have no complete execution at n=3"
    );

    let s = crate::verify(le_cfg(), ring_impl(3, true));
    assert_eq!(
        (s.execs, s.block),
        (0, 28),
        "the ring split brain must have no complete execution at n=3"
    );

    // The correct pair, the same question: `blocked = 0` is what the ring's
    // silent `_ => return` defect cost and what its repair bought.
    for n in 2..=4usize {
        let s = crate::verify(le_cfg(), ring_impl(n, false));
        assert_eq!(
            s.block, 0,
            "the correct ring must not block at n={n}; a blocked ending here is the \
             `_ => return` defect returning"
        );
    }
}

/// **F41: no invisible thread's `ThreadId` is ever observed by a visible one.**
///
/// Both programs put `ThreadId`s inside values a visible participant receives —
/// the leader in `BeFollower`, the peers in `BeLeader` — and ids are handed out
/// per program in spawn order, so an elector's or the oracle's id reaching an
/// observation would make every such observation mismatch and the tool would
/// report a violation that is not there. The structural defence is that
/// participants are spawned **first** on both sides and `le_announce` only ever
/// sends `ps[..]`; this measures the result of that defence instead of
/// restating it.
///
/// Participants are `t1..=tn`, electors and the oracle `t(n+1)` upwards, so the
/// check is: every `opaque_id` appearing in any visible observation of either
/// program is `≤ n`. Read out of the rendered observation, which is the only
/// place a `Val`'s contents are legible from here — a text check, and named as
/// one.
///
/// `n = 2`, for the cost reason in
/// [`the_election_pairs_are_sound_by_the_naive_oracle`]. The evidence at
/// `n = 3, 4` is the conforming runs themselves: a leaked id mismatches at
/// position 0 of every row, so `demo_ring_2pc_conforms` could not be silent.
///
/// Cost: under 0.01 s.
///
/// **Mutation, MEASURED**: swap `le_impl`'s two spawn loops so the electors are
/// created first. This test fails naming `t3`, and so do both election tests
/// above — the tool reports a violation that is not there, which is F41 itself
/// rather than a restatement of it.
#[test]
fn no_elector_or_oracle_id_is_ever_observed_by_a_participant() {
    use crate::conformance::oracle::vis_of_program;
    let vis = le_visible(2);
    let spec = vis_of_program(le_cfg(), &vis, le_spec(2)).expect("spec");
    let all2all = vis_of_program(le_cfg(), &vis, le_impl(2, false)).expect("impl");
    let ring = vis_of_program(le_cfg(), &vis, ring_impl(2, false)).expect("impl");
    let programs = [("spec", spec), ("all-to-all", all2all), ("ring", ring)];
    for (tag, set) in &programs {
        assert!(
            !set.is_empty(),
            "{tag}: nothing was enumerated, so this proves nothing"
        );
        for w in set.iter() {
            for e in &w.word {
                let text = crate::conformance::report::obs_text(&e.obs);
                for (k, _) in text.match_indices("opaque_id: ") {
                    let rest = &text[k + "opaque_id: ".len()..];
                    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
                    let id: usize = digits.parse().expect("an id follows `opaque_id: `");
                    assert!(
                        (1..=2).contains(&id),
                        "{tag}: `{}` observed `{text}`, which carries t{id} — not one of the \
                         two participants t1, t2, so an invisible thread's id has reached an \
                         observation (F41)",
                        e.thread
                    );
                }
            }
        }
    }
}
