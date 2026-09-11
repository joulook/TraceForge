//! Adversarial tests for probe mode (S1) and the morphism (S2).
//!
//! Written by the developer agent against the acceptance criteria and the
//! draft, deliberately without reading the implementation's own tests first,
//! and with the aim of *breaking* the code rather than confirming it. Kept in
//! its own file so that what independent derivation covers can be compared
//! against what the author's tests cover.

#![cfg(test)]

use std::sync::atomic::{AtomicUsize, Ordering};

use crate::conformance::morphism::{
    follows, matches, observations_follow, observations_match, order_is_reflected, statuses,
    statuses_agree, Status,
};
use crate::conformance::obs::{wobs, ObsError, Wobs};
use crate::conformance::prober::{probe_from, probe_once};
use crate::conformance::testing::{names, run_once};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::thread::{self, main_thread_id, ThreadId};
use crate::{Config, ConsType};

// ---------------------------------------------------------------------------
// Helpers. Nothing here touches the implementation; a helper that needed to
// would be a finding, not a helper.
// ---------------------------------------------------------------------------

fn cfg(cons: ConsType) -> Config {
    Config::builder().with_cons_type(cons).build()
}

fn fifo() -> Config {
    cfg(ConsType::FIFO)
}

/// Spawn a named thread, the way the §8 pairing rule expects programs to.
fn named<F>(name: &str, f: F) -> ThreadId
where
    F: FnOnce() + Send + 'static,
{
    thread::Builder::new()
        .name(name.to_owned())
        .spawn(f)
        .unwrap()
        .thread()
        .id()
}

/// The kinds a row observed, as a printable vector, for assertions that want
/// to be explicit about *which* observation moved rather than only that the
/// comparison flipped.
fn shape(w: &Wobs, name: &str) -> Vec<String> {
    w.row(name)
        .unwrap_or_else(|| panic!("no row for `{name}`"))
        .observations()
        .iter()
        .map(|(_, o)| format!("{o:?}"))
        .collect()
}

fn sizes(g: &ExecutionGraph) -> Vec<(ThreadId, usize)> {
    g.thread_ids()
        .into_iter()
        .map(|t| (t, g.thread_size(t)))
        .collect()
}

// ===========================================================================
// (M1) — what an observation is
// ===========================================================================

/// A send of `v` and a receive that observed `v` must not compare equal.
///
/// Property: an observation records its *kind*. If `Obs` compared only values,
/// two programs in which a visible thread sends where the other receives would
/// be indistinguishable — and every value-only test would still pass, because
/// hand-written pairs put sends opposite sends.
#[test]
fn m1_send_and_receive_of_the_same_value_are_different_observations() {
    // "main" sends 7.
    let sender = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 7u64);
    });
    // "main" receives 7.
    let receiver = run_once(fifo(), || {
        let m = main_thread_id();
        named("w", move || crate::send_msg(m, 7u64));
        let _: u64 = crate::recv_msg_block();
    });

    let vis = names(&["main"]);
    let ws = wobs(&sender, &vis).unwrap();
    let wr = wobs(&receiver, &vis).unwrap();

    // Not vacuous: each side really observed one event.
    assert_eq!(shape(&ws, "main").len(), 1, "{:?}", shape(&ws, "main"));
    assert_eq!(shape(&wr, "main").len(), 1, "{:?}", shape(&wr, "main"));

    assert!(
        !observations_match(&ws, &wr, &vis),
        "a send and a receive of the same value compared equal: {:?} vs {:?}",
        shape(&ws, "main"),
        shape(&wr, "main")
    );
    assert!(!observations_follow(&ws, &wr, &vis));
    assert!(!observations_follow(&wr, &ws, &vis));
}

/// A send's destination is not observed (CA §4, Ex. relay).
#[test]
fn m1_send_destination_is_not_observed() {
    let to_first = run_once(fifo(), || {
        let a = named("a", || {
            let _: u64 = crate::recv_msg_block();
        });
        named("b", || {});
        crate::send_msg(a, 7u64);
    });
    let to_second = run_once(fifo(), || {
        named("a", || {});
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(b, 7u64);
    });

    let vis = names(&["main"]);
    let w1 = wobs(&to_first, &vis).unwrap();
    let w2 = wobs(&to_second, &vis).unwrap();
    assert_eq!(shape(&w1, "main").len(), 1);
    assert!(
        observations_match(&w1, &w2, &vis),
        "the destination reached the compared value: {:?} vs {:?}",
        shape(&w1, "main"),
        shape(&w2, "main")
    );
}

/// The same declared name with different `ThreadId`s on the two sides.
///
/// This is the test criterion 8 names as the one that catches a `ThreadId`
/// inside the observation. The assertion that the two ids really differ is
/// what stops it passing for the wrong reason.
#[test]
fn m1_same_name_different_thread_ids_still_match() {
    let plain = run_once(fifo(), || {
        let m = main_thread_id();
        named("worker", move || crate::send_msg(m, 7u64));
        let _: u64 = crate::recv_msg_block();
    });
    let noisy = run_once(fifo(), || {
        let m = main_thread_id();
        named("noise1", || {});
        named("noise2", || {});
        named("worker", move || crate::send_msg(m, 7u64));
        let _: u64 = crate::recv_msg_block();
    });

    let vis = names(&["worker"]);
    let wp = wobs(&plain, &vis).unwrap();
    let wn = wobs(&noisy, &vis).unwrap();

    let tp = wp.row("worker").unwrap().thread().unwrap();
    let tn = wn.row("worker").unwrap().thread().unwrap();
    assert_ne!(
        tp, tn,
        "the two sides gave `worker` the same ThreadId, so this test would \
         pass even if the observation carried one"
    );
    assert_eq!(shape(&wp, "worker").len(), 1);

    assert!(
        observations_match(&wp, &wn, &vis),
        "(M1) became a function of spawn order: {:?} vs {:?}",
        shape(&wp, "worker"),
        shape(&wn, "worker")
    );
}

/// `"main"` declared visible, carrying a visible event.
///
/// The event is what keeps it honest: a resolution that missed `main`
/// altogether would give the empty sequence on both sides and compare equal.
#[test]
fn m1_main_resolves_and_carries_its_events() {
    let g = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
        crate::send_msg(w, 2u64);
    });
    let vis = names(&["main"]);
    let w = wobs(&g, &vis).unwrap();
    let row = w.row("main").expect("`main` must be a key");
    assert!(
        !row.is_unspawned(),
        "`main` did not resolve; row-scanning for TCreate is the implementation \
         that gets this wrong"
    );
    assert_eq!(row.thread(), Some(main_thread_id()));
    assert_eq!(
        shape(&w, "main").len(),
        2,
        "main resolved but contributed nothing: {:?}",
        shape(&w, "main")
    );
}

/// Two threads carrying one declared visible name is an error, not a
/// first-match.
#[test]
fn m1_duplicate_visible_name_is_an_error() {
    let g = run_once(fifo(), || {
        named("w", || {});
        named("w", || {});
    });
    assert_eq!(
        wobs(&g, &names(&["w"])).unwrap_err(),
        ObsError::AmbiguousName {
            name: "w".to_owned()
        }
    );
}

/// A user thread named `"main"` collides with the reserved name.
///
/// `ExecutionGraph::new` names the main thread `"main"`, so a program that also
/// names a spawned thread `"main"` makes the reserved name ambiguous. The
/// question is whether that is caught or silently resolved to one of them.
#[test]
fn m1_user_thread_named_main_collides_with_the_reserved_name() {
    let g = run_once(fifo(), || {
        named("main", || {});
    });
    assert_eq!(
        wobs(&g, &names(&["main"])).unwrap_err(),
        ObsError::AmbiguousName {
            name: "main".to_owned()
        }
    );
}

/// Two Rust types for what the user means as one message.
///
/// `msg_equals` downcasts, so `1u64` and `1u32` are unequal at every position.
/// The criteria allow silent inequality only if the reason is recorded and the
/// difference is legible; this pins both halves — no panic, and `type_name`
/// tells them apart.
#[test]
fn m1_cross_type_values_are_unequal_and_legible() {
    let wide = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });
    let narrow = run_once(fifo(), || {
        let w = named("w", || {
            let _: u32 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u32);
    });

    let vis = names(&["main"]);
    let ww = wobs(&wide, &vis).unwrap();
    let wn = wobs(&narrow, &vis).unwrap();
    assert!(!observations_match(&ww, &wn, &vis));

    let tw = ww.row("main").unwrap().observations()[0].1.type_name();
    let tn = wn.row("main").unwrap().observations()[0].1.type_name();
    assert_ne!(tw, tn, "the type difference is not visible in a report");
}

/// A blocking receive with nothing to read contributes **no** observation,
/// where a non-blocking one on the same program shape contributes `⊥`.
///
/// This is Ex. blocking, and it is the discrimination criterion 2's "`⊥` when
/// `rf` is `None`" leaves ambiguous: only the non-blocking case produces a
/// `RecvMsg` at all.
#[test]
fn m1_blocking_and_non_blocking_empty_receives_differ() {
    let blocking = run_once(fifo(), || {
        named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
    });
    let non_blocking = run_once(fifo(), || {
        named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
    });

    let vis = names(&["w"]);
    let wb = wobs(&blocking, &vis).unwrap();
    let wn = wobs(&non_blocking, &vis).unwrap();

    assert_eq!(
        shape(&wb, "w"),
        Vec::<String>::new(),
        "a blocked receive contributed an observation"
    );
    assert_eq!(
        shape(&wn, "w").len(),
        1,
        "a non-blocking empty receive contributed nothing: {:?}",
        shape(&wn, "w")
    );
    assert!(
        !observations_match(&wb, &wn, &vis),
        "Ex. blocking's two shapes are indistinguishable"
    );

    // And the statuses differ, which is the other half of Ex. blocking.
    assert_eq!(
        statuses(&blocking, &wb, &vis).unwrap()["w"],
        Status::Blocked
    );
    assert_eq!(
        statuses(&non_blocking, &wn, &vis).unwrap()["w"],
        Status::Done
    );
}

// ===========================================================================
// (M1) — the pending-value precondition, both paths
// ===========================================================================

/// A visible thread's **own** send, observed before the send re-executed.
#[test]
#[should_panic(expected = "whose value is still pending")]
fn m1_pending_own_send_is_loud() {
    let mut g = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 7u64);
    });
    // Exactly what the engine does at the start of every execution, and
    // therefore what a gate at a mid-replay point sees.
    g.initialize_for_execution();
    let _ = wobs(&g, &names(&["main"]));
}

/// A visible thread with **no sends of its own**, observing through `rf` a send
/// that lives on an invisible thread.
///
/// The assertion on the send arm never runs for this shape, so an
/// implementation with one assertion covering only that arm reports a blanked
/// value — and two programs sending different values then compare *equal*,
/// because `msg_equals` on two blanked values is true.
#[test]
#[should_panic(expected = "whose value is still pending")]
fn m1_pending_send_read_by_a_visible_receive_is_loud() {
    let mut g = run_once(fifo(), || {
        let m = main_thread_id();
        named("src", move || crate::send_msg(m, 7u64));
        let _: u64 = crate::recv_msg_block();
    });
    g.initialize_for_execution();
    let _ = wobs(&g, &names(&["main"]));
}

/// The wrong answer the two assertions above exist to prevent, demonstrated on
/// the values themselves rather than through the extractor.
///
/// If the assertions were removed, these two programs — which send *different*
/// values — would compare equal. The test asserts the premise (blanking makes
/// the two graphs' send values compare equal) so the reader can see the
/// assertions are not decoration.
#[test]
fn m1_blanked_send_values_would_compare_equal() {
    let build = |v: u64| {
        let mut g = run_once(fifo(), move || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, v);
        });
        g.initialize_for_execution();
        g
    };
    let g1 = build(1);
    let g2 = build(2);

    let send_val = |g: &ExecutionGraph| {
        let t = main_thread_id();
        (0..g.thread_size(t) as u32)
            .find_map(|i| match g.label(Event::new(t, i)) {
                LabelEnum::SendMsg(s) => Some(s.val().clone()),
                _ => None,
            })
            .expect("main sends")
    };
    let v1 = send_val(&g1);
    let v2 = send_val(&g2);
    assert!(v1.is_pending() && v2.is_pending());
    assert_eq!(
        v1, v2,
        "premise of the pending assertions does not hold on this tree"
    );
}

// ===========================================================================
// (M1) — prefix versus equality, and the vacuity traps
// ===========================================================================

/// `follows` is directional: a shorter specification follows a longer
/// implementation, and never the other way round.
#[test]
fn m1_prefix_is_directional() {
    let long = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
        crate::send_msg(w, 2u64);
    });
    let short = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });

    let vis = names(&["main"]);
    let wl = wobs(&long, &vis).unwrap();
    let ws = wobs(&short, &vis).unwrap();
    assert_eq!(shape(&wl, "main").len(), 2);
    assert_eq!(shape(&ws, "main").len(), 1);

    assert!(
        observations_follow(&ws, &wl, &vis),
        "short must follow long"
    );
    assert!(!observations_match(&ws, &wl, &vis), "short must not match");
    assert!(
        !observations_follow(&wl, &ws, &vis),
        "a specification carrying an event the implementation does not have \
         must not follow it"
    );
}

/// Equal length, one position different: neither follows nor matches.
#[test]
fn m1_conflict_at_a_shared_position_is_caught() {
    let mk = |v: u64| {
        run_once(fifo(), move || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, v);
        })
    };
    let g1 = mk(1);
    let g2 = mk(2);
    let vis = names(&["main"]);
    let w1 = wobs(&g1, &vis).unwrap();
    let w2 = wobs(&g2, &vis).unwrap();
    assert!(!observations_follow(&w1, &w2, &vis));
    assert!(!observations_match(&w1, &w2, &vis));
}

/// A name that is not a key of the `Wobs` must be loud, not an empty sequence.
///
/// This is the vacuous-pass shape: `Wobs::of` answers `&[]` for an absent key,
/// so a comparison that went through it would succeed on both sides.
#[test]
#[should_panic(expected = "does not match what was extracted")]
fn m1_comparing_a_name_the_wobs_was_not_built_for_is_loud() {
    let g = run_once(fifo(), || {
        named("w", || {});
    });
    let built = wobs(&g, &names(&["w"])).unwrap();
    let _ = observations_match(&built, &built, &names(&["w", "ghost"]));
}

/// With **no** declared visible threads every pair matches and follows.
///
/// Correct against Def. follow, whose clauses quantify over `Tvis` — but it is
/// the largest vacuous pass in the module, and nothing in S2 refuses it.
/// Recorded as a test so that a later guard has to change this line.
#[test]
fn m1_empty_visible_list_matches_anything() {
    let a = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });
    let b = run_once(fifo(), || {});
    let vis: Vec<String> = Vec::new();
    let wa = wobs(&a, &vis).unwrap();
    let wb = wobs(&b, &vis).unwrap();
    assert!(matches(&b, &a, &wb, &wa, &vis));
    assert!(follows(&b, &a, &wb, &wa, &vis));
}

/// A declared name that resolves on neither side reads as empty on both, so
/// (M1) holds vacuously for it on partial graphs.
///
/// `Row::Unspawned` keeps the case distinguishable, and `statuses` is where it
/// is raised; `follows`/`matches` cannot raise it, because an unspawned thread
/// is the ordinary case there. This pins the residual exposure rather than
/// claiming it is a defect.
#[test]
fn m1_unresolvable_name_is_vacuous_for_follows_and_loud_for_statuses() {
    let g = run_once(fifo(), || {
        named("w", || {});
    });
    let vis = names(&["typo"]);
    let w = wobs(&g, &vis).unwrap();
    assert!(w.row("typo").unwrap().is_unspawned());
    assert!(observations_match(&w, &w, &vis));
    assert_eq!(
        statuses(&g, &w, &vis),
        Err(ObsError::NotSpawned {
            name: "typo".to_owned()
        })
    );
}

// ===========================================================================
// (M2) — direction, invisible paths, lifecycle edges
// ===========================================================================

/// Two programs with **identical** observations that differ only in whether a
/// visible send is read by a visible receive.
///
/// The specification side is the more ordered one, which (M2) forbids; swapping
/// the sides must flip the answer. An executed witness on which the two
/// directions disagree is what criterion 4 asks for, and a check written the
/// wrong way round passes the first half and fails the second.
#[test]
fn m2_is_directional_on_an_executed_witness() {
    // Ordered: "a" sends straight to "b".
    let ordered = run_once(fifo(), || {
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        named("a", move || crate::send_msg(b, 7u64));
    });
    // Concurrent: "a" sends to main, and "b" reads a send of main's that is
    // not porf-after anything "a" did.
    let concurrent = run_once(fifo(), || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 7u64));
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(b, 7u64);
    });

    let vis = names(&["a", "b"]);
    let wo = wobs(&ordered, &vis).unwrap();
    let wc = wobs(&concurrent, &vis).unwrap();

    // (M1) agrees, so only (M2) can separate them.
    assert_eq!(shape(&wo, "a").len(), 1);
    assert_eq!(shape(&wo, "b").len(), 1);
    assert!(
        observations_match(&wo, &wc, &vis),
        "the witness is not (M1)-neutral: {:?}/{:?} vs {:?}/{:?}",
        shape(&wo, "a"),
        shape(&wo, "b"),
        shape(&wc, "a"),
        shape(&wc, "b")
    );

    assert!(
        !order_is_reflected(&ordered, &concurrent, &wo, &wc, &vis),
        "(M2) accepted a specification more ordered than the implementation"
    );
    assert!(
        order_is_reflected(&concurrent, &ordered, &wc, &wo, &vis),
        "(M2) rejected an implementation more ordered than the specification"
    );
}

/// `vo` runs *through* invisible threads, over two hops.
#[test]
fn m2_sees_order_through_two_invisible_relays() {
    let relayed = run_once(fifo(), || {
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        let r2 = named("r2", move || {
            let v: u64 = crate::recv_msg_block();
            crate::send_msg(b, v);
        });
        let r1 = named("r1", move || {
            let v: u64 = crate::recv_msg_block();
            crate::send_msg(r2, v);
        });
        named("a", move || crate::send_msg(r1, 7u64));
    });
    let concurrent = run_once(fifo(), || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 7u64));
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(b, 7u64);
    });

    let vis = names(&["a", "b"]);
    let wr = wobs(&relayed, &vis).unwrap();
    let wc = wobs(&concurrent, &vis).unwrap();
    assert!(observations_match(&wr, &wc, &vis));

    assert!(
        !order_is_reflected(&relayed, &concurrent, &wr, &wc, &vis),
        "an ordering that reaches its target only through invisible threads \
         was not seen"
    );
}

/// A join in which **neither participant is visible** still orders two visible
/// events (criterion 8's third join shape, A7).
///
/// Both programs are identical except that one has `main` join the invisible
/// relay. In the draft's `(po ∪ rf)⁺` there is no edge either way; in
/// TraceForge the join pulls the relay's whole prefix into `main`'s clock, so
/// `a`'s send precedes `b`'s receive. Expected answer derived, not assumed:
/// with the join, `vo(a.send, b.recv)` holds on the specification side and not
/// on the implementation side, so (M2) must fail.
#[test]
fn m2_a_join_between_two_invisible_threads_orders_visible_events() {
    let joined = run_once(fifo(), || {
        let x = thread::Builder::new()
            .name("x".to_owned())
            .spawn(|| {
                let _: u64 = crate::recv_msg_block();
            })
            .unwrap();
        let xid = x.thread().id();
        named("a", move || crate::send_msg(xid, 7u64));
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        let _ = x.join();
        crate::send_msg(b, 7u64);
    });
    let unjoined = run_once(fifo(), || {
        let x = thread::Builder::new()
            .name("x".to_owned())
            .spawn(|| {
                let _: u64 = crate::recv_msg_block();
            })
            .unwrap();
        let xid = x.thread().id();
        named("a", move || crate::send_msg(xid, 7u64));
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(b, 7u64);
    });

    let vis = names(&["a", "b"]);
    let wj = wobs(&joined, &vis).unwrap();
    let wu = wobs(&unjoined, &vis).unwrap();
    assert!(
        observations_match(&wj, &wu, &vis),
        "the two sides differ in (M1), so this says nothing about (M2)"
    );

    assert!(
        !order_is_reflected(&joined, &unjoined, &wj, &wu, &vis),
        "the join between two invisible threads produced no visible ordering; \
         either `in_porf`'s TJoin arm did not fire or the pair was not matched"
    );
    assert!(
        order_is_reflected(&unjoined, &joined, &wu, &wj, &vis),
        "the reverse direction should be accepted: the implementation is the \
         more ordered side"
    );
}

/// Shapes (i) and (ii): a join of a **visible** thread, present on one side
/// only.
#[test]
fn m2_join_of_a_visible_thread_is_directional() {
    let joins = run_once(fifo(), || {
        let a = thread::Builder::new()
            .name("a".to_owned())
            .spawn(|| crate::send_msg(main_thread_id(), 7u64))
            .unwrap();
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        let _ = a.join();
        crate::send_msg(b, 7u64);
    });
    let does_not_join = run_once(fifo(), || {
        named("a", || crate::send_msg(main_thread_id(), 7u64));
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(b, 7u64);
    });

    let vis = names(&["a", "b"]);
    let wj = wobs(&joins, &vis).unwrap();
    let wn = wobs(&does_not_join, &vis).unwrap();
    assert!(observations_match(&wj, &wn, &vis));

    // (ii) specification joins, implementation does not → reject.
    assert!(!order_is_reflected(&joins, &does_not_join, &wj, &wn, &vis));
    // (i) implementation joins, specification does not → accept.
    assert!(order_is_reflected(&does_not_join, &joins, &wn, &wj, &vis));
}

/// Unequal row lengths must not panic or silently consult the extra events.
///
/// The specification side carries one more visible event than the
/// implementation, and that event has a `vo` edge to nothing the matching
/// relates. (M2) is defined on matched pairs only, so it must hold; `follows`
/// must still be false, from the prefix clause alone.
#[test]
fn m2_ignores_events_beyond_the_matching() {
    let long = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
        crate::send_msg(w, 2u64);
    });
    let short = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });
    let vis = names(&["main", "w"]);
    let wl = wobs(&long, &vis).unwrap();
    let ws = wobs(&short, &vis).unwrap();

    assert!(order_is_reflected(&long, &short, &wl, &ws, &vis));
    assert!(!follows(&long, &short, &wl, &ws, &vis));
    assert!(follows(&short, &long, &ws, &wl, &vis));
    assert!(!matches(&short, &long, &ws, &wl, &vis));
}

// ===========================================================================
// (M3)
// ===========================================================================

/// A visible thread that fails an assertion and then exits is *errored*, not
/// *done* — on a graph from a real run, because the `… BLK Assert, END` row is
/// engine behaviour and a hand-built graph asserting it proves only that the
/// author believed it.
#[test]
fn m3_errored_beats_done_on_a_real_run() {
    let config = Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_keep_going_after_error(true)
        .build();
    let g = run_once(config, || {
        named("w", || crate::assert(false));
    });

    // The premise: the row really does end in `End` after the `Block(Assert)`.
    let vis = names(&["w"]);
    let w = wobs(&g, &vis).unwrap();
    let tid = w.row("w").unwrap().thread().unwrap();
    let row: Vec<String> = (0..g.thread_size(tid) as u32)
        .map(|i| format!("{:?}", g.label(Event::new(tid, i))))
        .collect();
    assert!(
        matches!(g.thread_last(tid), Some(LabelEnum::End(_))),
        "the premise of the row scan does not hold on this tree; row = {row:?}"
    );

    assert_eq!(
        statuses(&g, &w, &vis).unwrap()["w"],
        Status::Errored,
        "a last-label rule called an errored visible thread done; row = {row:?}"
    );
}

/// (M3) is restricted to `Tvis`: an invisible thread left blocked on one side
/// against an invisible thread that finished on the other must not matter.
#[test]
fn m3_ignores_invisible_threads() {
    let stuck_invisible = run_once(fifo(), || {
        named("v", || {});
        named("hidden", || {
            let _: u64 = crate::recv_msg_block();
        });
    });
    let finished_invisible = run_once(fifo(), || {
        named("v", || {});
        named("hidden", || {});
    });

    let vis = names(&["v"]);
    let w1 = wobs(&stuck_invisible, &vis).unwrap();
    let w2 = wobs(&finished_invisible, &vis).unwrap();

    // Not vacuous: the invisible threads really do differ in status.
    let all = names(&["v", "hidden"]);
    let a1 = wobs(&stuck_invisible, &all).unwrap();
    let a2 = wobs(&finished_invisible, &all).unwrap();
    assert_eq!(
        statuses(&stuck_invisible, &a1, &all).unwrap()["hidden"],
        Status::Blocked
    );
    assert_eq!(
        statuses(&finished_invisible, &a2, &all).unwrap()["hidden"],
        Status::Done
    );

    assert!(statuses_agree(
        &statuses(&stuck_invisible, &w1, &vis).unwrap(),
        &statuses(&finished_invisible, &w2, &vis).unwrap()
    ));
}

/// (M3) on a graph that is plainly not complete must not answer.
#[test]
#[should_panic(expected = "requires a complete execution")]
fn m3_refuses_a_partial_graph() {
    // A probe leaves every thread parked at its first choice point, so the
    // spawned thread's last label is its `Begin`.
    let (_offers, graph) = probe_from(fifo(), ExecutionGraph::default(), || {
        named("w", || crate::send_msg(main_thread_id(), 1u64));
        let _: u64 = crate::recv_msg_block();
    });
    let vis = names(&["w"]);
    let w = wobs(&graph, &vis).unwrap();
    let _ = statuses(&graph, &w, &vis);
}

/// The half of the completeness precondition that is **not** enforced.
///
/// `is_complete` exempts `main`, because main never gets an `End` label. So a
/// graph in which every spawned thread has stopped but `main` is parked
/// mid-execution passes the assertion, and `main` — the reserved visible name
/// of §8's own worked example — is reported *done* while it is sitting on an
/// uninstalled send.
///
/// This is a genuine wrong answer rather than a refusal. It is latent in S2
/// because nothing here calls `statuses`; `Done` (S3) guards it by requiring
/// the probe to offer nothing. Pinned so the guard cannot be dropped silently.
#[test]
fn m3_reports_a_parked_main_as_done() {
    let (offers, graph) = probe_from(fifo(), ExecutionGraph::default(), || {
        named("w", || {});
        crate::send_msg(main_thread_id(), 1u64);
    });
    assert_eq!(offers.len(), 1, "main should have parked at its send");
    assert_eq!(offers[0].pos().thread, main_thread_id());

    let vis = names(&["main"]);
    let w = wobs(&graph, &vis).unwrap();
    assert_eq!(
        statuses(&graph, &w, &vis).unwrap()["main"],
        Status::Done,
        "if this now fails, the precondition grew a check — good"
    );
}

// ===========================================================================
// (S1) probe mode
// ===========================================================================

macro_rules! no_user_code_past {
    ($name:ident, $counter:ident, $body:expr) => {
        static $counter: AtomicUsize = AtomicUsize::new(0);

        /// A side effect planted immediately after the choice point must not
        /// happen in a probe (O7(i)).
        #[test]
        // `coin_toss` is deprecated in favour of `nondet()`, but it is still a
        // public path to `handle_ctoss` and therefore still has to park.
        #[allow(deprecated)]
        fn $name() {
            $counter.store(0, Ordering::SeqCst);
            let offers = probe_once(fifo(), $body);
            assert!(
                !offers.is_empty(),
                "nothing parked, so the flag could not have been set anyway"
            );
            assert_eq!(
                $counter.load(Ordering::SeqCst),
                0,
                "user code ran past a choice point in a probe"
            );
        }
    };
}

no_user_code_past!(s1_send_parks_before_user_code, PAST_SEND, || {
    let w = named("w", || {
        let _: u64 = crate::recv_msg_block();
    });
    crate::send_msg(w, 1u64);
    PAST_SEND.fetch_add(1, Ordering::SeqCst);
});

no_user_code_past!(s1_blocking_recv_parks_before_user_code, PAST_RECV_B, || {
    let m = main_thread_id();
    named("w", move || crate::send_msg(m, 1u64));
    let _: u64 = crate::recv_msg_block();
    PAST_RECV_B.fetch_add(1, Ordering::SeqCst);
});

no_user_code_past!(
    s1_non_blocking_recv_parks_before_user_code,
    PAST_RECV_NB,
    || {
        let _: Option<u64> = crate::recv_msg();
        PAST_RECV_NB.fetch_add(1, Ordering::SeqCst);
    }
);

no_user_code_past!(s1_nondet_bool_parks_before_user_code, PAST_NONDET, || {
    let _ = crate::nondet();
    PAST_NONDET.fetch_add(1, Ordering::SeqCst);
});

no_user_code_past!(s1_coin_toss_parks_before_user_code, PAST_TOSS, || {
    let _ = crate::coin_toss();
    PAST_TOSS.fetch_add(1, Ordering::SeqCst);
});

no_user_code_past!(s1_choice_range_parks_before_user_code, PAST_CHOICE, || {
    use crate::Nondet;
    let _ = (0usize..3usize).nondet();
    PAST_CHOICE.fetch_add(1, Ordering::SeqCst);
});

// `RangeInclusive<usize>::nondet` is a *separate* `impl` from `Range`'s, with
// its own park site (lib.rs:1657). The exclusive-range test above does not
// reach it. Gap found by review round 1 (M2) and closed by the lead.
no_user_code_past!(
    s1_choice_range_inclusive_parks_before_user_code,
    PAST_RANGE_INC,
    || {
        use crate::Nondet;
        let _ = (0usize..=3usize).nondet();
        PAST_RANGE_INC.fetch_add(1, Ordering::SeqCst);
    }
);

no_user_code_past!(s1_named_nondet_parks_before_user_code, PAST_NAMED, || {
    let _ = crate::named_nondet("retry");
    PAST_NAMED.fetch_add(1, Ordering::SeqCst);
});

/// A blocking receive with nothing to read is **not** offered, is recorded as a
/// `Block(Value)`, and extracts as *blocked*.
#[test]
fn s1_blocking_receive_with_no_source_is_blocked_not_offered() {
    let (offers, graph) = probe_from(fifo(), ExecutionGraph::default(), || {
        named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
    });
    assert!(
        offers.is_empty(),
        "a receive nothing can satisfy was offered: {:?}",
        offers.iter().map(|o| o.kind()).collect::<Vec<_>>()
    );

    let vis = names(&["w"]);
    let w = wobs(&graph, &vis).unwrap();
    let tid = w.row("w").unwrap().thread().unwrap();
    assert!(
        matches!(graph.thread_last(tid), Some(LabelEnum::Block(_))),
        "no Block was installed for the disabled receive"
    );
    assert_eq!(statuses(&graph, &w, &vis).unwrap()["w"], Status::Blocked);
    assert_eq!(shape(&w, "w"), Vec::<String>::new());
}

/// Probing twice from the same graph gives the same answer and the same graph.
#[test]
fn s1_reprobing_is_idempotent() {
    let program = || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    };
    let (o1, g1) = probe_from(fifo(), ExecutionGraph::default(), program);
    let (o2, g2) = probe_from(fifo(), ExecutionGraph::default(), program);

    let key = |os: &[crate::conformance::probe::Offer]| {
        let mut v: Vec<(String, Event)> =
            os.iter().map(|o| (o.kind().to_owned(), o.pos())).collect();
        v.sort();
        v
    };
    assert!(!o1.is_empty());
    assert_eq!(key(&o1), key(&o2));
    assert_eq!(sizes(&g1), sizes(&g2));
}

/// Probing against a **non-empty** graph: the prefix replays, and the offers
/// are the ones past it.
///
/// Criterion 6 lists this as untested at the end of S1.
#[test]
fn s1_probe_against_a_non_empty_graph_advances_the_frontier() {
    let program = || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
        crate::send_msg(w, 2u64);
    };

    let (first, g0) = probe_from(fifo(), ExecutionGraph::default(), program);
    let main_offer = first
        .iter()
        .find(|o| o.pos().thread == main_thread_id())
        .expect("main parks at its first send");
    let first_pos = main_offer.pos();

    let g1 = crate::conformance::prober::install(fifo(), g0, main_offer);
    let (second, _g2) = probe_from(fifo(), g1, program);

    let main_again = second
        .iter()
        .find(|o| o.pos().thread == main_thread_id())
        .expect("main parks again, at its second send");
    assert_eq!(
        main_again.pos().index,
        first_pos.index + 1,
        "the second probe did not resume past the installed prefix"
    );
    assert_eq!(main_again.kind(), "send");
}

/// A blocking receive whose source does not exist yet blocks; once the source
/// is installed the **same position** becomes a receive offer.
///
/// This is the order-of-operations case the design leans on hardest and that
/// nothing in `offers(H)` can be read off statically: a `Block(Value)` lands in
/// `H` on the first probe, and a later probe against an extended `H` has to
/// supersede it rather than replay it. If the block were replayed, a
/// specification could never receive anything the search installed, and the
/// search would silently only ever find `⊥` executions.
///
/// The asking-leaves-no-trace property of `recv_sources` rides along, because
/// this is the first graph on which there is a receive offer to ask about.
#[test]
fn s1_an_installed_send_supersedes_an_earlier_block() {
    let program = || {
        let m = main_thread_id();
        named("w", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    };

    let (first, g0) = probe_from(fifo(), ExecutionGraph::default(), program);
    assert!(
        first.iter().all(|o| o.kind() != "recv"),
        "main's receive was offered although no send exists to satisfy it"
    );
    assert!(
        matches!(g0.thread_last(main_thread_id()), Some(LabelEnum::Block(_))),
        "no Block(Value) was installed for the unsatisfiable receive"
    );

    let send = first
        .iter()
        .find(|o| o.kind() == "send")
        .expect("`w` parks at its send");
    let g1 = crate::conformance::prober::install(fifo(), g0, send);

    let (second, g2) = probe_from(fifo(), g1, program);
    let recv = second
        .iter()
        .find(|o| o.kind() == "recv")
        .unwrap_or_else(|| {
            panic!(
                "the receive is still not offered after its source was \
                 installed; offers were {:?}",
                second.iter().map(|o| o.kind()).collect::<Vec<_>>()
            )
        });
    assert_eq!(recv.pos().thread, main_thread_id());
    assert_eq!(recv.sources().len(), 1, "sources {:?}", recv.sources());
    assert!(
        !recv.may_read_nothing(),
        "a blocking receive was offered ⊥ as an option"
    );

    // Asking the graph the same question changes nothing about it.
    let before = sizes(&g2);
    let sources = crate::conformance::prober::recv_sources(fifo(), &g2, recv);
    assert_eq!(before, sizes(&g2), "asking changed the graph");
    assert_eq!(
        sources,
        recv.sources(),
        "the graph-only enumeration disagrees with the offer's own"
    );
}

/// The offer *set* does not depend on the order the threads were spawned in.
///
/// Keyed by declared name, not by `ThreadId` or by kind: three offers all of
/// kind `send` would compare equal under any permutation whatsoever, which is
/// the vacuous version of this test.
#[test]
fn s1_offer_set_is_independent_of_spawn_order() {
    let key = |(offers, g): (Vec<crate::conformance::probe::Offer>, ExecutionGraph)| {
        let mut v: Vec<(String, &'static str)> = offers
            .iter()
            .map(|o| {
                let tclab = g.get_thread_tclab(o.pos().thread);
                let name = tclab.name().clone().unwrap_or_else(|| "?".to_owned());
                (name, o.kind())
            })
            .collect();
        v.sort();
        v
    };
    let pq = key(probe_from(fifo(), ExecutionGraph::default(), || {
        let p = named("p", || crate::send_msg(main_thread_id(), 1u64));
        named("q", || crate::send_msg(main_thread_id(), 2u64));
        crate::send_msg(p, 3u64);
    }));
    let qp = key(probe_from(fifo(), ExecutionGraph::default(), || {
        named("q", || crate::send_msg(main_thread_id(), 2u64));
        let p = named("p", || crate::send_msg(main_thread_id(), 1u64));
        crate::send_msg(p, 3u64);
    }));
    assert_eq!(
        pq,
        vec![
            ("main".to_owned(), "send"),
            ("p".to_owned(), "send"),
            ("q".to_owned(), "send"),
        ]
    );
    assert_eq!(pq, qp);
}

/// The sources a receive is offered are the model's, not a fixed list.
///
/// Two sends from one thread to one receiver: under `Bag` both are readable,
/// under `FIFO` and `Causal` only the first. Derived from the models, and it is
/// what makes "conformance is scoped to asyn/p2p/cd" more than a config check —
/// almost everything else in the module runs under `FIFO` alone.
#[test]
fn s1_receive_source_sets_follow_the_model() {
    for (cons, expected) in [
        (ConsType::Bag, 2usize),
        (ConsType::FIFO, 1),
        (ConsType::Causal, 1),
    ] {
        let config = cfg(cons);
        let program = || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
            crate::send_msg(w, 2u64);
        };

        // Install both of main's sends, one probe at a time.
        let mut graph = ExecutionGraph::default();
        for step in 0..2 {
            let (offers, g) = probe_from(config.clone(), graph, program);
            let send = offers
                .iter()
                .find(|o| o.pos().thread == main_thread_id() && o.kind() == "send")
                .unwrap_or_else(|| panic!("{cons:?}: main did not park at send {step}"));
            graph = crate::conformance::prober::install(config.clone(), g, send);
        }

        let (offers, _) = probe_from(config.clone(), graph, program);
        let recv = offers
            .iter()
            .find(|o| o.kind() == "recv")
            .unwrap_or_else(|| panic!("{cons:?}: `w`'s receive was not offered"));
        assert_eq!(
            recv.sources().len(),
            expected,
            "{cons:?}: sources were {:?}",
            recv.sources()
        );
    }
}

/// Mailbox is out of scope, and the constructor-side assertion is what
/// guarantees it — a `Config` can reach a `Must` without passing any builder.
#[test]
#[should_panic(expected = "mailbox is out of scope")]
fn s1_mailbox_config_is_refused_at_the_constructor() {
    let _ = probe_once(cfg(ConsType::Mailbox), || {});
}

/// `inbox` is outside conformance scope and must be refused during a probe.
#[test]
#[should_panic(expected = "outside conformance scope")]
fn s1_inbox_is_refused_during_a_probe() {
    let _ = probe_once(fifo(), || {
        let _ = crate::inbox();
    });
}

/// Probe mode must be inert when it is off: the same program run through the
/// ordinary path installs the labels the probe withheld.
#[test]
fn s1_ordinary_runs_are_unaffected() {
    let program = || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    };
    let graph = run_once(fifo(), program);
    let vis = names(&["main", "w"]);
    let w = wobs(&graph, &vis).unwrap();
    assert_eq!(shape(&w, "main").len(), 1);
    assert_eq!(shape(&w, "w").len(), 1);
    assert_eq!(statuses(&graph, &w, &vis).unwrap()["w"], Status::Done);
}

// ===========================================================================
// Identity, ⊥, and the shapes that only the install path can build
// ===========================================================================

/// A graph matches itself.
///
/// Trivial-looking, and the first thing a morphism must do. It is here because
/// the next test shows it is not free.
#[test]
fn m1_a_graph_matches_itself() {
    let g = run_once(fifo(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });
    let vis = names(&["main", "w"]);
    let w = wobs(&g, &vis).unwrap();
    assert_eq!(shape(&w, "main").len(), 1);
    assert_eq!(shape(&w, "w").len(), 1);
    assert!(matches(&g, &g, &w, &w, &vis));
    assert!(follows(&g, &g, &w, &w, &vis));
}

/// A message type whose `PartialEq` is not reflexive makes a graph fail to
/// match **itself**.
///
/// `Obs`'s value comparison is the engine's `msg_equals`, which is the user's
/// `PartialEq`. `f64` is an ordinary `Message`, and `NaN != NaN`, so a
/// specification execution that is literally the implementation execution is
/// rejected and the program is reported as non-conforming with no diagnostic.
/// The draft has no such values — `Val` is a finite set compared by equality —
/// so this is a fragment obligation TraceForge does not enforce, not an
/// arithmetic accident. Pinned as observed behaviour; the assertion is written
/// so that a later well-formedness check turns it red.
#[test]
fn m1_non_reflexive_message_equality_defeats_self_matching() {
    let g = run_once(fifo(), || {
        let w = named("w", || {
            let _: f64 = crate::recv_msg_block();
        });
        crate::send_msg(w, f64::NAN);
    });
    let vis = names(&["main", "w"]);
    let w = wobs(&g, &vis).unwrap();
    assert_eq!(shape(&w, "main").len(), 1);
    assert!(
        !observations_match(&w, &w, &vis),
        "if this now fails, a well-formedness check on message values landed"
    );
}

/// `⊥` and a value are different observations.
///
/// Built through `install_recv`, because a plain run cannot be made to take one
/// arm rather than the other on demand — and `⊥` against a real value is the
/// comparison a `Recv(Option<Val>)` that compared only the inner value would
/// get wrong in the direction nobody tests.
#[test]
fn m1_bottom_and_a_value_are_different_observations() {
    fn program() {
        let w = named("w", || {
            let _: Option<u64> = crate::recv_msg();
        });
        crate::send_msg(w, 1u64);
    }

    // Install main's send so that `w`'s receive has a source to choose from.
    let (first, g0) = probe_from(fifo(), ExecutionGraph::default(), program);
    let send = first
        .iter()
        .find(|o| o.kind() == "send")
        .expect("main parks at its send");
    let g1 = crate::conformance::prober::install(fifo(), g0, send);

    let (second, g2) = probe_from(fifo(), g1, program);
    let recv = second
        .iter()
        .find(|o| o.kind() == "recv")
        .expect("`w`'s non-blocking receive is offered");
    assert!(
        recv.may_read_nothing(),
        "a non-blocking receive was not offered ⊥"
    );
    let source = *recv.sources().first().expect("one source");

    let read_something =
        crate::conformance::prober::install_recv(fifo(), g2.clone(), recv, Some(source));
    let read_nothing = crate::conformance::prober::install_recv(fifo(), g2, recv, None);

    let vis = names(&["w"]);
    let ws = wobs(&read_something, &vis).unwrap();
    let wn = wobs(&read_nothing, &vis).unwrap();
    assert_eq!(shape(&ws, "w").len(), 1, "{:?}", shape(&ws, "w"));
    assert_eq!(shape(&wn, "w").len(), 1, "{:?}", shape(&wn, "w"));
    assert!(
        !observations_match(&ws, &wn, &vis),
        "⊥ and a value compared equal: {:?} vs {:?}",
        shape(&ws, "w"),
        shape(&wn, "w")
    );
}

/// A parked choice point installs **no** label (O7(ii)).
#[test]
fn s1_a_parked_choice_point_installs_no_label() {
    let (offers, graph) = probe_from(fifo(), ExecutionGraph::default(), || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    });
    assert_eq!(offers.len(), 1);
    assert_eq!(offers[0].kind(), "send");

    for t in graph.thread_ids() {
        for i in 0..graph.thread_size(t) as u32 {
            assert!(
                !matches!(graph.label(Event::new(t, i)), LabelEnum::SendMsg(_)),
                "the parked send was installed after all, at {:?}",
                Event::new(t, i)
            );
        }
    }
    // The offer sits at the frontier of a row the probe left untouched. Note
    // what this does **not** establish: it does not observe `prev_pos` giving
    // the position back. `prev_pos` moves the runtime's instruction counter,
    // not the graph, so this assertion holds with `prev_pos` deleted — that is
    // finding F-3, and S1's criterion 2 now records the clause as
    // unobservable rather than checked. Claiming otherwise here would rebuild
    // the false record the criterion was corrected for.
    assert_eq!(
        offers[0].pos().index as usize,
        graph.thread_size(offers[0].pos().thread)
    );
}

/// Driving a program to completion through probe + install produces the same
/// per-thread sequence of label **kinds** as a plain run of it.
///
/// A partial discharge of §11.1's "probe-driven event sequences equal to plain
/// runs'", and the limitation is the point: this compares kinds only — the
/// other variants are collapsed to `OTHER` — so it does **not** establish
/// O8's install canonicality, which is about rf, values and clocks agreeing
/// too. A discrepancy here would still mean the search explores graphs the
/// engine never would, and the likeliest shape of one is a leftover
/// `Block(Value)` from the probe that first found the receive disabled, which
/// is what this does catch.
#[test]
fn s1_probe_driven_label_kinds_equal_a_plain_runs() {
    fn program() {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    }

    let mut graph = ExecutionGraph::default();
    for round in 0..8 {
        let (offers, g) = probe_from(fifo(), graph, program);
        if offers.is_empty() {
            graph = g;
            break;
        }
        let o = &offers[0];
        graph = if o.kind() == "recv" {
            crate::conformance::prober::install_recv(fifo(), g, o, o.sources().first().copied())
        } else {
            crate::conformance::prober::install(fifo(), g, o)
        };
        assert!(round < 7, "the install loop did not converge");
    }

    let plain = run_once(fifo(), program);
    assert_eq!(
        row_kinds(&graph),
        row_kinds(&plain),
        "probe-driven graph differs from the plain run's"
    );
}

/// Per declared thread name, the sequence of label kinds in its row.
fn row_kinds(g: &ExecutionGraph) -> Vec<(String, Vec<&'static str>)> {
    let mut out: Vec<(String, Vec<&'static str>)> = g
        .thread_ids()
        .into_iter()
        .map(|t| {
            let tclab = g.get_thread_tclab(t);
            let name = tclab.name().clone().unwrap_or_else(|| format!("{t:?}"));
            let kinds = (0..g.thread_size(t) as u32)
                .map(|i| match g.label(Event::new(t, i)) {
                    LabelEnum::Begin(_) => "BEGIN",
                    LabelEnum::End(_) => "END",
                    LabelEnum::TCreate(_) => "TCREATE",
                    LabelEnum::TJoin(_) => "TJOIN",
                    LabelEnum::SendMsg(_) => "SEND",
                    LabelEnum::RecvMsg(_) => "RECV",
                    LabelEnum::Block(_) => "BLOCK",
                    _ => "OTHER",
                })
                .collect();
            (name, kinds)
        })
        .collect();
    out.sort();
    out
}
