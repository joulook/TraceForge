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
    statuses_agree, CompleteExecution, Status,
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
        statuses(
            CompleteExecution::assume_finished_at_gate(&blocking),
            &wb,
            &vis
        )
        .unwrap()["w"],
        Status::Blocked
    );
    assert_eq!(
        statuses(
            CompleteExecution::assume_finished_at_gate(&non_blocking),
            &wn,
            &vis
        )
        .unwrap()["w"],
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
        statuses(CompleteExecution::assume_finished_at_gate(&g), &w, &vis),
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
        statuses(CompleteExecution::assume_finished_at_gate(&g), &w, &vis).unwrap()["w"],
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
        statuses(
            CompleteExecution::assume_finished_at_gate(&stuck_invisible),
            &a1,
            &all
        )
        .unwrap()["hidden"],
        Status::Blocked
    );
    assert_eq!(
        statuses(
            CompleteExecution::assume_finished_at_gate(&finished_invisible),
            &a2,
            &all
        )
        .unwrap()["hidden"],
        Status::Done
    );

    assert!(statuses_agree(
        &statuses(
            CompleteExecution::assume_finished_at_gate(&stuck_invisible),
            &w1,
            &vis
        )
        .unwrap(),
        &statuses(
            CompleteExecution::assume_finished_at_gate(&finished_invisible),
            &w2,
            &vis
        )
        .unwrap()
    ));
}

/// (M3) on a graph that is plainly not complete must not answer.
///
/// Since F33 was fixed this is a *typed* refusal rather than a panic: the
/// graph cannot produce a `CompleteExecution`, so `statuses` is unreachable
/// for it. A parked spawned thread's last label is its `Begin`, which fails
/// the spawned-thread check outright.
#[test]
fn m3_refuses_a_partial_graph() {
    let probed = probe_from(fifo(), ExecutionGraph::default(), || {
        named("w", || crate::send_msg(main_thread_id(), 1u64));
        let _: u64 = crate::recv_msg_block();
    });
    assert!(
        CompleteExecution::try_finished(probed.graph()).is_none(),
        "a probe-parked spawned thread must not witness completeness"
    );
    assert!(
        probed.complete().is_none(),
        "and neither does a probe with offers outstanding"
    );
}

/// **F33, fixed** — the case that motivated the witness type.
///
/// `is_complete` must exempt `main` (it never gets an `End` label, A8), so a
/// graph in which every *spawned* thread has stopped but main is parked passes
/// the checkable half. It used to reach `statuses` and be answered `Done`.
/// Now the specification side is witnessed by an exhausted probe instead, and
/// a probe with offers outstanding is refused.
#[test]
fn m3_no_longer_reports_a_parked_main_as_done() {
    let probed = probe_from(fifo(), ExecutionGraph::default(), || {
        named("w", || {});
        crate::send_msg(main_thread_id(), 1u64);
    });
    assert_eq!(
        probed.offers().len(),
        1,
        "main should have parked at its send"
    );
    assert_eq!(probed.offers()[0].pos().thread, main_thread_id());

    // The checkable half still passes — it is not what saves us.
    assert!(CompleteExecution::try_finished(probed.graph()).is_some());
    // The real witness refuses.
    assert!(probed.complete().is_none());
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
    let probed = probe_from(fifo(), ExecutionGraph::default(), || {
        named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
    });
    assert!(
        probed.offers().is_empty(),
        "a receive nothing can satisfy was offered: {:?}",
        probed.offers().iter().map(|o| o.kind()).collect::<Vec<_>>()
    );

    let vis = names(&["w"]);
    let w = wobs(probed.graph(), &vis).unwrap();
    let tid = w.row("w").unwrap().thread().unwrap();
    assert!(
        matches!(probed.graph().thread_last(tid), Some(LabelEnum::Block(_))),
        "no Block was installed for the disabled receive"
    );
    // Through the real witness: this probe is exhausted, so it has one. Going
    // via `assume_finished_at_gate` here would be the F33 pattern, and it is
    // what review round 2 found this test doing.
    let exec = probed
        .complete()
        .expect("an exhausted probe of a blocked program is a complete execution");
    assert_eq!(statuses(exec, &w, &vis).unwrap()["w"], Status::Blocked);
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
    let (o1, g1) = probe_from(fifo(), ExecutionGraph::default(), program).into_parts();
    let (o2, g2) = probe_from(fifo(), ExecutionGraph::default(), program).into_parts();

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

    let (first, g0) = probe_from(fifo(), ExecutionGraph::default(), program).into_parts();
    let main_offer = first
        .iter()
        .find(|o| o.pos().thread == main_thread_id())
        .expect("main parks at its first send");
    let first_pos = main_offer.pos();

    let g1 = crate::conformance::prober::install(fifo(), g0, main_offer);
    let (second, _g2) = probe_from(fifo(), g1, program).into_parts();

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

    let (first, g0) = probe_from(fifo(), ExecutionGraph::default(), program).into_parts();
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

    let (second, g2) = probe_from(fifo(), g1, program).into_parts();
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
    let key_of = |probed: crate::conformance::prober::Probed| {
        let (offers, g) = probed.into_parts();
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
    let pq = key_of(probe_from(fifo(), ExecutionGraph::default(), || {
        let p = named("p", || crate::send_msg(main_thread_id(), 1u64));
        named("q", || crate::send_msg(main_thread_id(), 2u64));
        crate::send_msg(p, 3u64);
    }));
    let qp = key_of(probe_from(fifo(), ExecutionGraph::default(), || {
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
            let (offers, g) = probe_from(config.clone(), graph, program).into_parts();
            let send = offers
                .iter()
                .find(|o| o.pos().thread == main_thread_id() && o.kind() == "send")
                .unwrap_or_else(|| panic!("{cons:?}: main did not park at send {step}"));
            graph = crate::conformance::prober::install(config.clone(), g, send);
        }

        let (offers, _) = probe_from(config.clone(), graph, program).into_parts();
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
    assert_eq!(
        statuses(CompleteExecution::assume_finished_at_gate(&graph), &w, &vis).unwrap()["w"],
        Status::Done
    );
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
    let (first, g0) = probe_from(fifo(), ExecutionGraph::default(), program).into_parts();
    let send = first
        .iter()
        .find(|o| o.kind() == "send")
        .expect("main parks at its send");
    let g1 = crate::conformance::prober::install(fifo(), g0, send);

    let (second, g2) = probe_from(fifo(), g1, program).into_parts();
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
    })
    .into_parts();
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
        let (offers, g) = probe_from(fifo(), graph, program).into_parts();
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

// ===========================================================================
// (S1, F35) installing a chosen nondet value
//
// Written against `conf-plan.md` §5.2/§5.5 and `alg.tex`'s `ln:innernd` +
// `SetND` before reading `probe.rs`/`prober.rs`/`must.rs`. The properties
// derived there, and which test carries each:
//
//   D1  `nondet_values` is the operator's whole domain S, not the value the
//       probe rolled (`ln:innernd` loops `for v ∈ S`; §5.1 "with its value
//       range"). --- s1nd_toss_offers_both_booleans_*, s1nd_choice_offers_*
//   D2  empty for a non-nondet offer.  --- s1nd_non_nondet_offers_*
//   D3  no duplicates, stable order.   --- folded into D1's tests
//   D4  install fixes the value, for every v ∈ S and especially for v the
//       probe did *not* produce.       --- s1nd_installing_a_toss_takes_*,
//                                          s1nd_installing_a_choice_takes_*
//   D5  install adds exactly one event, at the frontier, last in the row
//       (`alg.tex:728`, `alg.tex:1081` "SetND ... leav[es] |G.E| ... alone").
//                                      --- s1nd_installing_a_value_adds_*
//   D6  nothing else moves: no other label's value, no rf, no stamp
//       (§5.2 "no later views exist to repair --- only its own clocks").
//                                      --- s1nd_installing_a_value_disturbs_*
//   D7  the frontier is a precondition, not an assumption (§3 item 11).
//                                      --- s1nd_reinstalling_a_stale_*
//   D8  wrong-kind and out-of-range are rejected loudly, never coerced.
//                                      --- s1nd_out_of_range_*, s1nd_wrong_kind_*
//   D9  siblings do not disturb each other (§5.2 "cloning H at every branch
//       point"; `alg.tex:940`).        --- s1nd_sibling_installs_*
//   D10 probe -> install(v) -> probe advances the program down v's branch.
//       This is the property F35 exists for; a test that only checks the
//       graph grew would miss it.      --- s1nd_installed_*_selects_the_branch
//   D11 a nondet is invisible to the morphism, so installing one adds no
//       observation (`alg.tex:851`).   --- s1nd_installing_a_value_adds_no_obs
//   D12 the two cases of `NondetValue` are told apart.
//                                      --- s1nd_nondet_value_cases_are_distinct
// ===========================================================================

use crate::conformance::probe::{NondetValue, Offer};
use crate::conformance::prober::{install, install_nondet, install_recv};

/// The value a `CToss`/`Choice` offer's own label carries --- what the probe
/// produced. Read so the tests below can assert the *other* value is offered
/// and installable, which is the case `install_nondet` exists for.
fn offered_value(o: &Offer) -> NondetValue {
    match o.label() {
        LabelEnum::CToss(c) => NondetValue::Toss(c.result()),
        LabelEnum::Choice(c) => NondetValue::Choice(c.result()),
        other => panic!("not a nondet offer: {other}"),
    }
}

/// The value stored on a nondet label in a graph.
fn value_at(g: &ExecutionGraph, pos: Event) -> NondetValue {
    match g.label(pos) {
        LabelEnum::CToss(c) => NondetValue::Toss(c.result()),
        LabelEnum::Choice(c) => NondetValue::Choice(c.result()),
        other => panic!("not a nondet label at {pos}: {other}"),
    }
}

/// Everything about a graph that installing a *value* must leave alone:
/// per event its kind, its rf (for a receive), its stamp, and the value of
/// any nondet. Deliberately not `format!("{g}")` --- Display is a diagnostic,
/// and a check on it could pass while the fields the search reads moved.
fn fingerprint(g: &ExecutionGraph) -> Vec<(Event, String, Option<Event>, usize)> {
    let mut out = Vec::new();
    for t in g.thread_ids() {
        for i in 0..g.thread_size(t) as u32 {
            let e = Event::new(t, i);
            let lab = g.label(e);
            let rf = match lab {
                LabelEnum::RecvMsg(r) => r.rf(),
                _ => None,
            };
            let desc = match lab {
                LabelEnum::CToss(c) => format!("CToss({})", c.result()),
                LabelEnum::Choice(c) => format!("Choice({} of {:?})", c.result(), c.range()),
                other => format!("{other}"),
            };
            out.push((e, desc, rf, lab.stamp()));
        }
    }
    out
}

/// One probe of `f` from `g`, returning the offers and the probe's graph.
fn probe(g: ExecutionGraph, f: fn()) -> (Vec<Offer>, ExecutionGraph) {
    probe_from(fifo(), g, f).into_parts()
}

/// Exactly one offer, which must be a nondet.
fn one_nondet_offer(g: ExecutionGraph, f: fn()) -> (Offer, ExecutionGraph) {
    let (offers, g) = probe(g, f);
    assert_eq!(offers.len(), 1, "expected one offer, got {offers:?}");
    let o = offers.into_iter().next().unwrap();
    assert!(
        matches!(o.kind(), "nondet" | "choice"),
        "expected a nondet offer, got {}",
        o.kind()
    );
    (o, g)
}

// --- the programs -----------------------------------------------------------

/// A boolean choice whose two branches offer *different kinds* next, so the
/// next probe's offers say which branch was taken --- the D10 instrument.
fn toss_branches() {
    use crate::Nondet;
    let w = named("w", || {
        let _: u64 = crate::recv_msg_block();
    });
    if crate::nondet() {
        crate::send_msg(w, 1u64);
    } else {
        let _ = (0usize..3usize).nondet();
    }
}

/// The same for a three-way range: value 0 sends, 1 tosses, 2 does nothing.
fn choice_branches() {
    use crate::Nondet;
    let w = named("w", || {
        let _: u64 = crate::recv_msg_block();
    });
    match (0usize..3usize).nondet() {
        0 => crate::send_msg(w, 1u64),
        1 => {
            let _ = crate::nondet();
        }
        _ => {}
    }
}

/// `alg.tex`'s `ex:restart`, as a program: the chosen value is *sent*, so the
/// installed value shows up as an observation rather than only as a branch.
fn restart_spec() {
    use crate::Nondet;
    let c = named("c", || {});
    named("a", move || {
        let n = (5usize..=6usize).nondet();
        crate::send_msg(c, n as u64);
    });
}

fn a_single_toss() {
    let _ = crate::nondet();
}

fn a_named_toss() {
    let _ = crate::named_nondet("retry");
}

fn an_inclusive_choice() {
    use crate::Nondet;
    let _ = (5usize..=7usize).nondet();
}

fn a_singleton_choice() {
    use crate::Nondet;
    let _ = (4usize..=4usize).nondet();
}

fn a_send_and_a_recv() {
    let m = main_thread_id();
    named("w", move || crate::send_msg(m, 1u64));
    let _: u64 = crate::recv_msg_block();
}

// --- D1/D3: the domain, not the roll ----------------------------------------

/// A `CToss` offers **both** booleans, whichever one the probe rolled.
///
/// The adversarial half is the last assertion: an implementation that echoed
/// the probe's own value --- the path of least resistance F35 names --- would
/// satisfy "the offer is non-empty" and "the offer contains the rolled value"
/// and still lose completeness. Asserting the *complement* is present is what
/// separates an option set from a commitment.
#[test]
fn s1nd_toss_offers_both_booleans_whatever_the_probe_rolled() {
    for prog in [a_single_toss as fn(), a_named_toss as fn()] {
        let (o, _) = one_nondet_offer(ExecutionGraph::default(), prog);
        let values = o.nondet_values();
        assert_eq!(
            values,
            vec![NondetValue::Toss(false), NondetValue::Toss(true)],
            "a toss must offer its whole domain in a stable order"
        );
        let NondetValue::Toss(rolled) = offered_value(&o) else {
            panic!("a CToss offer carried a Choice value");
        };
        assert!(
            values.contains(&NondetValue::Toss(!rolled)),
            "the offer echoes the probe's roll ({rolled}) instead of offering the domain"
        );
    }
}

/// An exclusive range `0..3` offers exactly 0, 1, 2 --- three values, not four
/// and not two. `Range::nondet` converts to `RangeInclusive::new(start, end-1)`
/// (lib.rs), so an enumerator written against the *user's* range or against a
/// half-open reading of the label's would be off by one at one end or the other.
#[test]
fn s1nd_choice_offers_every_value_of_an_exclusive_range() {
    let (o, _) = one_nondet_offer(ExecutionGraph::default(), choice_branches);
    assert_eq!(
        o.nondet_values(),
        vec![
            NondetValue::Choice(0),
            NondetValue::Choice(1),
            NondetValue::Choice(2)
        ]
    );
}

/// An inclusive range with a non-zero start offers 5, 6, 7 --- the *values*,
/// not the indices. An enumerator written as `0..len` would pass every
/// zero-based test and install a value the program can never produce here.
#[test]
fn s1nd_choice_offers_every_value_of_an_inclusive_nonzero_range() {
    let (o, _) = one_nondet_offer(ExecutionGraph::default(), an_inclusive_choice);
    assert_eq!(
        o.nondet_values(),
        vec![
            NondetValue::Choice(5),
            NondetValue::Choice(6),
            NondetValue::Choice(7)
        ]
    );
}

/// A one-element range offers exactly one value, and it is the element.
/// `b_a` at `ln:innernd` is `max|S|`; a degenerate range that offered zero
/// values would make the branch unreachable and a `SpecVisit` silently return ⊥.
#[test]
fn s1nd_choice_offers_a_singleton_range_exactly_once() {
    let (o, _) = one_nondet_offer(ExecutionGraph::default(), a_singleton_choice);
    assert_eq!(o.nondet_values(), vec![NondetValue::Choice(4)]);
}

// --- D2: nothing for a non-nondet -------------------------------------------

/// A send offer and a receive offer have no values. The `ln:innernd` /
/// `ln:innerrf` / `ln:innersend` cases are disjoint; a send that offered
/// values would make the search dispatch on it twice.
#[test]
fn s1nd_non_nondet_offers_have_no_values() {
    let (offers, g) = probe(ExecutionGraph::default(), a_send_and_a_recv);
    let send = offers.iter().find(|o| o.kind() == "send").expect("a send");
    assert!(send.nondet_values().is_empty(), "send: {send:?}");

    let g = install(fifo(), g, send);
    let (offers, _) = probe(g, a_send_and_a_recv);
    let recv = offers.iter().find(|o| o.kind() == "recv").expect("a recv");
    assert!(recv.nondet_values().is_empty(), "recv: {recv:?}");
}

// --- D4: the install takes --------------------------------------------------

/// Installing a toss stores **that** boolean --- both ways round, including
/// the one the probe did not produce.
///
/// The failing direction: delete the `probe_set_value` call from
/// `install_nondet` and one of the two iterations fails, because the label
/// arrives carrying the probe's own roll.
#[test]
fn s1nd_installing_a_toss_takes_both_ways() {
    for v in [false, true] {
        let (o, g) = one_nondet_offer(ExecutionGraph::default(), toss_branches);
        let pos = o.pos();
        let g = install_nondet(fifo(), g, &o, NondetValue::Toss(v));
        assert_eq!(
            value_at(&g, pos),
            NondetValue::Toss(v),
            "installing Toss({v}) did not take"
        );
    }
}

/// Installing a choice stores **that** value, for every value of the range,
/// from the same probe graph each time.
#[test]
fn s1nd_installing_a_choice_takes_every_value_of_its_range() {
    let (o, g0) = one_nondet_offer(ExecutionGraph::default(), an_inclusive_choice);
    let pos = o.pos();
    for v in o.nondet_values() {
        let g = install_nondet(fifo(), g0.clone(), &o, v);
        assert_eq!(value_at(&g, pos), v, "installing {v:?} did not take");
    }
}

// --- D5/D6: nothing else moves ----------------------------------------------

/// Installing a value adds exactly one event, to the offer's own row, at the
/// end of it --- `alg.tex:1081`: `SetND` "leav[es] |G.E| and the insertion
/// order alone", so the whole growth is the `⊕ e` that precedes it.
#[test]
fn s1nd_installing_a_value_adds_exactly_one_event_at_the_frontier() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), toss_branches);
    let pos = o.pos();
    let before = sizes(&g);
    let after_graph = install_nondet(fifo(), g, &o, NondetValue::Toss(true));
    let after = sizes(&after_graph);

    for (t, n) in &before {
        let m = after
            .iter()
            .find(|(u, _)| u == t)
            .map(|(_, m)| *m)
            .unwrap_or_else(|| panic!("thread {t:?} vanished"));
        let expected = if *t == pos.thread { n + 1 } else { *n };
        assert_eq!(m, expected, "row of {t:?} changed by more than the install");
    }
    assert_eq!(before.len(), after.len(), "a thread appeared");
    assert_eq!(
        pos.index as usize + 1,
        after_graph.thread_size(pos.thread),
        "the installed event is not last in its row"
    );
    assert_eq!(value_at(&after_graph, pos), NondetValue::Toss(true));
}

/// The installed event is stamp-maximal --- the frontier claim §5.2 leans on
/// when it says "no later views exist to repair". If some event carried a
/// larger stamp, the cut-free mutation would be leaving state above the
/// frontier untouched.
#[test]
fn s1nd_the_installed_value_is_stamp_maximal() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), toss_branches);
    let pos = o.pos();
    let g = install_nondet(fifo(), g, &o, NondetValue::Toss(false));
    let mine = g.label(pos).stamp();
    for (e, desc, _, stamp) in fingerprint(&g) {
        if e != pos {
            assert!(
                stamp < mine,
                "{desc} at {e} has stamp {stamp} >= the installed event's {mine}"
            );
        }
    }
}

/// Installing a value leaves every *other* label exactly as it was: same
/// kind, same rf, same stamp, same nondet value. Run on a graph that already
/// holds a receive reading a send, so there is an rf edge available to break.
#[test]
fn s1nd_installing_a_value_disturbs_no_other_label() {
    fn prog() {
        let m = main_thread_id();
        named("w", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
        let _ = crate::nondet();
    }

    // Drive the program to the point where a receive is installed and reading,
    // and the next offer is the toss.
    let (offers, g) = probe(ExecutionGraph::default(), prog);
    let send = offers.iter().find(|o| o.kind() == "send").expect("a send");
    let g = install(fifo(), g, send);
    let (offers, g) = probe(g, prog);
    let recv = offers.iter().find(|o| o.kind() == "recv").expect("a recv");
    let rf = recv.sources().first().copied();
    assert!(rf.is_some(), "the test needs a real rf edge to protect");
    let g = install_recv(fifo(), g, recv, rf);

    let (o, g) = one_nondet_offer(g, prog);
    let pos = o.pos();
    let before = fingerprint(&g);
    let g = install_nondet(fifo(), g, &o, NondetValue::Toss(true));
    let after: Vec<_> = fingerprint(&g).into_iter().filter(|r| r.0 != pos).collect();
    assert_eq!(before, after, "installing a value moved something else");
}

// --- D11: a nondet is invisible ---------------------------------------------

/// Installing a nondet value adds no observation: `Φ` for a non-receive is
/// "`G ⊕ e` follows `G₁`", and `alg.tex:851` says an invisible event always
/// passes it. If a choice point showed up in `wobs` the filter would start
/// rejecting extensions the draft says are free.
#[test]
fn s1nd_installing_a_value_adds_no_observation() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), restart_spec);
    let visible = names(&["a", "c"]);
    let before = wobs(&g, &visible).expect("wobs before");
    let g = install_nondet(fifo(), g, &o, NondetValue::Choice(6));
    let after = wobs(&g, &visible).expect("wobs after");
    assert_eq!(shape(&before, "a"), shape(&after, "a"));
    assert_eq!(shape(&before, "c"), shape(&after, "c"));
}

// --- D10: the branch is actually taken --------------------------------------

/// **The property F35 exists for.** Probe, install a chosen boolean, probe
/// again: the program must resume on *that* branch. The two branches of
/// `toss_branches` offer different kinds next, so the second probe's offers
/// name the branch taken.
///
/// A test that only checked "the graph grew" or "the label says `true`" would
/// pass against an engine that re-rolled the value on replay and ran the other
/// branch --- which is precisely how "always take the first option" would look.
#[test]
fn s1nd_installed_toss_selects_the_branch_on_the_next_probe() {
    for (v, expected) in [(true, "send"), (false, "choice")] {
        let (o, g) = one_nondet_offer(ExecutionGraph::default(), toss_branches);
        let g = install_nondet(fifo(), g, &o, NondetValue::Toss(v));
        let (offers, _) = probe(g, toss_branches);
        let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
        assert_eq!(
            kinds,
            vec![expected],
            "after installing Toss({v}) the program did not resume on that branch"
        );
    }
}

/// The same for a range, over all three values, including the one whose branch
/// offers nothing at all --- the case where "the next probe has offers" is the
/// *wrong* expectation and a laxer assertion would hide a mis-install.
#[test]
fn s1nd_installed_choice_selects_the_branch_on_the_next_probe() {
    for (v, expected) in [(0usize, vec!["send"]), (1, vec!["nondet"]), (2, Vec::new())] {
        let (o, g) = one_nondet_offer(ExecutionGraph::default(), choice_branches);
        let g = install_nondet(fifo(), g, &o, NondetValue::Choice(v));
        let (offers, _) = probe(g, choice_branches);
        let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
        assert_eq!(
            kinds, expected,
            "after installing Choice({v}) the program did not resume on that branch"
        );
    }
}

/// `alg.tex`'s `ex:restart` end to end, at the level of *observations*: the
/// value the search installs is the value the specification is then seen to
/// send. `ex:restart` is the example that motivates `ln:rebuild`, and it only
/// makes sense if installing 6 after the probe produced 5 actually yields the
/// graph in which `n` is 6.
#[test]
fn s1nd_installed_choice_reaches_the_observation_ex_restart_needs() {
    let mut seen = Vec::new();
    for v in [5usize, 6] {
        let (o, g) = one_nondet_offer(ExecutionGraph::default(), restart_spec);
        assert_eq!(
            o.nondet_values(),
            vec![NondetValue::Choice(5), NondetValue::Choice(6)]
        );
        let g = install_nondet(fifo(), g, &o, NondetValue::Choice(v));

        let (offers, g) = probe(g, restart_spec);
        let send = offers
            .iter()
            .find(|o| o.kind() == "send")
            .unwrap_or_else(|| panic!("installing Choice({v}) did not reach the send: {offers:?}"));
        let g = install(fifo(), g, send);

        let w = wobs(&g, &names(&["a", "c"])).expect("wobs");
        seen.push(shape(&w, "a"));
    }
    assert_ne!(
        seen[0], seen[1],
        "both installed values produced the same observation, so the value did not reach the send"
    );
    assert!(
        seen[0].iter().any(|s| s.contains('5')),
        "installing 5 did not produce a send of 5: {:?}",
        seen[0]
    );
    assert!(
        seen[1].iter().any(|s| s.contains('6')),
        "installing 6 did not produce a send of 6: {:?}",
        seen[1]
    );
}

// --- D9: siblings do not interfere ------------------------------------------

/// Two installs from the same probe graph, as the `ln:innernd` loop does them:
/// the second iteration must see the graph the first was given, not the graph
/// the first produced. `alg.tex:940` --- a branch is not "disturbed by what a
/// sibling did".
#[test]
fn s1nd_sibling_installs_do_not_disturb_each_other() {
    let (o, g0) = one_nondet_offer(ExecutionGraph::default(), toss_branches);
    let pos = o.pos();
    let baseline = fingerprint(&g0);

    let a = install_nondet(fifo(), g0.clone(), &o, NondetValue::Toss(false));
    assert_eq!(fingerprint(&g0), baseline, "installing mutated the source");
    let b = install_nondet(fifo(), g0.clone(), &o, NondetValue::Toss(true));

    assert_eq!(value_at(&a, pos), NondetValue::Toss(false));
    assert_eq!(value_at(&b, pos), NondetValue::Toss(true));
    assert_eq!(fingerprint(&g0), baseline, "the source graph moved");
}

// --- D7/D8: the rejections --------------------------------------------------

/// A stale nondet offer --- one recorded against a graph that has since grown
/// --- is refused, not written over the row. §3 item 11 calls the frontier a
/// precondition; this is the check that it is asserted rather than assumed.
#[test]
#[should_panic(expected = "is not at its thread's frontier")]
fn s1nd_reinstalling_a_stale_nondet_offer_is_rejected() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), toss_branches);
    let g = install_nondet(fifo(), g, &o, NondetValue::Toss(true));
    let _ = install_nondet(fifo(), g, &o, NondetValue::Toss(false));
}

/// A value outside a `Choice`'s range is refused rather than installed. The
/// `expected` string is the message the caller actually gets, recorded
/// verbatim: it is `event_label.rs`'s bare `assert!`, and it names neither the
/// offending value, nor the range, nor the position, nor `probe_set_value`.
/// That is a diagnosability finding, reported rather than fixed --- fixing it
/// would mean editing `event_label.rs`, which this task may not touch.
#[test]
#[should_panic(expected = "a value outside it is one the program could never have produced")]
fn s1nd_out_of_range_choice_is_rejected() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), an_inclusive_choice);
    assert_eq!(o.nondet_values().len(), 3, "range 5..=7");
    let _ = install_nondet(fifo(), g, &o, NondetValue::Choice(9));
}

/// Below the range, not only above it: `5..=7` must refuse 4. An
/// implementation that checked only an upper bound would pass the test above.
#[test]
#[should_panic(expected = "a value outside it is one the program could never have produced")]
fn s1nd_below_range_choice_is_rejected() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), an_inclusive_choice);
    let _ = install_nondet(fifo(), g, &o, NondetValue::Choice(4));
}

/// Putting a `Toss` on a `Choice` label is reachable --- `install_nondet` takes
/// any `NondetValue` with any offer --- and must be refused. The assertion is
/// on the *diagnosis*: the message must say the value does not match the
/// label, since here the label is a perfectly good `Choice` and it is the
/// value that is wrong.
#[test]
#[should_panic(expected = "is the wrong kind of value for the choice point")]
fn s1nd_wrong_kind_value_on_a_choice_is_rejected() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), an_inclusive_choice);
    let _ = install_nondet(fifo(), g, &o, NondetValue::Toss(true));
}

/// And a `Choice` on a `CToss` label.
#[test]
#[should_panic(expected = "is the wrong kind of value for the choice point")]
fn s1nd_wrong_kind_value_on_a_toss_is_rejected() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), a_single_toss);
    let _ = install_nondet(fifo(), g, &o, NondetValue::Choice(0));
}

/// `install_nondet` on an offer that is neither kind --- a send --- is refused
/// too, rather than installing the send and leaving the caller believing a
/// value was chosen.
#[test]
#[should_panic(expected = "probe_set_value is for CToss and Choice labels only")]
fn s1nd_a_send_offer_is_not_a_nondet() {
    let (offers, g) = probe(ExecutionGraph::default(), a_send_and_a_recv);
    let send = offers
        .into_iter()
        .find(|o| o.kind() == "send")
        .expect("a send");
    assert!(send.nondet_values().is_empty());
    let _ = install_nondet(fifo(), g, &send, NondetValue::Toss(true));
}

// --- D12 --------------------------------------------------------------------

/// The search tells branches apart by these values, so the cases must not
/// collapse: `Toss(false)` is not `Toss(true)`, and no `Toss` equals a
/// `Choice` --- in particular `Toss(false)` is not `Choice(0)`.
#[test]
fn s1nd_nondet_value_cases_are_distinct() {
    assert_ne!(NondetValue::Toss(false), NondetValue::Toss(true));
    assert_ne!(NondetValue::Toss(false), NondetValue::Choice(0));
    assert_ne!(NondetValue::Toss(true), NondetValue::Choice(1));
    assert_ne!(NondetValue::Choice(0), NondetValue::Choice(1));
    assert_eq!(NondetValue::Toss(true), NondetValue::Toss(true));
    assert_eq!(NondetValue::Choice(7), NondetValue::Choice(7));
}

// --- harder: does the value survive the probes that follow it? --------------
//
// The tests above install once and look. The search installs, probes, installs
// again, and probes again, and every one of those probes *re-executes the
// program over the graph*. `handle_ctoss`/`handle_choice` build a **fresh**
// label on the replay path --- `CToss::new(pos, gen_bool())`, whose result is
// a new roll --- and hand it to `validate_replay_event`, which for a `CToss`
// returns `Ok(())` without comparing results at all. So "replay quietly writes
// the rolled value back over the installed one" is a live shape of defect that
// a single install-and-inspect test cannot see, and it would degrade the
// search to exactly the "always take the first option" F35 warns about.

/// A nondet whose value must survive a re-probe: install, probe, and look at
/// the graph the probe *returned*, not at the one install produced.
#[test]
fn s1nd_an_installed_value_survives_the_next_probe() {
    for v in [false, true] {
        let (o, g) = one_nondet_offer(ExecutionGraph::default(), toss_branches);
        let pos = o.pos();
        let g = install_nondet(fifo(), g, &o, NondetValue::Toss(v));
        let (_, g) = probe(g, toss_branches);
        assert_eq!(
            value_at(&g, pos),
            NondetValue::Toss(v),
            "re-probing overwrote the installed value"
        );
    }
}

/// The same for a range, and over every value: the probe must not write the
/// label's construction default (`Choice::new` sets `result = *range.start()`)
/// back over an installed 6 or 7.
#[test]
fn s1nd_an_installed_choice_survives_the_next_probe() {
    let (o, g0) = one_nondet_offer(ExecutionGraph::default(), an_inclusive_choice);
    let pos = o.pos();
    for v in [5usize, 6, 7] {
        let g = install_nondet(fifo(), g0.clone(), &o, NondetValue::Choice(v));
        let (_, g) = probe(g, an_inclusive_choice);
        assert_eq!(
            value_at(&g, pos),
            NondetValue::Choice(v),
            "re-probing reset the choice to its range start"
        );
    }
}

/// Two choice points in a row, all four combinations, installed one at a time
/// the way `SpecVisit` recurses. Checks three things at once: the first value
/// is still there after the second install, the second value took, and the
/// program's control flow saw both --- the `a == b` branch sends, the others
/// do not.
#[test]
fn s1nd_two_sequential_tosses_each_keep_their_installed_value() {
    fn two_tosses() {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        let a = crate::nondet();
        let b = crate::nondet();
        if a == b {
            crate::send_msg(w, 1u64);
        }
    }

    for a in [false, true] {
        for b in [false, true] {
            let (o1, g) = one_nondet_offer(ExecutionGraph::default(), two_tosses);
            let p1 = o1.pos();
            let g = install_nondet(fifo(), g, &o1, NondetValue::Toss(a));

            let (o2, g) = one_nondet_offer(g, two_tosses);
            let p2 = o2.pos();
            assert_ne!(p1, p2, "the second probe re-offered the first choice point");
            let g = install_nondet(fifo(), g, &o2, NondetValue::Toss(b));

            assert_eq!(
                value_at(&g, p1),
                NondetValue::Toss(a),
                "installing the second value disturbed the first ({a}, {b})"
            );
            assert_eq!(value_at(&g, p2), NondetValue::Toss(b));

            let (offers, g) = probe(g, two_tosses);
            let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
            let expected: Vec<&str> = if a == b { vec!["send"] } else { vec![] };
            assert_eq!(
                kinds, expected,
                "control flow after installing ({a}, {b}) is wrong"
            );
            assert_eq!(value_at(&g, p1), NondetValue::Toss(a), "({a}, {b})");
            assert_eq!(value_at(&g, p2), NondetValue::Toss(b), "({a}, {b})");
        }
    }
}

/// `named_nondet` is a third spelling of a boolean choice, with a `name` field
/// and a thread-index freezing table behind it (`lib.rs`). Installing a value
/// on one must take and must survive the re-probe like any other, and the
/// program must resume on the installed branch.
#[test]
fn s1nd_a_named_toss_installs_and_selects_its_branch() {
    fn named_branches() {
        use crate::Nondet;
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        if crate::named_nondet("retry") {
            crate::send_msg(w, 1u64);
        } else {
            let _ = (0usize..3usize).nondet();
        }
    }

    for (v, expected) in [(true, "send"), (false, "choice")] {
        let (o, g) = one_nondet_offer(ExecutionGraph::default(), named_branches);
        let pos = o.pos();
        assert_eq!(
            o.nondet_values(),
            vec![NondetValue::Toss(false), NondetValue::Toss(true)]
        );
        let g = install_nondet(fifo(), g, &o, NondetValue::Toss(v));
        let (offers, g) = probe(g, named_branches);
        assert_eq!(value_at(&g, pos), NondetValue::Toss(v));
        let kinds: Vec<_> = offers.iter().map(|o| o.kind()).collect();
        assert_eq!(
            kinds,
            vec![expected],
            "named_nondet({v}) took the wrong branch"
        );
    }
}

/// With **two** threads parked at choice points, installing one leaves the
/// other's row alone and the other offer still outstanding. The search reaches
/// this at every node with more than one offered event, and an install that
/// resolved "the" nondet rather than *this* one would corrupt a sibling row.
#[test]
fn s1nd_installing_one_threads_value_leaves_the_others_offer_alone() {
    fn two_threads_two_tosses() {
        let m = main_thread_id();
        named("w", move || {
            if crate::nondet() {
                crate::send_msg(m, 1u64);
            }
        });
        let _ = crate::nondet();
    }

    let (offers, g) = probe(ExecutionGraph::default(), two_threads_two_tosses);
    assert_eq!(offers.len(), 2, "expected both threads parked: {offers:?}");
    let main_offer = offers
        .iter()
        .find(|o| o.pos().thread == main_thread_id())
        .expect("main's toss");
    let w_offer = offers
        .iter()
        .find(|o| o.pos().thread != main_thread_id())
        .expect("w's toss");
    let main_pos = main_offer.pos();
    let w_pos = w_offer.pos();
    let before = sizes(&g);

    let g = install_nondet(fifo(), g, w_offer, NondetValue::Toss(true));

    assert!(
        !g.contains(main_pos),
        "installing w's value installed main's parked toss too"
    );
    for (t, n) in &before {
        let m = g.thread_size(*t);
        let expected = if *t == w_pos.thread { n + 1 } else { *n };
        assert_eq!(m, expected, "row of {t:?} moved");
    }
    assert_eq!(value_at(&g, w_pos), NondetValue::Toss(true));

    // Main's choice point is still on offer, and w has resumed on the `true`
    // branch, so its send is now offered as well.
    let (offers, _) = probe(g, two_threads_two_tosses);
    let mut kinds: Vec<_> = offers
        .iter()
        .map(|o| (o.pos().thread == main_thread_id(), o.kind()))
        .collect();
    kinds.sort();
    assert_eq!(
        kinds,
        vec![(false, "send"), (true, "nondet")],
        "offers after installing only w's value: {offers:?}"
    );
}

/// A nondet offer carries no rf options. The search dispatches on the offer's
/// kind, but `sources()`/`may_read_nothing()` are readable on every offer, and
/// a nondet that claimed it "may read nothing" would let a `SetRF`-shaped
/// caller through on a label with no rf field.
#[test]
fn s1nd_a_nondet_offer_carries_no_rf_options() {
    for prog in [a_single_toss as fn(), an_inclusive_choice as fn()] {
        let (o, _) = one_nondet_offer(ExecutionGraph::default(), prog);
        assert!(o.sources().is_empty(), "{o:?}");
        assert!(!o.may_read_nothing(), "{o:?}");
    }
}

// --- O-3: `install` is send-only, and the roll it would have carried --------
//
// The developer found O-3 in the P3-S1-nondet-install pass and reported it as a
// hazard: `prober::install` took **any** `Offer`, installed `offer.label()` as
// it stood, and so --- for a nondet offer --- carried the value the *probe*
// rolled, with no decision applied. That roll comes from the config's seed,
// which `ConfigBuilder` defaults to `rand::rng().next_u64()`, so a search
// routing a nondet offer through `install` would not have taken "always the
// first option" (bad, but reproducible); it would have taken **a uniformly
// random option**: a different graph per run from the same program and the
// same `H`, and a conformance verdict presenting as flakiness rather than as a
// readable bug. The same shape applied to a *receive* offer, which would have
// been installed with no `rf` at all.
//
// `install` now asserts its offer is a send. These five tests are the
// developer's own check on that fix, written from the implementation rather
// than adapted from the test that pinned the hazard, and they are deliberately
// separate claims rather than one test doing three things:
//
//   * the refusal fires for each of the three kinds that carry a decision, and
//     each panic is pinned to *its own* message, so a refusal for the wrong
//     reason (the frontier assertion, say) is not mistaken for this one;
//   * `install` still accepts a send, so "refuses" is not satisfiable by
//     refusing everything;
//   * the roll really does vary with the seed --- the premise the whole
//     finding rests on --- and `install_nondet` overrides it at every seed.
//
// The receive case is new here: it is the half of O-3 the report named and no
// test covered.

/// A seeded config, so a claim about the probe's *own* rolled value can be
/// made deterministically. `Config::builder().build()` takes
/// `seed: rand::rng().next_u64()` (lib.rs:302) and `Must::gen_bool` draws from
/// a PCG seeded with it, so the value a probe produces at a fresh `CToss` is
/// random per config --- which is why the tests above never assert *which*
/// value a probe rolled, only that both are offered and the chosen one takes.
fn seeded(seed: u64) -> Config {
    Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_seed(seed)
        .build()
}

/// The receive offer of [`a_send_and_a_recv`], with the graph it was offered
/// against. The send has to be installed first: a blocking receive with
/// nothing to read is not enabled, so the first probe does not offer it.
fn one_recv_offer() -> (Offer, ExecutionGraph) {
    let (offers, g) = probe(ExecutionGraph::default(), a_send_and_a_recv);
    let send = offers.iter().find(|o| o.kind() == "send").expect("a send");
    let g = install(fifo(), g, send);
    let (offers, g) = probe(g, a_send_and_a_recv);
    let recv = offers
        .into_iter()
        .find(|o| o.kind() == "recv")
        .expect("a recv");
    (recv, g)
}

/// A `CToss` offer --- `kind() == "nondet"` --- is refused, and the message
/// names `install_nondet`.
///
/// The message is pinned rather than the panic merely being caught, because
/// `install` is reachable in a state where *another* assertion would fire (a
/// stale offer trips `probe_install`'s frontier check), and a test that only
/// asked "did it panic?" would pass on that instead. What must hold is that a
/// decision-carrying offer is refused **for carrying a decision**.
#[test]
#[should_panic(expected = "`install` takes a send offer; a nondet offer carries a \
                decision and must go through `install_nondet`")]
fn s1nd_install_refuses_a_nondet_offer() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), a_single_toss);
    let _ = install(fifo(), g, &o);
}

/// A `Choice` offer --- `kind() == "choice"`, a *different* string --- is
/// refused too, and routed to the same operation.
///
/// Not redundant with the `CToss` case: `install`'s message picks the
/// operation to name with `match offer.kind()`, whose first arm is
/// `"nondet" | "choice"`. A check on only one of the two would pass if that
/// arm lost its second pattern and the `Choice` fell through to the
/// `_ => "the operation for its kind"` backstop.
#[test]
#[should_panic(expected = "`install` takes a send offer; a choice offer carries a \
                decision and must go through `install_nondet`")]
fn s1nd_install_refuses_a_choice_offer() {
    let (o, g) = one_nondet_offer(ExecutionGraph::default(), an_inclusive_choice);
    let _ = install(fifo(), g, &o);
}

/// A receive offer is refused, and routed to `install_recv`.
///
/// The second half of O-3, which the original report named and nothing tested.
/// Its failure mode is different from the nondet one and in one respect worse:
/// a receive installed through `install` gets no `rf` at all, so it reads
/// nothing --- which for a *blocking* receive is not a behaviour the program
/// has. That graph would then be carried forward as a graph of Spec.
#[test]
#[should_panic(expected = "`install` takes a send offer; a recv offer carries a \
                decision and must go through `install_recv`")]
fn s1nd_install_refuses_a_receive_offer() {
    let (o, g) = one_recv_offer();
    let _ = install(fifo(), g, &o);
}

/// `install` still installs a send --- the direction three `#[should_panic]`
/// tests cannot establish between them.
///
/// Without this, replacing the assertion with `assert!(false, "...")` carrying
/// the same message would satisfy every refusal test above while breaking the
/// only route the search has for a send.
#[test]
fn s1nd_install_still_accepts_a_send_offer() {
    let (offers, g) = probe(ExecutionGraph::default(), a_send_and_a_recv);
    let send = offers.iter().find(|o| o.kind() == "send").expect("a send");
    let pos = send.pos();
    let before = g.thread_size(pos.thread);

    let g = install(fifo(), g, send);

    assert_eq!(
        g.thread_size(pos.thread),
        before + 1,
        "the send was not installed"
    );
    assert!(
        matches!(g.label(pos), LabelEnum::SendMsg(_)),
        "the label at {pos} is not the send: {}",
        g.label(pos)
    );
}

/// The premise the O-3 finding rests on: the probe's roll is **not** fixed by
/// the program, and `install_nondet` does not inherit it.
///
/// If the roll were determined by the program, routing a nondet through
/// `install` would have been a stable wrong answer rather than a
/// non-reproducible one, and the refusal above would be a smaller matter than
/// the doc on `install` claims. Over seeds `0..24` both rolls occur, so it is
/// not; and at every one of those seeds, installing each boolean through
/// `install_nondet` yields that boolean.
///
/// Stated as a loop over explicit seeds rather than trusting the default
/// config, so the claim is deterministic --- a test that relied on
/// `rand::rng()` to produce both values would itself be flaky.
#[test]
fn s1nd_the_probes_roll_varies_with_the_seed_and_install_nondet_overrides_it() {
    let mut rolled: Vec<NondetValue> = Vec::new();

    for seed in 0..24u64 {
        let c = seeded(seed);
        let (offers, g) =
            probe_from(c.clone(), ExecutionGraph::default(), a_single_toss).into_parts();
        assert_eq!(offers.len(), 1, "offers: {offers:?}");
        let o = &offers[0];

        let roll = offered_value(o);
        if !rolled.contains(&roll) {
            rolled.push(roll);
        }

        for v in [false, true] {
            let chosen = install_nondet(c.clone(), g.clone(), o, NondetValue::Toss(v));
            assert_eq!(
                value_at(&chosen, o.pos()),
                NondetValue::Toss(v),
                "install_nondet did not override the roll (seed {seed}, value {v})"
            );
        }
    }

    assert_eq!(
        rolled.len(),
        2,
        "no seed in 0..24 rolled the other way, so this test is not showing \
         what it claims to show: {rolled:?}"
    );
}

// ===========================================================================
// (A11) symmetric thread spawning: the guard, and the inertness argument
//
// Derived from `criteria/P3-S3-search.md` criterion 8's A11 paragraph and the
// round-05 verdict's M3, before reading `must.rs`'s guard:
//
//   A1  A probe of a program that calls `spawn_symmetric` is refused, and the
//       refusal names the operation.
//   A2  The refusal also fires when the symmetric spawn is already in the
//       prefix and is therefore *replayed* — which is the half that makes the
//       guard's placement (handler entry, above the replay branch) load-bearing
//       rather than decorative, since every probe past the first replays.
//   A3  A2 is not vacuous: an ordinary run of the same program really does
//       mark the symmetric thread's `Begin` with a `sym_id`.
//   A4  The inertness argument, executed rather than asserted. `filter_symmetric_rfs`
//       narrows only inside `if blab.sym_id().is_some() && …`, where `blab` is
//       the *source* thread's `Begin`. So if no `Begin` reachable under a probe
//       can carry a `sym_id`, the filter's narrowing branch is unreachable and
//       `Offer::sources()` is the unfiltered rf enumeration — which is the
//       whole reason criterion 8's equality holds.
// ===========================================================================

/// Two senders of the same value to `main`, the second spawned *symmetric* to
/// the first, and a blocking receive so an ordinary run has something to read.
fn symmetric_senders() {
    let m = main_thread_id();
    let a = named("a", move || crate::send_msg(m, 1u64));
    let _b = crate::spawn_symmetric(move || crate::send_msg(m, 1u64), a);
    let _: u64 = crate::recv_msg_block();
}

/// **A1.** Probing a program that spawns a symmetric thread is refused.
///
/// The failure direction is a soundness one, not a scope nicety: a symmetric
/// `Begin` is the only thing that makes `filter_symmetric_rfs` narrow, that
/// filter runs inside the receive preflight, and `cons.rs` has no symmetry
/// reasoning at all — so a source it removes is one the receive *could*
/// consistently read. The search loops the sources it is offered, so a dropped
/// source is a cover never found and a conformance violation reported that is
/// not there.
///
/// To break it: delete the `if sym_cid.is_some()` guard at `handle_tcreate`'s
/// entry. The probe then runs to completion and this test fails with "note:
/// test did not panic as expected".
#[test]
#[should_panic(expected = "symmetric thread spawning")]
fn a11_probing_a_symmetric_spawn_is_refused() {
    let _ = probe_once(fifo(), symmetric_senders);
}

/// **A2.** And refused when the spawn is *replayed* out of the prefix.
///
/// Every probe after the first replays the graph it is given, so a guard
/// placed inside `handle_tcreate`'s non-replay branch would fire on the first
/// probe and never again — and the graph carrying the symmetric `Begin` is
/// exactly the one the filter reads. This is the placement claim, executed.
///
/// To break it: move the guard below `if self.is_replay(pos) { … return; }`.
/// A1 still passes; this one stops panicking.
#[test]
#[should_panic(expected = "symmetric thread spawning")]
fn a11_a_replayed_symmetric_spawn_is_refused_too() {
    let g = run_once(fifo(), symmetric_senders);
    let _ = probe_from(fifo(), g, symmetric_senders);
}

/// **A3.** A2 is not vacuous: outside probe mode the same program really does
/// produce a `Begin` carrying a `sym_id`, so the graph A2 replays is one the
/// filter would act on.
#[test]
fn a11_an_ordinary_run_marks_the_symmetric_threads_begin() {
    let g = run_once(fifo(), symmetric_senders);
    let marked: Vec<ThreadId> = g
        .thread_ids()
        .into_iter()
        .filter(|t| g.thread_first(*t).and_then(|b| b.sym_id()).is_some())
        .collect();
    assert_eq!(
        marked.len(),
        1,
        "exactly one symmetric thread was spawned, so exactly one `Begin` \
         should carry a `sym_id`; graph:\n{g}"
    );
}

/// Every `Begin` in `g` is unmarked — the condition under which
/// `filter_symmetric_rfs`'s narrowing branch cannot be entered for any source.
fn no_begin_is_symmetric(g: &ExecutionGraph, where_: &str) {
    for t in g.thread_ids() {
        if let Some(b) = g.thread_first(t) {
            assert!(
                b.sym_id().is_none(),
                "{where_}: a probe-reachable graph carries a symmetric `Begin` \
                 on {t:?}, so `filter_symmetric_rfs` can narrow:\n{g}"
            );
        }
    }
}

/// Drive `f` by probe-and-install under the greedy policy, running `check` at
/// every node. Bounded, so a mistake here fails rather than spins.
fn walk_probe_nodes(f: fn(), check: &dyn Fn(&ExecutionGraph, &str)) {
    let mut g = ExecutionGraph::default();
    for step in 0..24 {
        let (offers, probed) = probe(g, f);
        check(&probed, &format!("step {step}"));
        if offers.is_empty() {
            return;
        }
        let o = &offers[0];
        g = match o.kind() {
            "send" => install(fifo(), probed, o),
            "recv" => install_recv(fifo(), probed, o, o.sources().first().copied()),
            _ => install_nondet(fifo(), probed, o, o.nondet_values()[0]),
        };
    }
    panic!("walk_probe_nodes: more than 24 steps");
}

/// **A4. The inertness argument, executed.**
///
/// `sym_id` is set in exactly one place — `Begin::new(pos, parent, symm_id)`,
/// whose only call site is inside `handle_tcreate` — and A1/A2 pin the guard
/// above it on both the fresh and the replay path. This checks the consequence
/// on real probe-reachable graphs: over a battery of spawning shapes, and at
/// every node of a greedy drive of each, no `Begin` carries a `sym_id`.
///
/// That is the premise `filter_symmetric_rfs` needs to be inert, and inertness
/// is what makes `Offer::sources()` the unfiltered rf enumeration — criterion
/// 8's equality.
///
/// What it is **not**: a proof over all programs. It is a reachability check
/// over a finite battery. The general claim rests on the single call site plus
/// A1/A2; see the report's vacuity audit.
#[test]
fn a11_no_probe_reachable_begin_carries_a_sym_id() {
    fn plain_spawn() {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        let _: u64 = crate::recv_msg_block();
    }
    fn nested_spawn() {
        let m = main_thread_id();
        named("outer", move || {
            named("inner", move || crate::send_msg(m, 2u64));
        });
        let _: u64 = crate::recv_msg_block();
    }
    fn join_chain() {
        let t = thread::spawn(|| 7i32);
        let _ = t.join();
        let u = thread::spawn(|| 8i32);
        let _ = u.join();
    }
    fn two_senders_one_recv() {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
    }
    fn spawn_then_toss() {
        let m = main_thread_id();
        named("a", move || {
            if crate::nondet() {
                crate::send_msg(m, 1u64);
            } else {
                crate::send_msg(m, 2u64);
            }
        });
        let _: u64 = crate::recv_msg_block();
    }

    for f in [
        plain_spawn as fn(),
        nested_spawn,
        join_chain,
        two_senders_one_recv,
        spawn_then_toss,
    ] {
        walk_probe_nodes(f, &no_begin_is_symmetric);
    }
}

// ===========================================================================
// (F37, criterion 8) what a receive may be made to read
//
// Derived from criterion 8 and the round-05 verdict's M4 before reading
// `install_recv`'s guards or `cons.rs`:
//
//   B1  `install_recv` refuses `rf = None` on a receive that may not read
//       nothing. Failure mode if it did not: the graph shows a blocking
//       `RECV() [TIMEOUT]`, a behaviour the program does not have.
//   B2  `install_recv` refuses a source the offer did not list. Failure mode:
//       an inconsistent graph is carried forward as a graph of Spec, so the
//       tool goes **silent on a real violation** — criterion 8's worse
//       direction.
//   B3  Neither refusal is `assert!(false)`: an admissible decision still goes
//       through.
//   C1  `Offer::sources()` misses nothing (the "one fewer" direction): every
//       send in the graph that it did *not* offer leaves a graph the program
//       has no execution of.
//   C2  `Offer::sources()` adds nothing (the "one more" direction): every send
//       it *did* offer leaves a graph the program does have an execution of.
//
// The oracle for C1/C2 is `crate::verify` on the same program: an ordinary
// exploration that enumerates the program's executions and observes the values
// received. It shares `cons.rs`'s rf enumeration with the probe path, so it is
// not an independent decision procedure — see the report. It is independent of
// probe mode, of `Offer`, and of `install_recv`, which is what the criterion's
// two directions are about.
// ===========================================================================

/// Two sends from **one** thread on **one** channel, then two receives. Under
/// FIFO only the sb-minimal unread send is readable, so the graph holds a send
/// that `sources()` must not offer — which is what C1 needs.
fn fifo_two_sends() {
    let m = main_thread_id();
    named("b", move || {
        crate::send_msg(m, 1u64);
        crate::send_msg(m, 2u64);
    });
    let _: u64 = crate::recv_msg_block();
    let _: u64 = crate::recv_msg_block();
}

/// The same program, recording what `main` observed, for the `verify` oracle.
static FIFO_TWO_SENDS_SEEN: std::sync::Mutex<Vec<(u64, u64)>> = std::sync::Mutex::new(Vec::new());

fn fifo_two_sends_recorded() {
    let m = main_thread_id();
    named("b", move || {
        crate::send_msg(m, 1u64);
        crate::send_msg(m, 2u64);
    });
    let x: u64 = crate::recv_msg_block();
    let y: u64 = crate::recv_msg_block();
    FIFO_TWO_SENDS_SEEN.lock().unwrap().push((x, y));
}

/// Two **independent** senders and one receive: both sends are readable, so
/// `sources()` offers two and C2 is checked on a set with more than one member.
fn two_threads_one_recv() {
    let m = main_thread_id();
    named("a", move || crate::send_msg(m, 1u64));
    named("b", move || crate::send_msg(m, 2u64));
    let _: u64 = crate::recv_msg_block();
}

static TWO_THREADS_SEEN: std::sync::Mutex<Vec<u64>> = std::sync::Mutex::new(Vec::new());

fn two_threads_one_recv_recorded() {
    let m = main_thread_id();
    named("a", move || crate::send_msg(m, 1u64));
    named("b", move || crate::send_msg(m, 2u64));
    let x: u64 = crate::recv_msg_block();
    TWO_THREADS_SEEN.lock().unwrap().push(x);
}

/// The `u64` a send label in `g` carries.
fn sent_u64(g: &ExecutionGraph, e: Event) -> u64 {
    *g.send_label(e)
        .unwrap_or_else(|| panic!("no send at {e}"))
        .val()
        .as_any_ref()
        .downcast_ref::<u64>()
        .expect("the test programs send u64")
}

/// Every send position in `g`, in row order.
fn all_sends(g: &ExecutionGraph) -> Vec<Event> {
    let mut out = Vec::new();
    for t in g.thread_ids() {
        for i in 0..g.thread_size(t) as u32 {
            let e = Event::new(t, i);
            if g.send_label(e).is_some() {
                out.push(e);
            }
        }
    }
    out
}

/// Drive `f` until its receive is offered, installing every send on the way.
/// Returns that receive offer and the graph it was offered against.
fn node_with_every_send_installed(f: fn()) -> (Offer, ExecutionGraph) {
    let mut g = ExecutionGraph::default();
    for _ in 0..16 {
        let (offers, probed) = probe(g, f);
        match offers.iter().position(|o| o.kind() == "send") {
            Some(i) => g = install(fifo(), probed, &offers[i]),
            None => {
                let recv = offers
                    .into_iter()
                    .find(|o| o.kind() == "recv")
                    .expect("a receive is offered once every send is installed");
                return (recv, probed);
            }
        }
    }
    panic!("node_with_every_send_installed: more than 16 steps");
}

/// **B1.** ⊥ is refused on a receive that may not read nothing.
///
/// To break it: delete `install_recv`'s `None` arm. The test then reports
/// "did not panic as expected" — and the graph it would have built carries a
/// timed-out blocking receive.
#[test]
#[should_panic(expected = "cannot install ⊥ on the blocking receive")]
fn f37_install_recv_refuses_bottom_on_a_blocking_receive() {
    let (recv, g) = one_recv_offer();
    assert!(
        !recv.may_read_nothing(),
        "this fixture must offer a *blocking* receive, or the test is vacuous"
    );
    let _ = install_recv(fifo(), g, &recv, None);
}

/// **B2.** A source the offer did not list is refused.
///
/// The source used is a **real send that is in the graph** — `b`'s second,
/// which FIFO makes unreadable while the first is unread — not a fabricated
/// position. A fabricated one would also trip `probe_set_rf`'s own handling
/// and would not show that the guard is about the *enumeration*.
///
/// To break it: delete `install_recv`'s `Some(src)` arm. The test then reports
/// "did not panic as expected", and C1 below says what the resulting graph is.
#[test]
#[should_panic(expected = "is not among the sources offered")]
fn f37_install_recv_refuses_a_source_the_offer_did_not_list() {
    let (recv, g) = node_with_every_send_installed(fifo_two_sends);
    let sends = all_sends(&g);
    assert_eq!(sends.len(), 2, "two sends are in the graph");
    let not_offered = *sends
        .iter()
        .find(|e| !recv.sources().contains(e))
        .expect("FIFO leaves one of the two unreadable, or the test is vacuous");
    let _ = install_recv(fifo(), g, &recv, Some(not_offered));
}

/// **B3.** Neither guard is `assert!(false)`: an offered source still installs,
/// and the installed graph reads from it.
#[test]
fn f37_install_recv_still_accepts_an_offered_source() {
    let (recv, g) = node_with_every_send_installed(fifo_two_sends);
    let src = recv.sources()[0];
    let pos = recv.pos();
    let g = install_recv(fifo(), g, &recv, Some(src));
    assert_eq!(
        g.recv_label(pos).expect("the receive was installed").rf(),
        Some(src)
    );
}

/// **C1 and C2 — criterion 8's equality, both directions.**
///
/// The claim: `Offer::sources()` is exactly the set of sends for which
/// extending with that source leaves a graph the specification has. The
/// directions fail differently. One **fewer** is a cover never found, so a
/// violation is reported that is not there — visible. One **more** is an
/// inconsistent graph accepted as a cover, so the tool goes silent on a real
/// violation — worse.
///
/// The oracle is `crate::verify` on the same program, recording what `main`
/// observed in each execution. `fifo_two_sends` has exactly one execution,
/// `(1, 2)`; `main`'s first receive never observes `2`.
///
/// C1 has to be written against `Must::probe_install` + `probe_set_rf`
/// directly, because F37's guard (B2) refuses the non-offered source through
/// `install_recv` **by design** — that guard is the thing standing between this
/// graph and the search.
///
/// Recorded here rather than asserted as a property: `Checker::is_consistent`
/// cannot tell the two graphs apart. It only inspects pairs of `TotalOrder`
/// sends (`cons.rs:415`), and conformance excludes `TotalOrder`, so it is
/// **vacuously true** on every graph in scope. The rf enumeration is therefore
/// the whole of the consistency filter for a receive, which is exactly why
/// criterion 8's equality is load-bearing.
#[test]
fn c8_sources_is_exactly_the_set_of_sends_the_program_can_read_here() {
    // --- the oracle -------------------------------------------------------
    FIFO_TWO_SENDS_SEEN.lock().unwrap().clear();
    let stats = crate::verify(fifo(), fifo_two_sends_recorded);
    let seen = FIFO_TWO_SENDS_SEEN.lock().unwrap().clone();
    assert_eq!(
        seen,
        vec![(1u64, 2u64)],
        "the program has one execution and `main` observes (1, 2); stats: \
         {} executions",
        stats.execs
    );

    // --- the node ---------------------------------------------------------
    let (recv, g) = node_with_every_send_installed(fifo_two_sends);
    let sends = all_sends(&g);
    assert_eq!(sends.len(), 2, "two sends are in the graph: {sends:?}");
    let offered: Vec<Event> = recv.sources().to_vec();
    assert_eq!(
        offered.len(),
        1,
        "FIFO leaves only the sb-minimal unread send readable; offered {offered:?}"
    );
    let not_offered = *sends.iter().find(|e| !offered.contains(e)).unwrap();
    assert_eq!(sent_u64(&g, offered[0]), 1, "the offered send carries 1");
    assert_eq!(sent_u64(&g, not_offered), 2, "the withheld send carries 2");

    // --- C2: nothing extra ------------------------------------------------
    let good = install_recv(fifo(), g.clone(), &recv, Some(offered[0]));
    let read = good
        .recv_label(recv.pos())
        .expect("installed")
        .rf()
        .expect("reads a send");
    assert_eq!(read, offered[0]);
    assert!(
        seen.iter().any(|(x, _)| *x == sent_u64(&good, read)),
        "the offered source produces an observation the program has"
    );

    // --- C1: nothing missing ----------------------------------------------
    // `install_recv` refuses this by design (B2), so the raw engine operations
    // it wraps are used instead.
    let mut must = crate::must::Must::with_initial_graph(fifo(), g.clone());
    let pos = must.probe_install(recv.label().clone());
    must.probe_set_rf(pos, Some(not_offered));
    let bad = must.take_graph();
    assert_eq!(
        bad.recv_label(pos).expect("installed").rf(),
        Some(not_offered),
        "the withheld source really was installed, or C1 is vacuous"
    );
    assert!(
        !seen.iter().any(|(x, _)| *x == sent_u64(&bad, not_offered)),
        "the withheld source produces an observation the program does not have"
    );

    // --- what TraceForge's own consistency predicate says about the pair ---
    assert!(
        crate::must::Must::with_initial_graph(fifo(), good).is_consistent(),
        "the offered source leaves a consistent graph"
    );
    assert!(
        crate::must::Must::with_initial_graph(fifo(), bad).is_consistent(),
        "RECORDED, NOT DESIRED: `Checker::is_consistent` inspects only pairs \
         of TotalOrder sends (cons.rs:415) and conformance excludes \
         TotalOrder, so it is vacuously true in scope and cannot distinguish \
         these two graphs. If this assertion ever fails, `is_consistent` has \
         gained a FIFO arm and criterion 8 has a second oracle."
    );
}

/// **C2 again, on a set with more than one member**, so the singleton above is
/// not mistaken for "the enumeration always returns one". Two independent
/// senders: both are offered, and the program really does have an execution
/// reading each.
#[test]
fn c8_every_offered_source_of_a_two_source_receive_is_one_the_program_has() {
    TWO_THREADS_SEEN.lock().unwrap().clear();
    let _ = crate::verify(fifo(), two_threads_one_recv_recorded);
    let mut seen = TWO_THREADS_SEEN.lock().unwrap().clone();
    seen.sort();
    seen.dedup();
    assert_eq!(seen, vec![1u64, 2u64], "both sends are readable here");

    let (recv, g) = node_with_every_send_installed(two_threads_one_recv);
    let sends = all_sends(&g);
    assert_eq!(sends.len(), 2);
    assert_eq!(
        recv.sources().len(),
        2,
        "both sends are offered: {:?}",
        recv.sources()
    );
    for src in recv.sources() {
        let g2 = install_recv(fifo(), g.clone(), &recv, Some(*src));
        assert_eq!(g2.recv_label(recv.pos()).unwrap().rf(), Some(*src));
        assert!(
            seen.contains(&sent_u64(&g2, *src)),
            "offered source {src} carries a value no execution observes"
        );
    }
    // And nothing is withheld here, so the "one fewer" direction is empty.
    for e in &sends {
        assert!(
            recv.sources().contains(e),
            "{e} is a send the program can read but was not offered"
        );
    }
}
