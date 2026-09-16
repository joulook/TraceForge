//! §11.5's refinement pair suite: outcomes pinned per pair, per model.
//!
//! Criterion 8. §11.5 states its own acceptance conditions — "per model:
//! positive pairs (**silence required** — the false-alarm floor) and negative
//! pairs (**report required**)" — and until this file those obligations
//! appeared only inside the *generator's* criterion, which says what may be
//! emitted and never what must be asserted. A harness that generated all five
//! shapes and ran only the property test satisfied every criterion while never
//! establishing the false-alarm floor.
//!
//! # Pinned by construction, not by observation
//!
//! Every expected outcome below is a consequence of the pair's *shape*, not a
//! value read off a run:
//!
//! - a **positive** pair must yield a `Certificate` — not merely silence.
//!   `mod.rs`: the certificate types "are the difference between a certificate
//!   and a run that merely produced no report, which is the one distinction
//!   the theorem turns on". A suite that accepted silence would pass on a run
//!   that exhausted its inner budget having established nothing.
//! - a **negative** pair must yield at least one report, and the suite says
//!   *which cause*.
//!
//! A suite whose expected values were read off a run is a transcript, not
//! evidence.
//!
//! # The three models
//!
//! {asyn/`Bag`, p2p/`FIFO`, cd/`Causal`}. Mailbox/`TotalOrder` is out of
//! scope (§9) and is refused by the tool rather than skipped here.

use crate::conformance::{verify, ConfBuilder, ConfVerdict, ReportCause};
use crate::{recv_msg_block, send_msg, thread, ConsType, Config};

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new()
        .name(n.to_string())
        .spawn(f)
        .unwrap()
}

fn conf(model: ConsType, visible: &[&str]) -> crate::conformance::ConfConfig {
    ConfBuilder::new()
        .visible_threads(visible.iter().copied())
        .config(Config::builder().with_cons_type(model).build())
        .build()
        .expect("in-scope configuration")
}

/// The three in-scope models, with the names §9 uses.
fn models() -> [(ConsType, &'static str); 3] {
    [
        (ConsType::Bag, "asyn"),
        (ConsType::FIFO, "p2p"),
        (ConsType::Causal, "cd"),
    ]
}

// --- the pairs -------------------------------------------------------------

/// `A` sends `1` to a visible `C`, through an invisible relay.
fn relayed() {
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

/// `A` sends `1` straight to a visible `C`.
fn direct() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 1i32);
}

/// As `direct`, but the observed value differs — an (M1) break.
fn direct_two() {
    let c = named("c", || {
        let _v: i32 = recv_msg_block();
    });
    send_msg(c.thread().id(), 2i32);
}

/// A declared **visible** thread fails an assertion. §4.4's case.
fn visible_error() {
    let _w = named("w", || {
        crate::assert(false);
    });
}

/// The specification for the visible-error pair: same visible name, no
/// failure. The implementation's `err` is what the report is about.
fn visible_ok() {
    let _w = named("w", || {});
}

// --- the obligations -------------------------------------------------------

/// **Positive pairs, per model: a certificate is required.** This is §11.5's
/// false-alarm floor — the tool must be *silent with a reason* on a pair that
/// genuinely refines, under every communication model in scope.
///
/// The pair is non-reflexive: the implementation relays through an invisible
/// thread the specification does not have, so the two programs differ while
/// `vis` does not (`ex:relay` publishes `vis(P₁) = vis(P₂)`).
///
/// **Mutation, MEASURED**: give `Obs::Send` the send's destination
/// (`Send(Val, String)` carrying `format!("{:?}", slab.loc())`, compared in
/// `Obs`'s `PartialEq`). Applied at gate 3 —
/// `positive_pairs_certify_under_every_model ... FAILED`, 338 passed /
/// 14 failed. The relay's `send(R,1)` and the direct `send(C,1)` then differ,
/// so the invisible refactor stops being invisible and the floor is lost.
///
/// **Mutation, REFUTED as a mutation**: the line this test used to carry —
/// "accept `ConfVerdict::Inconclusive` as a pass". That is a *weakening of the
/// test*, not a change to the code under test, and a weakening can never make
/// a test fail. Under criterion 19 it was undischargeable as written. The
/// property it was reaching for — that `Inconclusive` is not a certificate —
/// is covered by
/// `differential_smoke::a_bounded_inner_search_is_inconclusive_and_never_a_certificate`.
#[test]
fn positive_pairs_certify_under_every_model() {
    for (model, name) in models() {
        let verdict = verify(conf(model, &["main", "c"]), relayed, direct)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        assert!(
            matches!(verdict, ConfVerdict::Conforms(_)),
            "{name}: a refining pair must yield a certificate, not merely silence; got \
             {verdict:?}"
        );
    }
}

/// **Negative pairs, per model: a report is required, and its cause is
/// pinned.**
///
/// **Mutation, MEASURED**: make `Obs`'s `PartialEq` ignore the value (both the
/// `Send` and the `Recv(Some(..))` arms return `true`). Applied at gate 3 —
/// `negative_pairs_report_nocover_under_every_model ... FAILED`, on
/// `an (M1) break must be reported; got Conforms`.
///
/// **Mutation, REFUTED as a mutation**: the line this test used to carry —
/// "assert only that the verdict is not `Conforms`" — is a weakening of the
/// test, which cannot make it fail (criterion 19).
#[test]
fn negative_pairs_report_nocover_under_every_model() {
    for (model, name) in models() {
        let verdict = verify(conf(model, &["main", "c"]), direct, direct_two)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let ConfVerdict::Reported(outcome) = &verdict else {
            panic!("{name}: an (M1) break must be reported; got {verdict:?}");
        };
        assert!(
            outcome
                .reports()
                .iter()
                .any(|r| matches!(r.cause(), ReportCause::NoCover)),
            "{name}: the cause must be NoCover, not merely 'some report'"
        );
    }
}

/// **Visible-error pairs, per model, with their expected cause** (§11.5's
/// fifth shape, and criterion 8's last clause).
///
/// §4.4: a *declared visible* thread's failed assertion is a conformance
/// report, because the theorem speaks about visible behaviour. An invisible
/// thread's failure is a diagnostic and must never reach here — that half is
/// `invisible_error_inertness` below.
///
/// **Mutation, MEASURED**: in `Must::conf_assert_failure`, route the *visible*
/// case to `record_invisible_error` too — i.e. replace the
/// `let Some(name) = visible else { .. }` binding by an unconditional
/// `record_invisible_error(fallback_name, pos); return;`. Applied at gate 3;
/// this test fails on
/// `a visible thread's failed assertion must be reported; got Conforms`.
///
/// **Mutation, REFUTED as a mutation**: the line this test used to carry —
/// "accept any `ReportCause`" — is a weakening of the test, which cannot make
/// it fail (criterion 19).
#[test]
fn visible_error_pairs_report_visible_error_under_every_model() {
    for (model, name) in models() {
        let verdict = verify(conf(model, &["main", "w"]), visible_error, visible_ok)
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let ConfVerdict::Reported(outcome) = &verdict else {
            panic!("{name}: a visible thread's failed assertion must be reported; got {verdict:?}");
        };
        assert!(
            outcome.reports().iter().any(|r| matches!(
                r.cause(),
                ReportCause::VisibleError { thread, .. } if thread == "w"
            )),
            "{name}: the cause must be VisibleError naming `w`; got {:?}",
            outcome.reports().iter().map(|r| r.cause()).collect::<Vec<_>>()
        );
    }
}

/// **Invisible-error inertness** (§11.5, Lemma inert observable; criterion 11).
///
/// An *invisible* thread's failed assertion on a dead branch must change
/// nothing: the report set is **identical** with and without it. Compared as
/// sets rather than counts, because two different reports of the same
/// cardinality would pass a count comparison.
///
/// **Rewritten by the developer at gate 3 — the previous fixture was inert
/// against its own named mutation.** It compared a pair that already reported
/// `NoCover` (`direct_two` against `direct`), and on a reporting run the extra
/// report is masked: routing the invisible failure to `report_visible_error`
/// left the rendered cause set unchanged and the test passed. Measured: with
/// the mutation applied the full lib suite failed **only** on
/// `gate_tests::c5_*` and `s5_tests::c2_*`, never here.
///
/// The base pair is therefore a **conforming** one, where the invisible
/// thread's failure is the only thing that could produce a report at all. Both
/// verdict *kind* and report set are compared, because a run that changed from
/// `Conforms` to `Reported` with one report would otherwise be compared as
/// `[] != [cause]` only by accident of rendering.
///
/// The failing assertion is **unconditional**, and that is deliberate. A first
/// attempt put it behind a receive that never returns — "dead" in the literal
/// sense — and measured at gate 3 that the mutation below still fails nothing,
/// because an assertion that never executes gives the reroute nothing to
/// reroute. "Dead branch" in Lemma inert observable is about what a visible
/// thread can *observe*, not about reachability.
///
/// **Mutation, MEASURED**: route an invisible thread's assertion failure to
/// `report_visible_error` instead of `record_invisible_error` — replace
/// `Must::conf_assert_failure`'s `let Some(name) = visible else { .. }` by
/// `let name = visible.unwrap_or(fallback_name);`. Applied at gate 3; this test
/// fails on a report set that gained an entry.
#[test]
fn an_invisible_threads_failed_assertion_changes_no_report() {
    fn without() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        send_msg(c.thread().id(), 1i32);
    }
    fn with_invisible_error() {
        let c = named("c", || {
            let _v: i32 = recv_msg_block();
        });
        // Invisible, and its assertion fails. "Dead" in Lemma inert
        // observable's sense — the branch contributes nothing a visible thread
        // can observe — not in the sense of unreachable: an assertion that
        // never executes gives the mutation nothing to reroute, which was
        // measured at gate 3 and is why this is unconditional.
        let _x = named("x", || crate::assert(false));
        send_msg(c.thread().id(), 1i32);
    }

    let render = |v: &ConfVerdict| -> (String, Vec<String>) {
        let kind = match v {
            ConfVerdict::Conforms(_) => "Conforms",
            ConfVerdict::Reported(_) => "Reported",
            ConfVerdict::Inconclusive(_) => "Inconclusive",
        }
        .to_owned();
        let mut out: Vec<String> = match v {
            ConfVerdict::Reported(o) => o
                .reports()
                .iter()
                .map(|r| format!("{:?}", r.cause()))
                .collect(),
            _ => Vec::new(),
        };
        out.sort();
        (kind, out)
    };

    let a = verify(conf(ConsType::FIFO, &["main", "c"]), without, direct).expect("run");
    let b = verify(
        conf(ConsType::FIFO, &["main", "c"]),
        with_invisible_error,
        direct,
    )
    .expect("run");

    assert_eq!(
        render(&a).0,
        "Conforms",
        "the base pair must conform, or the invisible failure has something to hide behind"
    );
    assert_eq!(
        render(&a),
        render(&b),
        "an invisible thread's failed assertion changed the verdict or the report set"
    );
}

// --- cross-model pairs -----------------------------------------------------

/// A pair whose sends use **three different communication models inside one
/// program**: `NoOrder`/asyn and `CausalOrder`/cd on two named channels, and
/// the run-global `FIFO`/p2p on the plain `send_msg` to the relay.
///
/// §11.5 asks for "cross-model sends within {asyn, p2p, cd}" *within a pair*,
/// and nothing in the tree had one: `send_msg` takes its model from the
/// run-global `cons_type`, so the only per-channel knob is
/// `channel::Builder::with_comm` (`channel.rs:48-51`), and the three tests
/// above run one single-model pair three times under three global
/// `cons_type`s — which satisfies the words and not the shape. The generator
/// has no cross-model mode either.
///
/// The pair is non-reflexive: the implementation routes `c1`'s value through an
/// invisible relay the specification does not have.
fn cross_model_relayed() {
    let (tx1, rx1) = crate::channel::Builder::<i32>::new()
        .with_comm(crate::CommunicationModel::NoOrder)
        .build();
    let (tx2, rx2) = crate::channel::Builder::<i32>::new()
        .with_comm(crate::CommunicationModel::CausalOrder)
        .build();
    let _c1 = named("c1", move || {
        let _v = rx1.recv_msg_block();
    });
    let _c2 = named("c2", move || {
        let _v = rx2.recv_msg_block();
    });
    // Invisible relay, reached by a plain `send_msg` under the *global* model.
    let r = named("r", move || {
        let v: i32 = recv_msg_block();
        tx1.send_msg(v);
    });
    send_msg(r.thread().id(), 1i32);
    tx2.send_msg(2i32);
}

fn cross_model_direct() {
    let (tx1, rx1) = crate::channel::Builder::<i32>::new()
        .with_comm(crate::CommunicationModel::NoOrder)
        .build();
    let (tx2, rx2) = crate::channel::Builder::<i32>::new()
        .with_comm(crate::CommunicationModel::CausalOrder)
        .build();
    let _c1 = named("c1", move || {
        let _v = rx1.recv_msg_block();
    });
    let _c2 = named("c2", move || {
        let _v = rx2.recv_msg_block();
    });
    tx1.send_msg(1i32);
    tx2.send_msg(2i32);
}

fn cross_model_direct_mutated() {
    let (tx1, rx1) = crate::channel::Builder::<i32>::new()
        .with_comm(crate::CommunicationModel::NoOrder)
        .build();
    let (tx2, rx2) = crate::channel::Builder::<i32>::new()
        .with_comm(crate::CommunicationModel::CausalOrder)
        .build();
    let _c1 = named("c1", move || {
        let _v = rx1.recv_msg_block();
    });
    let _c2 = named("c2", move || {
        let _v = rx2.recv_msg_block();
    });
    tx1.send_msg(1i32);
    tx2.send_msg(3i32);
}

/// **A cross-model pair is accepted and certifies** (criterion 9's per-channel
/// model requirement, criterion 12's first O-2 test).
///
/// The run-global `cons_type` is `FIFO`; the two channels override it to
/// `NoOrder` and `CausalOrder`. `ConfBuilder` accepts the configuration — the
/// §9 guards are at *handler* level, not config level, which is what makes a
/// per-channel escape hatch safe — and the non-reflexive pair certifies.
///
/// `main` is declared visible so the pair contains visible **sends** as well as
/// visible receives. Measured at gate 3: with only `c1`/`c2` visible the pair
/// has no visible send at all and the mutation below is inert on it, which is
/// the "passes for the wrong reason" shape this file is meant to avoid.
///
/// **Mutation, MEASURED**: give `Obs::Send` the send's destination, as in
/// `positive_pairs_certify_under_every_model`. Applied at gate 3 —
/// `a_cross_model_pair_is_in_scope_and_certifies ... FAILED`, 346 passed /
/// 16 failed — because `main`'s send goes to the relay in the implementation
/// and to the channel in the specification.
#[test]
fn a_cross_model_pair_is_in_scope_and_certifies() {
    let verdict = verify(
        conf(ConsType::FIFO, &["main", "c1", "c2"]),
        cross_model_relayed,
        cross_model_direct,
    )
    .expect("a per-channel model inside {asyn, p2p, cd} is in scope");
    assert!(
        matches!(verdict, ConfVerdict::Conforms(_)),
        "a cross-model invisible refactor must certify; got {verdict:?}"
    );
}

/// **And a cross-model negative reports**, so the positive above is not passing
/// because the harness cannot see anything on this shape at all.
///
/// **Mutation, MEASURED**: make `Obs`'s `PartialEq` ignore the value. Applied
/// at gate 3 — `a_cross_model_negative_pair_reports ... FAILED`, 328 passed /
/// 34 failed.
#[test]
fn a_cross_model_negative_pair_reports() {
    let verdict = verify(
        conf(ConsType::FIFO, &["main", "c1", "c2"]),
        cross_model_direct,
        cross_model_direct_mutated,
    )
    .expect("run");
    let ConfVerdict::Reported(outcome) = &verdict else {
        panic!("an (M1) break on the cd channel must be reported; got {verdict:?}");
    };
    assert!(
        outcome
            .reports()
            .iter()
            .any(|r| matches!(r.cause(), ReportCause::NoCover)),
        "the cause must be NoCover"
    );
}

/// **A per-channel `TotalOrder` is refused even though the global `cons_type`
/// is in scope** (criterion 12's second O-2 test).
///
/// Criterion 12 records that this "has no test in the tree today — every
/// existing scope test sets the model globally". **That is not so**, and the
/// record is corrected here rather than duplicated. Three families already do
/// it, all with `Builder::with_comm(CommunicationModel::TotalOrder)` under an
/// in-scope global `cons_type`:
///
/// - `gate_tests::c7_outer_run_rejects_a_total_order_send` / `_receive`,
/// - `s5_tests::c5_precheck_guard_total_order_send` / `_receive`,
/// - `prober::tests::an_out_of_scope_channel_is_refused_under_an_in_scope_config`
///   and `..._on_the_receive_side_too`, whose own rustdoc states the case
///   exactly: "a default (in-scope) config with an out-of-scope channel".
///
/// This test adds the one thing they do not show: that the refusal survives
/// *beside* an in-scope per-channel override in the same program, so it is the
/// send's own model that is checked and not the mere presence of an override.
/// It also pins that the refusal arrives as a **panic**, not an `Err` — a
/// caller of `verify` cannot handle it.
///
/// **Mutation, MEASURED**: disable the `TotalOrder` guard in `handle_send`
/// (`must.rs:966`). Applied at gate 3 —
/// `a_per_channel_total_order_send_is_refused_beside_in_scope_overrides ...
/// FAILED`, 356 passed / 6 failed.
#[test]
fn a_per_channel_total_order_send_is_refused_beside_in_scope_overrides() {
    fn with_a_mailbox_send() {
        let (tx1, rx1) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::NoOrder)
            .build();
        let (txm, _rxm) = crate::channel::Builder::<i32>::new()
            .with_comm(crate::CommunicationModel::TotalOrder)
            .build();
        let _c1 = named("c1", move || {
            let _v = rx1.recv_msg_block();
        });
        tx1.send_msg(1i32);
        txm.send_msg(9i32);
    }
    // §9's handler-level guards *panic* inside the model-checked thread rather
    // than returning `Err`, so the refusal is observed the way `gate_tests`
    // observes it. That is itself worth pinning: a caller of `verify` cannot
    // handle this as an error.
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = verify(
            conf(ConsType::FIFO, &["c1"]),
            with_a_mailbox_send,
            cross_model_direct,
        );
    }));
    std::panic::set_hook(previous);
    let payload = out.expect_err("a TotalOrder send is outside §9's fragment and must be refused");
    let rendered = payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .unwrap_or_else(|| "<non-string panic payload>".to_owned());
    assert!(
        rendered.contains("`a TotalOrder (mailbox) send` is outside conformance scope"),
        "the refusal must name the mailbox send; got {rendered}"
    );
}
