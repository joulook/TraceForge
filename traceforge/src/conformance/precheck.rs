//! §5.4: the specification err-freedom precheck, default on.
//!
//! CA §7's A-candidate 5 assumes no specification graph contains `err`. With
//! the specification a Rust program that can `assert` anywhere, that assumption
//! is established by running it once, on its own, before the conformance
//! question is asked at all.
//!
//! # §5.4 and §9 were in direct conflict, and the amendment is here
//!
//! Blocked item **E**. §9 names the precheck as a *third engine* the config
//! predicate applies to and says the handler-entry guards are "armed in the
//! probe `Must` too … and in the err-freedom precheck run". §5.4 specified the
//! precheck as "one plain `verify` run of the Spec closure, same config,
//! **conformance off**" — and with `conf` and `probe` both `None`,
//! `assert_config_in_scope` is never called (its only callers are
//! `enable_probe` and `enable_conformance`) and every `reject_out_of_scope`
//! site is inert, because that function tests `probe.is_some() ||
//! conf.is_some()`. A specification using `inbox`, `sample`, a `TotalOrder`
//! channel, a monitor, symmetric spawning, a predetermined choice or a
//! symbolic constraint would run **unguarded** through the precheck and be
//! caught later, by a different engine, with a different message.
//!
//! **The owner amended §5.4, not §9**: the precheck gets a mode that arms both
//! layers. "Conformance's *gate* is off in that run; its *guards* are not."
//!
//! # A departure from the ruling's stated mechanism, stated
//!
//! The ruling's mechanism was "a precheck condition alongside
//! `probe.is_some() || conf.is_some()`" in `reject_out_of_scope`. That
//! condition is **not needed**, and adding it would be dead code: the precheck
//! engine here carries a gate-disabled `ConfCtx`, so `conf.is_some()` is
//! already true and the existing condition already fires. What *was* missing
//! is the engine's **name** in the message — `reject_out_of_scope` chose
//! between "probe" and "conformance" and had no third answer — and that is
//! what the touch-point adds. Blocked item **F**'s mechanism turned out to be
//! blocked item **E**'s mechanism; one flag serves both, which is why it is
//! worth saying rather than quietly doing.
//!
//! # What is *not* built, and belongs to S1
//!
//! §5.4's third clause — "belt-and-braces: probe mode hard-errors on meeting a
//! `Block(Assert)`" (§3 item 10(d)) — **does not exist on this tree**. There is
//! no such check in `handle_block`, in `lib.rs::assert`, or in `prober.rs`. A
//! specification assertion under *probe* therefore falls to `traceforge::assert`'s third branch's
//! branch: a raw graph dump to stdout (`traceforge::assert`'s third branch, its `print_graph` line), then a panic the probe
//! worker catches and re-raises on the gate's thread. That is a defect S5
//! exposes in S1 and is reported rather than fixed here.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::config::ConfConfig;
use crate::conformance::ctx::{ConfCtx, ConfMode, ReportKind};
use crate::conformance::report::ConfError;
use crate::must::Must;

/// Run the specification on its own and fail the conformance run if any
/// assertion fires.
///
/// Returns `Err(ConfError::SpecNotErrorFree)` rather than panicking, because
/// this is the outcome of a run that started legitimately (blocked item C's
/// ruling). A specification that is out of *scope*, by contrast, still
/// panics — that is "this program is not a valid input", and §9 asks for a
/// message naming the event.
pub(crate) fn run(
    cc: &ConfConfig,
    specification: &Arc<dyn Fn() + Send + Sync>,
) -> Result<(), ConfError> {
    // §9's third call site, explicit and named, as criterion 5 requires. It
    // runs *before* an engine exists, so an out-of-scope configuration is
    // refused without the precheck ever starting.
    crate::conformance::assert_config_in_scope(&cc.config, "precheck");

    // `explore` is generic over a *sized* closure, so the trait object is
    // wrapped rather than passed through. One allocation per precheck.
    let specification = Arc::clone(specification);
    let specification = Arc::new(move || specification());
    let must = Rc::new(RefCell::new(Must::new(cc.config.clone(), false)));
    // The gate is off — no probe worker, no `Cover` — and the guards are on,
    // because `conf.is_some()`.
    must.borrow_mut()
        .enable_conformance(ConfCtx::gate_disabled(
            cc.config.clone(),
            cc.visible.clone(),
            ConfMode::Precheck,
        ));

    crate::explore(&must, &specification);

    let must = must.borrow();
    let ctx = must
        .conf_ctx()
        .expect("conformance: the precheck context was taken and not put back");

    // Both halves of §4.4's split count here. The precheck's question is "can
    // any specification execution fail an assertion?", and an **invisible**
    // thread's failure is still a specification graph containing `err` — the
    // distinction that makes an invisible failure not a *conformance report*
    // is about the theorem's reach, not about err-freedom.
    if let Some(r) = ctx.reports().first() {
        let detail = match &r.kind {
            ReportKind::VisibleError { thread, pos } => format!(
                "A declared visible thread `{thread}` failed an assertion at {pos} during \
                 the precheck run of the specification."
            ),
            ReportKind::NoCover => {
                "The precheck recorded a cover failure, which a gate-disabled engine \
                 cannot produce; this is an internal inconsistency."
                    .to_owned()
            }
        };
        return Err(ConfError::SpecNotErrorFree { detail });
    }
    if let Some(d) = ctx.diagnostics().first() {
        return Err(ConfError::SpecNotErrorFree {
            detail: format!(
                "The thread `{}` failed an assertion at {} during the precheck run of the \
                 specification. It is not a declared visible thread, which changes what a \
                 *report* would mean but not whether the specification is error-free.",
                d.thread, d.pos
            ),
        });
    }
    Ok(())
}
