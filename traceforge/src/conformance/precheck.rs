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
//! # The third clause, built by Part 2 (`P4-ENUMERATOR` criterion 9)
//!
//! §5.4's third clause — "belt-and-braces: probe mode hard-errors on meeting a
//! `Block(Assert)`" (§3 item 10(d)) — now exists, in three pieces: a
//! specification assertion under *probe* takes `traceforge::assert`'s probe
//! branch, which installs the `Block(Assert)` and suspends the thread (no
//! print, no persisted failure, no panic); the inner search scans every probe
//! output (`search::spec_assertion`) and returns
//! `ObsError::SpecNotAssertionSafe`; the gate records it, writes the end
//! `SearchEnd::SpecNotAssertionSafe` first, makes every later gate inert, and
//! `run` returns `ConfError::SpecNotAssertionSafe` before any verdict. This
//! precheck remains the primary check; the in-search clause is the cheap
//! partial one. (Until Part 2 this comment recorded the clause as missing and
//! the probe path as printing and panicking; that was the defect
//! `s5_tests::f_probe_mode_has_no_block_assert_hard_error` pinned.)

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use crate::conformance::config::{CompletionCover, ConfConfig};
use crate::conformance::ctx::{ConfCtx, ConfMode, ReportKind};
use crate::conformance::obs::is_visible;
use crate::conformance::report::{ConfError, FlatEligibility};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::thread::main_thread_id;

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
) -> Result<Option<FlatEligibility>, ConfError> {
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
    let mut ctx = ConfCtx::gate_disabled(cc.config.clone(), cc.visible.clone(), ConfMode::Precheck);
    // `P4-FLAT` F1: only under `Flat` is every complete Spec graph kept for the
    // eligibility scan (memory `O(|Graphs(Spec)|)`); under `Sweep` the
    // precheck behaves exactly as before.
    let flat = cc.completion_cover == CompletionCover::Flat;
    if flat {
        ctx.collect_graphs();
    }
    must.borrow_mut().enable_conformance(ctx);

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
    Ok(if flat {
        Some(eligibility(ctx.collected(), &cc.visible))
    } else {
        None
    })
}

/// `P4-FLAT` F1/F5: the scan over the collected complete Spec graphs, in scan
/// order — graphs in completion order, threads by `ThreadId`, events by index.
pub(crate) fn eligibility(graphs: &[ExecutionGraph], visible: &[String]) -> FlatEligibility {
    let mut out = FlatEligibility {
        communication_flat: true,
        thread_flat: true,
        spec_graphs_scanned: graphs.len(),
        first_invisible: None,
    };
    for g in graphs {
        // `thread_ids()` is an ordered set: threads by `ThreadId`.
        for tid in g.thread_ids() {
            let name: Option<String> = g.get_thread_tclab(tid).name().clone();
            let declared = name
                .as_deref()
                .is_some_and(|n| visible.iter().any(|v| v == n));
            let mut communicates = false;
            for index in 0..g.thread_size(tid) as u32 {
                let e = Event::new(tid, index);
                if !matches!(g.label(e), LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_)) {
                    continue;
                }
                communicates = true;
                if !is_visible(g, e, visible) {
                    out.communication_flat = false;
                    if out.first_invisible.is_none() {
                        out.first_invisible =
                            Some((name.clone().unwrap_or_else(|| tid.to_string()), e.to_string()));
                    }
                }
            }
            // `flat.tex`'s class, read with TraceForge's undeclared `main`.
            if tid == main_thread_id() {
                if !declared && communicates {
                    out.thread_flat = false;
                }
            } else if !declared {
                out.thread_flat = false;
            }
        }
    }
    out
}
