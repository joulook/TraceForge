//! Tests for S5: reports, triage, the precheck, the config layer and the
//! public entry.
//!
//! **These were written by the same agent that wrote S5's production code**,
//! which is not the arrangement S1–S4 had and is a real weakening of the
//! four-gate rule. The owner assigned it that way (§12: "developer, lead
//! reviews semantics"). The compensation is method, and it is recorded here so
//! a reviewer can check it rather than take it on trust: the required
//! properties were derived from `criteria/P3-S5-reports.md` and `conf-plan.md`
//! **before** any S5 code was written and before S4's tests were read, and
//! every derived property has exactly one disposition in the S5 report —
//! *tested by <name>*, *structurally undiscriminating because …*, or **open**.
//! A property with no test is an open item, not an audit row.
//!
//! Test names carry the criterion they discharge, so `cargo test --list` is
//! the coverage table.

#![cfg(test)]

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::conformance::config::{out_of_scope, ScopeField};
use crate::conformance::ctx::{ConfMode, Gate};
use crate::conformance::diagnose::{canonical_vis, Recompute};
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::report::{
    self, ConfNote, ConfVerdict, Diagnostics, NotACertificate, Obligation,
    ReplaySnapshot, ReportCause, ReportGate, SearchEnd, SpecErrFreedom, TriageFailure,
    TriageOutcome,
};
use crate::conformance::testing::{names, run_once};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;
use crate::conformance::{verify, verify_conformance, ConfBuilder, ConfError};
use crate::thread::{self, main_thread_id, ThreadId};
use crate::{Config, ConsType, SchedulePolicy};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn base(visible: &[&str]) -> ConfBuilder {
    ConfBuilder::new()
        .visible_threads(visible.to_vec())
        .cons_type(ConsType::FIFO)
}

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

/// The implementation used by most of the pairs below: two invisible senders
/// and one visible receive on `main`.
fn two_senders() {
    let m = main_thread_id();
    named("a", move || crate::send_msg(m, 1u64));
    named("b", move || crate::send_msg(m, 2u64));
    let _: u64 = crate::recv_msg_block();
}

/// A specification that cannot cover [`two_senders`]: `main` sends rather than
/// receives.
fn uncoverable_spec() {
    let w = named("w", || {
        let _: u64 = crate::recv_msg_block();
    });
    crate::send_msg(w, 99u64);
}

fn panic_message<F: FnOnce()>(f: F) -> Option<String> {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    std::panic::set_hook(previous);
    match out {
        Ok(()) => None,
        Err(p) => Some(
            p.downcast_ref::<&'static str>()
                .map(|s| (*s).to_owned())
                .or_else(|| p.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "<non-string panic payload>".to_owned()),
        ),
    }
}

/// Everything before an in-file `#[cfg(test)] mod … { … }`, keeping
/// `#[cfg(test)] mod foo;` declarations (which introduce no code here).
fn strip_inline_test_module(full: &str) -> String {
    let lines: Vec<&str> = full.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if line.trim_start() != "#[cfg(test)]" {
            continue;
        }
        let Some(next) = lines
            .iter()
            .skip(i + 1)
            .find(|l| !l.trim().is_empty())
            .map(|l| l.trim_start())
        else {
            continue;
        };
        // `mod tests {` opens a body; `mod gate_tests;` does not.
        if next.starts_with("mod ") || next.starts_with("pub(crate) mod ") || next.starts_with("pub mod ") {
            if next.ends_with('{') {
                return lines[..i].join("\n");
            }
            continue;
        }
    }
    full.to_owned()
}

fn conformance_sources() -> Vec<(String, String)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/conformance");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("src/conformance must be readable") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        let name = path.file_name().unwrap().to_str().unwrap().to_owned();
        out.push((name, std::fs::read_to_string(&path).unwrap()));
    }
    out.sort();
    out
}

/// The test modules. They are `#[cfg(test)]`, so nothing they print is in a
/// user's output at all, which is why they are out of criterion 1's domain
/// rather than allowlisted within it.
const TEST_ONLY_FILES: [&str; 13] = [
    "adversarial.rs",
    "bench.rs",
    "differential.rs",
    "differential_smoke.rs",
    "gate_tests.rs",
    "generator.rs",
    // §11.6's oracle and its examples. Both are `#[cfg(test)]` and neither is
    // reachable from the public API (S6 criterion 17), so they are test-only
    // in the same sense as the rest of this list.
    "oracle.rs",
    "oracle_tests.rs",
    "paper_examples.rs",
    "refinement_suite.rs",
    "s5_harden.rs",
    "s5_tests.rs",
    "testing.rs",
];

// ===========================================================================
// Criterion 1 --- a report does not claim more than §7.2 licenses.
//
// Three obligations, each a diff with an exit status, plus the snapshots.
// ===========================================================================

/// **Obligation 1**: one rendering module, and the domain is enumerable.
///
/// The scope is `traceforge/src/conformance/**` and nothing else — a crate-wide
/// grep returns 89 `println!`/`eprintln!` sites no S5 work can remove, which is
/// why the first version of this criterion was not checkable.
///
/// The allowlist, disposed of by name:
///
/// - **`obs.rs`'s `Display for ObsError`** (S2, `626748a`) — **exempt**. It is
///   consumed by `panic!` at `ConfCtx::gate`'s `ObsError` arm and by `search.rs`'s error
///   propagation, i.e. it is the text of a §8 *usage error*, which blocked item
///   C's ruling puts in criterion 1's domain as panic text rather than as
///   rendering. Moving it into `report.rs` would reopen S2's gate for a string
///   that is already covered by the third obligation below.
/// - **`ctx.rs`'s `Display for VisibleThreadError`** (S4, `8ebe6a3`) —
///   **exempt**, for the same reason: `ConfCtx::gate`'s spawn-order panic is `panic!("conformance:
///   {e}")`, so the string reaches the user through a panic and is checked as
///   panic text.
///
/// What would break it: adding a `println!` to any non-test file under
/// `conformance/`, or a `Display` impl anywhere but `report.rs`.
#[test]
fn c1_no_user_facing_emission_outside_the_rendering_module() {
    const ALLOWED_DISPLAY: [(&str, &str); 2] =
        [("obs.rs", "ObsError"), ("ctx.rs", "VisibleThreadError")];

    let mut offences: Vec<String> = Vec::new();
    for (name, body) in conformance_sources() {
        if TEST_ONLY_FILES.contains(&name.as_str()) {
            continue;
        }
        for (n, line) in body.lines().enumerate() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("//") || trimmed.starts_with("///") {
                continue;
            }
            for macro_name in ["println!", "eprintln!", "print!", "eprint!"] {
                if trimmed.contains(macro_name) {
                    offences.push(format!("{name}:{}: {macro_name}", n + 1));
                }
            }
            if trimmed.contains("Display for") {
                let allowed = ALLOWED_DISPLAY
                    .iter()
                    .any(|(f, ty)| *f == name && trimmed.contains(ty));
                if name != "report.rs" && !allowed {
                    offences.push(format!("{name}:{}: {trimmed}", n + 1));
                }
            }
        }
    }
    assert!(
        offences.is_empty(),
        "user-facing emission outside `report.rs` and off the allowlist:\n  {}",
        offences.join("\n  ")
    );
}

/// **Obligation 3**: panic text is in the domain, and it is checkable.
///
/// Blocked item C's ruling makes `panic!` the user-facing string for two of the
/// five outcome classes — §8's visible-thread violations and §9's scope
/// rejections — and none of them is a `println!`, so the first obligation
/// passes over all of them in silence.
///
/// The property asserted is the one the project already keeps by convention and
/// has never checked: **every panic-family message produced under
/// `conformance/` names its engine**, starting either with `conformance: ` or
/// with the `{engine}: ` prefix `assert_config_in_scope` uses. A message that
/// does not is one a user cannot attribute.
///
/// What would break it: a bare `panic!("something went wrong")` anywhere in the
/// module.
/// The pre-existing messages that name no engine, allowlisted **as findings**
/// and identified by their own text.
///
/// **The array is the count.** The first version of this doc said "exactly one
/// new instance" nine lines above an allowlist naming three, which is the
/// shape round 3 was mostly about: a right fix with a wrong sentence beside it
/// (round 3, M1). A number in prose beside a list in code is a claim nothing
/// checks; the list is now the only statement of how many there are.
///
/// All are outside S5's write scope, so they are reported rather than repaired
/// — finding **F-1**.
const PANIC_ALLOWLIST: [&str; 5] = [
    // `obs.rs`, `visible_events`' non-send `unreachable!`.
    "receive at {pos} reads from a {other}, not a send",
    // `morphism.rs`, `CompleteExecution::assume_finished_at_gate`'s `.expect`.
    // `#[track_caller]`, and reachable on the completion gate.
    "a finished execution has no running spawned thread",
    // `morphism.rs`, `statuses`' row re-resolution `.expect`. An internal
    // invariant note rather than a sentence for a user, allowlisted anyway:
    // the criterion's rule is about the *form*, and judging a message
    // unreachable is the kind of call this project has got wrong before.
    "checked resolved just above",
    // **The two the assert arms could not see** until round 3's M1 fixed the
    // parser. Neither is mis-attributed — both say "probe" — so they are
    // exempt on their merits rather than merely tolerated. They are listed
    // because the allowlist is the enumeration, and a pass nobody wrote down
    // is indistinguishable from a message nobody saw.
    //
    // `probe.rs`, `ProbeCtx::record`'s unconsumed-park tripwire.
    "probe: a choice point was recorded while an earlier park was still",
    // `prober.rs`, `probe_from`'s park-outlives-the-probe assertion.
    "probe ended with an unconsumed park",
];

/// The macro forms whose message a user can read, with **which argument the
/// message is**.
///
/// `panic!`/`unreachable!` and `.expect` put it first; the assert macros put a
/// *condition* first and the message after it — one argument along for
/// `assert!`, two for the `_eq`/`_ne` forms.
///
/// **Round 3's M1.** The assert macros were added to this list at round 2
/// without changing the mechanism, which tested the text immediately after the
/// opening paren. For those three that is the condition, never a message, so
/// the scan could not fire for half its declared domain — round 1's
/// `assert_eq!(1, 1)` shape, one level up — and two real messages were
/// invisible to it.
const PANIC_FAMILY: [(&str, usize); 8] = [
    ("panic!(", 0),
    ("unreachable!(", 0),
    ("todo!(", 0),
    ("unimplemented!(", 0),
    (".expect(", 0),
    ("assert!(", 1),
    ("assert_eq!(", 2),
    ("assert_ne!(", 2),
];

/// The message argument of the macro invocation whose opening paren ends at
/// `open`, or `None` if that argument is absent or is not a string literal.
///
/// Walks balanced parens/brackets/braces and skips string literals, so a comma
/// inside a message or inside a nested call does not split an argument.
fn message_argument(body: &str, open: usize, index: usize) -> Option<String> {
    let chars: Vec<char> = body[open..].chars().collect();
    let (mut depth, mut arg, mut start) = (0i32, 0usize, 0usize);
    let (mut in_str, mut escaped) = (false, false);
    for (i, c) in chars.iter().copied().enumerate() {
        if in_str {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            ',' if depth == 0 => {
                if arg == index {
                    return literal(&chars[start..i].iter().collect::<String>());
                }
                arg += 1;
                start = i + 1;
            }
            _ => {}
        }
    }
    (arg == index).then(|| literal(&chars[start..].iter().collect::<String>()))?
}

/// The leading string literal of one argument, whitespace-normalised, or
/// `None` if the argument does not begin with one.
fn literal(arg: &str) -> Option<String> {
    let t = arg.trim_start();
    if !t.starts_with('"') {
        return None;
    }
    let mut out = String::new();
    let mut escaped = false;
    for c in t.chars().skip(1) {
        if escaped {
            escaped = false;
            if c != '\n' {
                out.push(c);
            }
            continue;
        }
        match c {
            '\\' => escaped = true,
            '"' => break,
            '\n' => {}
            _ => out.push(c),
        }
    }
    Some(out.split_whitespace().collect::<Vec<_>>().join(" "))
}

fn normalised(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Every message of a form in [`PANIC_FAMILY`], under `conformance/`, outside
/// the test modules.
fn panic_messages() -> Vec<(String, usize, String)> {
    let mut out = Vec::new();
    for (name, full) in conformance_sources() {
        if TEST_ONLY_FILES.contains(&name.as_str()) {
            continue;
        }
        let body = strip_inline_test_module(&full);
        for (form, index) in PANIC_FAMILY {
            let mut from = 0usize;
            while let Some(at) = body[from..].find(form) {
                let open = from + at + form.len();
                from = open;
                if let Some(message) = message_argument(&body, open, index) {
                    let line = body[..open].matches('\n').count() + 1;
                    out.push((name.clone(), line, message));
                }
            }
        }
    }
    out
}

#[test]
fn c1_every_panic_message_under_conformance_names_its_engine() {
    let allow: Vec<String> = PANIC_ALLOWLIST.iter().copied().map(normalised).collect();
    let messages = panic_messages();

    // **The parser has to find messages**, or the check passes by seeing
    // nothing. This is the mechanism half of round 3's M1: the previous
    // version tested the text immediately after the opening paren, which for
    // the three assert macros is a condition, so half the declared domain was
    // invisible and the control could not fail there.
    assert!(
        messages.len() > 40,
        "the scan found only {} messages under `conformance/`, too few for it to be reading \
         the module --- suspect the parser rather than the module",
        messages.len()
    );

    let offences: Vec<String> = messages
        .iter()
        .filter(|(_, _, m)| {
            !m.starts_with("conformance:")
                && !m.starts_with("{engine}:")
                && !allow.iter().any(|a| m.starts_with(a.as_str()))
        })
        .map(|(f, l, m)| format!("{f}:{l}: {m}"))
        .collect();
    assert!(
        offences.is_empty(),
        "panic-family text that does not name its engine:\n  {}",
        offences.join("\n  ")
    );
}

/// Every allowlisted message is **still there**, so the allowlist enumerates
/// live findings rather than strings that once matched something.
///
/// What would break it: S1 or S2 fixing one of F-1's instances without this
/// list following — which is the outcome F-1 asks for, and which should fail
/// here so the finding is closed rather than left standing.
#[test]
fn c1_the_panic_allowlist_has_no_stale_entries() {
    let messages = panic_messages();
    let missing: Vec<&str> = PANIC_ALLOWLIST
        .iter()
        .copied()
        .filter(|entry| {
            let key = normalised(entry);
            !messages.iter().any(|(_, _, m)| m.starts_with(key.as_str()))
        })
        .collect();
    assert!(
        missing.is_empty(),
        "allowlisted messages that no longer exist --- F-1 may be partly closed, and this \
         list must shrink with it:\n  {missing:#?}"
    );
}

/// **Snapshots**: the qualifying clause is present, one per outcome kind.
///
/// A wording regression fails here instead of shipping. The three clauses are
/// §7.2's, and they are asserted *by their constants*, so the test cannot drift
/// from the text.
///
/// What would break it: deleting any of the three sentences from
/// `ConfVerdict`'s `Display`.
#[test]
fn c1_a_reported_verdict_carries_every_qualifier() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .expect("this pair produces reports, not an error");
    assert!(
        matches!(v, ConfVerdict::Reported(_)),
        "the pair stopped reporting, so the snapshot has nothing to pin: {v:?}"
    );
    let text = v.to_string();
    for clause in [
        report::CANDIDATE_VIOLATION,
        report::NOT_A_COMPLETE_SET,
        report::ONLY_SILENCE_IS_A_VERDICT,
        report::RESIDUAL_SOURCES,
        report::SETTLED_CLAIM,
        report::UNSETTLED_CLAIM,
    ] {
        assert!(
            text.contains(clause),
            "a reported verdict dropped a required qualifier:\n  {clause}\n--- rendering ---\n{text}"
        );
    }
    assert!(
        !text.contains("violation found"),
        "the rendering claimed a violation outright"
    );
}

/// The two claims stay apart (§7.2's precision point).
///
/// CA §7 conflates the reported graph's event-extensions — settled by Lemma
/// gate — with non-exhaustiveness, which is A1 and is not settled. The tool
/// must not repeat the conflation its own design document corrects, and with
/// two fixed strings that is checkable by reading them rather than by auditing
/// prose.
///
/// What would break it: merging the two sentences, or giving either one the
/// other's subject.
#[test]
fn c1_the_settled_and_unsettled_claims_are_separate_sentences() {
    assert!(
        report::SETTLED_CLAIM.contains("event-extension"),
        "the settled claim stopped being about event-extensions"
    );
    assert!(
        !report::SETTLED_CLAIM.contains("complete set")
            && !report::SETTLED_CLAIM.contains("report list"),
        "the settled claim acquired non-exhaustiveness as a subject"
    );
    assert!(
        report::UNSETTLED_CLAIM.contains("report list"),
        "the unsettled claim stopped being about the report list"
    );
    assert!(
        !report::UNSETTLED_CLAIM.contains("event-extension"),
        "the unsettled claim acquired the settled subject"
    );
}

/// A certificate says it is one, and says what it rests on.
#[test]
fn c1_a_certificate_names_its_assumptions() {
    let v = verify(base(&["main"]).build().unwrap(), two_senders, two_senders)
        .expect("an identical pair cannot error");
    let ConfVerdict::Conforms(c) = &v else {
        panic!("an identical pair did not certify: {v:?}\n{v}");
    };
    let text = v.to_string();
    assert!(text.contains(report::ONLY_SILENCE_IS_A_VERDICT));
    assert!(
        c.assumptions()
            .iter()
            .any(|a| a.contains("A4 transport gap")),
        "the certificate did not name the open transport gap"
    );
    // The phrase appears once, negated. What must not appear is a *report*,
    // which is the only thing that renders the phrase affirmatively.
    assert!(
        text.contains("No candidate violation"),
        "a certificate did not say it found none:\n{text}"
    );
    assert_eq!(
        text.matches(report::CANDIDATE_VIOLATION).count(),
        1,
        "a certificate mentioned a candidate violation more than once:\n{text}"
    );
}

// ===========================================================================
// Criterion 2 --- every outcome stays distinguishable to the user.
// ===========================================================================

/// An exhaustion is not silence, and it names its remedy.
///
/// With a zero budget every `Cover` call exhausts, so the run reports nothing —
/// and that is exactly the failure mode the criterion names: "a user set the
/// budget too low and got a clean-looking result".
///
/// What would break it: making `ConfVerdict::of` treat an empty report list as
/// a certificate, or dropping the budget or the knob from the exhaustion's
/// rendering.
#[test]
fn c2_an_exhaustion_is_not_silence_and_names_its_budget_and_knob() {
    let v = verify(
        base(&["main"]).search_budget(0).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .unwrap();
    assert!(
        v.outcome().reports().is_empty(),
        "a zero budget established nothing and must report nothing"
    );
    assert!(
        !v.outcome().exhaustions().is_empty(),
        "a zero budget produced no exhaustion, so nothing is under test"
    );
    assert!(
        matches!(v, ConfVerdict::Inconclusive(_)),
        "an exhausted run passed as something other than inconclusive: {v:?}"
    );
    let text = v.to_string();
    assert!(text.contains(report::BUDGET_KNOB), "no knob named:\n{text}");
    assert!(
        text.contains("budget of 0 nodes") || text.contains("all 0 of its nodes"),
        "the budget that was hit was not named:\n{text}"
    );
}

/// `stop_at_first_report` produces an outcome that is **not** a certificate
/// even when it produces no report.
///
/// What would break it: inferring "the search completed" from an empty report
/// list, or setting `config.max_iterations` from the gate instead of using the
/// flag.
#[test]
fn c2_stop_at_first_report_alone_cannot_produce_a_silent_looking_outcome() {
    // A pair that conforms, but with the flag set. There is no report, so the
    // flag never fires — and the run *does* complete, so this must still be a
    // certificate. The discriminating case is the one below.
    let v = verify(
        base(&["main"])
            .stop_at_first_report(true)
            .build()
            .unwrap(),
        two_senders,
        two_senders,
    )
    .unwrap();
    assert!(
        matches!(v, ConfVerdict::Conforms(_)),
        "a completed run with the flag set and no report is still a certificate: {v:?}"
    );

    // Now the discriminating case: the flag fires.
    let v = verify(
        base(&["main"])
            .stop_at_first_report(true)
            .build()
            .unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .unwrap();
    assert_eq!(
        v.outcome().end(),
        SearchEnd::StoppedAtFirstReport,
        "the outer loop did not stop on the first report"
    );
    assert_eq!(
        v.outcome().reports().len(),
        1,
        "stop-at-first produced more than one report"
    );
    assert!(v
        .outcome()
        .not_a_certificate()
        .iter()
        .any(|r| matches!(r, NotACertificate::StoppedAtFirstReport)));
}

/// `max_iterations` alone cannot produce a silent-looking outcome.
///
/// Blocked item B's worked example: a conformance run with `max_iterations =
/// 1` that reports nothing is silence that means nothing, and before S5 nothing
/// anywhere noticed. It is **recorded**, not rejected: a bounded run is a
/// legitimate thing to ask for.
///
/// What would break it: adding `max_iterations` to §9's rejections (which would
/// make this a `ConfigError` instead — a different and wrong answer), or
/// dropping `SearchEnd::MaxIterations`.
#[test]
fn c2_max_iterations_alone_cannot_produce_a_silent_looking_outcome() {
    let config = Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_max_iterations(1)
        .build();
    let cc = base(&["main"]).config(config).build().unwrap();
    assert_eq!(cc.max_iterations(), Some(1), "the bound was not recorded");

    let v = verify(cc, two_senders, two_senders).unwrap();
    assert_eq!(v.outcome().end(), SearchEnd::MaxIterations(1));
    assert!(
        matches!(v, ConfVerdict::Inconclusive(_)),
        "a bounded run passed as a certificate: {v:?}"
    );
    assert!(v
        .outcome()
        .not_a_certificate()
        .iter()
        .any(|r| matches!(r, NotACertificate::BoundedRun { max_iterations: 1 })));
    assert!(v.to_string().contains("bounded run"));
}

/// The five-way partition reaches the user distinctly: report, exhaustion,
/// note, error, panic.
///
/// What would break it: folding any two of them into one type or one rendering.
#[test]
fn c2_the_five_outcome_classes_are_distinguishable() {
    // 1. report, and 3. note (an invisible thread's assertion) in one run.
    let v = verify(
        base(&["main"]).build().unwrap(),
        || {
            named("hidden", || crate::assert(false));
            let m = main_thread_id();
            named("a", move || crate::send_msg(m, 1u64));
            let _: u64 = crate::recv_msg_block();
        },
        uncoverable_spec,
    )
    .unwrap();
    assert!(!v.outcome().reports().is_empty(), "no report: {v:?}");
    assert!(
        v.outcome()
            .notes()
            .iter()
            .any(|n| matches!(n, ConfNote::InvisibleThread { .. })),
        "the invisible thread's assertion did not arrive as a note"
    );
    let text = v.to_string();
    assert!(text.contains("none of these is a report"));

    // 2. exhaustion --- covered by its own test above.
    // 4. error.
    let e = verify(
        base(&["main"]).build().unwrap(),
        || {},
        || crate::assert(false),
    )
    .expect_err("a specification that asserts must fail the run");
    assert!(matches!(e, ConfError::SpecNotErrorFree { .. }), "{e:?}");

    // 5. the documented panic.
    let msg = panic_message(|| {
        let _ = verify(
            base(&["main"]).build().unwrap(),
            || {
                let _ = crate::inbox();
            },
            || {},
        );
    })
    .expect("an out-of-scope implementation must panic");
    assert!(msg.contains("outside conformance scope"), "{msg}");
}

// ===========================================================================
// Criterion 3 --- triage is a second engine run.
// ===========================================================================

/// Triage completes the reported graph and reproduces its prefix.
///
/// "Reproduced byte-for-byte" is checked the way the engine itself checks it:
/// `validate_replay_event` compares every replayed label against the recorded
/// one and panics on divergence, and that panic would arrive here as a
/// `TriageFailure`. A triage that returns `Completed` has therefore replayed
/// the prefix without structural divergence.
///
/// **And "byte-for-byte" is narrower than §7.3's wording suggests**: the
/// `SendMsg` arm of `compare_for_replay` skips the value comparison when the
/// recorded value is pending, which it is for a re-executed send. See
/// `f_a_value_only_replay_divergence_is_not_caught`, which is the honest
/// statement of what this check does and does not establish.
///
/// What would break it: replacing `with_initial_graph` with an empty graph
/// (the completed trace would no longer extend the reported one), or turning
/// the replay divergence panic into a silent restart.
#[test]
fn c3_triage_completes_the_reported_graph_and_reproduces_its_prefix() {
    let v = verify(
        base(&["main"]).triage(true).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .expect("triage must not fail on a deterministic implementation");
    let reports = v.outcome().reports();
    assert!(!reports.is_empty(), "no report to triage");
    let mut completed = 0;
    for r in reports {
        let t = r.triage().expect("triage was on, so every report has one");
        match t {
            TriageOutcome::Completed { vis, dump, .. } => {
                completed += 1;
                assert!(
                    !dump.is_empty(),
                    "a completed triage produced no graph dump"
                );
                assert!(
                    !vis.statuses().is_empty(),
                    "a completed triage produced no status vector"
                );
            }
            TriageOutcome::Blocked { .. } => {}
            other => panic!("unexpected triage outcome on a NoCover report: {other:?}"),
        }
    }
    assert!(
        completed > 0,
        "every report's completion blocked, so the completing path is untested here"
    );
}

/// `max_iterations = 1` leaves **exactly one execution, and that execution is
/// a complete one** where it completes at all.
///
/// "Exactly one execution" alone passes vacuously in the blocked-completion
/// case, which is the failure it was written to catch — §7.3's cutoff at
/// `record_ending_telemetry`'s `max_iterations` test compares against `num_execs + num_blocked`, so one *blocked*
/// ending satisfies it. The engine half is asserted directly here.
///
/// What would break it: a `max_iterations` other than 1 in `triage.rs`, or
/// treating a blocked ending as a completion.
#[test]
fn c3_triage_runs_exactly_one_execution_and_says_when_it_did_not_complete() {
    use crate::conformance::triage::TRIAGE_MAX_ITERATIONS;
    assert_eq!(
        TRIAGE_MAX_ITERATIONS, 1,
        "triage stopped discarding revisits, so the `recvs`-staleness argument lapses \
         (see `triage.rs`)"
    );

    // Ex. blocking: the implementation's `main` blocks on a receive with
    // nothing to read, the specification's finishes. Same word (empty), a
    // different status vector — so the completion gate reports, and the
    // reported graph is a *blocked* one that triage cannot complete.
    let v = verify(
        base(&["main"]).triage(true).build().unwrap(),
        || {
            let _: u64 = crate::recv_msg_block();
        },
        || {},
    )
    .expect("triage must not fail here");
    let reports = v.outcome().reports();
    assert!(
        !reports.is_empty(),
        "Ex. blocking did not report, so the status conjunct is not doing its work"
    );
    assert!(
        reports
            .iter()
            .all(|r| matches!(r.triage(), Some(TriageOutcome::Blocked { .. }))),
        "a doomed, blocked graph was presented as a completed trace: {:?}",
        reports.iter().map(|r| r.triage()).collect::<Vec<_>>()
    );
    let text = v.to_string();
    assert!(
        text.contains("triage could not complete this graph"),
        "the degraded rendering is missing:\n{text}"
    );
    assert!(
        !text.contains("triage completed this graph"),
        "a blocked completion claimed to be a complete trace:\n{text}"
    );
}

/// A triage run writes **no counterexample file**, and the test is not vacuous:
/// `with_error_trace` is configured.
///
/// The default `error_trace_file` is `None`, under which
/// `store_replay_information` warns and writes nothing regardless — so the
/// existing form of this check passes for a reason that has nothing to do with
/// conformance. With the filename configured, the only thing standing between
/// triage and a file per report is the `conf.is_some()` early return at
/// `store_replay_information`'s conformance early return, which the gate-disabled `ConfCtx` keeps armed.
///
/// What would break it: giving triage `conf: None` (blocked item F's rejected
/// option), or deleting the exemption.
#[test]
fn c3_triage_writes_no_counterexample_file_with_error_trace_configured() {
    let dir = std::env::temp_dir().join(format!(
        "traceforge-s5-triage-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("triage.trace");

    let config = Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_error_trace(file.to_str().unwrap())
        .build();
    let v = verify(
        base(&["main"]).config(config).triage(true).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .expect("triage must not fail here");
    assert!(!v.outcome().reports().is_empty(), "nothing was triaged");
    assert!(
        !file.exists(),
        "triage wrote a counterexample file at {file:?} --- the \
         `store_replay_information` exemption is not armed"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A report whose implementation asserts on a visible thread, triaged: no
/// counterexample file, no stray output, and the outcome is a **replayed
/// assertion**.
///
/// This is the case blocked item F is about. With `conf: None` the triage
/// engine would take `traceforge::assert`'s branch 3 — a printed graph and a
/// panic — or branch 2, which latches the process's panic hook.
///
/// What would break it: the `conf: None` triage, or classifying the replayed
/// assertion as nondeterminism.
#[test]
fn c4_a_replayed_assertion_is_not_reported_as_a_nondeterministic_implementation() {
    let dir = std::env::temp_dir().join(format!(
        "traceforge-s5-assert-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("assert.trace");
    let config = Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_error_trace(file.to_str().unwrap())
        .build();

    let v = verify(
        base(&["main"]).config(config).triage(true).build().unwrap(),
        || crate::assert(false),
        || {},
    )
    .expect("a replayed assertion is not a triage failure");
    let reports = v.outcome().reports();
    assert_eq!(reports.len(), 1, "expected one visible-error report");
    assert!(matches!(
        reports[0].cause(),
        ReportCause::VisibleError { .. }
    ));
    assert_eq!(reports[0].gate(), ReportGate::NotAGate);
    match reports[0].triage() {
        Some(TriageOutcome::ReplayedAssertion { .. }) => {}
        other => panic!("a replayed assertion was classified as {other:?}"),
    }
    let text = v.to_string();
    assert!(
        text.contains("not** a nondeterministic implementation")
            || text.contains("not a nondeterministic implementation"),
        "the rendering did not distinguish a replayed assertion:\n{text}"
    );
    assert!(!file.exists(), "triage wrote a counterexample file");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A deliberately nondeterministic implementation fails **loudly**, as a
/// `ConfError`, and names replay divergence rather than anything else.
///
/// What would break it: swallowing the triage panic, or classifying every
/// escaped panic as nondeterminism (which would make this test pass for the
/// wrong reason — hence the companion test above, which must *not* classify).
#[test]
fn c4_a_nondeterministic_implementation_fails_triage_loudly() {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    COUNTER.store(0, Ordering::SeqCst);

    let e = verify(
        base(&["main"]).triage(true).build().unwrap(),
        || {
            // The divergence is **structural** — a differently named thread at
            // the same position — and it is on `main`'s own row, which the
            // reported graph contains and triage therefore replays. A
            // *value*-only divergence would not be caught; see
            // `f_a_value_only_replay_divergence_is_not_caught`.
            let n = COUNTER.fetch_add(1, Ordering::SeqCst);
            let w = if n == 0 {
                named("w", || {
                    let _: u64 = crate::recv_msg_block();
                })
            } else {
                named("other", || {
                    let _: u64 = crate::recv_msg_block();
                })
            };
            crate::send_msg(w, 1u64);
        },
        || {},
    );
    match e {
        Err(ConfError::TriageFailed {
            cause: TriageFailure::NondeterministicImpl { detail },
            ..
        }) => {
            assert!(
                detail.contains("Incorrect TraceForge Program"),
                "the origin was not carried: {detail}"
            );
            assert!(
                detail.contains("named"),
                "the divergence itself was not carried: {detail}"
            );
        }
        other => panic!("a nondeterministic implementation did not fail triage loudly: {other:?}"),
    }
}

/// The `recvs`-staleness argument, pinned — **and the staleness itself
/// observed**, which the first version claimed in its rustdoc and asserted
/// nowhere (gate-4 round 1, M1).
///
/// The `FreshRecv` gate fires at two sites inside `visit_rfs`, both **before**
/// `register_recv`, so a graph cloned at either is missing that receive's entry
/// in `ExecutionGraph::recvs`. The index is private, but `rev_matching_recvs`
/// reads it and is the only thing that does — so the shape is observable: on a
/// graph captured at a `FreshRecv` gate the receive is **absent** from the
/// sends's matching-receive list, and on the same program's completed graph it
/// is present.
///
/// The harm is bounded because `rev_matching_recvs`' only callers are the
/// backward-revisit computation, and triage discards its revisits under
/// `max_iterations = TRIAGE_MAX_ITERATIONS`. That constant is now **read by
/// `triage.rs`** rather than merely declared beside it, so the assertion below
/// is a real break-condition: setting it to 2 changes what triage does and
/// fails this test.
///
/// What would break it: raising triage's `max_iterations`; or the `FreshRecv`
/// gate moving after `register_recv`, at which point the staleness half of
/// this test fails and the argument is no longer needed.
#[test]
fn c3_the_recvs_staleness_argument_is_pinned_to_triage_discarding_revisits() {
    use crate::conformance::triage::TRIAGE_MAX_ITERATIONS;
    assert_eq!(
        TRIAGE_MAX_ITERATIONS, 1,
        "triage no longer discards its revisits, so `rev_matching_recvs` can read the \
         stale `recvs` index of a graph captured at a `FreshRecv` gate. Normalise the \
         index before triage uses it."
    );

    // A pair whose first *reporting* gate is a receive: `main` is invisible, so
    // the send gate finds a cover (both sides' `w` rows are still empty) and the
    // receive gate is where the values diverge.
    let implementation = || {
        let w = named("w", || {
            let _: u64 = crate::recv_msg_block();
        });
        crate::send_msg(w, 1u64);
    };
    let out = verify_conformance(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        implementation,
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 2u64);
        },
        names(&["w"]),
        4096,
    );
    let captured = out
        .reports
        .iter()
        .find(|r| r.gate == Some(Gate::FreshRecv))
        .map(|r| r.graph.clone())
        .expect("no report was raised at a `FreshRecv` gate, so the capture point the                  staleness argument is about was never reached");

    assert!(
        !recv_is_indexed(&captured),
        "the receive *is* in the `recvs` index of a graph captured at a `FreshRecv` gate, \
         so the gate no longer precedes `register_recv` and this argument is obsolete"
    );

    // The control: on a completed run of the same program the index is built,
    // so the absence above is the capture point and not the helper.
    let complete = run_once(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        implementation,
    );
    assert!(
        recv_is_indexed(&complete),
        "the receive is absent from a *completed* graph's `recvs` index too, so this test \
         observes nothing about the capture point"
    );
}

/// Is the graph's single receive listed against the send it reads?
///
/// `ExecutionGraph::recvs` is private; `rev_matching_recvs` is the only reader
/// and is `pub(crate)`, so this asks it the question the index exists to
/// answer.
fn recv_is_indexed(graph: &ExecutionGraph) -> bool {
    let events: Vec<Event> = graph
        .thread_ids()
        .into_iter()
        .flat_map(|t| (0..graph.thread_size(t) as u32).map(move |i| Event::new(t, i)))
        .collect();
    let send = events
        .iter()
        .find_map(|e| match graph.label(*e) {
            LabelEnum::SendMsg(s) => Some(s.clone()),
            _ => None,
        })
        .expect("the program under test has no send, so this helper has nothing to ask about");
    let indexed = graph.rev_matching_recvs(&send).next().is_some();
    indexed
}

// ===========================================================================
// Criterion 5 --- the err-freedom precheck.
// ===========================================================================

/// The precheck is default-on and fails the run.
///
/// What would break it: defaulting `skip_spec_errfree_check` to true, or
/// turning the precheck's finding into a warning.
#[test]
fn c5_the_precheck_fires_by_default_on_a_specification_that_asserts() {
    let e = verify(
        base(&["main"]).build().unwrap(),
        || {},
        || crate::assert(false),
    )
    .expect_err("a specification that asserts must fail the run");
    let ConfError::SpecNotErrorFree { detail } = &e else {
        panic!("wrong error: {e:?}");
    };
    assert!(detail.contains("failed an assertion"), "{detail}");
    assert!(e.to_string().contains("not well posed"));
}

/// The opt-out **records the assumption**.
///
/// An opt-out that leaves no trace is a silent change of what the verdict
/// means. With the precheck skipped, the same specification produces a verdict
/// — and the verdict says what it did not check.
///
/// What would break it: dropping `SpecErrFreedom` from the outcome, or
/// rendering a certificate without its assumptions.
#[test]
fn c5_the_precheck_opt_out_records_the_assumption() {
    let v = verify(
        base(&["main"])
            .skip_spec_errfree_check(true)
            .build()
            .unwrap(),
        two_senders,
        two_senders,
    )
    .expect("the precheck was skipped, so it cannot fail");
    assert_eq!(v.outcome().spec_err_freedom(), SpecErrFreedom::Assumed);
    let ConfVerdict::Conforms(c) = &v else {
        panic!("expected a certificate: {v:?}");
    };
    assert!(
        c.assumptions().iter().any(|a| a.contains("was assumed")),
        "the skipped precheck left no trace in the certificate"
    );
    assert!(v.to_string().contains("skip_spec_errfree_check"));
}

/// **One test per §9 guard kind, rejected *by the precheck*.**
///
/// Not merely "later, by the probe, with a different message": the assertion is
/// on the engine name, which only the precheck produces. Before S5 the precheck
/// did not exist, and §5.4's "conformance off" would have left every one of
/// these inert there.
///
/// The guard kinds are the `reject_out_of_scope` **call sites** — the
/// discriminator in the source, not §9's prose. Eight of them:
/// `monitor registration` (`reject_out_of_scope("monitor registration")`), `a TotalOrder (mailbox) receive`
/// (`:768`), `inbox` (`:903`), `a TotalOrder (mailbox) send` (`:946`),
/// `symmetric thread spawning` (`:1096`), `predetermined named choice`
/// (`:1249`), `sample` (`:1337`), `symbolic constraint evaluation` (`:1402`).
/// Seven are reachable; `predetermined named choice` is §3 item 13's backstop
/// and is unreachable while the config carrying it is refused at build time —
/// disposed of below rather than left out.
///
/// What would break it: reverting the engine label, or giving the precheck
/// `conf: None` (every one of these would then run unguarded).
fn assert_precheck_guard<F>(expected: &str, specification: F)
where
    F: Fn() + Send + Sync + 'static,
{
    let message = panic_message(move || {
        let _ = verify(base(&["main"]).build().unwrap(), || {}, specification);
    })
    .unwrap_or_else(|| panic!("the precheck accepted `{expected}` and the run returned normally"));
    // TraceForge's own panic hook wraps the payload ("A panic was detected\noriginal
    // panic: ..."), so the engine name is *inside* the payload rather than at its start.
    assert!(
        message.contains("precheck:"),
        "the rejection did not come from the precheck engine (so §5.4's guards are inert \
         there, or the message lost its engine).\n  wanted a `precheck:` prefix\n  got: \
         {message}"
    );
    assert!(
        message.contains(expected),
        "the precheck's rejection did not name the event.\n  wanted: {expected}\n  got: {message}"
    );
}

struct NoopMonitor;
impl crate::monitor_types::Monitor for NoopMonitor {}
fn no_create(_: ThreadId, _: ThreadId, _: crate::Val) -> Option<crate::Val> {
    None
}
fn no_accept(_: ThreadId, _: ThreadId, _: crate::Val) -> bool {
    false
}

#[test]
fn c5_precheck_guard_inbox() {
    assert_precheck_guard("`inbox` is outside conformance scope", || {
        let _ = crate::inbox();
    });
}

#[test]
fn c5_precheck_guard_sample() {
    assert_precheck_guard("`sample` is outside conformance scope", || {
        let _: i64 = crate::sample(rand::distr::Uniform::new(0i64, 3i64).unwrap(), 2);
    });
}

#[test]
fn c5_precheck_guard_total_order_send() {
    assert_precheck_guard(
        "`a TotalOrder (mailbox) send` is outside conformance scope",
        || {
            let (tx, _rx) = crate::channel::Builder::<i32>::new()
                .with_comm(crate::CommunicationModel::TotalOrder)
                .build();
            tx.send_msg(1);
        },
    );
}

#[test]
fn c5_precheck_guard_total_order_receive() {
    assert_precheck_guard(
        "`a TotalOrder (mailbox) receive` is outside conformance scope",
        || {
            let (_tx, rx) = crate::channel::Builder::<i32>::new()
                .with_comm(crate::CommunicationModel::TotalOrder)
                .build();
            let _ = rx.recv_msg();
        },
    );
}

#[test]
fn c5_precheck_guard_symmetric_spawning() {
    assert_precheck_guard(
        "`symmetric thread spawning` is outside conformance scope",
        || {
            let m = main_thread_id();
            let a = thread::spawn(move || crate::send_msg(m, 1u64));
            let _ = crate::spawn_symmetric(move || crate::send_msg(m, 1u64), a.thread().id());
        },
    );
}

#[test]
fn c5_precheck_guard_monitor_registration() {
    assert_precheck_guard("`monitor registration` is outside conformance scope", || {
        let m: std::sync::Arc<std::sync::Mutex<dyn crate::monitor_types::Monitor>> =
            std::sync::Arc::new(std::sync::Mutex::new(NoopMonitor));
        let _: crate::thread::JoinHandle<u64> =
            crate::spawn_monitor(|| 0u64, no_create, no_accept, m);
    });
}

#[test]
#[cfg(feature = "symbolic")]
fn c5_precheck_guard_symbolic() {
    assert_precheck_guard(
        "`symbolic constraint evaluation` is outside conformance scope",
        || {
            let b = crate::symbolic::fresh_bool();
            let _ = crate::symbolic::eval(b);
        },
    );
}

/// The eighth guard kind, `predetermined named choice`, disposed of rather than
/// omitted.
///
/// It is §3 item 13's backstop: predetermined named choices are excluded from
/// v1 by §9, so with the config refused the handler is unreachable, and the
/// guard turns a miss into a loud error instead of an unparked choice escaping
/// user code. What is checkable here is that the config really is refused
/// before an engine exists — which is what makes the handler unreachable.
///
/// What would break it: removing either predetermined map from the build-time
/// rejections, which would make the backstop reachable and this argument false.
#[test]
fn c5_precheck_guard_predetermined_named_choice_is_unreachable_by_construction() {
    let mut m = HashMap::new();
    m.insert("c".to_owned(), vec![vec![true]]);
    let config = Config::builder()
        .with_cons_type(ConsType::FIFO)
        .with_predetermined_choices(m)
        .build();
    let err = base(&["main"])
        .config(config)
        .build()
        .err()
        .expect("a predetermined-choice config must be refused");
    assert_eq!(err.field(), ScopeField::PredeterminedChoices);
}

/// §5.4 clause (iii) is **not built**, and this records what happens instead.
///
/// "Belt-and-braces: probe mode hard-errors on meeting a `Block(Assert)`" (§3
/// item 10(d)). There is no such check on this tree — no `BlockType::Assert`
/// arm in `handle_block`, none in `lib.rs::assert`'s probe path, none in
/// `prober.rs`. With the precheck **skipped**, a specification that asserts
/// therefore reaches `traceforge::assert`'s third branch's branch on the *probe* engine: a raw graph
/// dump to stdout and then a panic the probe worker catches and re-raises.
///
/// The test asserts the observed behaviour rather than the designed one, and
/// names it a defect, because repairing it is S1's work and outside S5's write
/// scope. What would break it: S1 building the designed hard error — at which
/// point this test should be rewritten to assert *that*.
#[test]
fn f_probe_mode_has_no_block_assert_hard_error() {
    let message = panic_message(|| {
        let _ = verify(
            base(&["main"])
                .skip_spec_errfree_check(true)
                .build()
                .unwrap(),
            two_senders,
            || {
                let m = main_thread_id();
                named("a", move || crate::send_msg(m, 1u64));
                crate::assert(false);
                let _: u64 = crate::recv_msg_block();
            },
        );
    });
    let Some(message) = message else {
        // If this ever stops panicking, §5.4 clause (iii) may have been built.
        panic!(
            "a specification that asserts under probe no longer reaches a panic; if S1 built \
             §3 item 10(d)'s hard error, rewrite this test to assert it"
        );
    };
    assert!(
        !message.contains("Spec must be error-free")
            && !message.contains("conformance: the specification asserted"),
        "§5.4 clause (iii) appears to exist after all --- rewrite this test: {message}"
    );
}

// ===========================================================================
// Criterion 6 --- stop-at-first.
// ===========================================================================

/// Stop-at-first defaults to `false`, and setting it changes the number of
/// reports, not what a report means.
///
/// What would break it: defaulting it to true, or draining `rqueue` instead of
/// using the flag (which would make the end indistinguishable from an
/// exhausted state space — the thing blocked item G refused).
#[test]
fn c6_stop_at_first_defaults_off_and_changes_only_where_the_loop_stops() {
    let program = || {
        let _ = crate::nondet();
        crate::assert(false);
    };
    let spec = || {
        let _ = crate::nondet();
    };

    let many = verify(base(&["main"]).build().unwrap(), program, spec).unwrap();
    assert!(
        many.outcome().reports().len() >= 2,
        "the default did not report-and-continue: {:?}",
        many.outcome().reports().len()
    );
    assert_eq!(many.outcome().end(), SearchEnd::StateSpaceExhausted);

    let one = verify(
        base(&["main"])
            .stop_at_first_report(true)
            .build()
            .unwrap(),
        program,
        spec,
    )
    .unwrap();
    assert_eq!(one.outcome().reports().len(), 1);
    assert_eq!(one.outcome().end(), SearchEnd::StoppedAtFirstReport);

    // The report itself means the same thing either way.
    assert_eq!(
        format!("{:?}", many.outcome().reports()[0].cause()),
        format!("{:?}", one.outcome().reports()[0].cause()),
        "stop-at-first changed what the first report says"
    );
}

/// The stop flag is **inert** when `conf` is `None` — item H's first condition.
///
/// An ordinary TraceForge run must be bit-identical, and the flag lives on
/// `ConfCtx`, so there is nothing to set. This is the observable half: a plain
/// `verify` explores exactly what it did before.
///
/// What would break it: moving the flag onto `Must` as a bare `bool` that
/// something else could set.
#[test]
fn c6_the_stop_flag_is_inert_without_conformance() {
    let program = || {
        let _ = crate::nondet();
        let _ = crate::nondet();
    };
    let s = crate::verify(Config::builder().with_cons_type(ConsType::FIFO).build(), program);
    assert_eq!(
        (s.execs, s.block),
        (4, 0),
        "an ordinary run's exploration changed, so the stop flag is not inert"
    );
}

// ===========================================================================
// Criterion 7 --- §9's config-time layer, diffed against the constructor
// predicate **per field**.
// ===========================================================================

/// Set one `Config` field out of scope, leaving the rest in scope.
fn out_of_scope_config(field: ScopeField) -> Config {
    let b = Config::builder().with_cons_type(ConsType::FIFO);
    match field {
        ScopeField::ConsType => b.with_cons_type(ConsType::Mailbox).build(),
        ScopeField::SchedulePolicy => b.with_policy(SchedulePolicy::Arbitrary).build(),
        ScopeField::Mode => {
            let mut c = b.build();
            c.mode = crate::ExplorationMode::Estimation;
            c
        }
        ScopeField::LossyBudget => b.with_lossy(1).build(),
        ScopeField::Parallel => b.with_parallel(true).build(),
        ScopeField::PartitionedParallelization => b.with_partitioned_parallelization(true).build(),
        ScopeField::PredeterminedChoices => {
            let mut m = HashMap::new();
            m.insert("c".to_owned(), vec![vec![true]]);
            b.with_predetermined_choices(m).build()
        }
        ScopeField::PredeterminedGlobalChoices => {
            let mut m = HashMap::new();
            m.insert("c".to_owned(), true);
            b.with_predetermined_global_choices(m).build()
        }
        #[cfg(feature = "symbolic")]
        ScopeField::Symbolic => b.with_symbolic(true).build(),
        #[cfg(not(feature = "symbolic"))]
        ScopeField::Symbolic => b.build(),
    }
}

/// **The diff, per field, with an exit status.**
///
/// Criterion 7's named failure mode: a `build()` that rejects `parallel` and
/// forgets `partitioned_parallelization` ticks the "parallel" cell of a
/// *per-assertion* diff — `assert_config_in_scope` tests both in one macro —
/// passes, and is caught only at `Must::new` with a panic. So the enumeration
/// is over the nine `Config` fields, which is the discriminator in the source,
/// and each field is driven through **both** layers independently.
///
/// The two lists were written independently: `ConfBuilder::build`'s from §9's
/// prose and the `Config` struct's fields, `assert_config_in_scope`'s from S4.
/// This is where they are compared.
///
/// What would break it: dropping any field from `ConfBuilder::build`, or
/// adding one to `assert_config_in_scope` without adding it here.
#[test]
fn c7_config_rejections_match_the_constructor_predicate_field_by_field() {
    let checked = ScopeField::checked();
    assert_eq!(
        checked.len(),
        if cfg!(feature = "symbolic") { 9 } else { 8 },
        "§9's config-time layer is nine cells, eight under default features"
    );

    let mut build_only = Vec::new();
    let mut assert_only = Vec::new();
    for field in ScopeField::ALL {
        let config = out_of_scope_config(field);
        let rejected_by_build = ConfBuilder::new()
            .config(config.clone())
            .visible_threads(["main"])
            .build()
            .is_err();
        let rejected_by_assert = panic_message(move || {
            crate::conformance::assert_config_in_scope(&config, "diff");
        })
        .is_some();
        let should = ScopeField::checked().contains(&field);
        if rejected_by_build != should {
            build_only.push(format!(
                "{:?}: build() {} it",
                field,
                if rejected_by_build {
                    "rejected"
                } else {
                    "accepted"
                }
            ));
        }
        if rejected_by_assert != should {
            assert_only.push(format!(
                "{:?}: assert_config_in_scope {} it",
                field,
                if rejected_by_assert {
                    "rejected"
                } else {
                    "accepted"
                }
            ));
        }
    }
    assert!(
        build_only.is_empty() && assert_only.is_empty(),
        "the two §9 layers disagree, field by field:\n  build: {:?}\n  assert: {:?}",
        build_only,
        assert_only
    );
}

/// One test per config-time rejection — the nine (eight by default) asked for,
/// generated from the same enumeration so none can go missing.
///
/// What would break it: a `ScopeField` variant with no predicate arm (a compile
/// error) or a predicate that answers `false` for its own field.
#[test]
fn c7_every_config_field_has_its_own_rejection() {
    for field in ScopeField::checked() {
        let config = out_of_scope_config(field);
        assert!(
            out_of_scope(&config, field),
            "{field:?} was not detected by its own predicate"
        );
        let refused = ConfBuilder::new()
            .config(config)
            .visible_threads(["main"])
            .build();
        match refused {
            Err(e) => assert_eq!(
                e.field(),
                field,
                "{field:?} was refused, but blamed on {:?}",
                e.field()
            ),
            Ok(_) => panic!("{field:?} was accepted by build()"),
        }
    }
}

/// `build()` is UX; `Must::new`'s assertion is the guarantee.
///
/// A `Config` that never passed `build()` still cannot reach a conformance
/// engine. This is the property §9 says must not be traded away for the
/// `Result`.
///
/// What would break it: removing the `assert_config_in_scope` call from
/// `enable_conformance` on the strength of `build()` having run.
#[test]
fn c7_the_constructor_assertion_still_catches_a_config_that_bypassed_build() {
    let message = panic_message(|| {
        // `verify_conformance` takes a raw `Config`, exactly as a
        // deserialized or entry-point-overwritten one would arrive.
        let _ = verify_conformance(
            out_of_scope_config(ScopeField::LossyBudget),
            || {},
            || {},
            names(&["main"]),
            16,
        );
    })
    .expect("a bypassed config reached a conformance engine unchecked");
    assert!(message.contains("lossy sends"), "{message}");
}

// ===========================================================================
// Criterion 8 --- §8's entry-point errors: three conditions × two programs.
// ===========================================================================

/// **Spawned twice, implementation.** Detected mid-search, as `AmbiguousName`,
/// arriving through `ConfCtx::gate`'s `ObsError` arm's panic.
#[test]
fn c8_a_visible_name_spawned_twice_in_the_implementation_is_refused() {
    let message = panic_message(|| {
        let _ = verify(
            base(&["main", "a"]).build().unwrap(),
            || {
                named("a", || {});
                named("a", || {});
                let m = main_thread_id();
                named("z", move || crate::send_msg(m, 1u64));
                let _: u64 = crate::recv_msg_block();
            },
            two_senders,
        );
    })
    .expect("two threads sharing a declared visible name must be refused");
    assert!(
        message.contains("a declared visible name must identify exactly one thread"),
        "{message}"
    );
}

/// **Spawned twice, specification.** Same condition, other program, and the
/// blame must name the specification.
#[test]
fn c8_a_visible_name_spawned_twice_in_the_specification_is_refused() {
    let message = panic_message(|| {
        let _ = verify(
            base(&["main", "a"]).build().unwrap(),
            || {
                named("a", || {});
                let m = main_thread_id();
                named("z", move || crate::send_msg(m, 1u64));
                let _: u64 = crate::recv_msg_block();
            },
            || {
                named("a", || {});
                named("a", || {});
            },
        );
    })
    .expect("an ambiguous name in the specification must be refused");
    assert!(
        message.contains("a declared visible name must identify exactly one thread"),
        "{message}"
    );
}

/// **Never spawned, implementation.** Raised by `statuses`, which runs only
/// under `done` with `outer_complete = true` — i.e. only at the completion
/// gate.
#[test]
fn c8_a_visible_name_never_spawned_in_the_implementation_is_refused() {
    let message = panic_message(|| {
        let _ = verify(
            base(&["main", "ghost"]).build().unwrap(),
            || {},
            || {},
        );
    })
    .expect("a declared visible thread that is never spawned must be refused");
    assert!(message.contains("was never spawned"), "{message}");
}

/// **Spawned late, implementation** — built in S4 (`check_spawn_order`), and
/// re-checked here because the gate's signature changed in S5.
#[test]
fn c8_a_visible_thread_spawned_after_communicating_is_refused() {
    let message = panic_message(|| {
        let _ = verify(
            base(&["main", "late"]).build().unwrap(),
            || {
                let m = main_thread_id();
                named("first", move || crate::send_msg(m, 1u64));
                let _: u64 = crate::recv_msg_block();
                named("late", || {});
            },
            // The specification covers the implementation, so nothing prunes
            // before the completion gate — where `late` finally exists and the
            // guard can see it. A specification that reported earlier would
            // leave the guard untested, which is what the first version of this
            // test did.
            || {
                named("late", || {});
                let m = main_thread_id();
                named("first", move || crate::send_msg(m, 1u64));
                let _: u64 = crate::recv_msg_block();
            },
        );
    })
    .expect("a late-spawned declared visible thread must be refused");
    assert!(
        message.contains("§8 requires each declared visible thread to be spawned before"),
        "{message}"
    );
}

/// **Spawned late, specification** — the cell S4 recorded as *not done*, and
/// which S5 closes **only in the precheck**, by running §8's guard on the
/// gate-disabled engine.
///
/// `check_spawn_order` runs at the gate on the implementation graph; the
/// specification's own graphs are built inside the search, where checking them
/// is an S2/S3 change. The precheck is the one engine that sees a
/// specification graph from outside the search, so this is where the cell gets
/// covered — at a cost: it is covered for the *specification's own executions*,
/// not for the partial graphs the search builds.
///
/// What would break it: removing the `check_spawn_order` call from a
/// gate-disabled `ConfCtx::gate`.
#[test]
fn c8_a_late_spawned_visible_thread_in_the_specification_is_refused_by_the_precheck() {
    let message = panic_message(|| {
        let _ = verify(
            base(&["main", "late"]).build().unwrap(),
            || {
                named("late", || {});
            },
            || {
                let m = main_thread_id();
                named("first", move || crate::send_msg(m, 1u64));
                let _: u64 = crate::recv_msg_block();
                named("late", || {});
            },
        );
    })
    .expect("a late-spawned visible thread in the specification must be refused");
    assert!(
        message.contains("§8 requires each declared visible thread to be spawned before"),
        "{message}"
    );
}

/// **A conditionally-spawned visible thread**, and what actually happens.
///
/// Criterion 8 asks for a test that this produces §8's error and **not** a
/// report. The consequence it names is real and is reproduced here, and the
/// criterion's requirement **cannot be met as stated**:
///
/// On the branch where `maybe` is absent, `wobs` reads it as `Row::Unspawned`
/// — an empty row, which is the *correct* reading on a partial graph. At a
/// **fresh** gate — `FreshRecv`, measured below, not the completion gate the
/// first two versions of this doc claimed — `Search::done` tests `matches`
/// first, and `matches` fails on the empty row: the specification has an
/// observation for `maybe` and the implementation has none. So `NoCover` is
/// answered and a report is raised, and `statuses` — the only thing that
/// raises `NotSpawned` — is never reached, because `done` returns at the
/// `matches` guard that precedes it. The program is reported as a conformance
/// violation, against a program §8 says is not a valid input.
///
/// Turning absence into a §8 error *earlier* is not available either: §8
/// forbids a visible thread spawned **after its program has communicated**,
/// and `check_spawn_order` deliberately permits an *unordered* spawn, so an
/// absent thread at a mid-search gate is not yet a violation of anything.
///
/// **The companion case matters too**, and it is checked below: when the
/// specification's row for the missing thread is *also* empty, `matches`
/// passes, `statuses` runs, and §8's error does arrive. So the behaviour is
/// not "never caught" — it is "caught or reported depending on the
/// specification", which is worse, because it is not predictable from the
/// implementation alone.
///
/// See the S5 report's findings for the routing.
#[test]
fn f_a_conditionally_spawned_visible_thread_is_reported_rather_than_refused() {
    // (a) The specification gives `maybe` an observation, so `matches` fails
    //     first and a report is raised.
    let v = verify(
        base(&["main", "maybe"]).build().unwrap(),
        || {
            let m = main_thread_id();
            if crate::nondet() {
                named("maybe", move || crate::send_msg(m, 7u64));
            } else {
                named("z", move || crate::send_msg(m, 7u64));
            }
            let _: u64 = crate::recv_msg_block();
        },
        || {
            let m = main_thread_id();
            named("maybe", move || crate::send_msg(m, 7u64));
            let _: u64 = crate::recv_msg_block();
        },
    );
    match v {
        Ok(v) => {
            let reports = v.outcome().reports();
            assert!(
                !reports.is_empty(),
                "neither a §8 error nor a report: this finding has changed shape and must \
                 be re-derived"
            );
            // **The gate matters, and getting the *reason* wrong put a route
            // that does not work on the owner's menu** (gate-4 rounds 1 M4 and
            // 2 M4). The report is raised at a *fresh* gate. `Search::done`
            // tests `matches` **first** and `!outer.complete` second, so at a
            // fresh gate a `NoCover` answer is precisely the case where
            // `matches` *was* reached and failed — the round-1 claim that
            // "neither conjunct is reached" was false, and route (ii) would
            // indeed be reached.
            //
            // What refuses route (ii) is the precondition, not the ordering:
            // `statuses` takes a `CompleteExecution`, and (M3) is defined only
            // at a complete execution — on a partial graph it answers
            // *blocked* for every thread that merely has not finished yet,
            // which is the wrong-answer-rather-than-error shape S2 built that
            // type to make unconstructible.
            // **Pinned, not merely excluded** (round 3, n2). The first
            // version asserted only that the gate is *not* `Completion`,
            // which is half the claim; F-6 says the gate is `FreshRecv`, and
            // if it ever becomes `Completion` the whole menu changes, while
            // if it becomes `FreshSend` the wording is wrong and nothing
            // would have said so.
            assert!(
                reports.iter().all(|r| r.gate() == ReportGate::FreshRecv),
                "F-6 says this report arrives at the fresh-receive gate; it arrived at \
                 {:?}. If that is `Completion`, `Search::done` reaches `statuses` and the \
                 route menu must be re-derived.",
                reports.iter().map(|r| r.gate()).collect::<Vec<_>>()
            );
            println!(
                "FINDING (criterion 8): a conditionally-spawned declared visible thread \
                 produced {} report(s) rather than §8's error, at {:?}.",
                reports.len(),
                reports.iter().map(|r| r.gate()).collect::<Vec<_>>()
            );
        }
        Err(e) => panic!("unexpected error channel: {e:?}"),
    }

    // (b) The specification leaves `maybe` empty too, so `matches` passes,
    //     `statuses` runs, and §8's error does arrive. Same implementation
    //     defect, opposite outcome.
    let message = panic_message(|| {
        let _ = verify(
            base(&["main", "maybe"]).build().unwrap(),
            || {
                let m = main_thread_id();
                if crate::nondet() {
                    named("maybe", || {});
                }
                named("z", move || crate::send_msg(m, 7u64));
                let _: u64 = crate::recv_msg_block();
            },
            || {
                let m = main_thread_id();
                named("maybe", || {});
                named("z", move || crate::send_msg(m, 7u64));
                let _: u64 = crate::recv_msg_block();
            },
        );
    })
    .expect("with an empty specification row, §8's error should arrive");
    assert!(message.contains("was never spawned"), "{message}");
}

// ===========================================================================
// Criterion 9 --- the diagnostics §7.1 promises.
// ===========================================================================

/// The diagnostics do not influence the search: `Cover`'s answer and the
/// `Budget`'s node spend are unchanged with them on and off.
///
/// Since they are recomputed *after* the run (blocked item D's ruling), this
/// holds trivially — and the test is the thing that keeps it trivial. The
/// comparison is between the sink's own figures from a run that builds
/// diagnostics (`verify`) and one that cannot (`verify_conformance`), on the
/// same pair: same reports, same gates, same exhaustion count.
///
/// What would break it: threading an accumulator into
/// `spec_visit`/`spec_step`/`phi`.
#[test]
fn c9_the_diagnostics_change_neither_the_cover_answer_nor_the_node_spend() {
    let raw = verify_conformance(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        two_senders,
        uncoverable_spec,
        names(&["main"]),
        4096,
    );
    let v = verify(
        base(&["main"]).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .unwrap();
    assert_eq!(
        raw.reports.len(),
        v.outcome().reports().len(),
        "building the diagnostics changed the report set"
    );
    assert_eq!(
        raw.exhaustions.len(),
        v.outcome().exhaustions().len(),
        "building the diagnostics changed the node spend"
    );
    let raw_gates: Vec<ReportGate> = raw.reports.iter().map(|r| ReportGate::of(r.gate)).collect();
    let new_gates: Vec<ReportGate> = v.outcome().reports().iter().map(|r| r.gate()).collect();
    assert_eq!(raw_gates, new_gates, "the gate sites moved");
}

/// A report carries a first failing obligation, and it is one of §7.1's four.
///
/// What would break it: a diagnostic that guesses instead of answering
/// "unavailable", or an obligation order that never reaches (M1).
#[test]
fn c9_a_nocover_report_names_a_first_failing_obligation() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .unwrap();
    let with_obligation = v
        .outcome()
        .reports()
        .iter()
        .filter(|r| matches!(r.diagnostics(), Diagnostics::Available { .. }))
        .count();
    assert!(
        with_obligation > 0,
        "no report carried a diagnostic at all: {:?}",
        v.outcome()
            .reports()
            .iter()
            .map(|r| r.diagnostics())
            .collect::<Vec<_>>()
    );
    let text = v.to_string();
    assert!(
        text.contains("first failing obligation"),
        "the obligation was not rendered:\n{text}"
    );
}

/// The canonical choice of failed attempt is **deterministic**.
///
/// §7.1's "best attempt" named no unique object — `follows` is a conjunction
/// over visible-thread rows, so two failures can be incomparable — which is why
/// A13 fixes the tie-break as lexicographic on the per-thread prefix-length
/// vector, then installation order. The property that makes it a tie-break
/// rather than a preference is that repeating the recomputation gives the same
/// answer.
///
/// What would break it: replacing the strict `>` in `Best::offer` with `>=`
/// (last-wins, which is traversal-order dependent), or ordering the visible
/// names by anything but their declaration.
#[test]
fn c9_the_canonical_failed_attempt_is_deterministic() {
    let run = || {
        verify(
            base(&["main"]).build().unwrap(),
            two_senders,
            uncoverable_spec,
        )
        .unwrap()
        .outcome()
        .reports()
        .iter()
        .map(|r| format!("{:?}", r.diagnostics()))
        .collect::<Vec<_>>()
    };
    assert_eq!(run(), run(), "the chosen failed attempt is not deterministic");
}

/// The recomputation refuses to guess.
///
/// Blocked item D's mitigation, exercised directly: a budget too small for the
/// recomputation to reproduce the gate's ⊥ must yield `Unavailable`, not a
/// fabricated obligation. `blame_for` cost S4 two rounds to learn that a
/// reconstruction which silently disagrees is worse than none.
///
/// **What would break it: dropping check *one*, and only check one** (gate-4
/// round 2, n2 — the first version claimed "either of the two checks", and
/// only one of them is a break condition here). With the budget at zero,
/// `Search::cover` exhausts first and returns before the second check is
/// reached, so deleting the second leaves this test green.
///
/// And the second check **cannot** be provoked by any input, which is worth
/// saying rather than leaving as an untested line: it fires exactly when this
/// module's traversal disagrees with S3's `Search::cover`, and that
/// disagreement is the defect it exists to detect. It is the same content the
/// `--naive-oracle` measures (F-17), arrived at from the other side: the
/// diagnostics already cross-check the two implementations on every `NoCover`
/// report, so `Diagnostics::Available` already implied what the deleted
/// `--naive-oracle` cross-check reported (F-17; flag removed in S6).
/// Both facts are findings rather than gaps, and both are routed.
#[test]
fn c9_a_recomputation_that_cannot_reproduce_the_verdict_says_so() {
    let graph = run_once(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        two_senders,
    );
    let r = Recompute::new(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        std::sync::Arc::new(two_senders),
        names(&["main"]),
        0, // no room to establish anything
        true,
    );
    match r.diagnose(&graph, true) {
        Diagnostics::Unavailable { because, .. } => {
            assert!(because.contains("budget"), "{because}");
        }
        other => panic!("a recomputation with no budget produced a diagnostic anyway: {other:?}"),
    }
}

// ===========================================================================
// Criterion 10 --- re-pointed. `--naive-oracle` was deleted in S6 (Poll 1);
// what survives here is the property that never depended on it, plus F-17's
// node-count evidence. The genuine oracle is `conformance::oracle`.
// ===========================================================================


/// **The oracle does not run where there is no `Cover` answer to check**
/// (gate-4 round 2, M1).
///
/// A §4.4 visible-error report is a failed assertion: `Report.gate` is `None`,
/// nothing asked the specification anything, so no inner-search diagnostic
/// is a false statement about it. Run there, the tool printed
/// "**disagreement** … Φ lost a cover, which is a defect in Φ or in this
/// report" one line below its own "inner-search diagnostics do not apply" — a
/// manufactured defect report against its own algorithm, on a program whose
/// only statement is `assert(false)`.
///
/// The test is the reviewer's own reproduction. What would break it: folding
/// the `VisibleError` arm into `phi.diagnose`, i.e. the diagnostics drifting
/// outside the `match` on `ReportKind` that gates them. Measured at gate 3 —
/// it is the **only** test that fails under that change, so it is the sole
/// protection of that gate.
#[test]
fn c10_a_visible_error_report_carries_no_inner_search_diagnostics() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        || crate::assert(false),
        || {},
    )
    .unwrap();
    let reports = v.outcome().reports();
    assert_eq!(reports.len(), 1);
    assert!(matches!(reports[0].cause(), ReportCause::VisibleError { .. }));
    assert_eq!(
        reports[0].diagnostics(),
        &Diagnostics::NotApplicable,
        "the diagnostics gate moved"
    );
    let text = v.to_string();
    assert!(
        text.contains("inner-search diagnostics do not apply"),
        "the diagnostics did not say they do not apply:\n{text}"
    );
}


/// **The two traversals visit the same number of nodes**, which is what
/// "Φ filters offers, not nodes" means and what the previous version of this
/// test only inferred from the two answers coinciding (gate-4 round 2, m1).
///
/// The derivation, which the reviewer re-derived independently from `alg.tex`
/// and the source and confirmed: budget is spent once per `SpecVisit` node. A
/// send or receive offer reaches `SpecVisit` only through `spec_step`, whose
/// `follows` check this module keeps in **both** modes — Φ is the filter on
/// the loop's *range*, not the morphism — so an offer Φ would reject is
/// instead tried and refused by `spec_step` at a cost of zero nodes. The one
/// offer kind that bypasses `spec_step` is a nondet, and a nondet changes no
/// observation, so its extension follows exactly when its parent does; the
/// parent followed, or the traversal would not be there.
///
/// Equal answers would be weaker evidence: two traversals of different sizes
/// can agree. The node counts are compared directly.
///
/// What would break it: dropping `spec_step`'s `follows` conjunct from the
/// un-Φ mode, which would make it a genuinely different algorithm — and one
/// whose termination is argued nowhere.
#[test]
fn c10_the_two_traversals_visit_the_same_number_of_nodes() {
    use crate::conformance::diagnose::{Answer, Recompute};

    /// One pair: a name, the implementation, the specification, and the
    /// declared visible threads.
    type Pair = (&'static str, fn(), fn(), Vec<&'static str>);

    let cases: Vec<Pair> = vec![
        ("simple", two_senders, uncoverable_spec, vec!["main"]),
        (
            "branching-nondets",
            || {
                let m = main_thread_id();
                named("p", move || crate::send_msg(m, 1u64));
                named("q", move || crate::send_msg(m, 2u64));
                let _: u64 = crate::recv_msg_block();
                let _: u64 = crate::recv_msg_block();
            },
            || {
                let m = main_thread_id();
                named("p", move || {
                    let v = if crate::nondet() { 7u64 } else { 8u64 };
                    crate::send_msg(m, v);
                });
                named("q", move || {
                    let v = if crate::nondet() { 7u64 } else { 8u64 };
                    crate::send_msg(m, v);
                });
                let _: u64 = crate::recv_msg_block();
                let _: u64 = crate::recv_msg_block();
            },
            vec!["main", "p", "q"],
        ),
    ];

    let cfg = || Config::builder().with_cons_type(ConsType::FIFO).build();
    let mut saw = (false, false);
    for (name, implementation, specification, vis) in cases {
        let graph = run_once(cfg(), implementation);
        let visible = names(&vis);
        for budget in 1..25usize {
            let mode = |use_phi| {
                Recompute::new(
                    cfg(),
                    std::sync::Arc::new(specification),
                    visible.clone(),
                    budget,
                    use_phi,
                )
                .answer_counting(&graph, true)
            };
            let phi = mode(true).expect("the pair is in scope");
            let un_phi = mode(false).expect("the pair is in scope");
            assert_eq!(
                phi, un_phi,
                "{name}: at budget {budget} the two modes differed in answer or in nodes \
                 spent, so \u{3a6} *does* filter nodes --- F-17 must be re-derived and \
                 an exhausted recomputation may be reachable after all"
            );
            match phi.0 {
                Answer::Exhausted => saw.0 = true,
                Answer::NoCover => saw.1 = true,
                Answer::Found => {}
            }
        }
    }
    assert!(
        saw.0 && saw.1,
        "the budget range covered only one outcome, so the comparison is not \
         discriminating: {saw:?}"
    );
}


// ===========================================================================
// Criteria 13 and 14 --- what a report contains, and what a user reads.
// ===========================================================================

/// **Five** gate rendering cases, each distinct.
///
/// §7.1's prose names four items and that is not the source's enumeration:
/// `Gate` has four variants — so "fresh add" is two of them — and "visible
/// error" is not a gate at all. A renderer built from the four names prints
/// `FreshSend` and `FreshRecv` identically and has no branch for `gate: None`,
/// which is *every* §4.4 report.
///
/// What would break it: collapsing the two fresh gates, or giving `NotAGate`
/// the same text as `Completion` (which is S4's F-E defect re-entering through
/// the rendering layer).
#[test]
fn c13_the_gate_site_renders_as_five_distinct_cases() {
    let all = [
        ReportGate::FreshSend,
        ReportGate::FreshRecv,
        ReportGate::RevisitApply,
        ReportGate::Completion,
        ReportGate::NotAGate,
    ];
    let rendered: Vec<String> = all.iter().map(|g| g.to_string()).collect();
    let mut sorted = rendered.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), 5, "two gate sites render identically: {rendered:?}");
    assert_ne!(rendered[0], rendered[1], "the two fresh gates are the same text");
    assert!(rendered[4].contains("no gate"), "{}", rendered[4]);

    // And the mapping is the one S4's F-E fix established.
    assert_eq!(ReportGate::of(None), ReportGate::NotAGate);
    assert_eq!(ReportGate::of(Some(Gate::FreshSend)), ReportGate::FreshSend);
    assert_eq!(ReportGate::of(Some(Gate::FreshRecv)), ReportGate::FreshRecv);
    assert_eq!(
        ReportGate::of(Some(Gate::RevisitApply)),
        ReportGate::RevisitApply
    );
    assert_eq!(
        ReportGate::of(Some(Gate::Completion)),
        ReportGate::Completion
    );
}

/// §7.1's first clause: a report carries the outer graph snapshot, **both**
/// halves.
///
/// The dump is `ExecutionGraph`'s own rendering. The serialized half is
/// `ReplayInformation::create` called directly, off the live outer `Must` — so
/// `store_replay_information`'s conformance early return (`store_replay_information`'s conformance early return, S4's
/// fix for F-C) is untouched, which this test also checks.
///
/// What would break it: deleting the exemption (F-C reopens), or letting
/// `top_sort`'s precondition fail (the snapshot then reads "unavailable", and
/// the assertion below catches it).
#[test]
fn c13_a_report_carries_the_graph_dump_and_the_serialized_replay_information() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .unwrap();
    for r in v.outcome().reports() {
        assert!(
            r.graph_dump().contains("thread"),
            "the report carries no graph dump"
        );
        match r.replay_snapshot() {
            ReplaySnapshot::Serialized(s) => {
                assert!(
                    s.contains("sorted_error_graph"),
                    "the serialized half is not replay information"
                );
            }
            ReplaySnapshot::Unavailable { because } => panic!(
                "`top_sort`'s precondition did not hold on a reported graph, so \
                 `ReplaySnapshot`'s argument is wrong: {because}"
            ),
        }
    }

    // The exemption is still in place: that is what keeps F-C closed.
    let source = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/must.rs"),
    )
    .unwrap();
    assert!(
        source.contains("if self.probe_active() || self.conf.is_some() {"),
        "`store_replay_information`'s conformance early return is gone --- F-C is reopened"
    );
}

/// A §4.4 report's snapshot works too, and it works because
/// `conf_assert_failure` installs the `Block(Assert)` **before** reporting.
///
/// That ordering is what makes `top_sort(Some(pos))` well defined for a
/// visible-error report, and it is the load-bearing half of `ReplaySnapshot`'s
/// argument.
///
/// What would break it: moving `handle_block` after `report_visible_error`.
#[test]
fn c13_a_visible_error_reports_snapshot_rests_on_the_block_being_installed_first() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        || crate::assert(false),
        || {},
    )
    .unwrap();
    let r = &v.outcome().reports()[0];
    assert!(
        matches!(r.replay_snapshot(), ReplaySnapshot::Serialized(_)),
        "the visible-error report could not be linearised, so the `Block(Assert)` was not \
         installed before the capture"
    );
    // The graph really does contain the block at the reported position.
    let ReportCause::VisibleError { pos, .. } = r.cause() else {
        panic!("expected a visible-error report");
    };
    assert!(
        r.graph_dump().contains("Block") || r.graph_dump().contains("Assert"),
        "no block label in the captured graph at {pos}:\n{}",
        r.graph_dump()
    );
}

/// §7.3's product is a ⟨word, **status vector**⟩ pair, and the status half is
/// what makes an (M3)-only difference visible.
///
/// `vis(σ) ≝ ⟨w, status_σ|_Tvis⟩` is a pair; the word-alone display is a
/// convention the draft licenses only for its two examples, "because their
/// status components all agree". **Ex. blocking** is the case where they do
/// not: the two sides' words coincide and only the statuses differ, so a
/// word-only rendering shows the user two identical words with nothing wrong in
/// them.
///
/// What would break it: dropping `VisTrace::statuses` from the rendering, or
/// rendering the word alone.
#[test]
fn c14_ex_blocking_renders_a_visible_difference_that_a_word_alone_cannot() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        || {
            let _: u64 = crate::recv_msg_block();
        },
        || {},
    )
    .unwrap();
    let reports = v.outcome().reports();
    assert!(!reports.is_empty(), "Ex. blocking did not report");
    let text = v.to_string();
    assert!(
        text.contains("(M3) status mismatch"),
        "the status-only difference was not named:\n{text}"
    );
    assert!(
        text.contains("blocked") && text.contains("done"),
        "the two statuses were not both shown:\n{text}"
    );

    // The words really do coincide: both sides have no visible observation, so
    // a word-only rendering has nothing to show.
    let imp = run_once(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        || {
            let _: u64 = crate::recv_msg_block();
        },
    );
    let spec = run_once(Config::builder().with_cons_type(ConsType::FIFO).build(), || {});
    let iv = canonical_vis(&imp, &names(&["main"]), CompleteExecution::try_finished(&imp)).unwrap();
    let sv =
        canonical_vis(&spec, &names(&["main"]), CompleteExecution::try_finished(&spec)).unwrap();
    assert_eq!(
        iv.word(),
        sv.word(),
        "the two sides' words differ, so this is not the status-only case"
    );
    assert_ne!(
        iv.statuses(),
        sv.statuses(),
        "the two sides' status vectors agree, so Ex. blocking is not reproduced"
    );
}

/// The canonical linearisation is **named, deterministic and tie-broken**.
///
/// `vis(G)` is a *set* — the linear extensions of `vo(G)` — so pinning "the
/// word" without naming a linearisation pins whichever one the implementation
/// emitted, which is a schedule-dependent snapshot. The rule is: repeatedly
/// take the `vo`-minimal visible events, and among them the one whose ⟨declared
/// thread name, index in that thread's row⟩ key is smallest.
///
/// The discriminating case is **concurrency between visible events**, which is
/// the ordinary case and is what (M2) exists to compare: two visible threads
/// with unordered observations. The linearisation must put them in *declared
/// name* order regardless of which ran first.
///
/// What would break it: sorting by `ThreadId` (spawn order) or by event
/// position, both of which are schedule artefacts.
#[test]
fn c14_the_canonical_linearisation_is_deterministic_and_name_ordered() {
    let program = || {
        let m = main_thread_id();
        // Two visible threads whose sends are mutually unordered.
        named("zulu", move || crate::send_msg(m, 1u64));
        named("alpha", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
        let _: u64 = crate::recv_msg_block();
    };
    let visible = names(&["alpha", "main", "zulu"]);
    let graph = run_once(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        program,
    );
    let a = canonical_vis(&graph, &visible, CompleteExecution::try_finished(&graph)).unwrap();
    let b = canonical_vis(&graph, &visible, CompleteExecution::try_finished(&graph)).unwrap();
    assert_eq!(a, b, "the linearisation is not deterministic");

    let word = a.word().to_vec();
    let alpha = word.iter().position(|w| w.starts_with("alpha:"));
    let zulu = word.iter().position(|w| w.starts_with("zulu:"));
    let (Some(alpha), Some(zulu)) = (alpha, zulu) else {
        panic!("both visible senders should appear in the word: {word:?}");
    };
    assert!(
        alpha < zulu,
        "the tie-break is not the declared name: {word:?}"
    );
    assert_eq!(
        a.statuses().len(),
        visible.len(),
        "the status vector has one entry per declared visible thread"
    );
}

// ===========================================================================
// Criterion 15 and the notes' licensed rendering.
// ===========================================================================

/// Triage is off by default, and the rendering says the knob exists.
#[test]
fn c15_triage_is_off_by_default() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .unwrap();
    assert!(
        v.outcome().reports().iter().all(|r| r.triage().is_none()),
        "triage ran without being asked for"
    );
    assert!(v.to_string().contains("ConfBuilder::triage(true)"));
}

/// The `AfterPrune` rendering names the position and the prune **without
/// claiming visibility**.
///
/// `AfterPrune ⟹ visible` is unproven and believed unreachable, and
/// `ConfNote::thread` is the runtime task name when the thread is not declared
/// visible — so the rendering is one adjective away from making the unproven
/// claim by accident.
///
/// What would break it: calling the thread "visible" in that arm.
#[test]
fn c15_the_after_prune_note_makes_no_visibility_claim() {
    let note = ConfNote::of(
        crate::conformance::ctx::DiagnosticReason::AfterPrune,
        "task-7".to_owned(),
        "<3, 4>".to_owned(),
    );
    let text = note.to_string();
    assert!(
        text.contains("after this execution was pruned"),
        "the licensed wording is gone: {text}"
    );
    assert!(
        !text.contains("visible thread"),
        "the note claimed visibility, which is unproven: {text}"
    );
    assert!(text.contains("unproven"), "{text}");
    // The divergence is **structural**: the two cases are different variants
    // with differently named position fields, because the position means a
    // different thing in each. S4's single `pos: Event` could be resolved as an
    // event in a case where nothing was installed at it.
    assert!(matches!(note, ConfNote::AfterPrune { .. }));
    assert!(
        text.contains("would have occupied"),
        "the post-prune position is presented as a real event: {text}"
    );

    // And the invisible-thread arm is a *different* sentence, because it is a
    // different claim.
    let other = ConfNote::of(
        crate::conformance::ctx::DiagnosticReason::InvisibleThread,
        "task-7".to_owned(),
        "<3, 4>".to_owned(),
    );
    assert_ne!(text, other.to_string());
    assert!(other.to_string().contains("not a declared visible thread"));
}

// ===========================================================================
// Criterion 17 / item H --- the engine touch-points are inert without
// conformance.
// ===========================================================================

/// Item H's first condition, checked rather than argued: **a conformance
/// feature must not cost or change anything for an existing TraceForge user**.
///
/// **The first version of this compared a run with itself**, which is a
/// determinism check that was true before S5 and would stay true if every
/// touch-point leaked (gate-4 round 1, m2). The break-condition it carried —
/// "moving the flag onto `Must` as a bare `bool`" — was half true for the same
/// reason: a leaked flag nothing sets changes nothing, so the test would not
/// have noticed.
///
/// So each of the four kinds of touch-point is now checked against something
/// that is not itself:
///
/// 1. **rows 6, 7** — the two new accessors, asked directly of a `Must` with
///    `conf: None`. `conf_stop_requested` must answer `false` and
///    `conf_record_end` must be a no-op, and neither may panic.
/// 2. **rows 8–10** — an ordinary exploration's ending count, against a
///    **fixed expected figure** rather than against a second run of itself.
///    A touch-point that stopped the loop early, or one whose `SearchEnd`
///    bookkeeping panicked, changes this number.
/// 3. **row 4** — an ordinary run may use every construct
///    `reject_out_of_scope` rejects.
/// 4. **rows 1–3, 11** — data-passing and visibility; the 1012-test
///    pre-existing suite being bit-identical is the check, and it is reported
///    rather than asserted here.
#[test]
fn c17_the_s5_engine_touch_points_are_inert_without_conformance() {
    // (1) The accessors, on a `Must` that never heard of conformance.
    let must = crate::must::Must::new(Config::builder().with_cons_type(ConsType::FIFO).build(), false);
    assert!(
        !must.conf_stop_requested(),
        "the stop flag answered `true` on a plain `Must`, so it does not live on `ConfCtx`"
    );
    let mut must = must;
    must.conf_record_end(SearchEnd::StoppedAtFirstReport);
    assert!(
        !must.conf_stop_requested(),
        "recording a search end on a plain `Must` changed something"
    );

    // (2) A fixed figure, not a second run of the same thing. Two senders and
    // two receives: each receive may read either send or the other one, and
    // the engine explores exactly these endings.
    let program = || {
        let m = main_thread_id();
        named("a", move || crate::send_msg(m, 1u64));
        named("b", move || crate::send_msg(m, 2u64));
        let _: u64 = crate::recv_msg_block();
        let _: u64 = crate::recv_msg_block();
    };
    let s = crate::verify(Config::builder().with_cons_type(ConsType::FIFO).build(), program);
    assert_eq!(
        (s.execs, s.block),
        (2, 0),
        "an ordinary exploration's ending count changed, so an S5 touch-point is not inert"
    );

    // (3) `reject_out_of_scope`'s label: an ordinary run may use the
    // constructs the guards reject.
    let s = crate::verify(
        Config::builder().with_cons_type(ConsType::FIFO).build(),
        || {
            let _ = crate::inbox();
            let _: i64 = crate::sample(rand::distr::Uniform::new(0i64, 2i64).unwrap(), 1);
        },
    );
    assert!(s.execs + s.block > 0, "the ordinary run did not run");
}

/// The gate-disabled context really has no gate, and the outer one cannot be
/// built that way.
#[test]
fn c17_a_gate_disabled_context_refuses_to_be_the_outer_run() {
    let message = panic_message(|| {
        let _ = crate::conformance::ctx::ConfCtx::gate_disabled(
            Config::builder().with_cons_type(ConsType::FIFO).build(),
            names(&["main"]),
            ConfMode::Outer,
        );
    })
    .expect("a gate-disabled outer context must be refused");
    assert!(message.contains("the outer run is the engine that has a gate"), "{message}");
    assert_eq!(ConfMode::Precheck.engine_label(), "precheck");
    assert_eq!(ConfMode::Triage.engine_label(), "triage");
    assert_eq!(ConfMode::Outer.engine_label(), "conformance");
}

/// A triage engine's §9 rejection names *its* engine.
///
/// Ruling F accepts the `reject_out_of_scope` arming that comes with giving
/// triage a `ConfCtx`: triage replays a prefix the outer run already admitted,
/// so a guard firing there means the outer run let something through — an
/// internal invariant violation worth hearing about.
///
/// This checks the label reaches the message; the invariant it backstops is not
/// reachable by construction, which is the point.
#[test]
fn c17_the_engine_label_distinguishes_all_three_conformance_engines() {
    for (mode, want) in [
        (ConfMode::Outer, "conformance"),
        (ConfMode::Precheck, "precheck"),
        (ConfMode::Triage, "triage"),
    ] {
        assert_eq!(mode.engine_label(), want);
    }
    // The outer engine's label, observed end to end.
    let message = panic_message(|| {
        let _ = verify(
            base(&["main"]).build().unwrap(),
            || {
                let _ = crate::inbox();
            },
            || {},
        );
    })
    .unwrap();
    assert!(message.contains("conformance:"), "{message}");
}

// ===========================================================================
// Criterion 11 --- the public surface.
// ===========================================================================

/// The public entry point is reachable from outside the crate's internals, and
/// the default budget is a named constant an exhaustion can point at.
#[test]
fn c11_the_public_surface_is_what_the_module_says_it_is() {
    assert_eq!(
        crate::conformance::DEFAULT_SEARCH_BUDGET,
        10_000,
        "the documented default changed without the exhaustion rendering following"
    );
    let cc = crate::conformance::ConfBuilder::new()
        .visible_threads(["main"])
        .build()
        .unwrap();
    assert_eq!(cc.search_budget(), crate::conformance::DEFAULT_SEARCH_BUDGET);
    assert_eq!(cc.visible_threads(), ["main".to_owned()]);
    assert_eq!(cc.max_iterations(), None);
}

/// **Finding**: a *value-only* replay divergence is not caught, so "the prefix
/// is reproduced byte-for-byte" is narrower than it sounds.
///
/// `compare_for_replay`'s `SendMsg` arm compares values — but only
/// `if !s.val().is_pending()`, and the engine blanks a recorded send's value
/// when it re-executes (the same blanking `visible_events`' pending-value assertion's assertion is about).
/// So a triage run in which the implementation sends a *different value* at the
/// same position replays without complaint, and §7.3's "determinism of Impl
/// over the prefix is the engine's standing replay assumption" is enforced for
/// structure and thread identity but not for payloads.
///
/// This is an engine property, not an S5 one: it is recorded here because §7.3
/// leans on it and because a reader of `TriageOutcome::Completed` would
/// otherwise believe more than is true.
///
/// What would break it: the engine comparing pending values, at which point
/// this test should be rewritten to assert a `NondeterministicImpl`.
#[test]
fn f_a_value_only_replay_divergence_is_not_caught() {
    static VALUES: AtomicUsize = AtomicUsize::new(0);
    VALUES.store(0, Ordering::SeqCst);
    let outcome = verify(
        base(&["main"]).triage(true).build().unwrap(),
        || {
            let n = VALUES.fetch_add(1, Ordering::SeqCst) as u64;
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, n);
        },
        || {},
    );
    match outcome {
        Ok(v) => {
            assert!(
                !v.outcome().reports().is_empty(),
                "the pair stopped reporting, so this finding has changed shape"
            );
        }
        Err(e) => panic!(
            "a value-only divergence is now caught, so §7.3's replay assumption is stronger \
             than this finding says --- rewrite it: {e:?}"
        ),
    }
}

/// §7.3's final paragraph, the half criterion 14 says nothing else requires:
/// the ⟨word, status vector⟩ pair is **presented next to the specification-side
/// first mismatch**.
///
/// Criterion 3 checks the mechanics of obtaining the completed graph and
/// criterion 1 checks that the words do not overclaim; nothing else requires
/// the *pairing* to be rendered. A brief that forces the plumbing and not the
/// product is how S5 ships a correct triage nobody can read.
///
/// What would break it: dropping `spec_mismatch` from `TriageOutcome::Completed`,
/// or rendering the trace without it.
#[test]
fn c14_a_completed_triage_renders_the_pair_next_to_the_spec_side_first_mismatch() {
    let v = verify(
        base(&["main"]).triage(true).build().unwrap(),
        two_senders,
        uncoverable_spec,
    )
    .unwrap();
    let completed: Vec<&TriageOutcome> = v
        .outcome()
        .reports()
        .iter()
        .filter_map(|r| r.triage())
        .filter(|t| matches!(t, TriageOutcome::Completed { .. }))
        .collect();
    assert!(!completed.is_empty(), "no completed triage to render");
    for t in completed {
        let TriageOutcome::Completed {
            vis, spec_mismatch, ..
        } = t
        else {
            unreachable!()
        };
        let text = t.to_string();
        assert!(
            text.contains("specification-side first mismatch"),
            "the pair was rendered without the mismatch it is presented against:\n{text}"
        );
        assert!(
            !spec_mismatch.is_empty() && text.contains(spec_mismatch.as_str()),
            "the specification-side mismatch is missing from the rendering:\n{text}"
        );
        assert!(
            text.contains("word, status vector"),
            "the trace was rendered as a word alone:\n{text}"
        );
        assert_eq!(
            vis.statuses().len(),
            1,
            "one status entry per declared visible thread"
        );
    }
}

/// **Never spawned, specification** — the sixth §8 cell.
///
/// The condition is detected inside the search, by `statuses` on the
/// specification side, and the error must name the *specification* rather than
/// blame whichever program the catch site happened to reconstruct first. That
/// attribution is `blame_for`'s job and it is S4's; this is the cell's test,
/// and it is also a live check that the reconstruction still answers
/// correctly.
#[test]
fn c8_a_visible_name_never_spawned_in_the_specification_is_refused() {
    let message = panic_message(|| {
        let _ = verify(
            base(&["main", "ghost"]).build().unwrap(),
            || {
                named("ghost", || {});
            },
            || {},
        );
    })
    .expect("a declared visible thread missing from the specification must be refused");
    assert!(message.contains("was never spawned"), "{message}");
    assert!(
        message.contains("specification"),
        "the error blamed the wrong program, or named none:\n{message}"
    );
}

/// §11.10's fourth test: **main-thread-visible pairing round-trips**.
///
/// §3 item 5: the main thread has no `TCreate` but a stable public identity,
/// `thread::main_thread_id()`, so the reserved declared name `"main"` maps to
/// it directly, is exempt from the TCreate-appearance check, and may not
/// additionally be used as a `Builder` name. The round-trip is: main
/// communicates visibly in *both* programs, the pairing relates the two main
/// threads, and a difference between them is seen.
///
/// What would break it: resolving `"main"` by scanning rows for a `TCreate`
/// (which finds every thread except this one), or exempting main from the
/// pairing.
#[test]
fn c11_main_thread_visible_pairing_round_trips() {
    // Same behaviour on both sides: the pairing must certify.
    let v = verify(
        base(&["main"]).build().unwrap(),
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
    )
    .unwrap();
    assert!(
        matches!(v, ConfVerdict::Conforms(_)),
        "main-to-main pairing did not certify an identical pair: {v:?}\n{v}"
    );

    // A difference in *main's own* visible behaviour must be seen, or the
    // pairing is passing vacuously.
    let v = verify(
        base(&["main"]).build().unwrap(),
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 2u64);
        },
    )
    .unwrap();
    assert!(
        !v.outcome().reports().is_empty(),
        "main's own visible send was not compared, so the pairing is vacuous"
    );

    // And `"main"` may not be used as a `Builder` name, on either side.
    let message = panic_message(|| {
        let _ = verify(
            base(&["main"]).build().unwrap(),
            || {
                named("main", || {});
            },
            || {},
        );
    })
    .expect("`main` as a Builder name must be refused");
    assert!(
        message.contains("reserved for each program's own main thread"),
        "{message}"
    );
}

/// "No stray output" from a triaged §4.4 report, checked structurally.
///
/// Criterion 12 asks for a triaged visible-error report to produce "no
/// counterexample file and no stray output". The file half is
/// `c4_a_replayed_assertion_is_not_reported_as_a_nondeterministic_implementation`.
/// The output half cannot be observed from inside the process — the engine
/// writes to the real stdout, which a test cannot capture — so it is checked
/// where it is decided instead: `traceforge::assert`'s `conf_active()` branch,
/// which is the branch a gate-disabled triage engine takes, must contain no
/// emission at all. The two branches that do emit are the ones ruling F exists
/// to avoid.
///
/// What would break it: adding a print to the conformance branch, or triage
/// falling through to branch 2 or 3.
#[test]
fn c3_the_triage_assert_branch_emits_nothing() {
    let lib = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs"),
    )
    .unwrap();
    let at = lib
        .find("if must.conf_active() {")
        .expect("`traceforge::assert`'s conformance branch is gone");
    let branch = &lib[at..at + 700];
    let end = branch
        .find("if must.config().keep_going_after_error")
        .expect("the conformance branch no longer precedes the keep-going branch");
    // Comments stripped: the branch's own rustdoc *mentions*
    // `persist_task_failure` to say it does not reach it.
    let branch: String = branch[..end]
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    for m in ["println!", "eprintln!", "print!", "persist_task_failure"] {
        assert!(
            !branch.contains(m),
            "`traceforge::assert`'s conformance branch reached `{m}`, so a triage run emits \
             text (or persists a file) per replayed assertion:\n{branch}"
        );
    }
    assert!(
        branch.contains("conf_assert_failure"),
        "the conformance branch stopped routing to the sink:\n{branch}"
    );
}

/// **Finding**: at a *following* attempt, (M1) can only fail by **length**,
/// so the value-versus-value mismatch a user wants is unreachable in §7.1's
/// diagnostic as specified.
///
/// §7.1 asks for "the furthest-**following** prefix a canonically chosen failed
/// `SpecVisit` attempt reached, and the first failing obligation". But
/// `follows` *is* the prefix form of (M1): if an attempt follows, its
/// observations are a prefix of the implementation's by definition, so a
/// position-wise disagreement between them cannot exist there. The only way
/// (M1) can fail at the canonically chosen attempt is that the rows have
/// different lengths.
///
/// The consequence, reproduced below: for a pair whose specification sends `2`
/// where the implementation sends `1`, the diagnostic says the specification's
/// row *ends* where the implementation continues — which is true, and is not
/// the sentence the user wants ("the specification would have sent 2"). That
/// sentence lives at a **non-following** attempt, which §7.1's wording excludes
/// by construction.
///
/// This is a defect in §7.1's design rather than in this implementation, and it
/// is routed in the S5 report. What would break the test: §7.1 being amended
/// and the diagnostic following it.
#[test]
fn f_m1_can_only_fail_by_length_at_a_following_attempt() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 1u64);
        },
        || {
            let w = named("w", || {
                let _: u64 = crate::recv_msg_block();
            });
            crate::send_msg(w, 2u64);
        },
    )
    .unwrap();
    let reports = v.outcome().reports();
    assert!(!reports.is_empty(), "the value-divergent pair stopped reporting");
    let mut saw = false;
    for r in reports {
        if let Diagnostics::Available {
            obligation:
                Obligation::ObservationMismatch {
                    spec, imp, position, ..
                },
            ..
        } = r.diagnostics()
        {
            saw = true;
            assert_eq!(*position, 0);
            assert!(
                spec.contains("nothing"),
                "(M1) reported a value-versus-value mismatch at a following attempt, which \
                 this finding says is unreachable --- re-derive it: spec={spec} imp={imp}"
            );
            assert!(imp.contains("send 1"), "{imp}");
        }
    }
    assert!(saw, "no (M1) obligation was produced at all");
}

// ===========================================================================
// Gate-4 round 1: the minors that are properties rather than prose.
// ===========================================================================

/// §7.1's tie-break, in its **discriminating case** (gate-4 round 1, m8).
///
/// The rule is lexicographic on the per-thread prefix-length vector in the
/// declared visible order, then installation order. End-to-end tests only ever
/// exercised it on pairs with one visible thread, where a vector order and a
/// scalar order coincide and "then installation order" never arises. The two
/// halves are asked directly here:
///
/// - **incomparable attempts**: `[1, 0]` and `[0, 5]` are `follows`-wise
///   incomparable — one longer on the first declared thread, the other on the
///   second — and the rule must take the first, deterministically, rather than
///   whichever the traversal reached last;
/// - **a repeat of the standing best** must *not* replace it, which is what
///   "then installation order" means when the vectors are equal.
///
/// What would break it: `>` becoming `>=` in `Best::offer` (last-wins, which
/// is traversal-order dependent), or comparing by `iter().sum()` (which makes
/// `[0, 5]` beat `[1, 0]` and turns the order into a scalar one §7.1 does not
/// have).
#[test]
fn c9_the_tie_break_is_lexicographic_then_installation_order() {
    use crate::conformance::diagnose::Best;
    let g = ExecutionGraph::default();

    let mut best = Best::new(2);
    best.offer(vec![1, 0], &g);
    assert_eq!(best.vector(), [1, 0]);
    assert_eq!(best.accepted(), 1);

    // Incomparable, and larger by *sum*: it must not win.
    best.offer(vec![0, 5], &g);
    assert_eq!(
        best.vector(),
        [1, 0],
        "an incomparable attempt replaced the standing best, so the order is not \
         lexicographic in the declared visible order"
    );
    assert_eq!(best.accepted(), 1);

    // Equal: installation order keeps the first.
    best.offer(vec![1, 0], &g);
    assert_eq!(
        best.accepted(),
        1,
        "an equal attempt replaced the standing best, so the choice depends on which \
         branch the traversal walked last"
    );

    // Strictly greater: it wins.
    best.offer(vec![1, 1], &g);
    assert_eq!(best.vector(), [1, 1]);
    assert_eq!(best.accepted(), 2);

    // Order is on the *declared* sequence, so position 0 dominates entirely.
    let mut best = Best::new(2);
    best.offer(vec![0, 9], &g);
    best.offer(vec![1, 0], &g);
    assert_eq!(best.vector(), [1, 0]);
}

/// **A report list the run stopped early says so** (gate-4 round 1, m6).
///
/// §7.2's "not a complete set of violations" is about *lost revisits* (A1).
/// It is not about a loop the user's `max_iterations` or the gate's
/// `stop_at_first_report` cut short — and a user reading one report off a
/// stop-at-first run had no way to know a second was never looked for.
///
/// What would break it: removing `render_truncation`, or calling it only from
/// the `Inconclusive` arm (where it started).
#[test]
fn c2_a_truncated_report_list_tells_the_user_it_is_truncated() {
    let program = || {
        let _ = crate::nondet();
        crate::assert(false);
    };
    let spec = || {
        let _ = crate::nondet();
    };

    let stopped = verify(
        base(&["main"]).stop_at_first_report(true).build().unwrap(),
        program,
        spec,
    )
    .unwrap();
    let text = stopped.to_string();
    assert!(
        text.contains("truncated by configuration"),
        "a stop-at-first report list did not say it was truncated:\n{text}"
    );

    let bounded = verify(
        base(&["main"])
            .config(
                Config::builder()
                    .with_cons_type(ConsType::FIFO)
                    .with_max_iterations(1)
                    .build(),
            )
            .build()
            .unwrap(),
        program,
        spec,
    )
    .unwrap();
    let text = bounded.to_string();
    assert!(
        text.contains("truncated by a bound you set"),
        "a bounded report list did not say it was truncated:\n{text}"
    );

    // And a complete run says no such thing, or the line is noise.
    let complete = verify(base(&["main"]).build().unwrap(), program, spec).unwrap();
    assert_eq!(complete.outcome().end(), SearchEnd::StateSpaceExhausted);
    assert!(
        !complete.to_string().contains("truncated"),
        "a complete run claimed its report list was truncated"
    );
}

/// A **different** assertion firing during triage is not "what this report
/// says should happen" (gate-4 round 1, m7).
///
/// The report names `main`'s visible failure. The replay also re-runs an
/// *invisible* thread whose assertion fails, and that arrives in the triage
/// sink as a note. Rendering it as `ReplayedAssertion` attributed a note to a
/// report that never mentioned it.
///
/// What would break it: routing the note branch back to `ReplayedAssertion`,
/// or dropping the thread-name comparison against the report's own cause.
#[test]
fn c4_an_unrelated_replayed_assertion_is_not_the_reports_own() {
    let v = verify(
        base(&["main"]).triage(true).build().unwrap(),
        || {
            named("hidden", || crate::assert(false));
            crate::assert(false);
        },
        || {},
    )
    .expect("neither assertion is a triage failure");
    let reports = v.outcome().reports();
    assert_eq!(reports.len(), 1, "expected one visible-error report");

    // Whichever of the two the replay reached first, the rendering must not
    // claim a thread the report does not name is "what this report says
    // should happen".
    let t = reports[0].triage().expect("triage was on");
    let text = t.to_string();
    match t {
        TriageOutcome::ReplayedAssertion { thread, .. } => {
            assert_eq!(
                thread, "main",
                "a thread the report does not name was rendered as the report's own"
            );
            assert!(text.contains("what this report says should happen"));
        }
        TriageOutcome::OtherAssertion { thread, .. } => {
            assert_ne!(thread, "main");
            assert!(
                text.contains("a *different* one from the failure this report names"),
                "an unrelated assertion was not distinguished:\n{text}"
            );
            assert!(!text.contains("what this report says should happen"));
        }
        other => panic!("unexpected triage outcome: {other:?}"),
    }
    assert!(
        !text.contains("nondeterministic implementation") || text.contains("**not** a nondeterministic implementation"),
        "either way it must not be called nondeterminism:\n{text}"
    );
}

/// A triage failure does not tell the user their reports are waiting for them
/// (gate-4 round 1, m7).
///
/// `ConfError::TriageFailed` leaves through `Err`, so the caller has no
/// verdict and no report list at all. "That report keeps its pre-triage form"
/// described something the caller cannot see.
///
/// What would break it: restoring the old sentence, or making `TriageFailed`
/// carry a partial verdict without saying so.
#[test]
fn c4_a_triage_failure_does_not_claim_the_caller_has_the_reports() {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    COUNTER.store(0, Ordering::SeqCst);
    let e = verify(
        base(&["main"]).triage(true).build().unwrap(),
        || {
            let n = COUNTER.fetch_add(1, Ordering::SeqCst);
            let w = if n == 0 {
                named("w", || {
                    let _: u64 = crate::recv_msg_block();
                })
            } else {
                named("other", || {
                    let _: u64 = crate::recv_msg_block();
                })
            };
            crate::send_msg(w, 1u64);
        },
        || {},
    )
    .expect_err("a nondeterministic implementation must fail triage");
    let text = e.to_string();
    assert!(
        !text.contains("keeps its pre-triage form"),
        "the error told the user about a report list they do not have:\n{text}"
    );
    assert!(
        text.contains("No verdict was produced and no report list is returned"),
        "the error did not say what the caller actually receives:\n{text}"
    );
    assert!(
        text.contains("ConfBuilder::triage(false)"),
        "the error named no way forward:\n{text}"
    );
}

/// **What §7.1's serialized half actually costs, measured through the public
/// API** (gate-4 round 2, M3).
///
/// The retention figure has now been stated wrongly twice. First as the
/// criteria's `O(reports × |G₁|)` while a `MustState` was retained alongside a
/// separately cloned graph — two identical `ExecutionGraph`s and an unbounded
/// `RQueue`. Then, after that was fixed, as "one `ExecutionGraph` and one
/// `String`" — true of the shapes and false about the size, because the
/// `String` *is* a sorted graph plus a `MustState` plus the `Config`, as text.
///
/// So it is measured rather than described. This test pins two things: that
/// the JSON is **not** pretty-printed (indentation was roughly two thirds of
/// it), and the per-event order of magnitude that the run-level figure in
/// `ReplaySnapshot`'s rustdoc is derived from.
///
/// What would break it: `to_string_pretty` returning, or the snapshot growing
/// a second copy of anything.
#[test]
fn c13_the_serialized_snapshot_size_is_measured_not_described() {
    let v = verify(
        base(&["main"]).build().unwrap(),
        || {
            let m = main_thread_id();
            named("a", move || crate::send_msg(m, 1u64));
            named("b", move || crate::send_msg(m, 1u64));
            let _: u64 = crate::recv_msg_block();
        },
        || {},
    )
    .unwrap();
    let reports = v.outcome().reports();
    assert!(!reports.is_empty(), "nothing was reported");
    for r in reports {
        let ReplaySnapshot::Serialized(json) = r.replay_snapshot() else {
            panic!("the snapshot was not produced: {:?}", r.replay_snapshot());
        };
        assert!(
            !json.contains("\n  "),
            "the replay snapshot is pretty-printed again; the indentation was about two \
             thirds of it"
        );
    }

    // **The cost is affine, not proportional** (round 3, m3). A per-event
    // figure alone understates a small report badly — the fit below has a
    // constant term of several hundred bytes, which at two events is a third
    // of the total — and F-18's regime is exactly the many-small-reports one.
    // So the model in `ReplaySnapshot`'s rustdoc is `a + b × events`, and both
    // coefficients are pinned here.
    let mut points: Vec<(usize, usize)> = Vec::new();
    for n in 1..=6usize {
        let Ok(v) = verify(
            base(&["main"]).build().unwrap(),
            move || {
                let m = main_thread_id();
                for _ in 0..n {
                    named("s", move || crate::send_msg(m, 1u64));
                }
                let _: u64 = crate::recv_msg_block();
            },
            || {},
        ) else {
            continue;
        };
        for r in v.outcome().reports() {
            if let ReplaySnapshot::Serialized(json) = r.replay_snapshot() {
                points.push((r.events(), json.len()));
            }
        }
    }
    points.sort_unstable();
    points.dedup();
    assert!(points.len() > 8, "too few points to fit: {points:?}");

    let n = points.len() as f64;
    let sx: f64 = points.iter().map(|p| p.0 as f64).sum();
    let sy: f64 = points.iter().map(|p| p.1 as f64).sum();
    let sxx: f64 = points.iter().map(|p| (p.0 * p.0) as f64).sum();
    let sxy: f64 = points.iter().map(|p| (p.0 * p.1) as f64).sum();
    let slope = (n * sxy - sx * sy) / (n * sxx - sx * sx);
    let intercept = (sy - slope * sx) / n;
    assert!(
        (450.0..700.0).contains(&slope) && (200.0..900.0).contains(&intercept),
        "the serialized snapshot's size model moved: measured `{intercept:.0} + {slope:.0} \
         × events`, and `ReplaySnapshot`'s rustdoc and finding F-18 both quote `~440 + \
         ~570 × events`. Re-derive both before changing these bounds.\n  {points:?}"
    );
}

/// **Every name a comment cites in backticks exists** (round 2 n1, round 3 m2).
///
/// Round 1's n1 was four dangling doc references. Two were fixed and the
/// report recorded n1 as discharged by `cargo doc`'s warning count, which is a
/// **different check**: a plain code span is not an intra-doc link, so
/// de-linking a dangling name silences the warning and leaves the name
/// dangling. Round 2 replaced that with a test — whose name filter matched
/// only `c<N>_…` and `f_…`, so it could not see any of the three that were
/// actually wrong: a function cited under the wrong module *and* the wrong
/// name, a test cited by a name it never had, and a count.
///
/// So the filter is gone. **Every** backticked identifier-shaped token in a
/// comment must name something the crate defines. That is the check n1 wanted
/// two rounds ago, and the reason it is a test rather than a sweep is that the
/// failure mode is *renaming*, which has happened in every round including
/// this one.
///
/// What it cannot check is a count or a claim about structure — "one `match`",
/// "exactly one new instance". Those are §13's subject.
///
/// **It searches code, not comments**, which is not a detail: with comment
/// lines included every cited name matches its own citation and the check
/// passes for any input. That is how the first version of *this* test behaved,
/// found by injecting two bogus names and watching it stay green.
/// Names from `alg.tex` and the draft that appear in these comments as
/// mathematics rather than as Rust items.
const DRAFT_NOTATION: [&str; 10] = [
    "Tvis",
    "SpecVisit",
    "SpecStep",
    "Obsalph",
    "obsposet",
    "next_Spec",
    "next_Impl",
    "consistent_Spec",
    "obs_G",
    "status_G",
];

/// Rustdoc attributes that look like identifiers inside a code span.
const DOC_ATTRIBUTES: [&str; 3] = ["no_run", "should_panic", "ignore"];

#[test]
fn c1_every_name_cited_in_a_comment_exists() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    // **Whole identifiers, not substrings.** A `contains` test passed the
    // round-2 dangling name that this check exists to catch, because a *test's
    // own name* contained it as a substring — the check let through the very
    // reference round 3's m2 was about. The crate's identifiers are collected
    // as words instead.
    let mut words: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut stack = vec![dir.clone()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let path = e.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().and_then(|x| x.to_str()) == Some("rs") {
                // **Code only.** Comment lines are stripped, because with them
                // in, every cited name matches its own citation and the check
                // passes for any input at all. Found by injecting two bogus
                // names into a doc comment and watching it stay green — which
                // is the negative case round 3 asks every control to have.
                for line in std::fs::read_to_string(&path).unwrap().lines() {
                    let t = line.trim_start();
                    if t.starts_with("//") {
                        continue;
                    }
                    for w in line.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
                        if !w.is_empty() {
                            words.insert(w.to_owned());
                        }
                    }
                }
            }
        }
    }

    let mine = [
        "config.rs", "report.rs", "diagnose.rs", "triage.rs",
        "precheck.rs", "mod.rs", "ctx.rs", "s5_tests.rs",
    ];
    let conf = dir.join("conformance");
    let mut dangling = Vec::new();
    for f in mine {
        let body = std::fs::read_to_string(conf.join(f)).unwrap();
        for (n, line) in body.lines().enumerate() {
            let t = line.trim_start();
            if !(t.starts_with("//") || t.starts_with("///") || t.starts_with("//!")) {
                continue;
            }
            for span in t.split('`').skip(1).step_by(2) {
                let tok = span.trim();
                // Identifier-shaped: a path of segments and nothing else.
                // Prose, generics and code fragments are out.
                if tok.len() < 4
                    || !tok.chars().all(|c| c.is_alphanumeric() || c == '_' || c == ':')
                    || !tok.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
                {
                    continue;
                }
                let last = tok.rsplit("::").next().unwrap_or(tok);
                // A bare lowercase word with no underscore is prose, not a
                // name ("main", "probe" as a noun); require a shape only an
                // identifier has.
                if !last.contains('_') && !last.chars().any(|c| c.is_uppercase()) {
                    continue;
                }
                // The draft's own notation is prose, not a Rust name. It is a
                // written list rather than a heuristic, so a *new* piece of
                // notation has to be added deliberately and cannot smuggle a
                // dangling identifier through with it.
                if DRAFT_NOTATION.contains(&last) || DOC_ATTRIBUTES.contains(&last) {
                    continue;
                }
                if words.contains(last) {
                    continue;
                }
                dangling.push(format!("{f}:{}: `{tok}`", n + 1));
            }
        }
    }
    assert!(
        dangling.is_empty(),
        "comments cite names the crate does not define:\n  {}",
        dangling.join("\n  ")
    );
}
