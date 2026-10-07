//! P4-DIFF gate 3, the **tester's** judgement functions (criteria
//! `P4-DIFF.md` revision 5.2, X1, X2, X4, criteria 1 and 4): the plan-key
//! projection, the certification oracle by semantic cause, and the test-only
//! graph mutator the negative fixtures are built with.
//!
//! Every rule below was written from the criteria and the paper (`alg.tex`
//! §8.1 `def:ext`/`lem:complete`, §8.4 `def:cone`/`lem:witness`/`cor:absence`,
//! `lem:sig`) before the lead's `grid.rs` was read; the derivations are in
//! `plan/traceForge/log/dev/P4-DIFF.report.md`, Part 0 (D3).
//!
//! Conventions this file keeps because `s5_tests`' source scans read it: no
//! print macro anywhere, and every panic-family message starts with
//! `conformance:`.

use std::collections::{BTreeMap, BTreeSet};

use crate::conformance::canon::{BlockKind, CanonLabel, CanonPos, CanonicalGraph, ThreadKey};
use crate::conformance::cert::Certificate;
use crate::conformance::morphism::CompleteExecution;
use crate::conformance::obs::{wobs, Wobs};
use crate::conformance::report::ReportTag;
use crate::conformance::sig::{cone, covered, Summary};
use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::msg::Val;

// =========================================================================
// Keys (X2, criterion 1)
// =========================================================================

/// The canonical form's rendering — Part 1's report key (`canon.rs`), the
/// only equality between engines (ruling 3 of the Phase 4 addendum).
pub(super) fn canon_key(g: &ExecutionGraph, visible: &[String]) -> String {
    let c = CanonicalGraph::of(g, visible)
        .unwrap_or_else(|e| panic!("conformance: no canonical form for a grid graph: {e:?}"));
    format!("{c:?}")
}

/// Whether a canonical label is a **paper event** (X2): a send, a receive, a
/// coin toss, a choice, or an assertion failure (`err`). Everything else —
/// `Begin`, `End`, `TCreate`, `TJoin`, `Unique`, `Block{Assume | Value |
/// Join}` — is engine bookkeeping the plan key drops.
fn paper_label(l: &CanonLabel) -> Option<String> {
    match l {
        CanonLabel::Send { .. }
        | CanonLabel::Recv { .. }
        | CanonLabel::CToss { .. }
        | CanonLabel::Choice { .. } => Some(format!("{l:?}")),
        CanonLabel::Block {
            kind: BlockKind::Assert,
        } => Some("err".to_owned()),
        CanonLabel::Begin
        | CanonLabel::End { .. }
        | CanonLabel::TCreate { .. }
        | CanonLabel::TJoin { .. }
        | CanonLabel::Unique
        | CanonLabel::Block { .. } => None,
    }
}

/// A position in paper indices: the thread and its count of earlier paper
/// events.
type PaperPos = (ThreadKey, u32);

/// **Plan §6's canonical report key, as a projection of Part 1's form**
/// (criterion 1): drop the bookkeeping labels, keep `Block{Assert}` as `err`,
/// renumber each thread's surviving events to paper indices `0, 1, …` in
/// program order, and project the rf map onto those indices (⊥ kept).
/// Receive labels carry no source (the form's `Recv` has none); values stay.
pub(super) fn plan_key(g: &ExecutionGraph, visible: &[String]) -> String {
    let c = CanonicalGraph::of(g, visible)
        .unwrap_or_else(|e| panic!("conformance: no canonical form for a grid graph: {e:?}"));
    let mut next: BTreeMap<ThreadKey, u32> = BTreeMap::new();
    let mut paper: BTreeMap<CanonPos, PaperPos> = BTreeMap::new();
    let mut events: Vec<(PaperPos, String)> = Vec::new();
    // `events()` is sorted by position, so within a thread it is program order.
    for (pos, label) in c.events() {
        if let Some(text) = paper_label(label) {
            let n = next.entry(pos.0.clone()).or_insert(0);
            let at = (pos.0.clone(), *n);
            *n += 1;
            paper.insert(pos.clone(), at.clone());
            events.push((at, text));
        }
    }
    let at = |p: &CanonPos| {
        paper.get(p).cloned().unwrap_or_else(|| {
            panic!("conformance: an rf endpoint {p:?} is not a paper event of its graph")
        })
    };
    let rf: Vec<(PaperPos, Option<PaperPos>)> = c
        .rf()
        .iter()
        .map(|(r, s)| (at(r), s.as_ref().map(at)))
        .collect();
    format!("{events:?} rf {rf:?}")
}

// =========================================================================
// The certification oracle (X4, criterion 4)
// =========================================================================

/// A report's semantic cause, as the oracle receives it (independently of
/// the engine that raised it — round 03 m2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Cause {
    NoCover,
    /// `pos` is the event rendered as `ReportCause.pos` renders it
    /// (`Event`'s `Display`).
    VisibleError {
        thread: String,
        pos: String,
    },
}

/// One report to certify: the graph, its semantic tag, its cause, and
/// whether its replay snapshot is `Serialized`.
pub(super) struct Claim<'a> {
    pub(super) graph: &'a ExecutionGraph,
    pub(super) tag: ReportTag,
    pub(super) cause: Cause,
    pub(super) serialized: bool,
}

/// The oracle run's record, each input supplied independently (round 03 m2):
/// the Spec family, the Impl family, the Spec-error record, and the visible
/// set those families were taken under. Summaries are computed once.
pub(super) struct Families {
    visible: Vec<String>,
    spec: Vec<(ExecutionGraph, Wobs, Summary)>,
    imp: Vec<(ExecutionGraph, Summary, String)>,
    spec_errors: usize,
}

fn summary_of(g: &ExecutionGraph, w: &Wobs, visible: &[String]) -> Summary {
    Summary::of(CompleteExecution::assume_finished_at_gate(g), w, visible)
        .unwrap_or_else(|e| panic!("conformance: no summary for a complete grid graph: {e:?}"))
}

fn wobs_of(g: &ExecutionGraph, visible: &[String]) -> Wobs {
    wobs(g, visible).unwrap_or_else(|e| panic!("conformance: no words for a grid graph: {e:?}"))
}

impl Families {
    pub(super) fn new(
        spec: &[ExecutionGraph],
        imp: &[ExecutionGraph],
        spec_errors: usize,
        visible: &[String],
    ) -> Self {
        let spec = spec
            .iter()
            .map(|g| {
                let w = wobs_of(g, visible);
                let s = summary_of(g, &w, visible);
                (g.clone(), w, s)
            })
            .collect();
        let imp = imp
            .iter()
            .map(|g| {
                let w = wobs_of(g, visible);
                (g.clone(), summary_of(g, &w, visible), canon_key(g, visible))
            })
            .collect();
        Self {
            visible: visible.to_vec(),
            spec,
            imp,
            spec_errors,
        }
    }

    pub(super) fn spec_len(&self) -> usize {
        self.spec.len()
    }

    pub(super) fn imp_len(&self) -> usize {
        self.imp.len()
    }

    /// Whether `imp` (a complete Impl graph) is covered by some member of the
    /// Spec family (`lem:sig`).
    pub(super) fn is_covered(&self, imp: &ExecutionGraph) -> bool {
        let w = wobs_of(imp, &self.visible);
        let s = summary_of(imp, &w, &self.visible);
        self.spec.iter().any(|(_, _, m)| covered(&s, m))
    }

    /// Whether some Impl family member is uncovered (X5 e's "exactly one
    /// iff").
    pub(super) fn some_impl_uncovered(&self) -> bool {
        self.imp
            .iter()
            .any(|(_, s, _)| !self.spec.iter().any(|(_, _, m)| covered(s, m)))
    }

    /// Canonical keys of the uncovered Impl members — the set the three
    /// enumerating engines must report (`thm:stateful`, `thm:cfirst`,
    /// `thm:gated`).
    pub(super) fn uncovered_keys(&self) -> BTreeSet<String> {
        self.imp
            .iter()
            .filter(|(_, s, _)| !self.spec.iter().any(|(_, _, m)| covered(s, m)))
            .map(|(_, _, k)| k.clone())
            .collect()
    }

    /// Whether the canonical form `key` is a member of the Impl family.
    pub(super) fn has_impl_key(&self, key: &str) -> bool {
        self.imp.iter().any(|(_, _, k)| k == key)
    }

    /// Whether some Spec member passes `cone(g, M)`.
    pub(super) fn some_cone(&self, g: &ExecutionGraph) -> bool {
        let w = wobs_of(g, &self.visible);
        self.spec
            .iter()
            .any(|(m, mw, _)| cone(g, &w, m, mw, &self.visible))
    }

    /// The Impl members that extend `g` (`def:ext`, through `Certificate`'s
    /// `valid_at` on canonical positions).
    fn extensions(&self, g: &ExecutionGraph) -> Result<Vec<usize>, String> {
        let cert = Certificate::absence_established(g, &self.visible)
            .map_err(|e| format!("no canonical form for the report: {e:?}"))?;
        let mut out = Vec::new();
        for (i, (m, _, _)) in self.imp.iter().enumerate() {
            if cert
                .valid_at(m, &self.visible)
                .map_err(|e| format!("valid_at refused Impl member #{i}: {e:?}"))?
            {
                out.push(i);
            }
        }
        Ok(out)
    }
}

/// The name of thread `t` in `g`, if it has one.
fn name_of(g: &ExecutionGraph, t: crate::thread::ThreadId) -> Option<String> {
    g.get_thread_tclab(t).name().clone()
}

/// Every `Block{Assert}` that is its thread's **last paper event**, with the
/// thread's name: the thread's last event, or its second-to-last when an
/// `End` follows it.
///
/// **Measured, not assumed** (gate 3): X4 reads "a `Block` is terminal", but
/// on R2's complete Impl graphs the errored thread `a` carries `END` at
/// `(t1, 2)` after its `BLK Assert` at `(t1, 1)`; the enumerator's report
/// graph, taken at the error, ends at the `BLK Assert`. `End` is bookkeeping
/// (no paper event), so `alg.tex` §8.1's "that event is the last it
/// contributes" is read on paper events.
fn last_asserts(g: &ExecutionGraph) -> Vec<(Option<String>, Event)> {
    let mut out = Vec::new();
    for t in g.thread_ids() {
        let mut n = g.thread_size(t);
        if n == 0 {
            continue;
        }
        if n >= 2 && matches!(g.label(Event::new(t, (n - 1) as u32)), LabelEnum::End(_)) {
            n -= 1;
        }
        let e = Event::new(t, (n - 1) as u32);
        if let LabelEnum::Block(b) = g.label(e) {
            if matches!(b.btype(), BlockType::Assert) {
                out.push((name_of(g, t), e));
            }
        }
    }
    out
}

/// **The certification oracle**, one case per semantic tag, the cases
/// mutually exclusive (X4). `Ok(())` accepts; `Err` names the conjunct that
/// failed.
///
/// - `GrowingExhaustion`: no Spec member passes `cone(report, M)`; at least one
///   Impl member extends the report; every Impl member that extends it is
///   uncovered.
/// - `CompleteCoverage`: the report is a member of the Impl family (canonical
///   equality) and no Spec member covers it.
/// - `VisibleError`: the cause's thread is declared visible; the cause names
///   a `Block{Assert}` that is its thread's last event; at least one Impl
///   member extends the report; the snapshot is `Serialized`; the oracle run
///   recorded no Spec error. **No `C₁`-absence demand** (plan §6 case (3)).
pub(super) fn certify(f: &Families, r: &Claim<'_>) -> Result<(), String> {
    match r.tag {
        ReportTag::GrowingExhaustion => {
            if r.cause != Cause::NoCover {
                return Err(format!("a GrowingExhaustion tag with cause {:?}", r.cause));
            }
            let w = wobs_of(r.graph, &f.visible);
            for (i, (m, mw, _)) in f.spec.iter().enumerate() {
                if cone(r.graph, &w, m, mw, &f.visible) {
                    return Err(format!(
                        "cone(report, M) holds for Spec member #{i}: a partial graph of Spec \
                         matches the report (lem:witness)"
                    ));
                }
            }
            let ext = f.extensions(r.graph)?;
            if ext.is_empty() {
                return Err("no member of the Impl family extends the report".to_owned());
            }
            for i in ext {
                let (_, s, _) = &f.imp[i];
                if let Some(j) = f.spec.iter().position(|(_, _, m)| covered(s, m)) {
                    return Err(format!(
                        "Impl member #{i} extends the report and is covered by Spec member #{j}"
                    ));
                }
            }
            Ok(())
        }
        ReportTag::CompleteCoverage => {
            if r.cause != Cause::NoCover {
                return Err(format!("a CompleteCoverage tag with cause {:?}", r.cause));
            }
            let key = canon_key(r.graph, &f.visible);
            if !f.has_impl_key(&key) {
                return Err("the report is not a member of the Impl family".to_owned());
            }
            let w = wobs_of(r.graph, &f.visible);
            let s = summary_of(r.graph, &w, &f.visible);
            if let Some(j) = f.spec.iter().position(|(_, _, m)| covered(&s, m)) {
                return Err(format!("the report is covered by Spec member #{j}"));
            }
            Ok(())
        }
        ReportTag::VisibleError => {
            let Cause::VisibleError { thread, pos } = &r.cause else {
                return Err(format!("a VisibleError tag with cause {:?}", r.cause));
            };
            if f.spec_errors > 0 {
                return Err(format!(
                    "the oracle run recorded {} Spec error(s): Spec is not assertion-safe",
                    f.spec_errors
                ));
            }
            // The visible-thread check.
            if !f.visible.iter().any(|v| v == thread) {
                return Err(format!(
                    "the errored thread `{thread}` is not declared visible"
                ));
            }
            // The cause/graph check.
            let named = last_asserts(r.graph)
                .into_iter()
                .any(|(n, e)| n.as_deref() == Some(thread.as_str()) && e.to_string() == *pos);
            if !named {
                return Err(format!(
                    "the cause ({thread}, {pos}) names no Block{{Assert}} at its thread's last \
                     position in the report graph"
                ));
            }
            if f.extensions(r.graph)?.is_empty() {
                return Err("no member of the Impl family extends the report".to_owned());
            }
            if !r.serialized {
                return Err("the report's snapshot is not Serialized".to_owned());
            }
            Ok(())
        }
    }
}

// =========================================================================
// The test-only mutator (criterion 4's negative fixtures)
// =========================================================================

/// The thread of `g` named `name`.
pub(super) fn thread_named(g: &ExecutionGraph, name: &str) -> crate::thread::ThreadId {
    g.thread_ids()
        .into_iter()
        .find(|t| name_of(g, *t).as_deref() == Some(name))
        .unwrap_or_else(|| panic!("conformance: no thread named `{name}` in the graph"))
}

/// The `k`-th send of thread `name`.
pub(super) fn send_of(g: &ExecutionGraph, name: &str, k: usize) -> Event {
    let t = thread_named(g, name);
    (0..g.thread_size(t) as u32)
        .map(|i| Event::new(t, i))
        .filter(|e| matches!(g.label(*e), LabelEnum::SendMsg(_)))
        .nth(k)
        .unwrap_or_else(|| panic!("conformance: thread `{name}` has no send number {k}"))
}

/// The first event of thread `name` (its `Begin`).
pub(super) fn begin_of(g: &ExecutionGraph, name: &str) -> Event {
    Event::new(thread_named(g, name), 0)
}

/// `g` restricted to the `porf` view of `e` (`copy_to_view`): a
/// `porf`-prefix-closed restriction, so a partial graph of the same program.
pub(super) fn restrict_to_porf(g: &ExecutionGraph, e: Event) -> ExecutionGraph {
    g.copy_to_view(&g.porf(e))
}

/// `g` with the send at `e` carrying `v` instead of its value.
pub(super) fn with_send_value(g: &ExecutionGraph, e: Event, v: i32) -> ExecutionGraph {
    let mut out = g.clone();
    match out.label_mut(e) {
        LabelEnum::SendMsg(s) => s.val = Val::new(v),
        other => panic!("conformance: the mutator expected a send at {e}, found {other:?}"),
    }
    out
}

// =========================================================================
// Self-tests of the projection (criterion 1's mechanism)
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// The projection is not the identity: two graphs whose forms differ
    /// only in bookkeeping share a plan key, and a value change separates
    /// them. Built from one program so the forms exist.
    #[test]
    fn the_projection_drops_bookkeeping_and_keeps_values() {
        use crate::conformance::grid::{naive_fixture, GridConfig, GridEnd, GridEngine, GridRaw};
        let f = naive_fixture(2, 2);
        let end =
            crate::conformance::grid::run_grid(&f, &GridConfig::new(GridEngine::Stateful), None);
        let GridEnd::Ok(r) = end else {
            panic!("conformance: the stateful run did not complete: {end:?}")
        };
        let GridRaw::Stateful(o) = &r.raw else {
            panic!("conformance: not a stateful outcome")
        };
        let g = &o.kept_impl_graphs[0];
        let v = &f.visible;
        let key = plan_key(g, v);
        assert!(!key.contains("Begin") && !key.contains("End") && !key.contains("TCreate"));
        assert!(!key.contains("Unique"));
        let changed = with_send_value(g, send_of(g, "c", 0), 7);
        assert_ne!(
            plan_key(&changed, v),
            key,
            "conformance: a value is in the key"
        );
        assert_ne!(canon_key(&changed, v), canon_key(g, v));
        // The paper indices: `c`'s first paper event is index 0 although its
        // raw index is 1 (after `Begin`).
        assert!(
            key.contains("(Declared(\"c\"), 0)"),
            "conformance: renumbered to paper indices: {key}"
        );
    }
}
