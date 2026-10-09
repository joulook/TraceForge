//! `P5-APPS` gate 3: the tester's tests (criteria `P5-APPS.md` revision 5).
//!
//! Application-derived bounded models, not real code from a deployed system.
//!
//! **How the expectations were made.** Every figure in [`PILOT`] was derived
//! from the criteria's encodings and the paper's `def:morph` **before** the
//! lead's fixtures or expectations were read: by hand at the hand-count sizes,
//! and over every pilot size by an independent model of the encodings (a
//! per-sender-FIFO enumerator of complete graphs with a `def:morph` check and a
//! search for a linearisation outside `vis(Spec)`), recorded in
//! `plan/traceForge/log/dev/P5-APPS.derived.md` (sha256 in `backlog/changes.md`
//! before the first run). The reconciliation with the lead's
//! `P5-APPS.expected.md` is in `P5-APPS.report.md`.
//!
//! **What is checked per pilot fixture** (criteria 4 and 5): the oracle run's
//! complete Impl and Spec graph counts; the uncovered count; each uncovered
//! graph's detection mechanism (M4: the morphism condition failing against
//! every Spec graph) recomputed here from `morphism.rs`'s three conditions and
//! cross-checked against the oracle's signature coverage; the blocked clients
//! of every status row; the number of uncovered graphs with a visible trace
//! outside `vis(Spec)`; then the four engines under the three selectors (the
//! enumerator at an unlimited budget with the memo on, the sweeping engines
//! exhaustive under `Always`): verdict, `end`, report-key equality with the
//! oracle's uncovered set for the enumerating engines, and certification of
//! every report of every engine.
//!
//! Conventions kept because the closed source scans read this file: no print
//! macro anywhere, and every panic-family message starts with `conformance:`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use crate::conformance::bench;
use crate::conformance::cert::Certificate;
use crate::conformance::config::{GatePolicy, GatedMode};
use crate::conformance::ctx::ReportKind;
use crate::conformance::eval::fixture_by_name;
use crate::conformance::gated::ReportSite;
use crate::conformance::grid::{
    a2_op, apps_fixtures, registry, row_of, Budget, Fixture, GridConfig, GridEnd, GridEngine,
    GridRaw, GridResult, Group, Req, Row, Tables,
};
use crate::conformance::grid_oracle::{canon_key, certify, Cause, Claim, Families};
use crate::conformance::morphism::{
    observations_match, order_is_reflected, statuses, CompleteExecution, Status,
};
use crate::conformance::obs::{wobs, Wobs};
use crate::conformance::report::{
    obs_text, ReplaySnapshot, ReportCause, ReportGate, ReportTag, SearchEnd,
};
use crate::conformance::selector::Selector;
use crate::exec_graph::ExecutionGraph;

const SELECTORS: [Selector; 3] = [Selector::Ltr, Selector::FewestEvents, Selector::Reverse];

// =========================================================================
// The derived expectations (criterion 3; `P5-APPS.derived.md`'s table)
// =========================================================================

/// One pilot fixture's derived figures.
#[derive(Clone, Copy, Debug)]
struct Exp {
    name: &'static str,
    /// Complete Impl graphs (`Graphs(Impl)`, M7).
    imp: usize,
    /// Complete Spec graphs.
    spec: usize,
    /// Uncovered complete Impl graphs: the enumerating engines' key-set size.
    unc: usize,
    /// Uncovered graphs with a visible trace outside `vis(Spec)`.
    genuine: usize,
    /// Mechanism per uncovered graph, `K:n` sorted, `K` in `O`, `S`, `V`,
    /// `V+O` (both fail against every Spec graph), `V|O` (mixed).
    mech: &'static str,
    /// Blocked visible threads per uncovered graph, `a+b:n` sorted.
    blocked: &'static str,
    /// "Conforming (vacuous)": the instance is identical to its base.
    vacuous: bool,
}

#[allow(clippy::too_many_arguments)]
const fn exp(
    name: &'static str,
    imp: usize,
    spec: usize,
    unc: usize,
    genuine: usize,
    mech: &'static str,
    blocked: &'static str,
    vacuous: bool,
) -> Exp {
    Exp {
        name,
        imp,
        spec,
        unc,
        genuine,
        mech,
        blocked,
        vacuous,
    }
}

/// Every pilot size of every row (criteria "Pilot sizes"), 132 fixtures.
const PILOT: [Exp; 132] = [
    exp("apps/a1/correct/spec/n2r1", 8, 16, 0, 0, "", "", false),
    exp("apps/a1/correct/spec/n3r1", 48, 16, 0, 0, "", "", false),
    exp("apps/a1/correct/spec/n4r1", 384, 16, 0, 0, "", "", false),
    exp("apps/a1/correct/spec/n2r2", 64, 256, 0, 0, "", "", false),
    exp("apps/a1/correct/spec/n2r3", 512, 4096, 0, 0, "", "", false),
    exp(
        "apps/a1/control-reverse/spec/n2r1",
        8,
        16,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a1/control-reverse/spec/n3r1",
        48,
        16,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a1/control-reverse/spec/n4r1",
        384,
        16,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a1/control-reverse/spec/n2r2",
        64,
        256,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a1/control-reverse/spec/n2r3",
        512,
        4096,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a1/eager/spec/n2r1",
        8,
        16,
        5,
        5,
        "O:3 V:1 V+O:1",
        "",
        false,
    ),
    exp(
        "apps/a1/eager/spec/n3r1",
        48,
        16,
        42,
        42,
        "O:30 V:2 V+O:10",
        "",
        false,
    ),
    exp(
        "apps/a1/eager/spec/n4r1",
        384,
        16,
        360,
        360,
        "O:264 V:8 V+O:88",
        "",
        false,
    ),
    exp(
        "apps/a1/eager/spec/n2r2",
        64,
        256,
        55,
        55,
        "O:27 V:7 V+O:21",
        "",
        false,
    ),
    exp(
        "apps/a1/eager/spec/n2r3",
        512,
        4096,
        485,
        485,
        "O:189 V:37 V+O:259",
        "",
        false,
    ),
    exp(
        "apps/a1/early-abort/spec/n2r1",
        8,
        16,
        4,
        4,
        "O:4",
        "",
        false,
    ),
    exp(
        "apps/a1/early-abort/spec/n3r1",
        48,
        16,
        32,
        32,
        "O:32",
        "",
        false,
    ),
    exp(
        "apps/a1/early-abort/spec/n4r1",
        384,
        16,
        296,
        296,
        "O:296",
        "",
        false,
    ),
    exp(
        "apps/a1/early-abort/spec/n2r2",
        64,
        256,
        48,
        48,
        "O:48",
        "",
        false,
    ),
    exp(
        "apps/a1/early-abort/spec/n2r3",
        512,
        4096,
        448,
        448,
        "O:448",
        "",
        false,
    ),
    exp(
        "apps/a1/silent/spec/n2r1",
        8,
        16,
        8,
        8,
        "S:8",
        "p1:8",
        false,
    ),
    exp(
        "apps/a1/silent/spec/n3r1",
        48,
        16,
        48,
        48,
        "S:48",
        "p1:48",
        false,
    ),
    exp(
        "apps/a1/silent/spec/n4r1",
        384,
        16,
        384,
        384,
        "S:384",
        "p1:384",
        false,
    ),
    exp(
        "apps/a1/silent/spec/n2r2",
        64,
        256,
        64,
        64,
        "S:64",
        "p1:64",
        false,
    ),
    exp(
        "apps/a1/silent/spec/n2r3",
        512,
        4096,
        512,
        512,
        "S:512",
        "p1:512",
        false,
    ),
    exp("apps/a2/pb/spec/k1q1", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/pb/spec/k2q1", 2, 2, 0, 0, "", "", false),
    exp("apps/a2/pb/spec/k3q1", 6, 6, 0, 0, "", "", false),
    exp("apps/a2/pb/spec/k1q2", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/pb/spec/k1q3", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/pb-br/spec/k1q1", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/pb-br/spec/k2q1", 2, 2, 0, 0, "", "", false),
    exp("apps/a2/pb-br/spec/k3q1", 6, 6, 0, 0, "", "", false),
    exp("apps/a2/pb-br/spec/k1q2", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/pb-br/spec/k1q3", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k1q1s1", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k2q1s1", 2, 2, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k3q1s1", 6, 6, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k1q2s1", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k1q3s1", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k1q1s2", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k2q1s2", 2, 2, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k3q1s2", 6, 6, 0, 0, "", "", false),
    exp("apps/a2/sh/spec/k1q3s2", 1, 1, 0, 0, "", "", false),
    exp("apps/a2/early-ack/spec/k2q1", 2, 2, 1, 1, "O:1", "", false),
    exp("apps/a2/early-ack/spec/k3q1", 6, 6, 4, 2, "O:4", "", false),
    exp(
        "apps/a2/early-ack/spec/k2q2",
        10,
        6,
        7,
        7,
        "O:3 V:2 V+O:1 V|O:1",
        "",
        false,
    ),
    exp(
        "apps/a2/early-ack/spec/k2q3",
        54,
        20,
        42,
        39,
        "O:21 V:8 V+O:9 V|O:4",
        "",
        false,
    ),
    exp("apps/a2/early-ack/spec/k1q2", 2, 1, 1, 1, "V:1", "", false),
    exp(
        "apps/a2/stale-get/spec/k2q1",
        2,
        2,
        1,
        1,
        "V|O:1",
        "",
        false,
    ),
    exp(
        "apps/a2/stale-get/spec/k3q1",
        6,
        6,
        3,
        3,
        "V|O:3",
        "",
        false,
    ),
    exp("apps/a2/stale-get/spec/k2q2", 6, 6, 6, 6, "V:6", "", false),
    exp(
        "apps/a2/stale-get/spec/k2q3",
        20,
        20,
        20,
        20,
        "V:20",
        "",
        false,
    ),
    exp("apps/a2/stale-get/spec/k1q2", 1, 1, 1, 1, "V:1", "", false),
    exp(
        "apps/a2/silent-put/spec/k1q1",
        1,
        1,
        1,
        1,
        "S:1",
        "c0:1",
        false,
    ),
    exp(
        "apps/a2/silent-put/spec/k2q1",
        2,
        2,
        2,
        2,
        "S:2",
        "c0:2",
        false,
    ),
    exp(
        "apps/a2/silent-put/spec/k3q1",
        6,
        6,
        6,
        6,
        "S:6",
        "c0:3 c2:3",
        false,
    ),
    exp(
        "apps/a2/silent-put/spec/k1q2",
        1,
        1,
        1,
        1,
        "S:1",
        "c0:1",
        false,
    ),
    exp(
        "apps/a2/silent-put/spec/k1q3",
        1,
        1,
        1,
        1,
        "S:1",
        "c0:1",
        false,
    ),
    exp("apps/a2/misroute/spec/k1q2s2", 1, 1, 1, 1, "V:1", "", false),
    exp("apps/a2/misroute/spec/k2q2s2", 6, 6, 6, 6, "V:6", "", false),
    exp(
        "apps/a2/misroute/spec/k3q2s2",
        90,
        90,
        90,
        90,
        "V:90",
        "",
        false,
    ),
    exp("apps/a2/misroute/spec/k1q3s2", 1, 1, 1, 1, "V:1", "", false),
    exp(
        "apps/a2/control-early-ack-primary/spec/k1q1",
        1,
        1,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-primary/spec/k2q1",
        2,
        2,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-primary/spec/k3q1",
        6,
        6,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-primary/spec/k1q2",
        1,
        1,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-primary/spec/k1q3",
        1,
        1,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-fwd/spec/k1q1",
        1,
        1,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-fwd/spec/k2q1",
        2,
        2,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-fwd/spec/k3q1",
        6,
        6,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-fwd/spec/k1q2",
        1,
        1,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a2/control-early-ack-fwd/spec/k1q3",
        1,
        1,
        0,
        0,
        "",
        "",
        false,
    ),
    exp("apps/a3/fifo/spec/k2q1", 4, 2, 0, 0, "", "", false),
    exp("apps/a3/fifo/spec/k3q1", 30, 6, 0, 0, "", "", false),
    exp("apps/a3/fifo/spec/k2q2", 28, 6, 0, 0, "", "", false),
    exp("apps/a3/control-lifo/spec/k2q1", 4, 2, 0, 0, "", "", true),
    exp("apps/a3/control-lifo/spec/k3q1", 30, 6, 0, 0, "", "", false),
    exp("apps/a3/control-lifo/spec/k2q2", 28, 6, 0, 0, "", "", true),
    exp(
        "apps/a3/double-grant/spec/k2q1",
        6,
        2,
        4,
        4,
        "O:4",
        "",
        false,
    ),
    exp(
        "apps/a3/double-grant/spec/k3q1",
        90,
        6,
        84,
        84,
        "O:84",
        "",
        false,
    ),
    exp(
        "apps/a3/double-grant/spec/k2q2",
        70,
        6,
        64,
        64,
        "O:64",
        "",
        false,
    ),
    exp(
        "apps/a3/wrong-round/spec/k2q1",
        4,
        2,
        4,
        4,
        "V:4",
        "",
        false,
    ),
    exp(
        "apps/a3/wrong-round/spec/k3q1",
        30,
        6,
        30,
        30,
        "V:30",
        "",
        false,
    ),
    exp(
        "apps/a3/wrong-round/spec/k2q2",
        28,
        6,
        28,
        28,
        "V:28",
        "",
        false,
    ),
    exp(
        "apps/a3/never-grant/spec/k2q1",
        4,
        2,
        1,
        1,
        "S:1",
        "c1:1",
        false,
    ),
    exp(
        "apps/a3/never-grant/spec/k3q1",
        28,
        6,
        10,
        10,
        "S:10",
        "c0+c2:1 c1+c2:1 c2:8",
        false,
    ),
    exp(
        "apps/a3/never-grant/spec/k2q2",
        21,
        6,
        8,
        8,
        "S:8",
        "c1:8",
        false,
    ),
    exp("apps/a4/hash/a4a/k1q1m1", 1, 1, 0, 0, "", "", false),
    exp("apps/a4/hash/a4a/k2q1m1", 2, 2, 0, 0, "", "", false),
    exp("apps/a4/hash/a4a/k3q1m1", 6, 6, 0, 0, "", "", false),
    exp("apps/a4/hash/a4a/k1q2m1", 1, 1, 0, 0, "", "", false),
    exp("apps/a4/hash/a4a/k1q1m2", 1, 2, 0, 0, "", "", false),
    exp("apps/a4/hash/a4a/k1q1m3", 1, 3, 0, 0, "", "", false),
    exp("apps/a4/hash/a4a/k2q1m2", 2, 8, 0, 0, "", "", false),
    exp("apps/a4/hash/a4b/k1q1m1", 1, 1, 0, 0, "", "", false),
    exp("apps/a4/hash/a4b/k2q1m1", 2, 2, 0, 0, "", "", false),
    exp("apps/a4/hash/a4b/k3q1m1", 6, 6, 0, 0, "", "", false),
    exp("apps/a4/hash/a4b/k1q2m1", 1, 1, 0, 0, "", "", false),
    exp("apps/a4/hash/a4b/k1q1m2", 1, 2, 0, 0, "", "", false),
    exp("apps/a4/hash/a4b/k1q1m3", 1, 3, 0, 0, "", "", false),
    exp("apps/a4/hash/a4b/k2q1m2", 2, 8, 0, 0, "", "", false),
    exp("apps/a4/rr/a4b/k1q1m1", 1, 1, 0, 0, "", "", false),
    exp("apps/a4/rr/a4b/k2q1m1", 2, 2, 0, 0, "", "", false),
    exp("apps/a4/rr/a4b/k3q1m1", 6, 6, 0, 0, "", "", false),
    exp("apps/a4/rr/a4b/k1q2m1", 1, 1, 0, 0, "", "", false),
    exp("apps/a4/rr/a4b/k1q1m2", 1, 2, 0, 0, "", "", false),
    exp("apps/a4/rr/a4b/k1q1m3", 1, 3, 0, 0, "", "", false),
    exp("apps/a4/rr/a4b/k2q1m2", 2, 8, 0, 0, "", "", false),
    exp("apps/a4/rr/a4a/k1q2m2", 1, 2, 1, 1, "V:1", "", false),
    exp("apps/a4/rr/a4a/k2q2m2", 6, 24, 4, 4, "V:4", "", false),
    exp("apps/a4/rr/a4a/k3q2m2", 90, 720, 90, 90, "V:90", "", false),
    exp("apps/a4/rr/a4a/k1q2m3", 1, 3, 1, 1, "V:1", "", false),
    exp("apps/a4/drop/a4b/k1q1m1", 1, 1, 1, 1, "S:1", "c0:1", false),
    exp("apps/a4/drop/a4b/k2q1m1", 2, 2, 2, 2, "S:2", "c1:2", false),
    exp("apps/a4/drop/a4b/k3q1m1", 6, 6, 6, 6, "S:6", "c2:6", false),
    exp("apps/a4/drop/a4b/k1q2m1", 1, 1, 1, 1, "S:1", "c0:1", false),
    exp("apps/a4/drop/a4b/k1q1m2", 1, 2, 1, 1, "S:1", "c0:1", false),
    exp("apps/a4/drop/a4b/k1q1m3", 1, 3, 1, 1, "S:1", "c0:1", false),
    exp("apps/a4/drop/a4b/k2q1m2", 2, 8, 2, 2, "S:2", "c1:2", false),
    exp(
        "apps/a4/pair-swap-hash/a4a/k2q1m1",
        2,
        2,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a4/pair-swap-hash/a4a/k2q2m1",
        4,
        6,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a4/pair-swap-hash/a4a/k2q1m2",
        2,
        8,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a4/pair-swap-hash/a4a/k2q1m3",
        2,
        18,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a4/pair-swap-hash/a4b/k2q1m1",
        2,
        2,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a4/pair-swap-hash/a4b/k2q2m1",
        4,
        6,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a4/pair-swap-hash/a4b/k2q1m2",
        2,
        8,
        0,
        0,
        "",
        "",
        false,
    ),
    exp(
        "apps/a4/pair-swap-hash/a4b/k2q1m3",
        2,
        18,
        0,
        0,
        "",
        "",
        false,
    ),
    exp("apps/a4/pair-swap-rr/a4b/k2q1m1", 2, 2, 0, 0, "", "", false),
    exp("apps/a4/pair-swap-rr/a4b/k2q2m1", 4, 6, 0, 0, "", "", false),
    exp("apps/a4/pair-swap-rr/a4b/k2q1m2", 2, 8, 0, 0, "", "", false),
    exp(
        "apps/a4/pair-swap-rr/a4b/k2q1m3",
        2,
        18,
        0,
        0,
        "",
        "",
        false,
    ),
];

fn exp_of(name: &str) -> Exp {
    *PILOT
        .iter()
        .find(|e| e.name == name)
        .unwrap_or_else(|| panic!("conformance: `{name}` is not a pilot fixture"))
}

/// The pilot lists, rebuilt from the criteria's text ("Pilot sizes"),
/// independently of [`PILOT`].
fn criteria_pilot_names() -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let a1 = [(2, 1), (3, 1), (4, 1), (2, 2), (2, 3)];
    for row in [
        "correct",
        "eager",
        "early-abort",
        "silent",
        "control-reverse",
    ] {
        for (n, r) in a1 {
            out.insert(format!("apps/a1/{row}/spec/n{n}r{r}"));
        }
    }
    let pb = [(1, 1), (2, 1), (3, 1), (1, 2), (1, 3)];
    for row in [
        "pb",
        "pb-br",
        "silent-put",
        "control-early-ack-primary",
        "control-early-ack-fwd",
    ] {
        for (k, q) in pb {
            out.insert(format!("apps/a2/{row}/spec/k{k}q{q}"));
        }
    }
    for (k, q) in pb {
        out.insert(format!("apps/a2/sh/spec/k{k}q{q}s1"));
    }
    for (k, q) in [(1, 1), (2, 1), (3, 1), (1, 3)] {
        out.insert(format!("apps/a2/sh/spec/k{k}q{q}s2"));
    }
    for row in ["early-ack", "stale-get"] {
        for (k, q) in [(2, 1), (3, 1), (2, 2), (2, 3), (1, 2)] {
            out.insert(format!("apps/a2/{row}/spec/k{k}q{q}"));
        }
    }
    for (k, q) in [(1, 2), (2, 2), (3, 2), (1, 3)] {
        out.insert(format!("apps/a2/misroute/spec/k{k}q{q}s2"));
    }
    for row in [
        "fifo",
        "double-grant",
        "never-grant",
        "wrong-round",
        "control-lifo",
    ] {
        for (k, q) in [(2, 1), (3, 1), (2, 2)] {
            out.insert(format!("apps/a3/{row}/spec/k{k}q{q}"));
        }
    }
    let seven = [
        (1, 1, 1),
        (2, 1, 1),
        (3, 1, 1),
        (1, 2, 1),
        (1, 1, 2),
        (1, 1, 3),
        (2, 1, 2),
    ];
    for row in ["hash/a4a", "hash/a4b", "rr/a4b", "drop/a4b"] {
        for (k, q, m) in seven {
            out.insert(format!("apps/a4/{row}/k{k}q{q}m{m}"));
        }
    }
    for (k, q, m) in [(1, 2, 2), (2, 2, 2), (3, 2, 2), (1, 2, 3)] {
        out.insert(format!("apps/a4/rr/a4a/k{k}q{q}m{m}"));
    }
    for row in [
        "pair-swap-hash/a4a",
        "pair-swap-hash/a4b",
        "pair-swap-rr/a4b",
    ] {
        for (k, q, m) in [(2, 1, 1), (2, 2, 1), (2, 1, 2), (2, 1, 3)] {
            out.insert(format!("apps/a4/{row}/k{k}q{q}m{m}"));
        }
    }
    out
}

// =========================================================================
// Harness (Part 6's X3 mapping, as `mixed_tests.rs` writes it)
// =========================================================================

fn ok(end: GridEnd) -> GridResult {
    match end {
        GridEnd::Ok(r) => r,
        GridEnd::Panicked {
            fixture,
            config,
            payload,
        } => panic!(
            "conformance: the engine panicked on `{fixture}` under {}: {payload}",
            config.label()
        ),
        GridEnd::Capped { fixture, .. } => panic!("conformance: `{fixture}` capped"),
    }
}

/// One engine run on the lean path (the owner's resource rule,
/// `P5-README.md`): `eval::run_row_in_process(.., keep_graphs = false)` —
/// the reports keep their graphs, the families are not kept.
fn grun(f: &Fixture, c: &GridConfig) -> GridResult {
    ok(crate::conformance::eval::run_row_in_process(f, c, false))
}

/// One report of a grid run, engine-independently.
struct Rep<'a> {
    graph: &'a ExecutionGraph,
    tag: ReportTag,
    cause: Cause,
    serialized: bool,
}

fn serialized(s: &ReplaySnapshot) -> bool {
    matches!(s, ReplaySnapshot::Serialized(_))
}

fn reports_of(r: &GridResult) -> Vec<Rep<'_>> {
    match &r.raw {
        GridRaw::Enumerator(o) => o
            .reports
            .iter()
            .map(|rep| {
                let (cause, rc) = match &rep.kind {
                    ReportKind::NoCover => (Cause::NoCover, ReportCause::NoCover),
                    ReportKind::VisibleError { thread, pos } => (
                        Cause::VisibleError {
                            thread: thread.clone(),
                            pos: pos.to_string(),
                        },
                        ReportCause::VisibleError {
                            thread: thread.clone(),
                            pos: pos.to_string(),
                        },
                    ),
                };
                Rep {
                    graph: &rep.graph,
                    tag: ReportTag::of(&rc, ReportGate::of(rep.gate)),
                    cause,
                    serialized: serialized(&rep.replay),
                }
            })
            .collect(),
        GridRaw::Stateful(o) => o
            .reports
            .iter()
            .map(|(g, s)| Rep {
                graph: g,
                tag: ReportTag::CompleteCoverage,
                cause: Cause::NoCover,
                serialized: serialized(s),
            })
            .collect(),
        GridRaw::CompleteFirst(o) => {
            let mut v: Vec<Rep<'_>> = o
                .cut_reports
                .iter()
                .map(|rep| {
                    let ReportKind::VisibleError { thread, pos } = &rep.kind else {
                        panic!("conformance: a cut report that is not a VisibleError")
                    };
                    Rep {
                        graph: &rep.graph,
                        tag: ReportTag::VisibleError,
                        cause: Cause::VisibleError {
                            thread: thread.clone(),
                            pos: pos.to_string(),
                        },
                        serialized: serialized(&rep.replay),
                    }
                })
                .collect();
            v.extend(o.reports.iter().map(|(g, s)| Rep {
                graph: g,
                tag: ReportTag::CompleteCoverage,
                cause: Cause::NoCover,
                serialized: serialized(s),
            }));
            v
        }
        GridRaw::Gated(o) => o
            .reports
            .iter()
            .map(|(g, s, site)| Rep {
                graph: g,
                tag: match site {
                    ReportSite::Completion => ReportTag::CompleteCoverage,
                    ReportSite::Gate(_) => ReportTag::GrowingExhaustion,
                },
                cause: Cause::NoCover,
                serialized: serialized(s),
            })
            .collect(),
        GridRaw::Verdict(_) => Vec::new(),
    }
}

/// What the contract reads of a run (`grid_tests.rs`'s `Status`).
struct St {
    reports: usize,
    exhaustions: usize,
    end: SearchEnd,
    failure: Option<String>,
}

fn st(r: &GridResult) -> St {
    match &r.raw {
        GridRaw::Enumerator(o) => St {
            reports: o.reports.len(),
            exhaustions: o.exhaustions.len(),
            end: o.end,
            failure: o
                .spec_error
                .as_ref()
                .map(|(t, e)| format!("spec_error on `{t}` at {e}")),
        },
        GridRaw::Stateful(o) => St {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (!o.spec_errors.is_empty()).then(|| format!("{:?}", o.spec_errors)),
        },
        GridRaw::CompleteFirst(o) => St {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (o.aborted || !o.spec_errors.is_empty())
                .then(|| format!("aborted={} {:?}", o.aborted, o.spec_errors)),
        },
        GridRaw::Gated(o) => St {
            reports: o.reports.len(),
            exhaustions: 0,
            end: o.impl_end,
            failure: (o.aborted || !o.spec_errors.is_empty())
                .then(|| format!("aborted={} {:?}", o.aborted, o.spec_errors)),
        },
        GridRaw::Verdict(_) => St {
            reports: 0,
            exhaustions: 0,
            end: SearchEnd::Unknown,
            failure: Some("a Verdict route in the pilot".to_owned()),
        },
    }
}

/// The pilot's configurations under one selector (criterion 4): the
/// enumerator at `Budget::Unlimited` with the memo on (the contract's row),
/// stateful, complete-first, gated `Exhaustive`/`Always`.
fn engines(s: Selector) -> [GridConfig; 4] {
    [
        GridConfig::new(GridEngine::Enumerator)
            .selector(s)
            .budget(Budget::Unlimited)
            .memo(true),
        GridConfig::new(GridEngine::Stateful).selector(s),
        GridConfig::new(GridEngine::CompleteFirst).selector(s),
        GridConfig::new(GridEngine::Gated)
            .selector(s)
            .gated(GatedMode::Exhaustive, GatePolicy::Always),
    ]
}

/// The oracle run (stateful, report-and-continue, `Ltr`, families kept).
struct Oracle {
    imp: Vec<ExecutionGraph>,
    spec: Vec<ExecutionGraph>,
    families: Families,
}

fn oracle(f: &Fixture) -> Oracle {
    // The only run that keeps graphs: stateful's two families (4 608 graphs
    // at A1 `(2,3)`), the certification oracle of P4-DIFF criterion 4.
    let r = ok(crate::conformance::eval::run_row_in_process(
        f,
        &GridConfig::new(GridEngine::Stateful),
        true,
    ));
    let GridRaw::Stateful(o) = r.raw else {
        unreachable!("conformance: the oracle run is stateful")
    };
    assert!(
        o.spec_errors.is_empty(),
        "conformance: `{}`: Spec errors {:?}",
        f.name,
        o.spec_errors
    );
    assert_eq!(
        (o.impl_end, o.spec_end),
        (
            SearchEnd::StateSpaceExhausted,
            SearchEnd::StateSpaceExhausted
        ),
        "conformance: `{}`: the oracle run is not exhaustive",
        f.name
    );
    let families = Families::new(&o.kept_spec_graphs, &o.kept_impl_graphs, 0, &f.visible);
    Oracle {
        imp: o.kept_impl_graphs,
        spec: o.kept_spec_graphs,
        families,
    }
}

// =========================================================================
// The morphism conditions, per Spec graph (M4), and vis-inclusion (M1)
// =========================================================================

fn words(g: &ExecutionGraph, vis: &[String]) -> Wobs {
    wobs(g, vis).unwrap_or_else(|e| panic!("conformance: no words for a complete graph: {e:?}"))
}

fn status_map(g: &ExecutionGraph, w: &Wobs, vis: &[String]) -> BTreeMap<String, Status> {
    statuses(CompleteExecution::assume_finished_at_gate(g), w, vis)
        .unwrap_or_else(|e| panic!("conformance: no statuses for a complete graph: {e:?}"))
}

/// A cross-thread `vo` edge over (visible thread index, position).
type Edge = ((usize, usize), (usize, usize));

/// A Spec graph with its words, statuses and cross-thread `vo` edges over
/// (visible thread index, position).
struct SpecView<'a> {
    graph: &'a ExecutionGraph,
    words: Wobs,
    statuses: BTreeMap<String, Status>,
    edges: Vec<Edge>,
}

fn vo_edges(g: &ExecutionGraph, w: &Wobs, vis: &[String]) -> Vec<Edge> {
    let evs: Vec<Vec<crate::event::Event>> = vis
        .iter()
        .map(|n| w.of(n).iter().map(|(e, _)| *e).collect())
        .collect();
    let mut out = Vec::new();
    for (ta, ea) in evs.iter().enumerate() {
        for (tb, eb) in evs.iter().enumerate() {
            if ta == tb {
                continue;
            }
            for (pa, a) in ea.iter().enumerate() {
                for (pb, b) in eb.iter().enumerate() {
                    if g.in_porf(*a, *b) {
                        out.push(((ta, pa), (tb, pb)));
                    }
                }
            }
        }
    }
    out
}

fn spec_views<'a>(spec: &'a [ExecutionGraph], vis: &[String]) -> Vec<SpecView<'a>> {
    spec.iter()
        .map(|g| {
            let w = words(g, vis);
            let s = status_map(g, &w, vis);
            let edges = vo_edges(g, &w, vis);
            SpecView {
                graph: g,
                words: w,
                statuses: s,
                edges,
            }
        })
        .collect()
}

/// The M4 mechanism of an Impl graph, `None` when some Spec graph covers it.
fn mechanism(spec: &[SpecView<'_>], g: &ExecutionGraph, vis: &[String]) -> Option<&'static str> {
    let w = words(g, vis);
    let s = status_map(g, &w, vis);
    let (mut all_v, mut all_o, mut all_s) = (true, true, true);
    for h in spec {
        let v = observations_match(&h.words, &w, vis);
        let o = order_is_reflected(h.graph, g, &h.words, &w, vis);
        let t = h.statuses == s;
        if v && o && t {
            return None;
        }
        all_v &= !v;
        all_o &= !o;
        all_s &= !t;
    }
    Some(if all_s {
        "S"
    } else if all_v && all_o {
        "V+O"
    } else if all_v {
        "V"
    } else if all_o {
        "O"
    } else {
        "V|O"
    })
}

/// Whether some linearisation of `vo(g)` (with the statuses) lies in no
/// `vis(H)` of a Spec graph `H` — a genuine vis-inclusion violation
/// (`thm:morph`, `cor:sound`). A Spec graph with other words or statuses
/// admits no linearisation of `g`; one with the same admits `σ` iff `σ`
/// respects its edges.
fn genuine(spec: &[SpecView<'_>], g: &ExecutionGraph, vis: &[String]) -> bool {
    let w = words(g, vis);
    let s = status_map(g, &w, vis);
    let cands: Vec<&SpecView<'_>> = spec
        .iter()
        .filter(|h| observations_match(&h.words, &w, vis) && h.statuses == s)
        .collect();
    if cands.is_empty() {
        return true;
    }
    let lens: Vec<usize> = vis.iter().map(|n| w.of(n).len()).collect();
    let imp_edges = vo_edges(g, &w, vis);
    let mut pos = vec![0usize; vis.len()];
    let mut at: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    let mut steps = 0usize;
    fn dfs(
        lens: &[usize],
        imp_edges: &[Edge],
        cands: &[&SpecView<'_>],
        pos: &mut Vec<usize>,
        at: &mut BTreeMap<(usize, usize), usize>,
        steps: &mut usize,
    ) -> bool {
        *steps += 1;
        assert!(
            *steps < 5_000_000,
            "conformance: the linearisation search is out of its budget"
        );
        let placed = at.len();
        if (0..lens.len()).all(|t| pos[t] == lens[t]) {
            return cands.iter().all(|h| {
                h.edges
                    .iter()
                    .any(|(a, b)| at.get(a).copied() > at.get(b).copied())
            });
        }
        for t in 0..lens.len() {
            if pos[t] == lens[t] {
                continue;
            }
            let e = (t, pos[t]);
            let ready = imp_edges
                .iter()
                .filter(|(_, b)| *b == e)
                .all(|(a, _)| at.contains_key(a));
            if !ready {
                continue;
            }
            at.insert(e, placed);
            pos[t] += 1;
            if dfs(lens, imp_edges, cands, pos, at, steps) {
                return true;
            }
            pos[t] -= 1;
            at.remove(&e);
        }
        false
    }
    dfs(&lens, &imp_edges, &cands, &mut pos, &mut at, &mut steps)
}

fn blocked(g: &ExecutionGraph, vis: &[String]) -> String {
    let w = words(g, vis);
    let s = status_map(g, &w, vis);
    vis.iter()
        .filter(|n| s.get(*n) == Some(&Status::Blocked))
        .cloned()
        .collect::<Vec<_>>()
        .join("+")
}

fn tally(m: &BTreeMap<String, usize>) -> String {
    m.iter()
        .filter(|(k, _)| !k.is_empty())
        .map(|(k, v)| format!("{k}:{v}"))
        .collect::<Vec<_>>()
        .join(" ")
}

// =========================================================================
// The pilot runner (criteria 4 and 5)
// =========================================================================

/// One fixture's checks: the oracle family against [`Exp`], then the four
/// engines × three selectors. Returns the failures and the table rows.
fn check_fixture(f: &Fixture, e: Exp, selectors: &[Selector]) -> (Vec<String>, Vec<Row>) {
    let mut fail = Vec::new();
    let name = f.name.as_str();
    let vis = &f.visible;
    if f.group != Group::Apps {
        fail.push(format!("{name}: group {:?}", f.group));
    }
    if f.config.seed != 0 || format!("{:?}", f.config.cons_type) != "FIFO" {
        fail.push(format!(
            "{name}: config seed {} cons {:?} (M6: FIFO, seed 0)",
            f.config.seed, f.config.cons_type
        ));
    }
    let t0 = Instant::now();
    let o = oracle(f);
    if (o.imp.len(), o.spec.len()) != (e.imp, e.spec) {
        fail.push(format!(
            "{name}: Impl/Spec complete graphs {}/{}, derived {}/{}",
            o.imp.len(),
            o.spec.len(),
            e.imp,
            e.spec
        ));
    }
    let want = o.families.uncovered_keys();
    if want.len() != e.unc {
        fail.push(format!(
            "{name}: {} uncovered Impl graphs, derived {}",
            want.len(),
            e.unc
        ));
    }
    let views = spec_views(&o.spec, vis);
    let mut mech: BTreeMap<String, usize> = BTreeMap::new();
    let mut blk: BTreeMap<String, usize> = BTreeMap::new();
    let mut gen = 0usize;
    let imp_keys: Vec<String> = o.imp.iter().map(|g| canon_key(g, vis)).collect();
    let mut gen_keys: BTreeSet<String> = BTreeSet::new();
    for (gi, g) in o.imp.iter().enumerate() {
        let m = mechanism(&views, g, vis);
        if m.is_none() != o.families.is_covered(g) {
            fail.push(format!(
                "{name}: the three morphism conditions say covered={} but the oracle's \
                 signature coverage says {}",
                m.is_none(),
                o.families.is_covered(g)
            ));
        }
        if let Some(m) = m {
            *mech.entry(m.to_owned()).or_default() += 1;
            *blk.entry(blocked(g, vis)).or_default() += 1;
            if genuine(&views, g, vis) {
                gen += 1;
                gen_keys.insert(imp_keys[gi].clone());
            }
        }
    }
    if tally(&mech) != e.mech {
        fail.push(format!(
            "{name}: mechanisms `{}`, derived `{}`",
            tally(&mech),
            e.mech
        ));
    }
    if tally(&blk) != e.blocked {
        fail.push(format!(
            "{name}: blocked clients `{}`, derived `{}`",
            tally(&blk),
            e.blocked
        ));
    }
    if gen != e.genuine {
        fail.push(format!(
            "{name}: {gen} uncovered graphs outside vis(Spec), derived {}",
            e.genuine
        ));
    }
    let oracle_secs = t0.elapsed().as_secs_f64();
    let mut rows = Vec::new();
    for s in selectors.iter().copied() {
        for c in engines(s) {
            let r = grun(f, &c);
            let x = st(&r);
            let label = format!("{name} {}", c.label());
            if let Some(why) = &x.failure {
                fail.push(format!("{label}: failure: {why}"));
            }
            if x.exhaustions != 0 || x.end != SearchEnd::StateSpaceExhausted {
                fail.push(format!(
                    "{label}: exhaustions {} end {:?}",
                    x.exhaustions, x.end
                ));
            }
            if (x.reports > 0) != (e.unc > 0) {
                fail.push(format!(
                    "{label}: {} reports, derived {} uncovered",
                    x.reports, e.unc
                ));
            }
            let reps = reports_of(&r);
            if c.engine != GridEngine::Enumerator {
                let keys: Vec<String> = reps.iter().map(|x| canon_key(x.graph, vis)).collect();
                let set: BTreeSet<String> = keys.iter().cloned().collect();
                if set.len() != keys.len() {
                    fail.push(format!("{label}: a key reported twice"));
                }
                if set != want {
                    fail.push(format!(
                        "{label}: report-key set of {} differs from the oracle's uncovered {}",
                        set.len(),
                        want.len()
                    ));
                }
            }
            // D6: a report is genuine iff some complete Impl graph it stands
            // for (itself, or an Impl family member extending a growing
            // report's prefix) has a word outside vis(Spec).
            let (mut d6_gen, mut d6_cand) = (0usize, 0usize);
            let mut d6_first = String::new();
            for rep in &reps {
                let is_gen = if rep.tag == ReportTag::GrowingExhaustion {
                    let cert = Certificate::absence_established(rep.graph, vis)
                        .unwrap_or_else(|e| panic!("conformance: no certificate: {e:?}"));
                    o.imp.iter().zip(&imp_keys).any(|(m, k)| {
                        gen_keys.contains(k)
                            && cert
                                .valid_at(m, vis)
                                .unwrap_or_else(|e| panic!("conformance: valid_at: {e:?}"))
                    })
                } else {
                    gen_keys.contains(&canon_key(rep.graph, vis))
                };
                if is_gen {
                    d6_gen += 1;
                } else {
                    d6_cand += 1;
                }
                if d6_first.is_empty() {
                    d6_first = if is_gen { "genuine" } else { "candidate-only" }.to_owned();
                }
            }
            if c.engine != GridEngine::Enumerator && d6_gen != e.genuine {
                fail.push(format!(
                    "{label}: {d6_gen} genuine reports (D6), derived {}",
                    e.genuine
                ));
            }
            for rep in &reps {
                if rep.cause != Cause::NoCover {
                    fail.push(format!("{label}: a report with cause {:?}", rep.cause));
                }
                if let Err(why) = certify(
                    &o.families,
                    &Claim {
                        graph: rep.graph,
                        tag: rep.tag,
                        cause: rep.cause.clone(),
                        serialized: rep.serialized,
                    },
                ) {
                    fail.push(format!("{label}: the oracle rejects a report: {why}"));
                }
            }
            let mut row: Row = vec![
                ("pilot_fixture", name.to_owned()),
                (
                    "derived_impl_spec_uncovered",
                    format!("{}/{}/{}", e.imp, e.spec, e.unc),
                ),
                ("tainted_at_start", format!("{}", r.tainted_at_start)),
                ("d6_genuine_reports", d6_gen.to_string()),
                ("d6_candidate_only_reports", d6_cand.to_string()),
                ("d6_first_report", d6_first),
            ];
            row.extend(row_of(&r));
            rows.push(row);
        }
    }
    if let Some(first) = rows.first_mut() {
        first.push(("oracle_and_derivation_secs", format!("{oracle_secs:.2}")));
    }
    (fail, rows)
}

fn names_where(pred: impl Fn(&str) -> bool) -> Vec<&'static str> {
    PILOT.iter().map(|e| e.name).filter(|n| pred(n)).collect()
}

/// One finished fixture: its index, failures, rows and wall time.
type Done = (usize, Vec<String>, Vec<Row>, f64);

/// Runs [`check_fixture`] over `names` on `workers` threads, fails with every
/// failure, and appends the rows to `P4_DIFF_TABLES` when it is set.
fn pilot(names: &[&'static str], title: &str, workers: usize) {
    assert!(!names.is_empty(), "conformance: {title}: no pilot fixture");
    let all: BTreeMap<String, Fixture> = apps_fixtures()
        .into_iter()
        .map(|f| (f.name.clone(), f))
        .collect();
    let next = AtomicUsize::new(0);
    let out: Mutex<Vec<Done>> = Mutex::new(Vec::new());
    std::thread::scope(|sc| {
        for _ in 0..workers {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= names.len() {
                    break;
                }
                let f = all
                    .get(names[i])
                    .unwrap_or_else(|| panic!("conformance: `{}` is not registered", names[i]));
                let t = Instant::now();
                let (fails, rows) = check_fixture(f, exp_of(names[i]), &SELECTORS);
                let secs = t.elapsed().as_secs_f64();
                out.lock()
                    .expect("conformance: the pilot's lock")
                    .push((i, fails, rows, secs));
            });
        }
    });
    let mut done = out.into_inner().expect("conformance: the pilot's lock");
    done.sort_by_key(|(i, ..)| *i);
    let failures: Vec<String> = done.iter().flat_map(|(_, f, ..)| f.clone()).collect();
    if std::env::var_os("P4_DIFF_TABLES").is_some() {
        let mut t = Tables::open();
        let rows: Vec<Row> = done.iter().flat_map(|(_, _, r, _)| r.clone()).collect();
        t.table(title, &rows);
        let secs: Vec<String> = done
            .iter()
            .map(|(i, _, _, s)| format!("{} {s:.1}s", names[*i]))
            .collect();
        t.note(&format!(
            "Per-fixture wall time (oracle + 12 runs): {}",
            secs.join("; ")
        ));
    }
    assert!(
        failures.is_empty(),
        "conformance: {title}: {} failures:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

/// Criterion 3's hand-count sizes (the default subset under the owner's
/// resource rule, gate 4 round 01 M2): each row's smallest bound, `(2,1)` /
/// `(2,1,2)`, and each mutant's smallest observable bound.
fn hand_count(n: &str) -> bool {
    const SIZES: [&str; 10] = [
        "/n2r1", "/k1q1", "/k2q1", "/k1q1s1", "/k2q1s1", "/k1q1s2", "/k2q1s2", "/k1q1m1",
        "/k2q1m2", "/k1q2m2",
    ];
    let mutant_value_bound = (n.starts_with("apps/a2/early-ack/")
        || n.starts_with("apps/a2/stale-get/"))
        && n.ends_with("/k1q2");
    SIZES.iter().any(|z| n.ends_with(z))
        || mutant_value_bound
        || n == "apps/a2/misroute/spec/k1q2s2"
        || (n.starts_with("apps/a4/pair-swap-") && n.ends_with("/k2q1m1"))
}

fn row_is(n: &str, rows: &[&str]) -> bool {
    rows.iter().any(|r| n.starts_with(&format!("apps/{r}/")))
}

// =========================================================================
// Criterion 2 — fixtures as code
// =========================================================================

/// **Criterion 2 / L11.** `apps_fixtures()` registers 263 fixtures (A1 45, A2
/// 90, A3 20, A4 108 — derived from "every series point × every row" before
/// the code was read), all `Group::Apps`, unique names; every pilot name
/// resolves through the runner's `fixture_by_name`; `registry()` holds none.
#[test]
fn c02_the_fixtures_resolve_by_name_and_the_registry_is_unchanged() {
    let all = apps_fixtures();
    let mut per_model: BTreeMap<String, usize> = BTreeMap::new();
    let mut names = BTreeSet::new();
    for f in &all {
        assert_eq!(f.group, Group::Apps, "conformance: `{}`'s group", f.name);
        assert!(
            names.insert(f.name.clone()),
            "conformance: `{}` registered twice",
            f.name
        );
        let model = f.name.split('/').nth(1).unwrap_or("").to_owned();
        *per_model.entry(model).or_default() += 1;
    }
    let want: BTreeMap<String, usize> = [("a1", 45), ("a2", 90), ("a3", 20), ("a4", 108)]
        .iter()
        .map(|(k, v)| ((*k).to_owned(), *v))
        .collect();
    assert_eq!(per_model, want, "conformance: L11's per-model counts");
    assert_eq!(all.len(), 263, "conformance: L11's total");
    for n in criteria_pilot_names() {
        let f = fixture_by_name(&n)
            .unwrap_or_else(|e| panic!("conformance: `{n}` does not resolve: {e:?}"));
        assert_eq!(
            f.group,
            Group::Apps,
            "conformance: `{n}` resolves to {:?}",
            f.group
        );
        assert!(
            names.contains(&n),
            "conformance: `{n}` resolves but is not in apps_fixtures"
        );
    }
    let reg = registry(2..=7, 4, 10);
    assert!(
        reg.iter()
            .all(|f| f.group != Group::Apps && !f.name.starts_with("apps/")),
        "conformance: registry() holds an application fixture"
    );
}

/// **Criterion 2.** A2's script function is the criteria's: put iff `i+j`
/// even, key `(⌊j/2⌋ + ⌊i/2⌋) mod 2`, `v = 10i+j` — the table of
/// `derived.md` written out for `(3, 3)`.
#[test]
fn c02_the_a2_script_is_the_criteria_s() {
    let p = |c, k, v| Req::Put { c, k, v };
    let g = |c, k| Req::Get { c, k };
    let want = [
        [p(0, 0, 0), g(0, 0), p(0, 1, 2)],
        [g(1, 0), p(1, 0, 11), g(1, 1)],
        [p(2, 1, 20), g(2, 1), p(2, 0, 22)],
    ];
    for (i, row) in want.iter().enumerate() {
        for (j, r) in row.iter().enumerate() {
            assert_eq!(&a2_op(i, j), r, "conformance: a2_op({i}, {j})");
        }
    }
}

fn fixture(name: &str) -> Fixture {
    apps_fixtures()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("conformance: `{name}` is not registered"))
}

/// Thread names in spawn order (`ThreadId` order), `main` dropped.
fn spawn_order(g: &ExecutionGraph) -> Vec<String> {
    g.thread_ids()
        .into_iter()
        .skip(1)
        .map(|t| g.get_thread_tclab(t).name().clone().unwrap_or_default())
        .collect()
}

fn same_order_everywhere(gs: &[ExecutionGraph], want: &[&str], what: &str) {
    for g in gs {
        let got = spawn_order(g);
        assert_eq!(got, want, "conformance: {what}: spawn order");
    }
}

/// **Criterion 2 (common encoding, M2).** Spawn orders observed on every
/// complete graph of both sides, for A1–A3: servers first, then clients, in
/// program order; one thread per role.
#[test]
fn c02_spawn_order_of_a1_to_a3() {
    let cases: [(&str, &[&str], &[&str]); 6] = [
        (
            "apps/a1/correct/spec/n3r1",
            &["coord", "p0", "p1", "p2"],
            &["coord", "p0", "p1"],
        ),
        (
            "apps/a2/pb/spec/k2q1",
            &["primary", "backup", "c0", "c1"],
            &["store", "c0", "c1"],
        ),
        (
            "apps/a2/pb-br/spec/k3q1",
            &["primary", "backup", "c0", "c1", "c2"],
            &["store", "c0", "c1", "c2"],
        ),
        (
            "apps/a2/sh/spec/k2q1s2",
            &["router", "shard0", "shard1", "c0", "c1"],
            &["store", "c0", "c1"],
        ),
        (
            "apps/a2/control-early-ack-fwd/spec/k2q1",
            &["primary", "backup", "c0", "c1"],
            &["store", "c0", "c1"],
        ),
        (
            "apps/a3/fifo/spec/k3q1",
            &["coordinator", "c0", "c1", "c2"],
            &["lock", "c0", "c1", "c2"],
        ),
    ];
    for (name, imp, spec) in cases {
        let o = oracle(&fixture(name));
        same_order_everywhere(&o.imp, imp, &format!("{name} Impl"));
        same_order_everywhere(&o.spec, spec, &format!("{name} Spec"));
    }
}

/// **T1 (fixed after gate 3).** A4's encoding fixes the spawn order
/// "balancer, servers, clients" on both sides; the lead's fix creates the
/// server channels in `main` and spawns the servers after the balancer and
/// the dispatcher. Failed on the gate-3 tree (servers first).
#[test]
fn t1_a4_spawns_the_balancer_before_its_servers() {
    let o = oracle(&fixture("apps/a4/hash/a4a/k2q1m2"));
    same_order_everywhere(&o.imp, &["balancer", "s0", "s1", "c0", "c1"], "A4 Impl");
    same_order_everywhere(&o.spec, &["dispatcher", "s0", "s1", "c0", "c1"], "A4 Spec");
}

/// The A4 spawn order at a second size (`m = 3`, `k = 3`), Impl and both
/// Specs: balancer/dispatcher, servers, clients (T1's fix).
#[test]
fn c02_a4_spawn_order_as_measured() {
    for (name, front) in [
        ("apps/a4/rr/a4b/k3q1m3", "dispatcher"),
        ("apps/a4/hash/a4a/k3q1m3", "dispatcher"),
    ] {
        let o = oracle(&fixture(name));
        same_order_everywhere(
            &o.imp,
            &["balancer", "s0", "s1", "s2", "c0", "c1", "c2"],
            &format!("{name} Impl"),
        );
        same_order_everywhere(
            &o.spec,
            &[front, "s0", "s1", "s2", "c0", "c1", "c2"],
            &format!("{name} Spec"),
        );
    }
}

/// The word of thread `n` (visible or not) in `g`, rendered.
fn word(g: &ExecutionGraph, n: &str) -> Vec<String> {
    let v = vec![n.to_owned()];
    words(g, &v)
        .of(n)
        .iter()
        .map(|(_, o)| obs_text(o))
        .collect()
}

fn words_of(gs: &[ExecutionGraph], n: &str) -> BTreeSet<Vec<String>> {
    gs.iter().map(|g| word(g, n)).collect()
}

fn owned(xs: &[&str]) -> Vec<String> {
    xs.iter().map(|s| (*s).to_owned()).collect()
}

/// **Criterion 2 (channel topology, observed).** `pb`'s primary forwards,
/// **waits for the backup's ack**, then replies; the early-ack control
/// replies before reading it. `pb-br`'s backup reads a client's get directly
/// (some graph) and acks puts; under the forwarded-gets control the get
/// reaches the backup through the primary. `main` communicates nothing in
/// A2–A4.
#[test]
fn c02_the_a2_channel_topology_is_observable() {
    let put = "Put { c: 0, k: 0, v: 0 }";
    let pb = oracle(&fixture("apps/a2/pb/spec/k1q1"));
    assert_eq!(
        words_of(&pb.imp, "primary"),
        BTreeSet::from([owned(&[
            &format!("receive {put}"),
            &format!("send Fwd({put})"),
            "receive AckPut",
            "send Ack",
        ])]),
        "conformance: pb's primary"
    );
    // n3: at every put of `pb`'s primary, at the hand-count sizes and at
    // `(1,3)` (two puts) and `(2,2)`: `send Fwd(..)` is followed at once by
    // `receive AckPut`, then `send Ack`.
    for size in ["k1q1", "k2q1", "k1q3", "k2q2"] {
        let o = oracle(&fixture(&format!("apps/a2/pb/spec/{size}")));
        for w in words_of(&o.imp, "primary") {
            let fwds: Vec<usize> = (0..w.len())
                .filter(|i| w[*i].starts_with("send Fwd("))
                .collect();
            assert!(
                !fwds.is_empty(),
                "conformance: pb {size}: no forward in {w:?}"
            );
            for i in fwds {
                assert!(
                    w.get(i + 1).map(String::as_str) == Some("receive AckPut")
                        && w.get(i + 2).map(String::as_str) == Some("send Ack"),
                    "conformance: pb {size}: the primary does not wait for the ack: {w:?}"
                );
            }
        }
    }
    let ctl = oracle(&fixture("apps/a2/control-early-ack-primary/spec/k1q1"));
    assert_eq!(
        words_of(&ctl.imp, "primary"),
        BTreeSet::from([owned(&[
            &format!("receive {put}"),
            &format!("send Fwd({put})"),
            "send Ack",
            "receive AckPut",
        ])]),
        "conformance: the early-ack control's primary"
    );
    let br = oracle(&fixture("apps/a2/pb-br/spec/k2q1"));
    assert_eq!(
        words_of(&br.imp, "backup"),
        BTreeSet::from([
            owned(&[
                "receive Get { c: 1, k: 0 }",
                "send None",
                &format!("receive {put}"),
                "send AckPut",
            ]),
            owned(&[
                &format!("receive {put}"),
                "send AckPut",
                "receive Get { c: 1, k: 0 }",
                "send Val(0)",
            ]),
        ]),
        "conformance: pb-br's backup"
    );
    assert_eq!(
        words_of(&br.imp, "primary"),
        BTreeSet::from([owned(&[
            &format!("receive {put}"),
            put_fwd(put).as_str(),
            "receive AckPut",
            "send Ack",
        ])]),
        "conformance: pb-br's primary (puts only, unwrapped forward)"
    );
    let fwd = oracle(&fixture("apps/a2/control-early-ack-fwd/spec/k2q1"));
    for w in words_of(&fwd.imp, "primary") {
        assert!(
            w.contains(&"receive Get { c: 1, k: 0 }".to_owned()),
            "conformance: the forwarded-gets control's primary does not read the get: {w:?}"
        );
    }
    for name in [
        "apps/a2/pb/spec/k2q1",
        "apps/a3/fifo/spec/k2q1",
        "apps/a4/hash/a4a/k2q1m2",
    ] {
        let o = oracle(&fixture(name));
        for g in o.imp.iter().chain(o.spec.iter()) {
            let main = *g
                .thread_ids()
                .iter()
                .next()
                .expect("conformance: a graph has main");
            let comms = (0..g.thread_size(main))
                .filter(|i| {
                    let e = crate::event::Event::new(main, *i as u32);
                    matches!(
                        g.label(e),
                        crate::event_label::LabelEnum::SendMsg(_)
                            | crate::event_label::LabelEnum::RecvMsg(_)
                    )
                })
                .count();
            assert_eq!(comms, 0, "conformance: {name}: main communicates");
        }
    }
}

fn put_fwd(put: &str) -> String {
    format!("send {put}")
}

// =========================================================================
// Criterion 3 — the derivation covers the pilot
// =========================================================================

/// **Criterion 3.** The derived table ([`PILOT`], `derived.md`'s) has one row
/// per pilot size of every row — the criteria's lists rebuilt from their text
/// — and every reporting row has a visible trace outside `vis(Spec)` (M1).
#[test]
fn c03_the_derived_table_covers_every_pilot_size() {
    let derived: BTreeSet<String> = PILOT.iter().map(|e| e.name.to_owned()).collect();
    assert_eq!(derived.len(), PILOT.len(), "conformance: a duplicated row");
    assert_eq!(
        derived,
        criteria_pilot_names(),
        "conformance: the derived table and the criteria's pilot lists differ"
    );
    for e in PILOT {
        assert_eq!(
            e.unc > 0,
            e.genuine > 0,
            "conformance: `{}`: a reporting row without a genuine violation",
            e.name
        );
        assert!(
            e.unc <= e.imp && e.genuine <= e.unc,
            "conformance: `{}`",
            e.name
        );
    }
}

// =========================================================================
// Criteria 4 and 5 — the pilot (every pilot size, four engines, three
// selectors) and the fault catalogue against the per-size table
// =========================================================================

/// **Criterion 4, A1 conforming** (`correct`, `(2,1)`, `(3,1)`, `(2,2)`).
#[test]
fn c04_pilot_a1_conforming() {
    pilot(
        &names_where(|n| hand_count(n) && row_is(n, &["a1/correct"])),
        "P5-APPS pilot — A1 correct",
        1,
    );
}

/// **Criterion 5, A1 catalogue** (eager, early-abort, silent, the reverse
/// control at `(2,1)`, `(3,1)`, `(2,2)`).
#[test]
fn c05_catalogue_a1() {
    pilot(
        &names_where(|n| {
            hand_count(n)
                && row_is(
                    n,
                    &[
                        "a1/eager",
                        "a1/early-abort",
                        "a1/silent",
                        "a1/control-reverse",
                    ],
                )
        }),
        "P5-APPS pilot — A1 catalogue",
        1,
    );
}

/// **Criteria 4 and 5 beyond the hand-count sizes: one fixture per process**
/// (gate 4 round 01 M1/M2). `APPS_FIXTURE` names a pilot fixture,
/// `APPS_SELECTORS` is `all` (default), `ltr`, `fewest` or `reverse`. The
/// checks are [`check_fixture`]'s, all of them: the stateful oracle keeps its
/// two families (`run_row_in_process(.., true)`), every engine runs on the
/// lean path, every report is certified and classified by D6. Rows to
/// `P4_DIFF_TABLES`. Run each pilot fixture outside [`hand_count`] with
///
/// ```text
/// ulimit -v 10000000; APPS_FIXTURE=apps/a1/silent/spec/n2r3 APPS_SELECTORS=ltr \
///   nice -n 10 timeout 1200 cargo test -j 2 -p traceforge --lib \
///   conformance::apps_tests::c04_c05_one_fixture -- --test-threads=2 --ignored --exact
/// ```
#[test]
#[ignore = "one fixture per process: APPS_FIXTURE, APPS_SELECTORS"]
fn c04_c05_one_fixture() {
    let name = std::env::var("APPS_FIXTURE").expect("conformance: APPS_FIXTURE is required");
    let sel = std::env::var("APPS_SELECTORS").unwrap_or_else(|_| "all".to_owned());
    let sels: Vec<Selector> = match sel.as_str() {
        "all" => SELECTORS.to_vec(),
        "ltr" => vec![Selector::Ltr],
        "fewest" => vec![Selector::FewestEvents],
        "reverse" => vec![Selector::Reverse],
        other => panic!("conformance: APPS_SELECTORS={other}"),
    };
    let f = fixture(&name);
    let t = Instant::now();
    let (fails, rows) = check_fixture(&f, exp_of(&name), &sels);
    let secs = t.elapsed().as_secs_f64();
    if std::env::var_os("P4_DIFF_TABLES").is_some() {
        let mut tb = Tables::open();
        tb.table(
            &format!(
                "P5-APPS pilot — {name} ({sel}; one process, lean engines, stateful oracle kept)"
            ),
            &rows,
        );
        tb.note(&format!(
            "Wall time (oracle, classification, {} runs; one process): {secs:.1}s",
            rows.len()
        ));
    }
    assert!(
        fails.is_empty(),
        "conformance: {name}: {} failures:\n  {}",
        fails.len(),
        fails.join("\n  ")
    );
}

/// **Criterion 4, A2 conforming** (`pb`, `pb-br`, `sh` at both `s`).
#[test]
fn c04_pilot_a2_conforming() {
    pilot(
        &names_where(|n| hand_count(n) && row_is(n, &["a2/pb", "a2/pb-br", "a2/sh"])),
        "P5-APPS pilot — A2 pb, pb-br, sh",
        1,
    );
}

/// **Criterion 5, A2 catalogue** (early-ack, stale-get, silent-put, misroute,
/// the two controls).
#[test]
fn c05_catalogue_a2() {
    pilot(
        &names_where(|n| {
            hand_count(n)
                && row_is(
                    n,
                    &[
                        "a2/early-ack",
                        "a2/stale-get",
                        "a2/silent-put",
                        "a2/misroute",
                        "a2/control-early-ack-primary",
                        "a2/control-early-ack-fwd",
                    ],
                )
        }),
        "P5-APPS pilot — A2 catalogue",
        1,
    );
}

/// **Criterion 4, A3 conforming** (FIFO).
#[test]
fn c04_pilot_a3_conforming() {
    pilot(
        &names_where(|n| hand_count(n) && row_is(n, &["a3/fifo"])),
        "P5-APPS pilot — A3 fifo",
        1,
    );
}

/// **Criterion 5, A3 catalogue** (double-grant, never-grant, wrong-round,
/// LIFO).
#[test]
fn c05_catalogue_a3() {
    pilot(
        &names_where(|n| {
            hand_count(n)
                && row_is(
                    n,
                    &[
                        "a3/double-grant",
                        "a3/never-grant",
                        "a3/wrong-round",
                        "a3/control-lifo",
                    ],
                )
        }),
        "P5-APPS pilot — A3 catalogue",
        1,
    );
}

/// **Criterion 4, A4 conforming** (`hash` × {A4a, A4b}, `rr` × A4b).
#[test]
fn c04_pilot_a4_conforming() {
    pilot(
        &names_where(|n| {
            hand_count(n) && row_is(n, &["a4/hash", "a4/rr"]) && !n.starts_with("apps/a4/rr/a4a/")
        }),
        "P5-APPS pilot — A4 hash, rr vs A4b",
        1,
    );
}

/// **Criterion 5, A4 catalogue** (`rr` × A4a, drop, pair-swap).
#[test]
fn c05_catalogue_a4() {
    pilot(
        &names_where(|n| {
            hand_count(n)
                && (n.starts_with("apps/a4/rr/a4a/")
                    || row_is(n, &["a4/drop", "a4/pair-swap-hash", "a4/pair-swap-rr"]))
        }),
        "P5-APPS pilot — A4 catalogue",
        1,
    );
}

/// **Criterion 5, "conforming (vacuous)".** LIFO at `k = 2` has exactly
/// FIFO's Impl family (at most one waiter); at `(3,1)` the families differ
/// (non-vacuous) although both conform.
#[test]
fn c05_lifo_is_vacuous_exactly_at_k_2() {
    let keys = |n: &str| -> BTreeSet<String> {
        let f = fixture(n);
        oracle(&f)
            .imp
            .iter()
            .map(|g| canon_key(g, &f.visible))
            .collect()
    };
    for size in ["k2q1", "k2q2", "k3q1"] {
        let a = keys(&format!("apps/a3/fifo/spec/{size}"));
        let b = keys(&format!("apps/a3/control-lifo/spec/{size}"));
        let vac = exp_of(&format!("apps/a3/control-lifo/spec/{size}")).vacuous;
        assert_eq!(
            a == b,
            vac,
            "conformance: LIFO at {size}: identical={}",
            a == b
        );
    }
}

/// The visible projection of a complete graph: the visible threads' words,
/// statuses and cross-thread `vo` edges — what `def:morph` compares, free of
/// the Rust type names the canonical key carries.
fn vis_key(g: &ExecutionGraph, vis: &[String]) -> String {
    let w = words(g, vis);
    let ws: Vec<Vec<String>> = vis
        .iter()
        .map(|n| w.of(n).iter().map(|(_, o)| obs_text(o)).collect())
        .collect();
    format!(
        "{ws:?} {:?} {:?}",
        status_map(g, &w, vis),
        vo_edges(g, &w, vis)
    )
}

/// **Criterion 5, the eager row against `bench.rs`.** `bench.rs`'s own
/// `two_pc(2, true)` / `two_pc_spec()` under the grid's FIFO seed-0 config:
/// 8 Impl graphs (DEMO-2PC's figure), reported with 5 uncovered — and the
/// same visible projections (words, statuses, `vo`) of the Impl family, the
/// Spec family and the uncovered set as the re-coded A1 at `(2,1)` (the
/// canonical keys differ only by the enums' Rust type names); likewise the
/// correct coordinator at `n = 2, 3`.
#[test]
fn c05_the_eager_row_reproduces_bench_rs() {
    let vis = vec!["p0".to_owned(), "p1".to_owned()];
    for (n, eager, grid_name, unc) in [
        (2, true, "apps/a1/eager/spec/n2r1", 5),
        (2, false, "apps/a1/correct/spec/n2r1", 0),
        (3, false, "apps/a1/correct/spec/n3r1", 0),
    ] {
        let b = Fixture {
            name: format!("bench/two_pc/n{n}/eager={eager}"),
            source: "bench.rs two_pc / two_pc_spec",
            group: Group::TwoPc,
            implementation: std::sync::Arc::new(bench::two_pc(n, eager)),
            specification: std::sync::Arc::new(bench::two_pc_spec()),
            visible: vis.clone(),
            config: crate::conformance::grid::cfg(crate::ConsType::FIFO),
            k: None,
            encoding: None,
            big_stack: false,
            table: None,
        };
        let ob = oracle(&b);
        let og = oracle(&fixture(grid_name));
        let proj = |gs: &[ExecutionGraph]| -> Vec<String> {
            let mut v: Vec<String> = gs.iter().map(|g| vis_key(g, &vis)).collect();
            v.sort();
            v
        };
        let unc_of = |o: &Oracle| -> Vec<String> {
            let gs: Vec<ExecutionGraph> = o
                .imp
                .iter()
                .filter(|g| !o.families.is_covered(g))
                .cloned()
                .collect();
            proj(&gs)
        };
        assert_eq!(
            proj(&ob.imp),
            proj(&og.imp),
            "conformance: {grid_name}: Impl families"
        );
        assert_eq!(
            proj(&ob.spec),
            proj(&og.spec),
            "conformance: {grid_name}: Spec families"
        );
        assert_eq!(
            unc_of(&ob),
            unc_of(&og),
            "conformance: {grid_name}: uncovered sets"
        );
        assert_eq!(unc_of(&ob).len(), unc, "conformance: {grid_name}");
        if eager {
            assert_eq!(ob.imp.len(), 8, "conformance: DEMO-2PC's 8 Impl graphs");
            let r = grun(&b, &GridConfig::new(GridEngine::Stateful));
            assert_eq!(
                st(&r).reports,
                5,
                "conformance: bench.rs's eager pair reports"
            );
        }
    }
}

/// The uncovered graphs of `name`'s oracle run.
fn uncovered(name: &str) -> (Fixture, Vec<ExecutionGraph>) {
    let f = fixture(name);
    let o = oracle(&f);
    let un = o
        .imp
        .iter()
        .filter(|g| !o.families.is_covered(g))
        .cloned()
        .collect();
    (f, un)
}

/// **Criterion 5, the hand-count words** (`derived.md` D-A1..D-A4): the
/// uncovered graph(s) at each row's smallest observable bound carry the
/// derived word and status.
#[test]
fn c05_the_hand_count_words() {
    let put = "send Put { c: 0, k: 0, v: 0 }";
    // A2 early-ack (2,1) and stale-get (2,1): `c0: Put Ack`, `c1: Get None`.
    for name in ["apps/a2/early-ack/spec/k2q1", "apps/a2/stale-get/spec/k2q1"] {
        let (_, un) = uncovered(name);
        assert_eq!(un.len(), 1, "conformance: {name}");
        assert_eq!(
            word(&un[0], "c0"),
            owned(&[put, "receive Ack"]),
            "conformance: {name}"
        );
        assert_eq!(
            word(&un[0], "c1"),
            owned(&["send Get { c: 1, k: 0 }", "receive None"]),
            "conformance: {name}"
        );
    }
    // A2 early-ack (1,2), stale-get (1,2), misroute (1,2,2): same-client `None`.
    for name in [
        "apps/a2/early-ack/spec/k1q2",
        "apps/a2/stale-get/spec/k1q2",
        "apps/a2/misroute/spec/k1q2s2",
    ] {
        let (_, un) = uncovered(name);
        assert_eq!(un.len(), 1, "conformance: {name}");
        assert_eq!(
            word(&un[0], "c0"),
            owned(&[
                put,
                "receive Ack",
                "send Get { c: 0, k: 0 }",
                "receive None"
            ]),
            "conformance: {name}"
        );
    }
    // A2 silent-put (1,1): `c0` sent its put and is blocked.
    let (f, un) = uncovered("apps/a2/silent-put/spec/k1q1");
    assert_eq!(word(&un[0], "c0"), owned(&[put]), "conformance: silent-put");
    assert_eq!(blocked(&un[0], &f.visible), "c0", "conformance: silent-put");
    // A3 double-grant (2,1): the 4 uncovered graphs read both `Acq`s first.
    let (_, un) = uncovered("apps/a3/double-grant/spec/k2q1");
    assert_eq!(un.len(), 4, "conformance: double-grant");
    for g in &un {
        let w = word(g, "coordinator");
        assert!(
            w.len() >= 2
                && w[0].starts_with("receive Acq")
                && w.iter()
                    .filter(|o| o.starts_with("receive"))
                    .nth(1)
                    .is_some_and(|o| o.starts_with("receive Acq")),
            "conformance: double-grant: {w:?}"
        );
    }
    // A3 never-grant (2,1): `c1` acquired and blocks; A3 wrong-round: `Grant(1, 1)`.
    let (f, un) = uncovered("apps/a3/never-grant/spec/k2q1");
    assert_eq!(un.len(), 1, "conformance: never-grant");
    assert_eq!(
        word(&un[0], "c1"),
        owned(&["send Acq(1)"]),
        "conformance: never-grant"
    );
    assert_eq!(
        blocked(&un[0], &f.visible),
        "c1",
        "conformance: never-grant"
    );
    let (_, un) = uncovered("apps/a3/wrong-round/spec/k2q1");
    for g in &un {
        assert_eq!(
            word(g, "c1"),
            owned(&["send Acq(1)", "receive Grant(1, 1)", "send Rel(1)"]),
            "conformance: wrong-round"
        );
    }
    // A4 rr vs A4a (1,2,2): the D3 word.
    let (_, un) = uncovered("apps/a4/rr/a4a/k1q2m2");
    assert_eq!(un.len(), 1, "conformance: rr vs A4a");
    assert_eq!(
        word(&un[0], "c0"),
        owned(&[
            "send A4Req(0, 0)",
            "receive A4Reply(0, 0)",
            "send A4Req(0, 1)",
            "receive A4Reply(1, 1)",
        ]),
        "conformance: rr vs A4a"
    );
    // A4 drop (1,1,1): `c0` sent and blocks.
    let (f, un) = uncovered("apps/a4/drop/a4b/k1q1m1");
    assert_eq!(
        word(&un[0], "c0"),
        owned(&["send A4Req(0, 0)"]),
        "conformance: drop"
    );
    assert_eq!(blocked(&un[0], &f.visible), "c0", "conformance: drop");
    // A1 eager (2,1): `derived.md`'s word is a linearisation of an uncovered
    // graph — `p0` and `p1` both `No`, `p0`'s vote read first, both `Abort`.
    let (_, un) = uncovered("apps/a1/eager/spec/n2r1");
    let target = (
        vec!["No".to_owned(), "Abort".to_owned()],
        vec!["No".to_owned(), "Abort".to_owned()],
    );
    let found = un.iter().any(|g| {
        let tail = |n: &str| -> Vec<String> {
            word(g, n)
                .iter()
                .skip(1)
                .map(|o| o.rsplit(' ').next().unwrap_or("").to_owned())
                .collect()
        };
        (tail("p0"), tail("p1")) == target
            && word(g, "coord")
                .iter()
                .filter(|o| o.starts_with("receive"))
                .count()
                == 3
    });
    assert!(
        found,
        "conformance: eager (2,1): no uncovered (No, No) graph"
    );
}

// =========================================================================
// Criterion 8 — labelling
// =========================================================================

/// **Criterion 8.** Neither the lead's `P5-APPS` block of `grid.rs` nor this
/// file calls a model by the forbidden label (the other artefacts are
/// checked by `grep` in the report).
#[test]
fn c08_no_model_carries_the_forbidden_label() {
    let needle = concat!("real", "-world");
    let grid = include_str!("grid.rs");
    let at = grid
        .find("// P5-APPS — application-derived bounded models")
        .expect("conformance: the P5-APPS block of grid.rs");
    assert!(
        !grid[at..].to_lowercase().contains(needle),
        "conformance: grid.rs's P5-APPS block uses the label"
    );
    assert!(
        !include_str!("apps_tests.rs")
            .to_lowercase()
            .contains(needle),
        "conformance: apps_tests.rs uses the label"
    );
}

// =========================================================================
// Criterion 6 — the scaling pilot, through `P5-HARNESS`'s runner
// =========================================================================

/// The catalogue series in the scaling pilot (gate 4 round 01 m3): the
/// costliest mutant of each model.
const CATALOGUE: [&str; 6] = [
    "a1/eager",
    "a1/silent",
    "a2/early-ack",
    "a2/misroute",
    "a3/double-grant",
    "a4/rr/a4a",
];

/// The scaling pilot's rows: every conforming series and the [`CATALOGUE`]
/// series, the four engines (the pilot's configurations, `Ltr`), one knob
/// stepped at a time from the smallest series point with the others at their
/// smallest values; one series scope per (series, engine, knob), built by
/// `eval::Series::of`, so the runner stops a scope at its first censored
/// size (H5 rule (2)).
fn scaling_rows() -> Vec<crate::conformance::eval::RowSpec> {
    use crate::conformance::eval::{RowSpec, RunKind, Series, Tier};
    // (series id, name for knob values, knob names, smallest, ceilings)
    type Namer = fn(&[i64]) -> String;
    type ScalingSeries = (
        &'static str,
        Namer,
        &'static [&'static str],
        Vec<i64>,
        Vec<i64>,
    );
    let series: Vec<ScalingSeries> = vec![
        (
            "a1/correct",
            |k| format!("apps/a1/correct/spec/n{}r{}", k[0], k[1]),
            &["n", "r"],
            vec![2, 1],
            vec![4, 3],
        ),
        (
            "a2/pb",
            |k| format!("apps/a2/pb/spec/k{}q{}", k[0], k[1]),
            &["k", "q"],
            vec![1, 1],
            vec![3, 3],
        ),
        (
            "a2/pb-br",
            |k| format!("apps/a2/pb-br/spec/k{}q{}", k[0], k[1]),
            &["k", "q"],
            vec![1, 1],
            vec![3, 3],
        ),
        (
            "a2/sh",
            |k| format!("apps/a2/sh/spec/k{}q{}s{}", k[0], k[1], k[2]),
            &["k", "q", "s"],
            vec![1, 1, 1],
            vec![3, 3, 2],
        ),
        (
            "a3/fifo",
            |k| format!("apps/a3/fifo/spec/k{}q{}", k[0], k[1]),
            &["k", "q"],
            vec![2, 1],
            vec![3, 2],
        ),
        (
            "a4/hash/a4a",
            |k| format!("apps/a4/hash/a4a/k{}q{}m{}", k[0], k[1], k[2]),
            &["k", "q", "m"],
            vec![1, 1, 1],
            vec![3, 2, 3],
        ),
        (
            "a4/hash/a4b",
            |k| format!("apps/a4/hash/a4b/k{}q{}m{}", k[0], k[1], k[2]),
            &["k", "q", "m"],
            vec![1, 1, 1],
            vec![3, 2, 3],
        ),
        (
            "a4/rr/a4b",
            |k| format!("apps/a4/rr/a4b/k{}q{}m{}", k[0], k[1], k[2]),
            &["k", "q", "m"],
            vec![1, 1, 1],
            vec![3, 2, 3],
        ),
        (
            "a1/eager",
            |k| format!("apps/a1/eager/spec/n{}r{}", k[0], k[1]),
            &["n", "r"],
            vec![2, 1],
            vec![4, 3],
        ),
        (
            "a1/silent",
            |k| format!("apps/a1/silent/spec/n{}r{}", k[0], k[1]),
            &["n", "r"],
            vec![2, 1],
            vec![4, 3],
        ),
        (
            "a2/early-ack",
            |k| format!("apps/a2/early-ack/spec/k{}q{}", k[0], k[1]),
            &["k", "q"],
            vec![1, 1],
            vec![3, 3],
        ),
        (
            "a2/misroute",
            |k| format!("apps/a2/misroute/spec/k{}q{}s2", k[0], k[1]),
            &["k", "q"],
            vec![1, 1],
            vec![3, 3],
        ),
        (
            "a3/double-grant",
            |k| format!("apps/a3/double-grant/spec/k{}q{}", k[0], k[1]),
            &["k", "q"],
            vec![2, 1],
            vec![3, 2],
        ),
        (
            "a4/rr/a4a",
            |k| format!("apps/a4/rr/a4a/k{}q{}m{}", k[0], k[1], k[2]),
            &["k", "q", "m"],
            vec![1, 1, 1],
            vec![3, 2, 3],
        ),
    ];
    let mut out = Vec::new();
    for (id, namer, knobs, base, ceil) in series {
        let variant = if CATALOGUE.contains(&id) {
            format!("mutant:{id}")
        } else {
            "conforming".to_owned()
        };
        for (ki, kname) in knobs.iter().enumerate() {
            for v in base[ki]..=ceil[ki] {
                let mut k = base.clone();
                k[ki] = v;
                for c in engines(Selector::Ltr) {
                    let mut kk = [None; 4];
                    for (i, x) in k.iter().enumerate() {
                        kk[i] = Some(*x);
                    }
                    let tier = Tier::default_tier();
                    let without: String = knobs
                        .iter()
                        .zip(&k)
                        .map(|(n, x)| {
                            if n == kname {
                                format!("{n}=*")
                            } else {
                                format!("{n}={x}")
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(",");
                    let family = format!("apps/{id}");
                    out.push(RowSpec {
                        fixture: namer(&k),
                        config: c.clone(),
                        rep: 0,
                        series: Some(Series::of(&family, &without, &c, &tier, RunKind::Timed, v)),
                        tier,
                        run_kind: RunKind::Timed,
                        family,
                        knobs: knobs
                            .iter()
                            .zip(&k)
                            .map(|(n, x)| format!("{n}={x}"))
                            .collect::<Vec<_>>()
                            .join(","),
                        k: kk,
                        variant: variant.clone(),
                        twin_key: String::new(),
                    });
                }
            }
        }
    }
    out
}

/// **Criterion 6.** The scaling pilot through the runner: one OS process per
/// row, the default tier (600 s, 4 GiB), release profile, `EVAL_OUT` the
/// store's directory, `EVAL_ALLOW_MIXED=1` on a dirty tree:
///
/// ```text
/// ulimit -v 10000000 && EVAL_OUT=<dir> EVAL_ALLOW_MIXED=1 nice -n 10 \
///     cargo test --release -j 2 -p traceforge --lib \
///     conformance::apps_tests::c06_scaling_pilot_through_the_runner -- --test-threads=2 --ignored --exact
/// ```
#[test]
#[ignore = "criterion 6: release profile, through the runner, EVAL_OUT required"]
fn c06_scaling_pilot_through_the_runner() {
    use crate::conformance::eval::{builtin_specs, Driver, Probes, Spec};
    let out_dir = std::env::var_os("EVAL_OUT").expect("conformance: EVAL_OUT is required");
    let rows = scaling_rows();
    let n = rows.len();
    let spec = Spec {
        name: "P5-APPS-scaling".to_owned(),
        rows,
    };
    let mut specs = builtin_specs();
    specs.push(spec.clone());
    let driver = Driver {
        spec,
        specs,
        out_dir: out_dir.into(),
        sample_period: std::time::Duration::from_millis(100),
        probes: Probes::real(),
        allow_mixed: std::env::var("EVAL_ALLOW_MIXED").is_ok_and(|v| v == "1"),
        only: std::env::var("EVAL_ONLY").ok(),
    };
    let s = driver
        .run()
        .unwrap_or_else(|e| panic!("conformance: the runner refused: {}", e.text()));
    assert_eq!(
        s.ran + s.skipped_present + s.skipped_rep + s.skipped_after_censor,
        n,
        "conformance: every scaling row is accounted for"
    );
}
