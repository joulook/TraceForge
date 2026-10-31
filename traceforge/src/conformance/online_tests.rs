//! C's tests (`criteria/ONLINE.md` rev 1.3, ONLINE-2; the derivation
//! `log/dev/ONLINE.derived-2.md` §4–§6): O1–O8 on inline programs, in the
//! default build (Rule 1). The expected values were derived by hand before any
//! run (the derivation's §4.3 table and §5); where a value depends on Must's
//! order of completions (a first miss's iteration, a failure's position), it is
//! taken from an independent reference: the offline stateful engine
//! (`stateful::run_with` under `index(Set)`, same configuration) and the typed
//! summaries of its kept graphs, never from C's code or the line renderer.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::conformance::compact::{CompactSummary, OrdCounts};
use crate::conformance::config::{ConfBuilder, ConfConfig, Engine, IndexKind};
use crate::conformance::interchange::{
    conf_join, encode_generic, normal_line, ExportHeader, ThreadNames, Verdict as JoinVerdict,
};
use crate::conformance::interchange_default_tests::{named, read_jsonl, scratch, split_block};
use crate::conformance::morphism::Status;
use crate::conformance::obs::Obs;
use crate::conformance::online::{self, End, Mode, OnlineOpts, OnlineOut, OnlineReport};
use crate::conformance::stateful::{self, StatefulOutcome};
use crate::exec_graph::ExecutionGraph;
use crate::msg::Val;
use crate::program::{run_cli, Entry, Program};
use crate::{Config, ConsType};

/// Writes a line to stderr (the `s5_tests` emission scan forbids the print
/// macros under `conformance/`).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

// =========================================================================
// P_o (derivation §4.1)
// =========================================================================

#[derive(Clone, Debug, PartialEq)]
pub(super) enum M {
    Tag(i32),
    Tok,
    Ch(char),
}

/// The visible threads, sorted.
pub(super) const VIS: [&str; 4] = ["alpha", "beta", "reader", "writer"];

pub(super) fn vis() -> Vec<String> {
    VIS.iter().map(|s| (*s).to_owned()).collect()
}

/// The specification and the implementation's variants (§4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Var {
    Spec,
    Fixed,
    Bug,
    Ch2,
    Ch3,
    AssertR,
    /// As `AssertR` on Tag(2) (added after the first run: under seed 0 the
    /// first graph carries Tag(3), so `AssertR` fails at iteration 1).
    AssertR2,
    AssertS,
}

pub(super) fn var_of(args: &[String]) -> Var {
    match args.first().map(String::as_str) {
        Some("bug") => Var::Bug,
        Some("ch2") => Var::Ch2,
        Some("ch3") => Var::Ch3,
        Some("assert-r") => Var::AssertR,
        Some("assert-r2") => Var::AssertR2,
        Some("assert-s") => Var::AssertS,
        _ => Var::Fixed,
    }
}

/// P_o: `writer` sends Tag(1) and Tag(2|3) to `reader` on channel K; `alpha`
/// sends Tok to the invisible `relay`, which forwards it to `beta`. The
/// specification's K is FIFO by construction and its relay always forwards;
/// the implementation's K takes the run's model, its relay has three branches
/// (c3 forwards early under `bug`), and main draws one unused `nondet()`.
pub(super) fn body(var: Var) {
    let spec = var == Var::Spec;
    let (tx, rx) = if spec {
        crate::channel::Builder::<M>::new()
            .with_comm(crate::loc::CommunicationModel::LocalOrder)
            .build()
    } else {
        crate::channel::Builder::<M>::new().build()
    };
    let reader = named("reader", move || {
        let _x1: M = rx.recv_msg_block();
        let x2: M = rx.recv_msg_block();
        if var == Var::AssertR {
            crate::assert(x2 != M::Tag(3));
        }
        if var == Var::AssertR2 {
            crate::assert(x2 != M::Tag(2));
        }
    });
    let writer = named("writer", move || {
        tx.send_msg(M::Tag(1));
        let v = if crate::nondet() { 2 } else { 3 };
        let m = match (var, v) {
            (Var::Ch2, 2) | (Var::Ch3, 3) => M::Ch('x'),
            _ => M::Tag(v),
        };
        tx.send_msg(m);
    });
    let beta = named("beta", || {
        let _: M = crate::recv_msg_block();
    });
    let bid = beta.thread().id();
    let relay = named("relay", move || {
        let forward = move || {
            let t: M = crate::recv_msg_block();
            crate::send_msg(bid, t);
        };
        if spec || crate::nondet() {
            forward();
        } else if crate::nondet() {
            if var == Var::AssertS {
                crate::send_msg(bid, M::Tag(0));
                crate::assert(false);
            } else {
                forward();
            }
        } else if var == Var::Bug {
            crate::send_msg(bid, M::Tok);
            let _: M = crate::recv_msg_block();
        } else {
            forward();
        }
    });
    let rid = relay.thread().id();
    let alpha = named("alpha", move || crate::send_msg(rid, M::Tok));
    if !spec {
        let _ = crate::nondet();
    }
    for h in [reader, writer, beta, relay, alpha] {
        h.join().unwrap();
    }
}

pub(super) type VisFn = Box<dyn Fn(&[String]) -> Vec<String>>;
pub(super) type EntryFn = Box<dyn Fn(&[String]) -> Entry>;

/// A program's three functions, owned, for `Program`.
pub(super) struct Prog {
    pub(super) vis: VisFn,
    pub(super) spec: EntryFn,
    pub(super) imp: EntryFn,
}

impl Prog {
    pub(super) fn program(&self) -> Program<'_> {
        Program {
            visible: &*self.vis,
            spec: &*self.spec,
            imp: &*self.imp,
        }
    }
    pub(super) fn cli(&self, args: &[&str]) -> (String, u8) {
        let a: Vec<String> = args.iter().map(|s| (*s).to_owned()).collect();
        // `B` (MEAS-0): `run_cli`'s text ends with the measurement block; C's
        // tests compare the subcommand's own text, before the block.
        let (text, code) = run_cli(&self.program(), &a);
        (split_block(&text).0, code)
    }
}

pub(super) fn o_prog() -> Prog {
    Prog {
        vis: Box::new(|_| vis()),
        spec: Box::new(|_| Arc::new(|| body(Var::Spec))),
        imp: Box::new(|a| {
            let v = var_of(a);
            Arc::new(move || body(v))
        }),
    }
}

pub(super) fn imp_of(var: Var) -> Arc<dyn Fn() + Send + Sync> {
    Arc::new(move || body(var))
}

pub(super) fn model_arg(m: ConsType) -> &'static str {
    match m {
        ConsType::Bag => "bag",
        _ => "fifo",
    }
}

pub(super) fn variant_arg(var: Var) -> &'static str {
    match var {
        Var::Spec | Var::Fixed => "fixed",
        Var::Bug => "bug",
        Var::Ch2 => "ch2",
        Var::Ch3 => "ch3",
        Var::AssertR => "assert-r",
        Var::AssertR2 => "assert-r2",
        Var::AssertS => "assert-s",
    }
}

/// `config_of`'s configuration with `--model m --seed 0`.
pub(super) fn cfg(m: ConsType) -> Config {
    Config::builder()
        .with_cons_type(m)
        .with_verbose(0)
        .with_seed(0)
        .build()
}

// =========================================================================
// The independent references (derivation §4.4)
// =========================================================================

pub(super) fn ref_cc(m: ConsType, stop: bool) -> ConfConfig {
    ConfBuilder::new()
        .config(cfg(m))
        .cons_type(m)
        .visible_threads(vis())
        .engine(Engine::Stateful)
        .index(IndexKind::Set)
        .stop_at_first_report(stop)
        .build()
        .expect("conformance: C: a reference configuration")
}

/// The offline stateful run on the same pair, keeping every implementation
/// graph (`stop` off) or stopping at the first report (`stop` on).
pub(super) fn reference(var: Var, m: ConsType, stop: bool) -> StatefulOutcome {
    let spec: Arc<dyn Fn() + Send + Sync> = Arc::new(|| body(Var::Spec));
    stateful::run_with(&ref_cc(m, stop), &imp_of(var), &spec, !stop)
}

/// A graph's features, read from its typed summary (§4.4's κ).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Kappa {
    /// The `Debug` of `writer`'s second value: `Tag(2)`, `Tag(3)`, `Ch('x')`.
    pub(super) second: String,
    pub(super) swapped: bool,
    pub(super) early: bool,
    pub(super) err: bool,
    /// `beta` received `Tag(0)` (assert-s's c2).
    pub(super) c2: bool,
}

pub(super) fn dbg_of(o: &Obs) -> String {
    match o {
        Obs::Send(v) | Obs::Recv(Some(v)) => format!("{:?}", &*v.val),
        Obs::Recv(None) => "⊥".to_owned(),
    }
}

pub(super) fn kappa(g: &ExecutionGraph) -> Kappa {
    let cs = CompactSummary::at_completion(g, &vis(), "implementation");
    let w = cs.sig.word("writer");
    let r = cs.sig.word("reader");
    let b = cs.sig.word("beta");
    let beta_from_alpha = match &cs.ord {
        OrdCounts::U8(c) => u16::from(c[3]),
        OrdCounts::U16(c) => c[3],
    };
    Kappa {
        second: dbg_of(&w[1]),
        swapped: dbg_of(&r[0]) != "Tag(1)",
        early: beta_from_alpha == 0,
        err: cs.sig.status("reader") == Some(Status::Errored),
        c2: dbg_of(&b[0]) == "Tag(0)",
    }
}

pub(super) fn v_of(k: &Kappa) -> i32 {
    match k.second.as_str() {
        "Tag(2)" => 2,
        "Tag(3)" => 3,
        other => panic!("conformance: C: no hand line for the value {other}"),
    }
}

/// The hand line L(V, π, β, ρ) (derivation §4.2).
pub(super) fn hand_line(v: i32, swapped: bool, early: bool, err: bool) -> String {
    let tag = |x: i32| format!(r#"{{"t":"Tag","f":[{x}]}}"#);
    let (r1, r2) = if swapped { (v, 1) } else { (1, v) };
    format!(
        concat!(
            r#"{{"statuses":{{"alpha":"done","beta":"done","reader":"{}","writer":"done"}},"#,
            r#""words":{{"alpha":[{{"s":{{"t":"Tok","f":[]}}}}],"beta":[{{"r":{{"t":"Tok","f":[]}}}}],"#,
            r#""reader":[{{"r":{}}},{{"r":{}}}],"writer":[{{"s":{}}},{{"s":{}}}]}},"#,
            r#""counts":[0,0,0,{},0,0,0,0,{},0,0,2,0,0,0,0,0,0]}}"#
        ),
        if err { "err" } else { "done" },
        tag(r1),
        tag(r2),
        tag(1),
        tag(v),
        if early { 0 } else { 1 },
        if swapped { 2 } else { 1 },
    )
}

pub(super) fn line_k(k: &Kappa) -> String {
    hand_line(v_of(k), k.swapped, k.early, k.err)
}

/// A graph's class against the specification lines `held` (values of V whose
/// line L(V,ok,c,done) is in the file): 'F' found, 'S' signature miss, 'X'
/// not found.
pub(super) fn class_of(k: &Kappa, held: &[i32]) -> char {
    let v = v_of(k);
    if k.swapped || k.err || !held.contains(&v) {
        'S'
    } else if k.early {
        'X'
    } else {
        'F'
    }
}

/// F, S, X, U, D and the distinct lines over the first `n` kept graphs.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct Counts {
    pub(super) f: usize,
    pub(super) s: usize,
    pub(super) x: usize,
    pub(super) u: usize,
    pub(super) d: usize,
    pub(super) lines: BTreeSet<String>,
}

pub(super) fn counts_over(ks: &[Kappa], held: &[i32]) -> Counts {
    let mut c = Counts {
        f: 0,
        s: 0,
        x: 0,
        u: 0,
        d: 0,
        lines: BTreeSet::new(),
    };
    let mut unc = HashSet::new();
    for k in ks {
        let l = line_k(k);
        match class_of(k, held) {
            'F' => c.f += 1,
            'S' => {
                c.s += 1;
                unc.insert(l.clone());
            }
            _ => {
                c.x += 1;
                unc.insert(l.clone());
            }
        }
        c.lines.insert(l);
    }
    c.u = c.s + c.x;
    c.d = unc.len();
    c
}

pub(super) fn kept_kappas(var: Var, m: ConsType) -> Vec<Kappa> {
    reference(var, m, false)
        .kept_impl_graphs
        .iter()
        .map(kappa)
        .collect()
}

/// The first miss by the offline engine: its iteration and its graph's κ.
pub(super) fn first_report(var: Var, m: ConsType) -> (usize, Kappa) {
    let o = reference(var, m, true);
    assert_eq!(o.counters.reports, 1, "conformance: C: the reference stops at one report");
    (o.counters.impl_graphs, kappa(&o.reports[0].0))
}

// =========================================================================
// Running C and reading its text
// =========================================================================

const LABELS: [&str; 9] = [
    "spec:       ",
    "lookups:    ",
    "verdict:    ",
    "mode:       ",
    "first miss: ",
    "uncovered:  ",
    "witness:    ",
    "at:         ",
    "FAILED:     ",
];

/// The specification file S (derivation §5): `export spec` through the shared
/// main.
pub(super) fn spec_file(p: &Prog, dir: &Path) -> PathBuf {
    let s = dir.join("S.jsonl");
    let ss = s.to_string_lossy().into_owned();
    assert_eq!(
        p.cli(&[
            "export", "spec", "--out", &ss, "--program", "o", "--size", "k1", "--model", "fifo",
            "--seed", "0", "--", "fixed",
        ]),
        (format!("exported: 2 lines from 2 graphs to {ss}\n"), 0),
        "conformance: C: the specification file"
    );
    s
}

pub(super) fn spec_head(path: &Path, lines: usize) -> String {
    format!(
        "spec:       {} (program o, size k1, model p2p, tool traceforge; {lines} lines, {lines} \
         distinct summaries held, 0 duplicates)\n",
        path.display()
    )
}

/// `online` through `run_cli` with `--seed 0`; `extra` before `--model`.
pub(super) fn run_online(p: &Prog, s: &Path, extra: &[&str], m: ConsType, var: Var) -> (String, u8) {
    let ss = s.to_string_lossy().into_owned();
    let mut a: Vec<&str> = vec!["online", "--spec", ss.as_str()];
    a.extend_from_slice(extra);
    a.extend_from_slice(&["--model", model_arg(m), "--seed", "0", "--", variant_arg(var)]);
    p.cli(&a)
}

/// `(I, T)` from a `first miss:` line.
pub(super) fn first_miss_of(text: &str) -> Option<(usize, u64)> {
    let l = text.lines().find(|l| l.starts_with("first miss: "))?;
    let rest = l.strip_prefix("first miss: iteration ")?;
    let (i, t) = rest.split_once(", ")?;
    let t = t.strip_suffix(" ms")?;
    Some((i.parse().ok()?, t.parse().ok()?))
}

pub(super) fn witness_of(text: &str) -> Option<String> {
    text.lines()
        .find_map(|l| l.strip_prefix("witness:    "))
        .map(str::to_owned)
}

/// The expected text (ONLINE-1), every line.
#[allow(clippy::too_many_arguments)]
fn expected_text(
    head: &str,
    n: (usize, usize, usize, usize),
    verdict: &str,
    bug_finder: bool,
    first: Option<(usize, u64, &str, bool)>,
    u: (usize, usize),
    failed: Option<&str>,
) -> String {
    let mut t = head.to_owned();
    t.push_str(&format!(
        "lookups:    {} ({} found, {} signature misses, {} not found)\n",
        n.0, n.1, n.2, n.3
    ));
    t.push_str(&format!("verdict:    {verdict}\n"));
    t.push_str(if bug_finder {
        "mode:       bug-finder (--stop-at-first)\n"
    } else {
        "mode:       full\n"
    });
    if let Some((i, ms, _, _)) = first {
        t.push_str(&format!("first miss: iteration {i}, {ms} ms\n"));
    }
    t.push_str(&format!(
        "uncovered:  {} graphs ({} distinct summaries)\n",
        u.0, u.1
    ));
    if let Some((i, _, w, not_found)) = first {
        t.push_str(&format!("witness:    {w}\n"));
        t.push_str(&format!(
            "at:         iteration {i}, {}\n",
            if not_found {
                "NotFound (the signature is held, no order is <= the query's)"
            } else {
                "NoSig (no specification summary has this signature)"
            }
        ));
    }
    if let Some(f) = failed {
        t.push_str(&format!("FAILED:     {f}\n"));
    }
    t
}

/// No line of `text` starts with an ONLINE-1 label (exit 2's "no result block").
fn no_result_block(text: &str) -> bool {
    text.lines()
        .all(|l| !LABELS.iter().any(|lab| l.starts_with(lab.trim_end())))
}

fn opts(mode: Mode, budget: Option<u64>, out: Option<OnlineOut>) -> OnlineOpts {
    OnlineOpts::new(mode, budget, out)
}

/// The counter invariants of ONLINE-0 on a report.
fn invariants(r: &OnlineReport) {
    assert_eq!(
        r.lookups,
        r.found + r.signature_misses + r.not_found,
        "conformance: C: lookups = F + S + X"
    );
    assert_eq!(
        r.uncovered_total,
        r.signature_misses + r.not_found,
        "conformance: C: U = S + X"
    );
    assert!(r.uncovered_distinct <= r.uncovered_total, "conformance: C: D <= U");
    assert!(
        r.lookups <= r.iterations && r.iterations <= r.lookups + 1,
        "conformance: C: lookups <= iterations <= lookups + 1"
    );
    if let Some(f) = &r.first {
        assert!(f.iteration <= r.iterations, "conformance: C: I <= iterations");
    }
}

/// A file's header text and its sorted body.
fn read_out(path: &Path) -> (String, Vec<String>) {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("conformance: C: {}: {e}", path.display()));
    let mut it = text.lines();
    let head = it.next().expect("conformance: C: a header").to_owned();
    let mut body: Vec<String> = it.map(str::to_owned).collect();
    body.sort();
    (head, body)
}

fn out_head(program: &str, size: &str, model: &str, enumeration: &str, f: (usize, u64, usize)) -> String {
    format!(
        concat!(
            r#"{{"format":1,"tool":"traceforge","program":"{}","size":"{}","#,
            r#""visible":["alpha","beta","reader","writer"],"model":"{}","enumeration":"{}","#,
            r#""first_miss_iteration":{},"first_miss_wall_ms":{},"uncovered_total":{},"encoding":1}}"#
        ),
        program, size, model, enumeration, f.0, f.1, f.2
    )
}

fn tmp_of(path: &Path) -> PathBuf {
    let mut t = path.as_os_str().to_owned();
    t.push(".tmp");
    PathBuf::from(t)
}

// =========================================================================
// O1, O2, O3
// =========================================================================

/// **O1** (violating; derivation §4.3, §5). bug/bag: `lookups: 24 (8 found, 12
/// signature misses, 4 not found)`, `uncovered: 16 graphs (6 distinct
/// summaries)`, `reports`, exit 0; the first miss's iteration and witness are
/// the offline engine's first report; U = the offline count, N = `count impl`,
/// D = `conf_join` on the two exports. bug/fifo (all misses NotFound) and
/// fixed/bag (all misses NoSig) as O1b, O1c. Failing directions: F1–F6.
#[test]
fn o1_violating_full_mode() {
    let p = o_prog();
    let dir = scratch("c-o1");
    let s = spec_file(&p, &dir);
    let head = spec_head(&s, 2);
    // (variant, model, N, F, S, X, U, D, export lines)
    for (var, m, n, f, sm, x, u, d, lines) in [
        (Var::Bug, ConsType::Bag, 24, 8, 12, 4, 16, 6, 8),
        (Var::Bug, ConsType::FIFO, 12, 8, 0, 4, 4, 2, 4),
        (Var::Fixed, ConsType::Bag, 24, 12, 12, 0, 12, 2, 4),
    ] {
        let tag = format!("{}/{}", variant_arg(var), model_arg(m));
        // The references, each against the hand values.
        let r = reference(var, m, false);
        let c = &r.counters;
        assert_eq!(
            (c.impl_graphs, c.lookups_succeeded, c.lookups_signature_miss, c.lookups_failed_after_tests, c.reports),
            (n, f, sm, x, u),
            "conformance: C: O1 {tag}: the offline engine against the hand table"
        );
        assert_eq!(
            (c.spec_graphs, c.orders_held, c.signatures),
            (2, 2, 2),
            "conformance: C: O1 {tag}: the offline index"
        );
        let ks: Vec<Kappa> = r.kept_impl_graphs.iter().map(kappa).collect();
        let cnt = counts_over(&ks, &[2, 3]);
        assert_eq!(
            (cnt.f, cnt.s, cnt.x, cnt.u, cnt.d, cnt.lines.len()),
            (f, sm, x, u, d, lines),
            "conformance: C: O1 {tag}: the typed classes against the hand table"
        );
        assert_eq!(
            p.cli(&["count", "impl", "--model", model_arg(m), "--seed", "0", "--", variant_arg(var)]),
            (format!("execs={n} blocked=0\n"), 0),
            "conformance: C: O1 {tag}: count impl"
        );
        let e = dir.join(format!("impl-{}-{}.jsonl", variant_arg(var), model_arg(m)));
        let es = e.to_string_lossy().into_owned();
        assert_eq!(
            p.cli(&["export", "impl", "--out", &es, "--model", model_arg(m), "--seed", "0", "--", variant_arg(var)]),
            (format!("exported: {lines} lines from {n} graphs to {es}\n"), 0),
            "conformance: C: O1 {tag}: export impl"
        );
        let j = conf_join(&s, &e).unwrap_or_else(|er| panic!("conformance: C: O1 {tag}: join: {er}"));
        assert_eq!(j.verdict, JoinVerdict::Violation, "conformance: C: O1 {tag}: the join's verdict");
        assert_eq!(j.uncovered.len(), d, "conformance: C: O1 {tag}: D = the join's count");
        // The first miss by the offline engine.
        let (i1, k1) = first_report(var, m);
        assert!(
            (1..=f + 1).contains(&i1),
            "conformance: C: O1 {tag}: the first miss {i1} is within the first F + 1 graphs"
        );
        assert_eq!(class_of(&ks[i1 - 1], &[2, 3]) != 'F', true, "conformance: C: O1 {tag}: kept graph I1 is a miss");
        assert_eq!(ks[i1 - 1], k1, "conformance: C: O1 {tag}: the two references agree on graph I1");
        let not_found = class_of(&k1, &[2, 3]) == 'X';
        // C.
        let (text, code) = run_online(&p, &s, &[], m, var);
        assert_eq!(code, 0, "conformance: C: O1 {tag}: exit 0 with a verdict: {text}");
        let (i, t) = first_miss_of(&text).unwrap_or_else(|| panic!("conformance: C: O1 {tag}: no first miss: {text}"));
        assert_eq!(i, i1, "conformance: C: O1 {tag}: the first miss's iteration");
        let w = line_k(&k1);
        let want = expected_text(&head, (n, f, sm, x), "reports", false, Some((i1, t, w.as_str(), not_found)), (u, d), None);
        assert_eq!(text, want, "conformance: C: O1 {tag}: the lines");
        note!("O1\t{tag}\tI={i1}\tT={t}\tclass={}", if not_found { "NotFound" } else { "NoSig" });
    }
}

/// **O2** (conforming). fixed/fifo: exactly five lines, `lookups: 12 (12
/// found, …)`, `conforms`, `uncovered: 0 graphs (0 distinct summaries)`, exit
/// 0. Failing directions: F3, F8, F9, F10.
#[test]
fn o2_conforming() {
    let p = o_prog();
    let dir = scratch("c-o2");
    let s = spec_file(&p, &dir);
    let r = reference(Var::Fixed, ConsType::FIFO, false);
    assert_eq!(
        (r.counters.impl_graphs, r.counters.lookups_succeeded, r.counters.reports),
        (12, 12, 0),
        "conformance: C: O2: the offline engine"
    );
    let (text, code) = run_online(&p, &s, &[], ConsType::FIFO, Var::Fixed);
    assert_eq!(
        (text.as_str(), code),
        (
            expected_text(&spec_head(&s, 2), (12, 12, 0, 0), "conforms", false, None, (0, 0), None).as_str(),
            0
        ),
        "conformance: C: O2: the lines"
    );
}

/// **O3** (bug-finder). bug/bag `--stop-at-first`: stops at O1's first miss,
/// `lookups: I1 (I1−1 found, …)`, `uncovered: 1 graphs (1 distinct
/// summaries)`, O1's witness and `at:`, `reports`, exit 0; fixed/fifo with
/// the flag never stops (O2's counts, the bug-finder `mode:`). Failing
/// directions: F4, F7.
#[test]
fn o3_bug_finder() {
    let p = o_prog();
    let dir = scratch("c-o3");
    let s = spec_file(&p, &dir);
    let head = spec_head(&s, 2);
    let (i1, k1) = first_report(Var::Bug, ConsType::Bag);
    let not_found = class_of(&k1, &[2, 3]) == 'X';
    let (text, code) = run_online(&p, &s, &["--stop-at-first"], ConsType::Bag, Var::Bug);
    assert_eq!(code, 0, "conformance: C: O3: exit 0: {text}");
    let (i, t) = first_miss_of(&text).unwrap_or_else(|| panic!("conformance: C: O3: no first miss: {text}"));
    assert_eq!(i, i1, "conformance: C: O3: the first miss's iteration");
    let (sm, x) = if not_found { (0, 1) } else { (1, 0) };
    let w = line_k(&k1);
    assert_eq!(
        text,
        expected_text(&head, (i1, i1 - 1, sm, x), "reports", true, Some((i1, t, w.as_str(), not_found)), (1, 1), None),
        "conformance: C: O3: the lines"
    );
    let (full, _) = run_online(&p, &s, &[], ConsType::Bag, Var::Bug);
    assert_eq!(witness_of(&full), witness_of(&text), "conformance: C: O3: full mode's witness");
    assert_eq!(first_miss_of(&full).map(|x| x.0), Some(i1), "conformance: C: O3: full mode's iteration");
    let (text, code) = run_online(&p, &s, &["--stop-at-first"], ConsType::FIFO, Var::Fixed);
    assert_eq!(
        (text, code),
        (expected_text(&head, (12, 12, 0, 0), "conforms", true, None, (0, 0), None), 0),
        "conformance: C: O3: bug-finder without a miss"
    );
}

// =========================================================================
// O4
// =========================================================================

/// **O4** (a later first miss): fixed/fifo against S without the line
/// L(V*,ok,c,done), V* the value the first explored graph does not carry: `1
/// lines, 1 distinct summaries held`, `lookups: 12 (6 found, 6 signature
/// misses, 0 not found)`, the first miss at I4 = 1 + the index of the first
/// kept graph with V* (≥ 2), `uncovered: 6 graphs (1 distinct summaries)`,
/// NoSig. Bug-finder on it: N = I4, U = 1. Failing directions: F5, F6.
#[test]
fn o4_a_later_first_miss() {
    let p = o_prog();
    let dir = scratch("c-o4");
    let s = spec_file(&p, &dir);
    let ks = kept_kappas(Var::Fixed, ConsType::FIFO);
    assert_eq!(ks.len(), 12, "conformance: C: O4: twelve graphs");
    let first_v = v_of(&ks[0]);
    let vstar = 5 - first_v;
    let i4 = 1 + ks.iter().position(|k| v_of(k) == vstar).expect("conformance: C: O4: a V* graph");
    assert!(i4 >= 2, "conformance: C: O4: the first miss is later than iteration 1");
    let removed = hand_line(vstar, false, false, false);
    let kept_line = hand_line(first_v, false, false, false);
    let (h, body) = read_jsonl(&s);
    let mut want_body = vec![removed.clone(), kept_line.clone()];
    want_body.sort();
    let mut got_body = body.clone();
    got_body.sort();
    assert_eq!(got_body, want_body, "conformance: C: O4: S holds the two hand lines");
    let s4 = dir.join("S-minus.jsonl");
    std::fs::write(&s4, format!("{}\n{kept_line}\n", serde_json::to_string(&h).unwrap()))
        .expect("conformance: C: O4: write the reduced file");
    let head = spec_head(&s4, 1);
    let (text, code) = run_online(&p, &s4, &[], ConsType::FIFO, Var::Fixed);
    assert_eq!(code, 0, "conformance: C: O4: exit 0: {text}");
    let (i, t) = first_miss_of(&text).unwrap_or_else(|| panic!("conformance: C: O4: no first miss: {text}"));
    assert_eq!(i, i4, "conformance: C: O4: the first miss's iteration");
    assert_eq!(
        text,
        expected_text(&head, (12, 6, 6, 0), "reports", false, Some((i4, t, removed.as_str(), false)), (6, 1), None),
        "conformance: C: O4: the lines"
    );
    let (text, code) = run_online(&p, &s4, &["--stop-at-first"], ConsType::FIFO, Var::Fixed);
    let (i, t) = first_miss_of(&text).unwrap_or_else(|| panic!("conformance: C: O4: bug-finder: {text}"));
    assert_eq!((i, code), (i4, 0), "conformance: C: O4: bug-finder");
    assert_eq!(
        text,
        expected_text(&head, (i4, i4 - 1, 1, 0), "reports", true, Some((i4, t, removed.as_str(), false)), (1, 1), None),
        "conformance: C: O4: bug-finder's lines"
    );
    note!("O4\tV*={vstar}\tI4={i4}");
}

// =========================================================================
// O5, O5a, O5p
// =========================================================================

/// **O5** (refusals, exit 2, no result block): a specification not
/// `complete`; unequal `visible`; usage errors; unreadable files. Failing
/// directions: F12, a wrong exit code.
#[test]
fn o5_refusals() {
    let p = o_prog();
    let dir = scratch("c-o5r");
    let s = spec_file(&p, &dir);
    let ss_owned = s.to_string_lossy().into_owned();
    let ss: &str = &ss_owned;
    let text = std::fs::read_to_string(&s).unwrap();
    let mut cases: Vec<(String, Vec<String>, Vec<String>)> = Vec::new();
    for e in ["bounded", "sampled", "aborted"] {
        let f = dir.join(format!("S-{e}.jsonl"));
        std::fs::write(&f, text.replacen("\"complete\"", &format!("\"{e}\""), 1)).unwrap();
        let fs = f.to_string_lossy().into_owned();
        cases.push((
            format!("enumeration {e}"),
            vec!["online".into(), "--spec".into(), fs.clone(), "--".into(), "fixed".into()],
            vec![fs, format!("`{e}`")],
        ));
    }
    // A valid file over three of the four names.
    let three = Prog {
        vis: Box::new(|_| vec!["alpha".to_owned(), "beta".to_owned(), "reader".to_owned()]),
        spec: Box::new(|_| Arc::new(|| body(Var::Spec))),
        imp: Box::new(|_| Arc::new(|| body(Var::Spec))),
    };
    let f3 = dir.join("S-three.jsonl");
    let f3s = f3.to_string_lossy().into_owned();
    let (o, c) = three.cli(&["export", "spec", "--out", &f3s, "--", "fixed"]);
    assert_eq!(c, 0, "conformance: C: O5: the three-name export: {o}");
    cases.push((
        "unequal visible".into(),
        vec!["online".into(), "--spec".into(), f3s, "--".into(), "fixed".into()],
        vec![
            format!("{:?}", ["alpha", "beta", "reader"]),
            format!("{:?}", VIS),
        ],
    ));
    let dup = dir.join("S-dup.jsonl");
    let first_body = text.lines().nth(1).unwrap().to_owned();
    std::fs::write(&dup, format!("{text}{first_body}\n")).unwrap();
    let bad = dir.join("S-bad.jsonl");
    std::fs::write(&bad, format!("{text}{{not json\n")).unwrap();
    let missing = dir.join("S-missing.jsonl");
    for (what, file, word) in [
        ("a duplicate line", &dup, "repeats"),
        ("an unparsable line", &bad, "not JSON"),
        ("a missing file", &missing, "S-missing.jsonl"),
    ] {
        cases.push((
            what.into(),
            vec!["online".into(), "--spec".into(), file.to_string_lossy().into_owned(), "--".into(), "fixed".into()],
            vec![word.to_owned()],
        ));
    }
    let usage: [(&str, &[&str], &str); 7] = [
        ("no --spec", &["online", "--", "fixed"], "--spec"),
        ("--spec without a value", &["online", "--spec"], "--spec"),
        ("--budget x", &["online", "--spec", ss, "--budget", "x", "--", "fixed"], "--budget"),
        ("--budget 0", &["online", "--spec", ss, "--budget", "0", "--", "fixed"], "--budget"),
        ("an unknown option", &["online", "--spec", ss, "--frob", "--", "fixed"], "--frob"),
        ("an unknown model", &["online", "--spec", ss, "--model", "mo", "--", "fixed"], "mo"),
        ("--program without --out", &["online", "--spec", ss, "--program", "x", "--", "fixed"], "--program"),
    ];
    for (what, args, word) in usage {
        cases.push((
            what.into(),
            args.iter().map(|a| (*a).to_owned()).collect(),
            vec![word.to_owned()],
        ));
    }
    for (what, args, words) in cases {
        let (out, code) = run_cli(&p.program(), &args);
        assert_eq!(code, 2, "conformance: C: O5: {what}: exit 2: {out}");
        assert!(no_result_block(&out), "conformance: C: O5: {what}: a result block: {out}");
        for w in &words {
            assert!(out.contains(w.as_str()), "conformance: C: O5: {what}: `{w}` not named: {out}");
        }
        assert!(out.contains("usage:"), "conformance: C: O5: {what}: no usage: {out}");
    }
}

/// **O5** (failures, exit 1; the budget). ch2/ch3 (the one whose first
/// Ch graph is not the first graph): the run stops at it, `lookups: p−1 (p−1
/// found, …)`, `partial`, `FAILED:` with G1's refusal text. The budget:
/// `--budget 3` → `partial`; `--budget 13` → O2; `--budget 12` (= the space)
/// → `partial` (the derivation's D2); bug/bag `--budget I1` → `reports`, U = 1.
#[test]
fn o5_failures_and_the_budget() {
    let p = o_prog();
    let dir = scratch("c-o5f");
    let s = spec_file(&p, &dir);
    let head = spec_head(&s, 2);
    // The refusal.
    let refusal = match encode_generic(&Val::new(M::Ch('x')), &ThreadNames::new()) {
        Err(e) => e.to_string(),
        Ok(t) => panic!("conformance: C: O5: Ch('x') encoded as {t}"),
    };
    let mut done = 0;
    for var in [Var::Ch2, Var::Ch3] {
        let ks = kept_kappas(var, ConsType::FIFO);
        let pos = 1 + ks.iter().position(|k| k.second == "Ch('x')").expect("conformance: C: O5: a Ch graph");
        if pos < 2 {
            continue;
        }
        done += 1;
        let (text, code) = run_online(&p, &s, &[], ConsType::FIFO, var);
        assert_eq!(code, 1, "conformance: C: O5: {var:?}: exit 1: {text}");
        assert_eq!(
            text,
            expected_text(&head, (pos - 1, pos - 1, 0, 0), "partial", false, None, (0, 0), Some(refusal.as_str())),
            "conformance: C: O5: {var:?}: the lines"
        );
        let r = online::online(&cfg(ConsType::FIFO), &vis(), imp_of(var), &s, opts(Mode::Full, None, None))
            .expect("conformance: C: O5: not refused");
        assert_eq!((r.iterations, r.end), (pos, End::Failed), "conformance: C: O5: {var:?}: stopped at p");
        invariants(&r);
        note!("O5\t{var:?}\tp={pos}");
    }
    assert_eq!(done, 1, "conformance: C: O5: exactly one of ch2/ch3 has p >= 2");
    // The budget.
    for (b, want) in [
        ("3", expected_text(&head, (3, 3, 0, 0), "partial", false, None, (0, 0), None)),
        ("13", expected_text(&head, (12, 12, 0, 0), "conforms", false, None, (0, 0), None)),
        ("12", expected_text(&head, (12, 12, 0, 0), "partial", false, None, (0, 0), None)),
    ] {
        let (text, code) = run_online(&p, &s, &["--budget", b], ConsType::FIFO, Var::Fixed);
        assert_eq!((text, code), (want, 0), "conformance: C: O5: --budget {b}");
    }
    let (i1, k1) = first_report(Var::Bug, ConsType::Bag);
    let not_found = class_of(&k1, &[2, 3]) == 'X';
    let bs = i1.to_string();
    let (text, code) = run_online(&p, &s, &["--budget", &bs], ConsType::Bag, Var::Bug);
    let (_, t) = first_miss_of(&text).unwrap_or_else(|| panic!("conformance: C: O5: budget I1: {text}"));
    let (sm, x) = if not_found { (0, 1) } else { (1, 0) };
    assert_eq!(
        (text, code),
        (
            expected_text(&head, (i1, i1 - 1, sm, x), "reports", false, Some((i1, t, line_k(&k1).as_str(), not_found)), (1, 1), None),
            0
        ),
        "conformance: C: O5: --budget I1"
    );
}

/// **O5a** (an assertion failure with revisits left): assert-r and assert-r2
/// (`reader`, visible) and assert-s (`relay`, invisible) under fifo: the run stops at the
/// failed completion, `iterations` = its position by the typed reference (not
/// the last graph), `lookups` one less, all found, `partial`, `FAILED:`
/// naming the thread, exit 1. Failing direction: the assertion not detected.
#[test]
fn o5a_an_assertion_with_revisits_left() {
    let p = o_prog();
    let dir = scratch("c-o5a");
    let s = spec_file(&p, &dir);
    let head = spec_head(&s, 2);
    for (var, thread, pick) in [
        (Var::AssertR, "reader", (|k: &Kappa| k.err) as fn(&Kappa) -> bool),
        (Var::AssertR2, "reader", (|k: &Kappa| k.err) as fn(&Kappa) -> bool),
        (Var::AssertS, "relay", (|k: &Kappa| k.c2) as fn(&Kappa) -> bool),
    ] {
        let ks = kept_kappas(var, ConsType::FIFO);
        assert_eq!(ks.len(), 12, "conformance: C: O5a: {var:?}: twelve graphs offline");
        let pos = 1 + ks.iter().position(pick).expect("conformance: C: O5a: a failing graph");
        assert!(pos < 12, "conformance: C: O5a: {var:?}: the failure is not on the last graph");
        assert!(
            ks[..pos - 1].iter().all(|k| class_of(k, &[2, 3]) == 'F'),
            "conformance: C: O5a: {var:?}: every graph before it is found"
        );
        let r = online::online(&cfg(ConsType::FIFO), &vis(), imp_of(var), &s, opts(Mode::Full, None, None))
            .expect("conformance: C: O5a: not refused");
        assert_eq!(
            (r.iterations, r.lookups, r.found, r.end),
            (pos, pos - 1, pos - 1, End::Failed),
            "conformance: C: O5a: {var:?}: stopped at the failed completion"
        );
        invariants(&r);
        let msg = r.failure.clone().expect("conformance: C: O5a: a message");
        assert!(msg.contains(&format!("`{thread}`")), "conformance: C: O5a: {var:?}: the thread: {msg}");
        let (text, code) = run_online(&p, &s, &[], ConsType::FIFO, var);
        assert_eq!(
            (text, code),
            (expected_text(&head, (pos - 1, pos - 1, 0, 0), "partial", false, None, (0, 0), Some(msg.as_str())), 1),
            "conformance: C: O5a: {var:?}: the lines"
        );
        note!("O5a\t{var:?}\tp={pos}\t{msg}");
    }
}

/// **O5p** (a panic, through the fault hook at iteration k): before any miss
/// (fixed/fifo, k = 3: `partial`, the payload) and after misses (bug/bag, k =
/// 20: the counts of the first 19 graphs by the typed reference, O1's first
/// miss kept, `reports`), exit 1, the invariants; with `--out`, the `aborted`
/// file holds the distinct lines of the first 19 graphs and their fields.
#[test]
fn o5p_a_panic() {
    let p = o_prog();
    let dir = scratch("c-o5p");
    let s = spec_file(&p, &dir);
    let head = spec_head(&s, 2);
    let payload = |k: usize| format!("conformance: online test fault at iteration {k}");
    // Before any miss.
    let mut o = opts(Mode::Full, None, None);
    o.fault_at = Some(3);
    let r = online::online(&cfg(ConsType::FIFO), &vis(), imp_of(Var::Fixed), &s, o)
        .expect("conformance: C: O5p: not refused");
    invariants(&r);
    assert_eq!(
        (r.iterations, r.lookups, r.found, r.end, r.exit_code()),
        (3, 2, 2, End::Failed, 1),
        "conformance: C: O5p: k = 3"
    );
    assert_eq!(
        r.render(),
        expected_text(&head, (2, 2, 0, 0), "partial", false, None, (0, 0), Some(payload(3).as_str())),
        "conformance: C: O5p: k = 3: the lines"
    );
    // After misses, with --out.
    let ks = kept_kappas(Var::Bug, ConsType::Bag);
    let c19 = counts_over(&ks[..19], &[2, 3]);
    let (i1, k1) = first_report(Var::Bug, ConsType::Bag);
    assert!(c19.u >= 11 && i1 < 20, "conformance: C: O5p: misses before the fault");
    let f = dir.join("out-fault.jsonl");
    let mut o = opts(
        Mode::Full,
        None,
        Some(OnlineOut {
            path: f.clone(),
            header: ExportHeader {
                program: "p".into(),
                size: "z".into(),
            },
        }),
    );
    o.fault_at = Some(20);
    let r = online::online(&cfg(ConsType::Bag), &vis(), imp_of(Var::Bug), &s, o)
        .expect("conformance: C: O5p: not refused");
    invariants(&r);
    assert_eq!(
        (r.iterations, r.lookups, r.found, r.signature_misses, r.not_found, r.uncovered_total, r.uncovered_distinct, r.end),
        (20, 19, c19.f, c19.s, c19.x, c19.u, c19.d, End::Failed),
        "conformance: C: O5p: k = 20: the state of the first 19 completions"
    );
    let first = r.first.clone().expect("conformance: C: O5p: the first miss kept");
    assert_eq!((first.iteration, first.line.clone()), (i1, line_k(&k1)), "conformance: C: O5p: the first miss");
    let not_found = class_of(&k1, &[2, 3]) == 'X';
    assert_eq!(
        r.render(),
        expected_text(
            &head,
            (19, c19.f, c19.s, c19.x),
            "reports",
            false,
            Some((i1, first.wall_ms, first.line.as_str(), not_found)),
            (c19.u, c19.d),
            Some(payload(20).as_str())
        ),
        "conformance: C: O5p: k = 20: the lines"
    );
    let (h, body) = read_out(&f);
    assert_eq!(
        h,
        out_head("p", "z", "asyn", "aborted", (i1, first.wall_ms, c19.u)),
        "conformance: C: O5p: the aborted file's header"
    );
    assert_eq!(body, c19.lines.iter().cloned().collect::<Vec<_>>(), "conformance: C: O5p: the aborted file's body");
}

// =========================================================================
// O6
// =========================================================================

/// **O6** (`--out`): complete with the run's fields (16 and O1's first miss;
/// 0 on O2), the body = `export impl`'s, readable by the join; the
/// implementation's `--program`/`--size`; `bounded` at the budget, `aborted`
/// after bug-finder and after a failure, each with its fields and body; no
/// file without `--out`.
#[test]
fn o6_out() {
    let p = o_prog();
    let dir = scratch("c-o6");
    let s = spec_file(&p, &dir);
    let (i1, _) = first_report(Var::Bug, ConsType::Bag);
    let ks_bug = kept_kappas(Var::Bug, ConsType::Bag);
    let ks_fix = kept_kappas(Var::Fixed, ConsType::FIFO);
    let lines_of = |ks: &[Kappa]| -> Vec<String> { counts_over(ks, &[2, 3]).lines.into_iter().collect() };
    // Full, bug/bag, defaults.
    let f = dir.join("full.jsonl");
    let fs = f.to_string_lossy().into_owned();
    let (text, code) = run_online(&p, &s, &["--out", &fs], ConsType::Bag, Var::Bug);
    assert_eq!(code, 0, "conformance: C: O6: full: {text}");
    let (_, t) = first_miss_of(&text).expect("conformance: C: O6: a first miss");
    let (h, body) = read_out(&f);
    assert_eq!(h, out_head("program:impl", "bug", "asyn", "complete", (i1, t, 16)), "conformance: C: O6: full header");
    let e = dir.join("impl.jsonl");
    let es = e.to_string_lossy().into_owned();
    let (o, c) = p.cli(&["export", "impl", "--out", &es, "--model", "bag", "--seed", "0", "--", "bug"]);
    assert_eq!(c, 0, "conformance: C: O6: export impl: {o}");
    let (_, ebody) = read_out(&e);
    assert_eq!(body, ebody, "conformance: C: O6: the body = export impl's");
    assert_eq!(body, lines_of(&ks_bug), "conformance: C: O6: the body = the hand lines");
    assert!(!tmp_of(&f).exists(), "conformance: C: O6: no .tmp left");
    let j = conf_join(&s, &f).unwrap_or_else(|er| panic!("conformance: C: O6: join: {er}"));
    assert_eq!((j.verdict, j.uncovered.len()), (JoinVerdict::Violation, 6), "conformance: C: O6: the join reads it");
    // Conforming, fifo, the implementation's metadata.
    let f2 = dir.join("conf.jsonl");
    let f2s = f2.to_string_lossy().into_owned();
    let (text, code) = run_online(&p, &s, &["--out", &f2s, "--program", "impl-o", "--size", "z9"], ConsType::FIFO, Var::Fixed);
    assert_eq!(code, 0, "conformance: C: O6: conforming: {text}");
    let (h, body) = read_out(&f2);
    assert_eq!(h, out_head("impl-o", "z9", "p2p", "complete", (0, 0, 0)), "conformance: C: O6: conforming header");
    assert_eq!(
        body,
        vec![hand_line(2, false, false, false), hand_line(3, false, false, false)],
        "conformance: C: O6: conforming body"
    );
    // The budget.
    let f3 = dir.join("b3.jsonl");
    let f3s = f3.to_string_lossy().into_owned();
    let (_, code) = run_online(&p, &s, &["--out", &f3s, "--budget", "3"], ConsType::FIFO, Var::Fixed);
    assert_eq!(code, 0, "conformance: C: O6: budget 3");
    let (h, body) = read_out(&f3);
    assert_eq!(h, out_head("program:impl", "fixed", "p2p", "bounded", (0, 0, 0)), "conformance: C: O6: budget 3 header");
    assert_eq!(body, lines_of(&ks_fix[..3]), "conformance: C: O6: budget 3 body");
    let f4 = dir.join("bi1.jsonl");
    let f4s = f4.to_string_lossy().into_owned();
    let bs = i1.to_string();
    let (text, _) = run_online(&p, &s, &["--out", &f4s, "--budget", &bs], ConsType::Bag, Var::Bug);
    let (_, t) = first_miss_of(&text).expect("conformance: C: O6: budget I1: a first miss");
    let (h, body) = read_out(&f4);
    assert_eq!(h, out_head("program:impl", "bug", "asyn", "bounded", (i1, t, 1)), "conformance: C: O6: budget I1 header");
    assert_eq!(body, lines_of(&ks_bug[..i1]), "conformance: C: O6: budget I1 body");
    // Bug-finder.
    let f5 = dir.join("bf.jsonl");
    let f5s = f5.to_string_lossy().into_owned();
    let (text, _) = run_online(&p, &s, &["--out", &f5s, "--stop-at-first"], ConsType::Bag, Var::Bug);
    let (_, t) = first_miss_of(&text).expect("conformance: C: O6: bug-finder: a first miss");
    let (h, body) = read_out(&f5);
    assert_eq!(h, out_head("program:impl", "bug", "asyn", "aborted", (i1, t, 1)), "conformance: C: O6: bug-finder header");
    assert_eq!(body, lines_of(&ks_bug[..i1]), "conformance: C: O6: bug-finder body");
    // A failure (the ch variant whose first Ch graph is not the first).
    let (var, pos) = [Var::Ch2, Var::Ch3]
        .into_iter()
        .map(|v| {
            let ks = kept_kappas(v, ConsType::FIFO);
            (v, 1 + ks.iter().position(|k| k.second == "Ch('x')").unwrap())
        })
        .find(|(_, pos)| *pos >= 2)
        .expect("conformance: C: O6: a ch variant with p >= 2");
    let ks_ch = kept_kappas(var, ConsType::FIFO);
    let f6 = dir.join("fail.jsonl");
    let f6s = f6.to_string_lossy().into_owned();
    let (text, code) = run_online(&p, &s, &["--out", &f6s], ConsType::FIFO, var);
    assert_eq!(code, 1, "conformance: C: O6: failure: {text}");
    let (h, body) = read_out(&f6);
    assert_eq!(
        h,
        out_head("program:impl", variant_arg(var), "p2p", "aborted", (0, 0, 0)),
        "conformance: C: O6: failure header"
    );
    assert_eq!(body, lines_of(&ks_ch[..pos - 1]), "conformance: C: O6: failure body");
    assert_eq!(body.len(), 1, "conformance: C: O6: failure body is the other value's line");
    // No --out: nothing written.
    let before: BTreeSet<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).collect();
    let (_, code) = run_online(&p, &s, &[], ConsType::Bag, Var::Bug);
    assert_eq!(code, 0, "conformance: C: O6: without --out");
    let after: BTreeSet<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).collect();
    assert_eq!(before, after, "conformance: C: O6: no file without --out");
}

// =========================================================================
// O7, O8
// =========================================================================

/// **O7** (the text): every ONLINE-1 line form, whole texts compared (O1–O6
/// compare theirs too); here the label columns, the witness's normal form and
/// absence of `n`, and the line order on a reporting, a conforming and a
/// failed run. Failing direction: F10 and any change of a label or form.
#[test]
fn o7_the_text() {
    let p = o_prog();
    let dir = scratch("c-o7");
    let s = spec_file(&p, &dir);
    for (extra, m, var, labels) in [
        (&[][..], ConsType::Bag, Var::Bug, &[0, 1, 2, 3, 4, 5, 6, 7][..]),
        (&["--stop-at-first"][..], ConsType::FIFO, Var::Bug, &[0, 1, 2, 3, 4, 5, 6, 7][..]),
        (&[][..], ConsType::FIFO, Var::Fixed, &[0, 1, 2, 3, 5][..]),
        (&[][..], ConsType::FIFO, Var::AssertR, &[0, 1, 2, 3, 5, 8][..]),
    ] {
        let (text, _) = run_online(&p, &s, extra, m, var);
        let got: Vec<usize> = text
            .lines()
            .map(|l| {
                LABELS
                    .iter()
                    .position(|lab| l.starts_with(lab) && l.len() > 12)
                    .unwrap_or_else(|| panic!("conformance: C: O7: an unlabelled line `{l}`"))
            })
            .collect();
        assert_eq!(got, labels, "conformance: C: O7: {var:?} the labels and their order: {text}");
        for l in text.lines() {
            assert_eq!(l.as_bytes()[11], b' ', "conformance: C: O7: 12 columns: `{l}`");
            assert_ne!(l.as_bytes()[12], b' ', "conformance: C: O7: the value starts at column 13: `{l}`");
        }
        if let Some(w) = witness_of(&text) {
            assert!(!w.contains("\"n\""), "conformance: C: O7: the witness has no `n`: {w}");
            assert_eq!(normal_line(&w, &vis()).as_deref(), Ok(w.as_str()), "conformance: C: O7: the witness is normal");
        }
    }
}

/// **O8** (the clock): P_x (derivation §4.5) with the index delay 300 ms:
/// the first miss at iteration 1 with `first_miss_wall_ms` < 300. Failing
/// direction: the clock started before the file is read (≥ 300).
#[test]
fn o8_the_clock() {
    let dir = scratch("c-o8");
    let s = dir.join("X.jsonl");
    std::fs::write(
        &s,
        concat!(
            r#"{"format":1,"tool":"t","program":"p","size":"s","visible":["x"],"model":"p2p","enumeration":"complete","encoding":1}"#,
            "\n",
            r#"{"statuses":{"x":"done"},"words":{"x":[{"s":0}]},"counts":[]}"#,
            "\n"
        ),
    )
    .unwrap();
    let px: Arc<dyn Fn() + Send + Sync> = Arc::new(|| {
        let y = named("y", || {
            let _: i64 = crate::recv_msg_block();
        });
        let yid = y.thread().id();
        let x = named("x", move || crate::send_msg(yid, -1i64));
        x.join().unwrap();
        y.join().unwrap();
    });
    let mut o = opts(Mode::Full, None, None);
    o.index_delay = Some(Duration::from_millis(300));
    let started = Instant::now();
    let r = online::online(&cfg(ConsType::FIFO), &["x".to_owned()], px, &s, o)
        .expect("conformance: C: O8: not refused");
    let wall = started.elapsed().as_millis() as u64;
    let first = r.first.clone().expect("conformance: C: O8: a miss");
    assert_eq!(
        (r.iterations, r.lookups, r.signature_misses, first.iteration, first.line.as_str()),
        (1, 1, 1, 1, r#"{"statuses":{"x":"done"},"words":{"x":[{"s":-1}]},"counts":[]}"#),
        "conformance: C: O8: one graph, a signature miss"
    );
    assert!(wall >= 300, "conformance: C: O8: the delay ran ({wall} ms)");
    assert!(
        first.wall_ms < 300,
        "conformance: C: O8: first_miss_wall_ms {} counts the index delay",
        first.wall_ms
    );
    note!("O8\tT={}\twall={wall}", first.wall_ms);
}
