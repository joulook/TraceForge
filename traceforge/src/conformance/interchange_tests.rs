//! `J3`'s tests (the tester's; `criteria/J3.md` J3-6). The lead creates this
//! module empty so that `mod.rs` can name it; every test in it is the tester's.
//! Since `H` (ruling Q15) this is the fixture-based half, behind
//! `fixture-tests`: the tests that need no fixture moved to
//! `interchange_default_tests.rs`, whose shared helpers this half imports; H's
//! A3 and C's old-count child are at the end.
//!
//! Derived first (`log/dev/J3.derived.md`, its gate-3 addendum): T1–T17. The
//! default suite holds the unit and in-process tests; the 74-row tests (T8 P-EQ,
//! T9 P-RND, T10 the joins) and the command as a process (T16) are ignored and run
//! one per invocation. Their directories come from the environment so that a
//! failing direction runs on scratch copies: `J3_OUT` (the exports; default the
//! place of record `plan/jmc-must/log/runs/J3/`), `J3_GOLDEN` (JMC's files; default
//! `plan/jmc-must/log/runs/J4/`, read-only), `J3_CONF_JOIN` (the binary; default
//! `target/debug/conf-join`).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::time::Instant;
use serde_json::Value;
use crate::ConsType;
use crate::conformance::compact::{CompactSummary, SetIndex};
use crate::conformance::config::{ConfConfig, IndexKind};
use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
use crate::conformance::grid::{apps_fixtures, Fixture, Grant, GridConfig, GridEngine, Msg, Prog, Rep, Req};
use crate::conformance::interchange::{encode_generic, model_name, normal_line, record_thread_names, ExportError, ExportHeader, ExportStats, JoinReport, MissClass, ThreadNames, Verdict};
use crate::conformance::morphism::Status;
use crate::conformance::obs::Obs;
use crate::conformance::stateful::{enumerate, EnumRun};
use crate::exec_graph::ExecutionGraph;
use crate::msg::Val;
use crate::conformance::interchange_default_tests::{scratch, named, read_jsonl, visible_of, ex, small_cc, header, AB, file, join_ok, label_cases};

/// Writes a line to stderr (the closed `s5_tests` emission scan forbids the
/// print macros in every file under `conformance/` but its test-only list).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

// =========================================================================
// Helpers: places, rows, programs, the package
// =========================================================================

fn plan_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../plan")
}

/// JMC's 148 golden files (read-only).
fn golden_dir() -> PathBuf {
    std::env::var_os("J3_GOLDEN")
        .map(PathBuf::from)
        .unwrap_or_else(|| plan_dir().join("jmc-must/log/runs/J4"))
}

/// The TraceForge exports (the place of record unless `J3_OUT` says otherwise).
fn out_dir() -> PathBuf {
    std::env::var_os("J3_OUT")
        .map(PathBuf::from)
        .unwrap_or_else(|| plan_dir().join("jmc-must/log/runs/J3"))
}



/// One of J4's 74 rows (derivation §3): its JMC name, the grid fixture whose
/// side is the program, which side, the family and the size.
#[derive(Clone, Debug)]
struct Row {
    jmc: String,
    family: &'static str,
    kind: String,
    k: usize,
    q: usize,
    s: Option<usize>,
}

impl Row {
    fn of(jmc: &str) -> Row {
        let parts: Vec<&str> = jmc.split('-').collect();
        let family = match parts[0] {
            "A3Lock" => "a3",
            "A2Store" => "a2",
            other => panic!("conformance: J3: a row of an unknown family `{other}`"),
        };
        let digits: Vec<usize> = parts
            .iter()
            .rev()
            .take_while(|p| p.chars().all(|c| c.is_ascii_digit()))
            .map(|p| p.parse().unwrap())
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        let kind = parts[1..parts.len() - digits.len()].join("-");
        let (k, q, s) = match digits.as_slice() {
            [k, q] => (*k, *q, None),
            [k, q, s] => (*k, *q, Some(*s)),
            other => panic!("conformance: J3: the size of `{jmc}`: {other:?}"),
        };
        Row {
            jmc: jmc.to_owned(),
            family,
            kind,
            k,
            q,
            s,
        }
    }

    fn is_spec(&self) -> bool {
        self.kind == "spec"
    }

    /// The grid fixture whose implementation (or, for a spec row, whose
    /// specification) is the program.
    fn fixture(&self) -> String {
        let (k, q) = (self.k, self.q);
        match (self.family, self.kind.as_str()) {
            ("a3", "spec") => format!("apps/a3/fifo/spec/k{k}q{q}"),
            ("a3", kind) => format!("apps/a3/{kind}/spec/k{k}q{q}"),
            ("a2", "spec") => format!("apps/a2/pb/spec/k{k}q{q}"),
            ("a2", kind @ ("sh" | "misroute")) => {
                format!(
                    "apps/a2/{kind}/spec/k{k}q{q}s{}",
                    self.s.expect("conformance: s")
                )
            }
            ("a2", kind) => format!("apps/a2/{kind}/spec/k{k}q{q}"),
            _ => unreachable!(),
        }
    }

    /// The JMC row of this row's specification (itself for a spec row).
    fn spec_row(&self) -> String {
        let fam = if self.family == "a3" {
            "A3Lock"
        } else {
            "A2Store"
        };
        format!("{fam}-spec-{}-{}", self.k, self.q)
    }

    fn side(&self) -> &'static str {
        if self.is_spec() {
            "spec"
        } else {
            "impl"
        }
    }
}

/// The 74 rows, from the golden files' names.
fn rows() -> Vec<Row> {
    let mut names: Vec<String> = std::fs::read_dir(golden_dir())
        .expect("conformance: J3: the golden directory")
        .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
        .filter_map(|n| n.strip_suffix(".must.jsonl").map(str::to_owned))
        .collect();
    names.sort();
    names.iter().map(|n| Row::of(n)).collect()
}

fn fixture(name: &str) -> Fixture {
    apps_fixtures()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("conformance: J3: no grid fixture `{name}`"))
}

/// The stateful engine under `Set` with the fixture's own `Config` and names.
fn cc_of(f: &Fixture) -> ConfConfig {
    GridConfig::new(GridEngine::Stateful)
        .index(IndexKind::Set)
        .conf_config(f)
}



/// A file's lines in the reader's normal form, as a set (with the count of
/// lines read, so a duplicate shows).
fn normal_set(path: &Path) -> (Vec<String>, BTreeSet<String>, usize) {
    let (head, lines) = read_jsonl(path);
    let visible = visible_of(&head);
    let set: BTreeSet<String> = lines
        .iter()
        .enumerate()
        .map(|(i, l)| {
            normal_line(l, &visible).unwrap_or_else(|e| {
                panic!(
                    "conformance: J3: {} line {}: refused: {e}",
                    path.display(),
                    i + 2
                )
            })
        })
        .collect();
    (visible, set, lines.len())
}

/// MIN-ENGINES §4's package, per fixture: `E1E` (specification, implementation
/// distinct), `E1T` (verdict, uncovered graphs), the distinct `UNCSET` keys.
#[derive(Clone, Debug, Default)]
struct Pkg {
    spec_distinct: usize,
    impl_distinct: usize,
    conforms: bool,
    uncovered_graphs: usize,
    uncovered_distinct: usize,
}

fn package() -> BTreeMap<String, Pkg> {
    let pkg = plan_dir().join("traceForge/log/dev/MIN-ENGINES.validation/part1-rerun.tar.gz");
    let dir = scratch("package");
    let st = std::process::Command::new("tar")
        .arg("xzf")
        .arg(&pkg)
        .arg("-C")
        .arg(&dir)
        .status()
        .expect("conformance: J3: tar");
    assert!(st.success(), "conformance: J3: tar xzf {}", pkg.display());
    let mut out = BTreeMap::new();
    for e in
        std::fs::read_dir(dir.join("rerun")).expect("conformance: J3: the extracted rerun files")
    {
        let text = std::fs::read_to_string(e.unwrap().path()).unwrap();
        let mut name = String::new();
        let mut p = Pkg::default();
        let mut unc = BTreeSet::new();
        for l in text.lines() {
            let f: Vec<&str> = l.split('\t').collect();
            let num = |i: usize| -> usize { f[i].split(' ').nth(1).unwrap().parse().unwrap() };
            match f[0] {
                "E1E" => {
                    name = f[1].to_owned();
                    if f[3] == "specification" {
                        p.spec_distinct = num(5);
                    } else {
                        p.impl_distinct = num(5);
                    }
                }
                "E1T" => {
                    name = f[1].to_owned();
                    p.conforms = f[3] == "verdict conforms";
                    p.uncovered_graphs = num(4);
                }
                "UNCSET" => {
                    unc.insert((f[1].to_owned(), f[2].to_owned()));
                }
                _ => {}
            }
        }
        p.uncovered_distinct = unc.len();
        out.insert(name, p);
    }
    out
}

/// The program of a row and its configuration.
fn program_of(row: &Row) -> (Fixture, Prog, ConfConfig) {
    let f = fixture(&row.fixture());
    let p = if row.is_spec() {
        f.specification.clone()
    } else {
        f.implementation.clone()
    };
    let cc = cc_of(&f);
    (f, p, cc)
}

/// Exports one row to `dir/<row>.traceforge.jsonl`, `size` from JMC's header.
fn export_row(row: &Row, dir: &Path) -> (PathBuf, ExportStats) {
    let (head, _) = read_jsonl(&golden_dir().join(format!("{}.must.jsonl", row.jmc)));
    let size = head["size"]
        .as_str()
        .expect("conformance: J3: a size")
        .to_owned();
    let (f, p, cc) = program_of(row);
    let header = ExportHeader {
        program: format!("{}:{}", f.name, row.side()),
        size,
    };
    let path = dir.join(format!("{}.traceforge.jsonl", row.jmc));
    let stats = ex(&cc, &p, &header, &path)
        .unwrap_or_else(|e| panic!("conformance: J3: export of {}: {e}", row.jmc));
    (path, stats)
}


// =========================================================================
// T1, T2: the encoder (J3-1; since G1 stage B the generic encoder, G1-1)
// =========================================================================

fn enc<T: crate::msg::Message + Clone + 'static>(v: &T) -> String {
    encode_generic(&crate::msg::Val::new(v.clone()), &ThreadNames::new())
        .unwrap_or_else(|e| panic!("conformance: J3: an A3/A2 value encodes: {e}"))
}

/// **T1** (E1): the canonical bytes of each of the eight tags, each literal also
/// found verbatim in a golden file. Failing direction: `f` before `t`, `Put`'s
/// fields reordered.
#[test]
fn t1_the_encoder_writes_jmcs_bytes() {
    let cases: Vec<(String, &str)> = vec![
        (enc(&Msg::Acq(0)), r#"{"t":"Acq","f":[0]}"#),
        (enc(&Msg::Rel(1)), r#"{"t":"Rel","f":[1]}"#),
        (enc(&Grant(1, 0)), r#"{"t":"Grant","f":[1,0]}"#),
        (
            enc(&Req::Put { c: 0, k: 0, v: 0 }),
            r#"{"t":"Put","f":[0,0,0]}"#,
        ),
        (
            enc(&Req::Put { c: 1, k: 0, v: 11 }),
            r#"{"t":"Put","f":[1,0,11]}"#,
        ),
        (enc(&Req::Get { c: 1, k: 0 }), r#"{"t":"Get","f":[1,0]}"#),
        (enc(&Rep::Val(0)), r#"{"t":"Val","f":[0]}"#),
        (enc(&Rep::Ack), r#"{"t":"Ack","f":[]}"#),
        (enc(&Rep::None), r#"{"t":"None","f":[]}"#),
    ];
    let mut golden = String::new();
    for e in std::fs::read_dir(golden_dir()).expect("conformance: J3: the golden directory") {
        golden.push_str(&std::fs::read_to_string(e.unwrap().path()).unwrap());
    }
    for (got, want) in &cases {
        assert_eq!(got, want, "conformance: J3: E1");
        assert!(
            golden.contains(want),
            "conformance: J3: {want} is not in a golden file"
        );
    }
}

/// The A3/A2 value domain at the 74 rows' sizes (k ≤ 3 clients, q ≤ 3 rounds):
/// every value a client sends or receives, as (type, value's encoding).
fn domain() -> Vec<(&'static str, String, String)> {
    let mut out = Vec::new();
    for i in 0..3usize {
        out.push(("Msg", format!("{:?}", Msg::Acq(i)), enc(&Msg::Acq(i))));
        out.push(("Msg", format!("{:?}", Msg::Rel(i)), enc(&Msg::Rel(i))));
        for j in 0..4usize {
            out.push(("Grant", format!("{:?}", Grant(i, j)), enc(&Grant(i, j))));
            let r = crate::conformance::grid::a2_op(i, j);
            out.push(("Req", format!("{r:?}"), enc(&r)));
            out.push((
                "Rep",
                format!("{:?}", Rep::Val((10 * i + j) as i32)),
                enc(&Rep::Val((10 * i + j) as i32)),
            ));
        }
    }
    for k in 0..2usize {
        for c in 0..3usize {
            out.push((
                "Req",
                format!("{:?}", Req::Get { c, k }),
                enc(&Req::Get { c, k }),
            ));
        }
    }
    out.push(("Rep", format!("{:?}", Rep::Ack), enc(&Rep::Ack)));
    out.push(("Rep", format!("{:?}", Rep::None), enc(&Rep::None)));
    out
}

/// **T2** (E2–E4): equal values encode equally (a clone; two constructions);
/// distinct values of one type encode differently over the domain; the four
/// types' tag sets are pairwise disjoint; an integer outside signed 64 bits is
/// refused. Failing direction: `Grant`'s second field dropped (two values
/// collide); the bound removed.
#[test]
fn t2_the_encoders_laws() {
    // E2
    assert_eq!(enc(&Grant(2, 1)), enc(&Grant(2, 1).clone()));
    assert_eq!(
        enc(&crate::conformance::grid::a2_op(1, 2)),
        enc(&crate::conformance::grid::a2_op(1, 2))
    );
    // E3: per type, distinct values (by `Debug`, which is structural here) ↦ distinct bytes
    let dom = domain();
    let mut by_value: BTreeMap<(&str, String), String> = BTreeMap::new();
    for (ty, dbg, e) in &dom {
        by_value.insert((*ty, dbg.clone()), e.clone());
    }
    let mut seen: BTreeMap<String, (&str, String)> = BTreeMap::new();
    for ((ty, dbg), e) in &by_value {
        if let Some(prev) = seen.insert(e.clone(), (*ty, dbg.clone())) {
            panic!(
                "conformance: J3: E3: {prev:?} and {:?} both encode as {e}",
                (ty, dbg)
            );
        }
    }
    assert!(
        by_value.len() > 40,
        "conformance: J3: non-vacuity: {} values",
        by_value.len()
    );
    // tag sets pairwise disjoint
    let mut tags: BTreeMap<String, BTreeSet<&str>> = BTreeMap::new();
    for (ty, _, e) in &dom {
        let v: Value = serde_json::from_str(e).unwrap();
        tags.entry(v["t"].as_str().unwrap().to_owned())
            .or_default()
            .insert(*ty);
    }
    for (t, types) in &tags {
        assert_eq!(
            types.len(),
            1,
            "conformance: J3: the tag {t} belongs to {types:?}"
        );
    }
    assert_eq!(
        tags.len(),
        8,
        "conformance: J3: the eight tags: {:?}",
        tags.keys()
    );
    // E4 (G1: the generic encoder's signed-64-bit bound)
    let e4 = |v: crate::msg::Val| encode_generic(&v, &ThreadNames::new());
    assert!(e4(crate::msg::Val::new(i64::MAX)).is_ok());
    assert!(e4(crate::msg::Val::new(i64::MIN)).is_ok());
    assert!(e4(crate::msg::Val::new(u64::MAX)).is_err(), "conformance: J3: E4");
    assert!(
        e4(crate::msg::Val::new(i64::MAX as u64 + 1)).is_err(),
        "conformance: J3: E4"
    );
    assert!(
        e4(crate::msg::Val::new(Grant(usize::MAX, 0))).is_err(),
        "conformance: J3: E4 through a type"
    );
}



/// `b` receives without blocking (⊥ or `Acq(0)`); `a` sends `Acq(0)` to `b`.
fn bottom_program() -> Prog {
    Arc::new(|| {
        let b = named("b", || {
            let _: Option<Msg> = crate::recv_msg();
        });
        let tb = b.thread().id();
        named("a", move || crate::send_msg(tb, Msg::Acq(0)));
    })
}

/// `a` sends `Acq(0)` … `Acq(255)` to `b`, which receives all 256 (blocking).
fn wide_program() -> Prog {
    Arc::new(|| {
        let b = named("b", || {
            for _ in 0..256 {
                let _: Msg = crate::recv_msg_block();
            }
        });
        let tb = b.thread().id();
        named("a", move || {
            for i in 0..256 {
                crate::send_msg(tb, Msg::Acq(i));
            }
        });
    })
}

/// A visible value the format refuses: `b` receives an `f64` (G1 stage B; J3's
/// unregistered `u64` encodes under the generic path).
fn refused_program() -> Prog {
    Arc::new(|| {
        let b = named("b", || {
            let _: f64 = crate::recv_msg_block();
        });
        let tb = b.thread().id();
        named("a", move || crate::send_msg(tb, 1.5f64));
    })
}

/// **T3** (E5, X4; G1 stage B): an export whose visible word holds a value the
/// format refuses (an `f64`) is refused naming the type and the form; with no
/// file at the path none is created, with one it is left byte for byte; no
/// `.tmp` either way. Failing direction: the file opened before the run.
#[test]
fn t3_a_refused_value_refuses_the_export() {
    let dir = scratch("t3");
    let path = dir.join("u.jsonl");
    let tmp = dir.join("u.jsonl.tmp");
    let cc = small_cc(&["a", "b"], ConsType::FIFO);
    let r = ex(&cc, &refused_program(), &header("t3"), &path);
    match &r {
        Err(ExportError::Refused {
            type_name, what, ..
        }) => {
            assert!(
                type_name.contains("f64") && what == "a float",
                "conformance: J3: E5 names {type_name}: {what}"
            )
        }
        other => panic!("conformance: J3: E5: {other:?}"),
    }
    assert!(
        !path.exists() && !tmp.exists(),
        "conformance: J3: X4: a file after a refusal"
    );
    std::fs::write(&path, "earlier\n").unwrap();
    let r = ex(&cc, &refused_program(), &header("t3"), &path);
    assert!(matches!(r, Err(ExportError::Refused { .. })));
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "earlier\n",
        "conformance: J3: X4"
    );
    assert!(!tmp.exists(), "conformance: J3: X4: a .tmp behind");
}

/// **T4** (X2): the line writer end to end on two small programs — ⊥ and a
/// receive of a value (`{"r":null}`, `{"r":{…}}`), and a word of 256 events
/// (`U16` counts, values above 255 written in full) — against lines derived here
/// by hand; `err` through the shared renderer (`normal_line`; no export can hold
/// one: an assertion refuses the export, below); no `n`. Failing direction:
/// `Errored` written `errored`; ⊥ written `{"r":{}}`.
#[test]
fn t4_the_line_writer() {
    let dir = scratch("t4");
    // ⊥
    let path = dir.join("bottom.jsonl");
    let cc = small_cc(&["a", "b"], ConsType::FIFO);
    let st = ex(&cc, &bottom_program(), &header("bottom"), &path).unwrap();
    let (head, lines) = read_jsonl(&path);
    assert_eq!(visible_of(&head), ["a", "b"]);
    let got: BTreeSet<String> = lines.into_iter().collect();
    let want: BTreeSet<String> = [
        r#"{"statuses":{"a":"done","b":"done"},"words":{"a":[{"s":{"t":"Acq","f":[0]}}],"b":[{"r":null}]},"counts":[0,0]}"#,
        r#"{"statuses":{"a":"done","b":"done"},"words":{"a":[{"s":{"t":"Acq","f":[0]}}],"b":[{"r":{"t":"Acq","f":[0]}}]},"counts":[0,1]}"#,
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    assert_eq!(got, want, "conformance: J3: X2 on ⊥");
    assert_eq!(st.lines, 2);
    // U16: a's 256 sends see none of b's events; b's j-th receive sees a's first j + 1
    let path = dir.join("wide.jsonl");
    let st = ex(&cc, &wide_program(), &header("wide"), &path).unwrap();
    let (_, lines) = read_jsonl(&path);
    assert_eq!((st.lines, lines.len()), (1, 1));
    let sends: Vec<String> = (0..256)
        .map(|i| format!(r#"{{"s":{{"t":"Acq","f":[{i}]}}}}"#))
        .collect();
    let recvs: Vec<String> = (0..256)
        .map(|i| format!(r#"{{"r":{{"t":"Acq","f":[{i}]}}}}"#))
        .collect();
    let counts: Vec<String> = (0..256)
        .map(|_| "0".to_owned())
        .chain((1..=256).map(|j| j.to_string()))
        .collect();
    let want = format!(
        r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{}],"b":[{}]}},"counts":[{}]}}"#,
        sends.join(","),
        recvs.join(","),
        counts.join(",")
    );
    assert_eq!(lines[0], want, "conformance: J3: X2 on U16 counts");
    // `err` and ⊥ through the shared renderer: the line is its own normal form
    let err = r#"{"statuses":{"a":"err","b":"blocked"},"words":{"a":[{"s":{"t":"Acq","f":[0]}}],"b":[{"r":null}]},"counts":[0,0]}"#;
    assert_eq!(
        normal_line(err, &["a".to_owned(), "b".to_owned()]).unwrap(),
        err
    );
    // one visible name: `counts` is `[]`
    let one = r#"{"statuses":{"a":"done"},"words":{"a":[{"s":{"t":"Acq","f":[0]}}]},"counts":[]}"#;
    assert_eq!(normal_line(one, &["a".to_owned()]).unwrap(), one);
    // an assertion refuses the export (so `err` never reaches a file), and leaves no file
    let asserting: Prog = Arc::new(|| {
        named("a", || crate::assert(false));
    });
    let path = dir.join("assert.jsonl");
    let r = ex(
        &small_cc(&["a"], ConsType::FIFO),
        &asserting,
        &header("assert"),
        &path,
    );
    assert!(
        matches!(r, Err(ExportError::SpecErrors(_))),
        "conformance: J3: {r:?}"
    );
    assert!(!path.exists());
}

/// **T5** (X3): the header — the names sorted and deduplicated from an unsorted
/// list with a repeat; `FIFO` → `p2p` (G1-4: `Bag` → `asyn`; MO, WB, Mailbox
/// refused by name, and an export under MO leaves no file); `program`/`size` as
/// given; no `seed`, `iterations` or `n`; the key order JMC writes. Failing
/// direction: the configuration's order kept.
#[test]
#[allow(deprecated)]
fn t5_the_header() {
    let dir = scratch("t5");
    let path = dir.join("h.jsonl");
    let cc = small_cc(&["b", "a", "b"], ConsType::FIFO);
    ex(&cc, &bottom_program(), &header("apps/x:impl"), &path).unwrap();
    let text = std::fs::read_to_string(&path).unwrap();
    let first = text.lines().next().unwrap();
    assert_eq!(
        first,
        r#"{"format":1,"tool":"traceforge","program":"apps/x:impl","size":"k1","visible":["a","b"],"model":"p2p","enumeration":"complete","encoding":1}"#
    );
    assert_eq!(model_name(ConsType::FIFO), Ok("p2p"));
    for c in [ConsType::MO, ConsType::WB, ConsType::Mailbox] {
        match model_name(c) {
            Err(ExportError::Model(name)) => assert_eq!(name, format!("{c:?}")),
            other => panic!("conformance: J3: {c:?}: {other:?}"),
        }
    }
    // `ConfBuilder` refuses MO, so the configuration is edited after the build:
    // the export's own model check refuses it before any run
    let p2 = dir.join("mo.jsonl");
    let mut mo = small_cc(&["a", "b"], ConsType::FIFO);
    mo.config.cons_type = ConsType::MO;
    let r = ex(&mo, &bottom_program(), &header("mo"), &p2);
    assert!(matches!(r, Err(ExportError::Model(_))) && !p2.exists());
    let p3 = dir.join("bag.jsonl");
    ex(
        &small_cc(&["a", "b"], ConsType::Bag),
        &bottom_program(),
        &header("bag"),
        &p3,
    )
    .unwrap();
    let (bag_head, _) = read_jsonl(&p3);
    assert_eq!(bag_head["model"], "asyn", "conformance: G1-4: Bag → asyn");
    let mut not_set = small_cc(&["a", "b"], ConsType::FIFO);
    not_set.index = IndexKind::Current;
    assert_eq!(
        ex(&not_set, &bottom_program(), &header("x"), &p2),
        Err(ExportError::NotSet)
    );
}

// =========================================================================
// T6, T7: the exporter = the index (X1), complete only and deterministic (X4, X5)
// =========================================================================

/// The independent side of X1: every completion of `program` summarised by the
/// engines' own `CompactSummary::at_completion` (not the exporter), rendered
/// here by hand (the format's X2), deduplicated.
fn independent_lines(f: &Fixture, program: &Prog) -> BTreeSet<String> {
    let out = Arc::new(Mutex::new(Vec::new()));
    let sink: CompletionSink = {
        let (out, vis) = (Arc::clone(&out), f.visible.clone());
        Box::new(move |g: &ExecutionGraph, _| {
            out.lock()
                .unwrap()
                .push(CompactSummary::at_completion(g, &vis, "j3"));
            SinkVerdict::Continue
        })
    };
    let mut config = f.config.clone();
    config.max_iterations = None;
    enumerate(
        EnumRun {
            config,
            visible: f.visible.clone(),
            mode: ConfMode::Enumerate,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        program,
    );
    let mut names = f.visible.clone();
    names.sort();
    names.dedup();
    let summaries = std::mem::take(&mut *out.lock().unwrap());
    summaries.iter().map(|s| hand_line(s, &names)).collect()
}

/// A value by hand (the oracle of T6 and G-T3): the four A3/A2 types' canonical
/// bytes written here by downcast, independent of the exporter's encoder (G1
/// stage B: J3's hand encoders are removed; their bytes are T1's literals).
fn hand_value(v: &crate::msg::Val) -> String {
    let a = v.as_any_ref();
    if let Some(x) = a.downcast_ref::<Msg>() {
        match x {
            Msg::Acq(c) => format!(r#"{{"t":"Acq","f":[{c}]}}"#),
            Msg::Rel(c) => format!(r#"{{"t":"Rel","f":[{c}]}}"#),
        }
    } else if let Some(Grant(c, r)) = a.downcast_ref::<Grant>() {
        format!(r#"{{"t":"Grant","f":[{c},{r}]}}"#)
    } else if let Some(x) = a.downcast_ref::<Req>() {
        match x {
            Req::Put { c, k, v } => format!(r#"{{"t":"Put","f":[{c},{k},{v}]}}"#),
            Req::Get { c, k } => format!(r#"{{"t":"Get","f":[{c},{k}]}}"#),
        }
    } else if let Some(x) = a.downcast_ref::<Rep>() {
        match x {
            Rep::Ack => r#"{"t":"Ack","f":[]}"#.to_owned(),
            Rep::Val(v) => format!(r#"{{"t":"Val","f":[{v}]}}"#),
            Rep::None => r#"{"t":"None","f":[]}"#.to_owned(),
        }
    } else {
        panic!(
            "conformance: J3: a value of `{}` in an A3/A2 word",
            v.type_name
        )
    }
}

/// The format's line by hand (`SUMMARY-FORMAT.md` "One line per distinct").
fn hand_line(s: &CompactSummary, names: &[String]) -> String {
    let statuses: Vec<String> = names
        .iter()
        .map(|n| {
            let st = match s.sig.status(n).unwrap() {
                Status::Done => "done",
                Status::Blocked => "blocked",
                Status::Errored => "err",
            };
            format!("\"{n}\":\"{st}\"")
        })
        .collect();
    let words: Vec<String> = names
        .iter()
        .map(|n| {
            let obs: Vec<String> = s
                .sig
                .word(n)
                .iter()
                .map(|o| match o {
                    Obs::Send(v) => format!("{{\"s\":{}}}", hand_value(v)),
                    Obs::Recv(Some(v)) => format!("{{\"r\":{}}}", hand_value(v)),
                    Obs::Recv(None) => "{\"r\":null}".to_owned(),
                })
                .collect();
            format!("\"{n}\":[{}]", obs.join(","))
        })
        .collect();
    let counts: Vec<String> = (0..s.ord.len()).map(|i| s.ord.at(i).to_string()).collect();
    format!(
        "{{\"statuses\":{{{}}},\"words\":{{{}}},\"counts\":[{}]}}",
        statuses.join(","),
        words.join(","),
        counts.join(",")
    )
}

/// T6's rows (the derivation's dozen) with the package's `E1E` for the side:
/// (JMC row, expected lines).
const T6_ROWS: [(&str, usize); 12] = [
    ("A3Lock-spec-2-1", 2),
    ("A3Lock-fifo-3-1", 12),
    ("A3Lock-never-grant-2-2", 11),
    ("A3Lock-double-grant-3-1", 36),
    ("A3Lock-wrong-round-2-2", 6),
    ("A2Store-pb-1-1", 1),
    ("A2Store-early-ack-2-3", 44),
    ("A2Store-silent-put-3-1", 6),
    ("A2Store-spec-3-2", 90),
    ("A2Store-sh-3-1-2", 6),
    ("A2Store-misroute-3-2-2", 90),
    ("A2Store-stale-get-2-3", 20),
];

/// **T6** (X1): on a dozen rows (blocked lines, all-blocked rows, a single
/// client, the largest files), the export's lines are in bijection with the
/// index — count = `orders_held` = the package's `E1E` — and equal, as a set,
/// to the program's distinct summaries computed without the exporter. Failing
/// direction: the exporter writes one order per slot (the export's own X1
/// assertion, or this test, fails).
#[test]
fn t6_the_export_is_the_index() {
    let dir = scratch("t6");
    for (jmc, want) in T6_ROWS {
        let row = Row::of(jmc);
        let (path, st) = export_row(&row, &dir);
        let (_, lines) = read_jsonl(&path);
        let (f, p, _) = program_of(&row);
        let indep = independent_lines(&f, &p);
        let got: BTreeSet<String> = lines.iter().cloned().collect();
        assert_eq!(
            (st.lines, st.orders_held, lines.len(), got.len()),
            (want, want, want, want),
            "conformance: J3: X1 on {jmc}"
        );
        assert_eq!(
            got, indep,
            "conformance: J3: X1 on {jmc}: the export ≠ the program's summaries"
        );
        note!(
            "T6\t{jmc}\tlines {}\tspec graphs {}",
            st.lines,
            st.spec_graphs
        );
    }
}

/// **T7** (X5): two exports of A3 double-grant 3-1's implementation, back to
/// back on this thread, are byte-equal (36 lines). (X4): a panicking run (a
/// declared name never spawned) leaves the earlier file as it was and no `.tmp`.
/// Failing directions: the writer reverses its entries on every second call (a
/// thread-local counter); the file opened at the path before the run.
#[test]
fn t7_the_export_is_deterministic_and_complete_only() {
    let dir = scratch("t7");
    let row = Row::of("A3Lock-double-grant-3-1");
    let (p1, s1) = export_row(&row, &dir);
    let b1 = std::fs::read(&p1).unwrap();
    let (p2, s2) = export_row(&row, &dir);
    let b2 = std::fs::read(&p2).unwrap();
    assert_eq!(s1, s2);
    assert_eq!(s1.lines, 36);
    assert!(b1 == b2, "conformance: J3: X5: two exports differ as bytes");
    // X4: a run that panics (`ghost` declared, never spawned)
    let path = dir.join("x4.jsonl");
    std::fs::write(&path, "earlier\n").unwrap();
    let cc = small_cc(&["a", "b", "ghost"], ConsType::FIFO);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ex(&cc, &bottom_program(), &header("x4"), &path)
    }));
    assert!(
        r.is_err(),
        "conformance: J3: X4: the run was expected to panic"
    );
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "earlier\n",
        "conformance: J3: X4"
    );
    assert!(
        !dir.join("x4.jsonl.tmp").exists(),
        "conformance: J3: X4: a .tmp behind"
    );
    let fresh = dir.join("x4-none.jsonl");
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ex(&cc, &bottom_program(), &header("x4"), &fresh)
    }));
    assert!(r.is_err());
    assert!(!fresh.exists() && !dir.join("x4-none.jsonl.tmp").exists());
}







/// **T11** (J4): the three miss classes apart, on TraceForge's own exports (scratch):
/// A3 wrong-round 2-1 (other values: `no-slot`), never-grant 2-1 (a blocked status:
/// `no-bucket`), double-grant 2-1 (orders: `not-found`). Failing direction: the
/// classes merged.
#[test]
fn t11_the_miss_classes() {
    let dir = scratch("t11");
    let (spec, _) = export_row(&Row::of("A3Lock-spec-2-1"), &dir);
    for (jmc, class, n) in [
        ("A3Lock-wrong-round-2-1", MissClass::NoSlot, 2),
        ("A3Lock-never-grant-2-1", MissClass::NoBucket, 1),
        ("A3Lock-double-grant-2-1", MissClass::NotFound, 2),
    ] {
        let (imp, _) = export_row(&Row::of(jmc), &dir);
        let r = join_ok(&spec, &imp);
        assert_eq!(r.verdict, Verdict::Violation, "conformance: J3: {jmc}");
        let classes: Vec<MissClass> = r.uncovered.iter().map(|(c, _)| *c).collect();
        assert_eq!(classes, vec![class; n], "conformance: J3: J4 on {jmc}");
        assert!(
            r.render().contains(&format!("\n{} {{", class.name())),
            "conformance: J3: {jmc}"
        );
    }
}





/// **T15** (R3): a signature whose word has 256 events decodes `U16` for every
/// order of its slot, whatever a line's largest count — so a specification line
/// with counts up to 256 and an implementation line with all counts ≤ 255 compare
/// without a panic, and the verdict is the pointwise one. Failing direction: the
/// width chosen per line by its largest count (the two orders' widths differ and
/// `le` panics).
#[test]
fn t15_one_width_per_signature() {
    let dir = scratch("t15");
    let sends: Vec<String> = (0..256)
        .map(|i| format!(r#"{{"s":{{"t":"Acq","f":[{i}]}}}}"#))
        .collect();
    let recvs: Vec<String> = (0..256)
        .map(|i| format!(r#"{{"r":{{"t":"Acq","f":[{i}]}}}}"#))
        .collect();
    let line = |b_counts: Vec<u32>| {
        let counts: Vec<String> = std::iter::repeat_n(0u32, 256)
            .chain(b_counts)
            .map(|c| c.to_string())
            .collect();
        format!(
            r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{}],"b":[{}]}},"counts":[{}]}}"#,
            sends.join(","),
            recvs.join(","),
            counts.join(",")
        )
    };
    let wide = line((1..=256).collect());
    let low = line(std::iter::repeat_n(0u32, 256).collect());
    let spec = file(&dir, "spec.jsonl", AB, &[&low]);
    let imp = file(&dir, "imp.jsonl", AB, &[&wide]);
    let r = join_ok(&spec, &imp);
    assert_eq!(
        r.verdict,
        Verdict::Conforms,
        "conformance: J3: low ≤ wide pointwise"
    );
    let r = join_ok(&imp, &spec);
    assert_eq!(r.verdict, Verdict::Violation, "conformance: J3: wide ≰ low");
    assert_eq!(r.uncovered.len(), 1);
    assert_eq!(r.uncovered[0].0, MissClass::NotFound);
}

/// Every line of every JMC golden file, with its `n` removed (`n` is the last key
/// in JMC's lines).
fn golden_lines() -> Vec<(PathBuf, usize, Vec<String>, String, String)> {
    let mut out = Vec::new();
    let mut paths: Vec<PathBuf> = std::fs::read_dir(golden_dir())
        .expect("conformance: J3: the golden directory")
        .map(|e| e.unwrap().path())
        .filter(|p| p.to_string_lossy().ends_with(".jsonl"))
        .collect();
    paths.sort();
    for p in paths {
        let (head, lines) = read_jsonl(&p);
        let visible = visible_of(&head);
        for (i, l) in lines.into_iter().enumerate() {
            let at = l.rfind(",\"n\":").unwrap_or_else(|| {
                panic!("conformance: J3: {} line {}: no `n`", p.display(), i + 2)
            });
            let without = format!("{}}}", &l[..at]);
            out.push((p.clone(), i + 2, visible.clone(), l, without));
        }
    }
    out
}

/// **T17** (ruling Q8): each of JMC's 1 080 golden lines, its values re-serialised
/// by the reader's rule, is byte-equal to the original with `n` removed — nothing
/// is rewritten; and no golden line is refused. Failing directions: a scratch copy
/// of one golden file with a value written `{"f":[0],"t":"Acq"}`, and one with a
/// space after a `:` (`J3_GOLDEN`); a reader writing `f` before `t`.
#[test]
fn t17_jmcs_lines_are_already_normal() {
    let lines = golden_lines();
    let mut bad = Vec::new();
    for (p, n, visible, _orig, without) in &lines {
        match normal_line(without, visible) {
            Ok(norm) if norm == *without => {}
            Ok(norm) => bad.push(format!("{} line {n}: rewritten as {norm}", p.display())),
            Err(e) => bad.push(format!("{} line {n}: refused: {e}", p.display())),
        }
    }
    for b in &bad {
        note!("T17\t{b}");
    }
    assert!(
        bad.is_empty(),
        "conformance: J3: T17: {} golden lines not normal",
        bad.len()
    );
    if std::env::var_os("J3_GOLDEN").is_none() {
        assert_eq!(lines.len(), 1080, "conformance: J3: the golden lines");
    }
}

// =========================================================================
// The main test: T8 (P-EQ), T9 (P-RND), T10 (the joins) — ignored, 74 rows
// =========================================================================

/// An independent join on normalised lines (no `SetIndex`, no `Sig`): a line is
/// covered iff a specification line has equal `statuses` and `words` (JSON
/// values) and counts ≤ its own pointwise. The uncovered lines.
fn mini_uncovered(spec: &BTreeSet<String>, imp: &BTreeSet<String>) -> BTreeSet<String> {
    let parse = |l: &str| -> (Value, Value, Vec<u64>) {
        let v: Value = serde_json::from_str(l).unwrap();
        let c = v["counts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_u64().unwrap())
            .collect();
        (v["statuses"].clone(), v["words"].clone(), c)
    };
    let held: Vec<(Value, Value, Vec<u64>)> = spec.iter().map(|l| parse(l)).collect();
    imp.iter()
        .filter(|l| {
            let (s, w, c) = parse(l);
            !held
                .iter()
                .any(|(s2, w2, c2)| *s2 == s && *w2 == w && c2.iter().zip(&c).all(|(a, b)| a <= b))
        })
        .cloned()
        .collect()
}

/// The package's entry for a row: an implementation row's own fixture; a
/// specification row's `E1E` specification count from any fixture of its family
/// at its size (all agree).
fn pkg_of(row: &Row, pkg: &BTreeMap<String, Pkg>) -> (usize, Option<Pkg>) {
    if !row.is_spec() {
        let p = pkg
            .get(&row.fixture())
            .unwrap_or_else(|| panic!("conformance: J3: the package has no {}", row.fixture()))
            .clone();
        return (p.impl_distinct, Some(p));
    }
    let size = format!("/spec/k{}q{}", row.k, row.q);
    let fam = format!("apps/{}/", row.family);
    let counts: BTreeSet<usize> = pkg
        .iter()
        .filter(|(n, _)| {
            n.starts_with(&fam) && (n.ends_with(&size) || n.contains(&format!("{size}s")))
        })
        .map(|(_, p)| p.spec_distinct)
        .collect();
    assert_eq!(
        counts.len(),
        1,
        "conformance: J3: {}'s E1E specification counts {counts:?}",
        row.jmc
    );
    (*counts.iter().next().unwrap(), None)
}

/// **T8, P-EQ (ruling Q1, all 74):** every row exported to `J3_OUT` (default the
/// place of record) and compared with JMC's `.must.jsonl` as normalised line sets
/// (`n` ignored), with equal `visible`; the line count = the run's `orders_held` =
/// the package's `E1E` = JMC's. Any difference is named by row and line. Failing
/// directions: scratch copies of one golden file (`J3_GOLDEN`) with a count + 1, a
/// value changed, a status flipped, a line removed; the exporter's names
/// unsorted.
#[test]
#[ignore]
fn t8_p_eq_the_74_exports_equal_jmcs() {
    let out = out_dir();
    std::fs::create_dir_all(&out).unwrap();
    let pkg = package();
    let rows = rows();
    assert_eq!(rows.len(), 74, "conformance: J3: the 74 rows");
    let mut bad = Vec::new();
    let mut total = 0;
    for row in &rows {
        let (path, st) = export_row(row, &out);
        let gold = golden_dir().join(format!("{}.must.jsonl", row.jmc));
        let (tv, tset, tn) = normal_set(&path);
        let (gv, gset, gn) = normal_set(&gold);
        let (e1e, _) = pkg_of(row, &pkg);
        total += tn;
        let mut row_bad = Vec::new();
        if tv != gv {
            row_bad.push(format!("visible {tv:?} vs JMC's {gv:?}"));
        }
        if (st.lines, st.orders_held, tn, tset.len(), gn, gset.len())
            != (e1e, e1e, e1e, e1e, e1e, e1e)
        {
            row_bad.push(format!(
                "counts: exported {} (orders_held {}, file {tn}, distinct {}), JMC {gn} (distinct {}), E1E {e1e}",
                st.lines,
                st.orders_held,
                tset.len(),
                gset.len()
            ));
        }
        for l in tset.difference(&gset) {
            row_bad.push(format!("only in TraceForge's: {l}"));
        }
        for l in gset.difference(&tset) {
            row_bad.push(format!("only in JMC's: {l}"));
        }
        note!(
            "T8\t{}\t{}\tlines {tn}\tE1E {e1e}\tJMC {gn}\tspec graphs {}\t{}",
            row.jmc,
            row.side(),
            st.spec_graphs,
            if row_bad.is_empty() {
                "equal"
            } else {
                "DIFFERENT"
            }
        );
        for b in row_bad {
            bad.push(format!("{}: {b}", row.jmc));
        }
    }
    for b in &bad {
        note!("T8\tDIFF\t{b}");
    }
    assert!(
        bad.is_empty(),
        "conformance: J3: P-EQ: {} differences",
        bad.len()
    );
    if std::env::var_os("J3_GOLDEN").is_none() {
        assert_eq!(total, 576, "conformance: J3: the 74 exports' lines");
    }
}

/// **T9, P-RND (all 74):** each `.random.jsonl` line set ⊆ TraceForge's export
/// (T8's files in `J3_OUT`). Failing direction: a scratch random file with a line
/// not in the export.
#[test]
#[ignore]
fn t9_p_rnd_the_samples_are_inside_the_exports() {
    let out = out_dir();
    let mut bad = Vec::new();
    let mut lines = 0;
    for row in rows() {
        let (_, tset, _) = normal_set(&out.join(format!("{}.traceforge.jsonl", row.jmc)));
        let (_, rset, rn) = normal_set(&golden_dir().join(format!("{}.random.jsonl", row.jmc)));
        lines += rn;
        for l in rset.difference(&tset) {
            bad.push(format!("{}: sampled but not in the export: {l}", row.jmc));
        }
        note!(
            "T9\t{}\trandom {rn}\texport {}\t{}",
            row.jmc,
            tset.len(),
            if rset.is_subset(&tset) {
                "⊆"
            } else {
                "NOT ⊆"
            }
        );
    }
    for b in &bad {
        note!("T9\tDIFF\t{b}");
    }
    assert!(
        bad.is_empty(),
        "conformance: J3: P-RND: {} lines",
        bad.len()
    );
    if std::env::var_os("J3_GOLDEN").is_none() {
        assert_eq!(lines, 504, "conformance: J3: the random files' lines");
    }
}

fn set_of(r: &JoinReport) -> BTreeSet<String> {
    r.uncovered.iter().map(|(_, l)| l.clone()).collect()
}

/// **T10, the joins:** on the 63 implementation rows the four joins — (TF spec,
/// JMC impl), (JMC spec, TF impl), (TF spec, TF impl), (JMC spec, JMC impl) — each
/// with the package's verdict (`E1T`) and uncovered count (distinct `UNCSET`), the
/// four uncovered sets equal and equal to an independent join's; the 11 identity
/// pairs conform both ways; the three sampled representatives (J3-4). Reads T8's
/// exports (`J3_OUT`). Failing directions: a join that ignores counts; a join
/// testing `≥`; a scratch export with one specification line removed.
#[test]
#[ignore]
fn t10_the_joins() {
    let out = out_dir();
    let gold = golden_dir();
    let pkg = package();
    let rows = rows();
    let tf = |r: &str| out.join(format!("{r}.traceforge.jsonl"));
    let jm = |r: &str| gold.join(format!("{r}.must.jsonl"));
    let mut bad = Vec::new();
    let (mut conform, mut violate) = (0, 0);
    let mut sampled: Vec<(String, bool, usize, bool)> = Vec::new();
    for row in rows.iter().filter(|r| !r.is_spec()) {
        let (_, p) = pkg_of(row, &pkg);
        let p = p.unwrap();
        let sr = row.spec_row();
        let pairs = [
            ("TF spec, JMC impl", tf(&sr), jm(&row.jmc)),
            ("JMC spec, TF impl", jm(&sr), tf(&row.jmc)),
            ("TF spec, TF impl", tf(&sr), tf(&row.jmc)),
            ("JMC spec, JMC impl", jm(&sr), jm(&row.jmc)),
        ];
        let want = if p.conforms {
            Verdict::Conforms
        } else {
            Verdict::Violation
        };
        if p.conforms {
            conform += 1;
        } else {
            violate += 1;
        }
        let mut sets = Vec::new();
        let mut got = Vec::new();
        for (what, s, i) in &pairs {
            let r = join_ok(s, i);
            if r.verdict != want || r.uncovered.len() != p.uncovered_distinct {
                bad.push(format!(
                    "{} ({what}): {:?} with {} uncovered, expected {want:?} with {}",
                    row.jmc,
                    r.verdict,
                    r.uncovered.len(),
                    p.uncovered_distinct
                ));
            }
            got.push(format!("{:?}/{}", r.verdict, r.uncovered.len()));
            sets.push(set_of(&r));
        }
        if sets.iter().any(|s| *s != sets[0]) {
            bad.push(format!("{}: the four uncovered sets differ", row.jmc));
        }
        let (_, ts, _) = normal_set(&tf(&sr));
        let (_, ti, _) = normal_set(&tf(&row.jmc));
        if mini_uncovered(&ts, &ti) != sets[0] {
            bad.push(format!(
                "{}: the independent join's uncovered set differs",
                row.jmc
            ));
        }
        note!(
            "T10\t{}\texpected {want:?}/{} (graphs {})\tgot {}",
            row.jmc,
            p.uncovered_distinct,
            p.uncovered_graphs,
            got.join(" ")
        );
        // the sampled outcome: the must join's uncovered lines met in the random file
        let (_, rset, _) = normal_set(&gold.join(format!("{}.random.jsonl", row.jmc)));
        let (_, mset, mn) = normal_set(&jm(&row.jmc));
        let _ = mset;
        sampled.push((
            row.jmc.clone(),
            !p.conforms,
            mn,
            !sets[0].is_disjoint(&rset),
        ));
    }
    // the identity pairs
    for row in rows.iter().filter(|r| r.is_spec()) {
        for (what, s, i) in [
            ("TF, JMC", tf(&row.jmc), jm(&row.jmc)),
            ("JMC, TF", jm(&row.jmc), tf(&row.jmc)),
        ] {
            let r = join_ok(&s, &i);
            if r.verdict != Verdict::Conforms || !r.uncovered.is_empty() {
                bad.push(format!(
                    "{} identity ({what}): {:?} with {}",
                    row.jmc,
                    r.verdict,
                    r.uncovered.len()
                ));
            }
        }
        note!("T10\t{}\tidentity both ways\tconforms", row.jmc);
    }
    // the sampled representatives: the smallest rows (by JMC's must line count, then name)
    sampled.sort_by(|a, b| (a.2, &a.0).cmp(&(b.2, &b.0)));
    let pick =
        |fault: bool, hit: bool| sampled.iter().find(|s| s.1 == fault && s.3 == hit).cloned();
    for (fault, hit, want) in [
        (true, true, "verdict: violation (sampled)"),
        (true, false, "verdict: no verdict (sampled)"),
        (false, false, "verdict: no verdict (sampled)"),
    ] {
        let Some((jmc, _, n, _)) = pick(fault, hit) else {
            note!(
                "T10\tsampled\tno fault row whose sample holds {} uncovered line",
                if hit { "an" } else { "no" }
            );
            assert!(
                fault && !hit,
                "conformance: J3: a sampled representative is missing"
            );
            continue;
        };
        let row = Row::of(&jmc);
        let r = join_ok(
            &tf(&row.spec_row()),
            &gold.join(format!("{jmc}.random.jsonl")),
        );
        let text = r.render();
        let line = text.lines().nth(2).unwrap().to_owned();
        let exit = r.exit_code();
        note!("T10\tsampled\t{jmc} ({n} lines)\t{line}\texit {exit}");
        if line != want || exit != u8::from(hit) {
            bad.push(format!(
                "{jmc} sampled: `{line}` exit {exit}, expected `{want}`"
            ));
        }
    }
    for b in &bad {
        note!("T10\tDIFF\t{b}");
    }
    assert_eq!(
        (conform, violate),
        (35, 28),
        "conformance: J3: the 63 rows' verdicts"
    );
    assert!(
        bad.is_empty(),
        "conformance: J3: the joins: {} differences",
        bad.len()
    );
}

// =========================================================================
// T16: the command as a process (ignored)
// =========================================================================

fn conf_join_bin() -> PathBuf {
    std::env::var_os("J3_CONF_JOIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../target/debug/conf-join"))
}

fn run_bin(spec: &Path, imp: &Path) -> (Vec<String>, String, i32) {
    let o = std::process::Command::new(conf_join_bin())
        .arg(spec)
        .arg(imp)
        .output()
        .unwrap_or_else(|e| panic!("conformance: J3: {}: {e}", conf_join_bin().display()));
    let stdout = String::from_utf8(o.stdout).unwrap();
    (
        stdout.lines().map(str::to_owned).collect(),
        String::from_utf8(o.stderr).unwrap(),
        o.status.code().expect("conformance: J3: an exit code"),
    )
}

/// **T16** (ruling Q2): the built binary, nine invocations, each asserting its
/// whole stdout line by line (the uncovered lines as a set), its stderr and its
/// exit code — (a) a conforming pair, (b) a violating pair, (c)–(h) T13's six
/// cases, (i) a refused pair. Reads T8's exports. Failing directions: the
/// criteria's mutation matrix, each in a scratch copy of the command's code.
#[test]
#[ignore]
fn t16_the_command() {
    let out = out_dir();
    let gold = golden_dir();
    let spec = out.join("A3Lock-spec-2-1.traceforge.jsonl");
    let spec_line = "spec: tool=traceforge program=apps/a3/fifo/spec/k2q1:spec size=k2q1 model=p2p enumeration=complete";
    let mut failures = Vec::new();
    let mut check = |name: &str,
                     got: (Vec<String>, String, i32),
                     head: Vec<String>,
                     tail: BTreeSet<String>,
                     stderr_ok: &dyn Fn(&str) -> bool,
                     exit: i32| {
        let (lines, err, code) = got;
        let n = head.len();
        let ok = lines.len() == n + tail.len()
            && lines[..n.min(lines.len())] == head[..]
            && lines.iter().skip(n).cloned().collect::<BTreeSet<_>>() == tail
            && stderr_ok(&err)
            && code == exit;
        note!(
            "T16\t({name})\texit {code}\tstdout {} lines\tstderr {:?}\t{}",
            lines.len(),
            err.trim_end(),
            if ok { "as expected" } else { "NOT as expected" }
        );
        if !ok {
            failures.push(format!("({name}): stdout {lines:#?} stderr {err:?} exit {code}; expected head {head:#?} tail {tail:#?} exit {exit}"));
        }
    };
    let empty = |e: &str| e.is_empty();
    // (a)
    check(
        "a",
        run_bin(&spec, &gold.join("A3Lock-fifo-2-1.must.jsonl")),
        vec![
            spec_line.to_owned(),
            "impl: tool=jmc program=a3-fifo-k2q1 size=k2q1 model=p2p enumeration=complete"
                .to_owned(),
            "verdict: conforms".to_owned(),
            "uncovered: 0".to_owned(),
        ],
        BTreeSet::new(),
        &empty,
        0,
    );
    // (b): the uncovered lines from the independent join, each `not-found`
    let dg = gold.join("A3Lock-double-grant-2-1.must.jsonl");
    let (_, sset, _) = normal_set(&spec);
    let (_, dset, _) = normal_set(&dg);
    let unc = mini_uncovered(&sset, &dset);
    assert_eq!(
        unc.len(),
        2,
        "conformance: J3: A3 double-grant 2-1 has two uncovered lines"
    );
    check(
        "b",
        run_bin(&spec, &dg),
        vec![
            spec_line.to_owned(),
            "impl: tool=jmc program=a3-double-grant-k2q1 size=k2q1 model=p2p enumeration=complete"
                .to_owned(),
            "verdict: violation".to_owned(),
            "uncovered: 2".to_owned(),
        ],
        unc.iter().map(|l| format!("not-found {l}")).collect(),
        &empty,
        1,
    );
    // (c)–(h)
    let dir = scratch("t16");
    for (i, (name, s, imp, verdict, uncovered, exit)) in label_cases(&dir).into_iter().enumerate() {
        let en = name.split(' ').next().unwrap().to_owned();
        let label = ["c", "d", "e", "f", "g", "h"][i];
        check(
            &format!("{label}: {name}"),
            run_bin(&s, &imp),
            vec![
                "spec: tool=t program=p size=s model=p2p enumeration=complete".to_owned(),
                format!("impl: tool=t program=p size=s model=p2p enumeration={en}"),
                verdict,
                format!("uncovered: {}", uncovered.len()),
            ],
            uncovered.into_iter().collect(),
            &empty,
            i32::from(exit),
        );
    }
    // (i): unequal `visible`
    let refused = |e: &str| {
        e.starts_with("conf-join: refused: ")
            && e.contains("`visible` lists differ")
            && e.ends_with('\n')
    };
    check(
        "i",
        run_bin(&spec, &gold.join("A3Lock-spec-3-1.must.jsonl")),
        vec![],
        BTreeSet::new(),
        &refused,
        2,
    );
    for f in &failures {
        note!("T16\tFAIL\t{f}");
    }
    assert!(
        failures.is_empty(),
        "conformance: J3: the command: {} invocations not as expected",
        failures.len()
    );
}

// =========================================================================
// G1 (the tester's; `criteria/G1.md` G1-7, `log/dev/G1.derived.md` addendum A)
// =========================================================================
//
// The generic path beside J3's hand path (stage A): the grammar, the
// refusals, hand = generic, `ThreadId`, the preconditions, the shared main,
// the models, the reader's extension; gates (1) and (2) on the 74 (ignored).






















/// **G-T3** (G1-6 gate (1), the value level): the generic encoder equals the
/// hand encoders' bytes on T1's literals and on every `domain()` value — at stage
/// A against `Encoders::encode` (52/52, record §2.3); since stage B against the
/// test's own byte oracle `hand_value`, J3's encoders being removed. Failing
/// direction: MU12 (a tagged value's fields reversed).
#[test]
fn g1_t3_hand_equals_generic() {
    let mut vals: Vec<Val> = Vec::new();
    for i in 0..3usize {
        vals.push(Val::new(Msg::Acq(i)));
        vals.push(Val::new(Msg::Rel(i)));
        for j in 0..4usize {
            vals.push(Val::new(Grant(i, j)));
            vals.push(Val::new(crate::conformance::grid::a2_op(i, j)));
            vals.push(Val::new(Rep::Val((10 * i + j) as i32)));
        }
    }
    for k in 0..2usize {
        for c in 0..3usize {
            vals.push(Val::new(Req::Get { c, k }));
        }
    }
    vals.push(Val::new(Rep::Ack));
    vals.push(Val::new(Rep::None));
    vals.push(Val::new(Req::Put { c: 1, k: 0, v: 11 }));
    vals.push(Val::new(Grant(1, 0)));
    let mut tags = BTreeSet::new();
    for v in &vals {
        let h = hand_value(v);
        let g = encode_generic(v, &ThreadNames::new())
            .unwrap_or_else(|e| panic!("conformance: G1: generic: {e}"));
        assert_eq!(g, h, "conformance: G1: generic ≠ hand on {:?}", &*v.val);
        let t: Value = serde_json::from_str(&g).unwrap();
        tags.insert(t["t"].as_str().unwrap().to_owned());
    }
    assert_eq!(tags.len(), 8, "conformance: G1: non-vacuity: the eight tags {tags:?}");
    note!("G-T3\t{} values, 8 tags: equal", vals.len());
}

























// ---------------------------------------------------------- gates 1, 2 --

fn g1_dir(var: &str, default: &str) -> PathBuf {
    let d = std::env::var_os(var)
        .map(PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join(default));
    std::fs::create_dir_all(&d).expect("conformance: G1: a directory");
    d
}

/// The export's index, rebuilt by the same `pub(crate)` calls (for the cost).
fn index_of(p: &Prog, cc: &ConfConfig) -> (SetIndex, ThreadNames) {
    let mut config = cc.config.clone();
    config.max_iterations = None;
    let state = Rc::new(RefCell::new((SetIndex::new(), ThreadNames::new())));
    let sink: CompletionSink = {
        let state = Rc::clone(&state);
        let visible = cc.visible.clone();
        Box::new(move |g: &ExecutionGraph, _: &crate::must::MustState| {
            let s = CompactSummary::at_completion(g, &visible, "specification");
            let mut st = state.borrow_mut();
            st.0.insert(&s);
            record_thread_names(g, &mut st.1);
            SinkVerdict::Continue
        })
    };
    let _ = enumerate(
        EnumRun {
            config,
            visible: cc.visible.clone(),
            mode: ConfMode::Enumerate,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        p,
    );
    let out = std::mem::replace(&mut *state.borrow_mut(), (SetIndex::new(), ThreadNames::new()));
    out
}

/// **Gate (1)** (G1-6, all 74; ignored; stage B: the generic path only): each J3
/// program exported through the generic `export` (to `G1_OUT`) has the bytes of
/// J3's file of record (`J3_OUT`, read-only) — on the release build, the build
/// that wrote them (the line order follows the build: `TypeId` in the frozen
/// `Sig::hash128`); the cost: each export's wall, and the encoding of every
/// observed value of the index and the write of the text, timed apart. Failing
/// direction: a scratch `J3_OUT` copy with one byte changed is reported by row.
#[test]
#[ignore]
fn g1_gate1_the_74_generic_exports_are_j3s_bytes() {
    let gen_dir = g1_dir("G1_OUT", "g1-generic");
    let record = out_dir();
    let mut bad = Vec::new();
    let (mut tg, mut teg, mut tw) = (0f64, 0f64, 0f64);
    let mut values = 0usize;
    note!("G1-gate1\trow\tlines\tgraphs\tgeneric_ms\tenc_generic_us\twrite_us\tvalues\tbytes");
    for row in rows() {
        let (head, _) = read_jsonl(&golden_dir().join(format!("{}.must.jsonl", row.jmc)));
        let size = head["size"].as_str().unwrap().to_owned();
        let (f, p, cc) = program_of(&row);
        let header = ExportHeader {
            program: format!("{}:{}", f.name, row.side()),
            size,
        };
        let name = format!("{}.traceforge.jsonl", row.jmc);
        let (gp, rp) = (gen_dir.join(&name), record.join(&name));
        let t0 = Instant::now();
        let gs = ex(&cc, &p, &header, &gp)
            .unwrap_or_else(|e| panic!("conformance: G1: REFUSED {}: {e}", row.jmc));
        let wg = t0.elapsed().as_secs_f64() * 1e3;
        let (gb, rb) = (std::fs::read(&gp).unwrap(), std::fs::read(&rp).unwrap());
        if gb != rb {
            bad.push(format!("{}: generic ≠ record", row.jmc));
        }
        if gs.lines != gs.orders_held {
            bad.push(format!("{}: stats {gs:?}", row.jmc));
        }
        // the cost, apart: encoding every observed value, and the write
        let (index, threads) = index_of(&p, &cc);
        let mut names = cc.visible.clone();
        names.sort();
        names.dedup();
        let mut vals: Vec<&Val> = Vec::new();
        for (_, sig, _, _) in index.entries() {
            for n in &names {
                for o in sig.word(n) {
                    match o {
                        Obs::Send(v) | Obs::Recv(Some(v)) => vals.push(v),
                        Obs::Recv(None) => {}
                    }
                }
            }
        }
        let t0 = Instant::now();
        for v in &vals {
            let _ = std::hint::black_box(encode_generic(v, &threads).unwrap());
        }
        let eg = t0.elapsed().as_secs_f64() * 1e6;
        let wpath = gen_dir.join("write-probe.tmp");
        let t0 = Instant::now();
        std::fs::write(&wpath, &gb).unwrap();
        let ww = t0.elapsed().as_secs_f64() * 1e6;
        let _ = std::fs::remove_file(&wpath);
        note!(
            "G1-gate1\t{}\t{}\t{}\t{wg:.3}\t{eg:.1}\t{ww:.1}\t{}\t{}",
            row.jmc,
            gs.lines,
            gs.spec_graphs,
            vals.len(),
            gb.len()
        );
        tg += wg;
        teg += eg;
        tw += ww;
        values += vals.len();
    }
    note!(
        "G1-gate1\tTOTAL\tgeneric {tg:.1} ms\tenc generic {:.3} ms\twrite {:.3} ms\tvalues {values}\tshare generic {:.3}%",
        teg / 1e3,
        tw / 1e3,
        100.0 * (teg + tw) / 1e3 / tg
    );
    for b in &bad {
        note!("G1-gate1\tDIFF\t{b}");
    }
    assert!(bad.is_empty(), "conformance: G1: gate (1): {} differences", bad.len());
}

/// **Gate (2)** (G1-6, all 74; ignored): the generic exports in `G1_OUT` equal
/// JMC's `.must.jsonl` (`J3_GOLDEN`) as normalised line sets with equal
/// `visible` (J3's P-EQ); 576 lines in all. Failing direction: a scratch golden
/// copy with one value changed.
#[test]
#[ignore]
fn g1_gate2_the_generic_exports_equal_jmcs() {
    let gen_dir = g1_dir("G1_OUT", "g1-generic");
    let mut bad = Vec::new();
    let mut total = 0;
    for row in rows() {
        let (tv, tset, tn) = normal_set(&gen_dir.join(format!("{}.traceforge.jsonl", row.jmc)));
        let (gv, gset, gn) = normal_set(&golden_dir().join(format!("{}.must.jsonl", row.jmc)));
        total += tn;
        let ok = tv == gv && tset == gset && tn == tset.len() && gn == gset.len();
        if !ok {
            bad.push(format!(
                "{}: visible {tv:?}/{gv:?}, lines {tn}/{gn}, only TF {}, only JMC {}",
                row.jmc,
                tset.difference(&gset).count(),
                gset.difference(&tset).count()
            ));
        }
        note!("G1-gate2\t{}\t{tn}\t{gn}\t{}", row.jmc, if ok { "equal" } else { "DIFFERENT" });
    }
    for b in &bad {
        note!("G1-gate2\tDIFF\t{b}");
    }
    assert!(bad.is_empty(), "conformance: G1: gate (2): {} differences", bad.len());
    assert_eq!(total, 576, "conformance: G1: the 74 exports' lines");
}

// =========================================================================
// H (the tester's, flagged half; `criteria/H.md` H-2 A3 and C's old side)
// =========================================================================

use crate::conformance::interchange_default_tests::record_cells;
use crate::conformance::record;

/// The cluster's 14 smoke rows' `EVAL_ROW` JSON (`cluster/smoke.rows`).
const SMOKE_ROWS: [&str; 14] = [
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"Stateful/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=1","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=16","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=32","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":524288000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"CompleteFirst/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"CFirstP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=1","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"CFirstP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=16","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n3r3","label":"SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=64","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":1048576000},"run_kind":"timed","family":"a1","knobs":"n=3,r=3","k":[3,3,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a3/double-grant/spec/k3q3","label":"CompleteFirst/Plain/stop=true/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a3","knobs":"k=3,q=3","k":[3,3,null,null],"variant":"mutant:double-grant","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"Gated/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep","rep":0,"tier":{"name":"c600","wall_ms":600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"Enumerator/Ltr/stop=false/Exhaustive/Always/memo=true/Unlimited/precheck=false/instr=false/cut=false/cover=Sweep","rep":0,"tier":{"name":"c600","wall_ms":600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"Explore/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"ExploreP/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/threads=1","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
    r#"{"fixture":"apps/a1/correct/spec/n2r2","label":"ExploreP/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/threads=16","rep":0,"tier":{"name":"c1h","wall_ms":3600000,"mem_kb":262144000},"run_kind":"timed","family":"a1","knobs":"n=2,r=2","k":[2,2,null,null],"variant":"conforming","twin_key":""}"#,
];

/// H-1's excluded cells E (34): the measurement cells, by the rule of
/// `log/dev/H.md` §2.0.
fn h_excluded(header: &[&'static str]) -> BTreeSet<&'static str> {
    const FIXED: [&str; 13] = [
        "proc_wall_ms",
        "pid",
        "rss_sampled_hwm_kb",
        "rss_child_hwm_kb",
        "run_dir",
        "wall_ms",
        "vm_hwm_kb_before",
        "vm_hwm_kb_after",
        "tainted_at_start",
        "cap_ms",
        "cpu_user_ms",
        "cpu_sys_ms",
        "vm_peak_kb",
    ];
    header
        .iter()
        .copied()
        .filter(|c| {
            FIXED.contains(c)
                || c.contains("_time_ms")
                || c.contains("wall_ms")
                || c.contains("vmhwm_kb")
                || c.ends_with("_lock_held_ms")
                || c.ends_with("_lock_wait_ms")
        })
        .collect()
}

/// H-1's identities (rev 1.4): `None` when the record does not fill the six
/// cells; else (I1, I2): `spec_flush_entries + spec_worker_duplicates =
/// spec_complete + spec_blocked`, `spec_flush_entries − spec_merge_duplicates =
/// orders_held`.
fn h_identities(header: &[&'static str], rec: &[String]) -> Option<(bool, bool)> {
    let get = |name: &str| -> Option<i64> {
        let i = header.iter().position(|h| *h == name)?;
        rec[i].parse().ok()
    };
    let (f, w, m) = (
        get("spec_flush_entries")?,
        get("spec_worker_duplicates")?,
        get("spec_merge_duplicates")?,
    );
    let (c, b, o) = (get("spec_complete")?, get("spec_blocked")?, get("orders_held")?);
    Some((f + w == c + b, f - m == o))
}

/// **H A3** (H-2 A, flagged build; under H-1 rev 1.4): on the 14 smoke rows, in
/// one process, the library copy (`record::run_row` on a `Subject` built from
/// the fixture) equals `eval.rs`'s `child_row` on every cell outside E. On a
/// row above one thread `sig_tests` is in E, the three flush counters are
/// checked by I1 and I2 on every run instead of by value, and the old path runs
/// three times: a cell whose three values differ is K-sched there and the
/// copy's value must be one of them. Failing direction: MA3 (one push in the
/// copy's `row_of` changed, a scratch mutant).
#[test]
fn h_a3_the_library_copy_equals_eval() {
    use crate::conformance::eval;
    let header = record::header();
    let e = h_excluded(&header);
    assert_eq!(e.len(), 34, "conformance: H: A3: E has 34 cells");
    const FLUSH: [&str; 3] = [
        "spec_flush_entries",
        "spec_worker_duplicates",
        "spec_merge_duplicates",
    ];
    let (mut compared, mut sched, mut idruns) = (0, 0, 0);
    for json in SMOKE_ROWS {
        let mut spec = eval::row_from_json(json)
            .unwrap_or_else(|| panic!("conformance: H: A3: {json} does not parse"));
        // as the old child `eval_row` does before `child_row` (SVERIFY-P I4-3 R1)
        if matches!(spec.config.engine, GridEngine::SverifyP | GridEngine::ExploreP) {
            spec.config.phase_peaks = true;
        }
        let threads = spec.config.threads;
        let runs = if threads > 1 { 3 } else { 1 };
        let old: Vec<Vec<String>> = (0..runs)
            .map(|_| {
                let row = eval::child_row(&spec, "A3")
                    .unwrap_or_else(|e| panic!("conformance: H: A3: old: {}", e.text()));
                eval::record_of(&row)
            })
            .collect();
        let f = eval::fixture_by_name(&spec.fixture)
            .unwrap_or_else(|e| panic!("conformance: H: A3: {}", e.text()));
        let new = record::run_row(json, "A3", |n| record::Subject {
            name: n.to_owned(),
            config: f.config.clone(),
            visible: f.visible.clone(),
            implementation: f.implementation.clone(),
            specification: f.specification.clone(),
        })
        .unwrap_or_else(|e| panic!("conformance: H: A3: new: {e}"));
        let new = record_cells(&new.record);
        assert_eq!(new.len(), 262, "conformance: H: A3: 262 cells");
        for o in &old {
            assert_eq!(o.len(), 262, "conformance: H: A3: 262 old cells");
        }
        for rec in old.iter().chain(std::iter::once(&new)) {
            if let Some(ids) = h_identities(&header, rec) {
                assert_eq!(ids, (true, true), "conformance: H: A3: {}: I1, I2", spec.fixture);
                idruns += 1;
            }
        }
        for (i, h) in header.iter().enumerate() {
            if e.contains(h) || (threads > 1 && (*h == "sig_tests" || FLUSH.contains(h))) {
                continue;
            }
            let seen: BTreeSet<&String> = old.iter().map(|o| &o[i]).collect();
            if seen.len() > 1 {
                sched += 1;
                assert!(
                    seen.contains(&new[i]),
                    "conformance: H: A3: {}: `{h}` = {} outside {seen:?}",
                    spec.fixture,
                    new[i]
                );
            } else {
                assert_eq!(
                    new[i], old[0][i],
                    "conformance: H: A3: {} ({}): `{h}`",
                    spec.fixture,
                    spec.config.label()
                );
            }
            compared += 1;
        }
    }
    // 14 rows × 228, less `sig_tests` and the three flush counters on the 5
    // rows above one thread
    assert_eq!(compared, 14 * 228 - 5 * 4, "conformance: H: A3: cells compared");
    assert!(idruns >= 4, "conformance: H: A3: identity runs {idruns}");
    note!("H-A3\trows 14\tcells {compared}\tK-sched cells {sched}\tidentity runs {idruns}");
}

/// **H C, the old side** (H-2 C; ignored, one point per process): with
/// `H_C_NAME` and `H_C_SIDE`, the fixture's side under its own `Config` with
/// `keep_going_after_error`, by plain Must, printed as `HCOUNT\t<name>\t<side>\t<execs>\t<block>`;
/// a no-op without `H_C_NAME`.
#[test]
#[ignore]
fn h_c_old_count() {
    use std::io::Write as _;
    let Ok(name) = std::env::var("H_C_NAME") else {
        return;
    };
    let side = std::env::var("H_C_SIDE").unwrap_or_else(|_| panic!("conformance: H: C: H_C_SIDE"));
    let f = crate::conformance::eval::fixture_by_name(&name)
        .unwrap_or_else(|e| panic!("conformance: H: C: {}", e.text()));
    let mut cfg = f.config.clone();
    cfg.keep_going_after_error = true;
    let p = match side.as_str() {
        "spec" => f.specification.clone(),
        "impl" => f.implementation.clone(),
        other => panic!("conformance: H: C: side `{other}`"),
    };
    let s = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || crate::verify(cfg, move || p()))
        .unwrap_or_else(|e| panic!("conformance: H: C: spawn: {e}"))
        .join()
        .unwrap_or_else(|_| panic!("conformance: H: C: {name} {side} panicked"));
    let line = format!("HCOUNT\t{name}\t{side}\t{}\t{}\n", s.execs, s.block);
    let mut out = std::io::stdout().lock();
    out.write_all(line.as_bytes())
        .unwrap_or_else(|e| panic!("conformance: H: C: stdout: {e}"));
    out.flush()
        .unwrap_or_else(|e| panic!("conformance: H: C: stdout: {e}"));
}
