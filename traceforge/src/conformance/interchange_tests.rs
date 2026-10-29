//! `J3`'s tests (the tester's; `criteria/J3.md` J3-6). The lead creates this
//! module empty so that `mod.rs` can name it; every test in it is the tester's.
//!
//! Derived first (`log/dev/J3.derived.md`, its gate-3 addendum): T1–T17. The
//! default suite holds the unit and in-process tests; the 74-row tests (T8 P-EQ,
//! T9 P-RND, T10 the joins) and the command as a process (T16) are ignored and run
//! one per invocation. Their directories come from the environment so that a
//! failing direction runs on scratch copies: `J3_OUT` (the exports; default the
//! place of record `plan/jmc-must/log/runs/J3/`), `J3_GOLDEN` (JMC's files; default
//! `plan/jmc-must/log/runs/J4/`, read-only), `J3_CONF_JOIN` (the binary; default
//! `target/debug/conf-join`).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use serde_json::Value;

use crate::conformance::compact::CompactSummary;
use crate::conformance::config::{ConfBuilder, ConfConfig, Engine, IndexKind};
use crate::conformance::ctx::{CompletionSink, ConfMode, SinkVerdict};
use crate::conformance::grid::{
    a3_a2_encoders, apps_fixtures, Fixture, Grant, GridConfig, GridEngine, Msg, Prog, Rep, Req,
};
use crate::conformance::interchange::{
    conf_join, export, model_of, normal_line, EncVal, Encoders, ExportError, ExportHeader,
    ExportStats, JoinReport, MissClass, SummaryEncode, Verdict,
};
use crate::conformance::morphism::Status;
use crate::conformance::obs::Obs;
use crate::conformance::stateful::{enumerate, EnumRun};
use crate::exec_graph::ExecutionGraph;
use crate::{thread, Config, ConsType};

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

/// A recreated scratch directory under the system temp dir (`TMPDIR`).
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("j3-tests-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("conformance: J3: a scratch directory");
    d
}

fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
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

/// A file's header and its summary lines as written.
fn read_jsonl(path: &Path) -> (Value, Vec<String>) {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("conformance: J3: {}: {e}", path.display()));
    let mut it = text.lines();
    let head: Value = serde_json::from_str(it.next().expect("conformance: J3: a header"))
        .unwrap_or_else(|e| panic!("conformance: J3: {}: the header: {e}", path.display()));
    (head, it.map(str::to_owned).collect())
}

fn visible_of(head: &Value) -> Vec<String> {
    head["visible"]
        .as_array()
        .expect("conformance: J3: a visible list")
        .iter()
        .map(|v| v.as_str().unwrap().to_owned())
        .collect()
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
    let stats = export(&cc, &p, &header, &a3_a2_encoders(), &path)
        .unwrap_or_else(|e| panic!("conformance: J3: export of {}: {e}", row.jmc));
    (path, stats)
}

// =========================================================================
// T1, T2: the encoder (J3-1)
// =========================================================================

fn enc<T: SummaryEncode>(v: &T) -> String {
    v.encode()
        .expect("conformance: J3: an A3/A2 value encodes")
        .render()
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
    // E4
    assert!(EncVal::int(i64::MAX).is_ok());
    assert!(EncVal::int(i64::MIN).is_ok());
    assert!(EncVal::int(u64::MAX).is_err(), "conformance: J3: E4");
    assert!(
        EncVal::int(i64::MAX as u64 + 1).is_err(),
        "conformance: J3: E4"
    );
    assert!(
        Grant(usize::MAX, 0).encode().is_err(),
        "conformance: J3: E4 through a type"
    );
}

// =========================================================================
// Small programs: T3 (E5), T4 (⊥, U16), T5 (the header), T7 (X4)
// =========================================================================

/// A configuration for a small program: FIFO, seed 0, the given names, the
/// stateful engine under `Set`.
fn small_cc(names: &[&str], model: ConsType) -> ConfConfig {
    ConfBuilder::new()
        .config(Config::builder().with_cons_type(model).with_seed(0).build())
        .visible_threads(names.iter().map(|s| (*s).to_owned()))
        .engine(Engine::Stateful)
        .index(IndexKind::Set)
        .build()
        .expect("conformance: J3: a small configuration")
}

fn header(program: &str) -> ExportHeader {
    ExportHeader {
        program: program.to_owned(),
        size: "k1".to_owned(),
    }
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

/// A visible value of a type no encoder is registered for: `b` receives a `u64`.
fn unregistered_program() -> Prog {
    Arc::new(|| {
        let b = named("b", || {
            let _: u64 = crate::recv_msg_block();
        });
        let tb = b.thread().id();
        named("a", move || crate::send_msg(tb, 7u64));
    })
}

/// **T3** (E5, X4): an export whose visible word holds a `u64` (no encoder) is
/// refused naming the type; with no file at the path none is created, with one
/// it is left byte for byte; no `.tmp` either way. Failing direction: a fallback
/// to `Debug` text; the file opened before the run.
#[test]
fn t3_an_unregistered_type_refuses_the_export() {
    let dir = scratch("t3");
    let path = dir.join("u.jsonl");
    let tmp = dir.join("u.jsonl.tmp");
    let cc = small_cc(&["a", "b"], ConsType::FIFO);
    let r = export(
        &cc,
        &unregistered_program(),
        &header("t3"),
        &a3_a2_encoders(),
        &path,
    );
    match &r {
        Err(ExportError::Unregistered { type_name }) => {
            assert!(
                type_name.contains("u64"),
                "conformance: J3: E5 names {type_name}"
            )
        }
        other => panic!("conformance: J3: E5: {other:?}"),
    }
    assert!(
        !path.exists() && !tmp.exists(),
        "conformance: J3: X4: a file after a refusal"
    );
    std::fs::write(&path, "earlier\n").unwrap();
    let r = export(
        &cc,
        &unregistered_program(),
        &header("t3"),
        &a3_a2_encoders(),
        &path,
    );
    assert!(matches!(r, Err(ExportError::Unregistered { .. })));
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        "earlier\n",
        "conformance: J3: X4"
    );
    assert!(!tmp.exists(), "conformance: J3: X4: a .tmp behind");
    // the same program with `u64` registered nowhere but A3's types present: still refused
    let only_a3 = Encoders::new().register::<Msg>().register::<Grant>();
    assert!(matches!(
        export(&cc, &unregistered_program(), &header("t3"), &only_a3, &path),
        Err(ExportError::Unregistered { .. })
    ));
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
    let st = export(
        &cc,
        &bottom_program(),
        &header("bottom"),
        &a3_a2_encoders(),
        &path,
    )
    .unwrap();
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
    let st = export(
        &cc,
        &wide_program(),
        &header("wide"),
        &a3_a2_encoders(),
        &path,
    )
    .unwrap();
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
    let r = export(
        &small_cc(&["a"], ConsType::FIFO),
        &asserting,
        &header("assert"),
        &a3_a2_encoders(),
        &path,
    );
    assert!(
        matches!(r, Err(ExportError::SpecErrors(_))),
        "conformance: J3: {r:?}"
    );
    assert!(!path.exists());
}

/// **T5** (X3): the header — the names sorted and deduplicated from an unsorted
/// list with a repeat; `FIFO` → `p2p`; every other `ConsType` refused by name
/// (`model_of`, and an export under `Bag` leaves no file); `program`/`size` as
/// given; no `seed`, `iterations` or `n`; the key order JMC writes. Failing
/// direction: the configuration's order kept.
#[test]
#[allow(deprecated)]
fn t5_the_header() {
    let dir = scratch("t5");
    let path = dir.join("h.jsonl");
    let cc = small_cc(&["b", "a", "b"], ConsType::FIFO);
    export(
        &cc,
        &bottom_program(),
        &header("apps/x:impl"),
        &a3_a2_encoders(),
        &path,
    )
    .unwrap();
    let text = std::fs::read_to_string(&path).unwrap();
    let first = text.lines().next().unwrap();
    assert_eq!(
        first,
        r#"{"format":1,"tool":"traceforge","program":"apps/x:impl","size":"k1","visible":["a","b"],"model":"p2p","enumeration":"complete","encoding":1}"#
    );
    assert_eq!(model_of(ConsType::FIFO), Ok("p2p"));
    for c in [
        ConsType::MO,
        ConsType::Bag,
        ConsType::WB,
        ConsType::CD,
        ConsType::Causal,
        ConsType::Mailbox,
    ] {
        match model_of(c) {
            Err(ExportError::Model(name)) => assert_eq!(name, format!("{c:?}")),
            other => panic!("conformance: J3: {c:?}: {other:?}"),
        }
    }
    let p2 = dir.join("bag.jsonl");
    let r = export(
        &small_cc(&["a", "b"], ConsType::Bag),
        &bottom_program(),
        &header("bag"),
        &a3_a2_encoders(),
        &p2,
    );
    assert!(matches!(r, Err(ExportError::Model(_))) && !p2.exists());
    let mut not_set = small_cc(&["a", "b"], ConsType::FIFO);
    not_set.index = IndexKind::Current;
    assert_eq!(
        export(
            &not_set,
            &bottom_program(),
            &header("x"),
            &a3_a2_encoders(),
            &p2
        ),
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

/// A value by hand: the four types' encoders, by downcast.
fn hand_value(v: &crate::msg::Val) -> String {
    let a = v.as_any_ref();
    if let Some(x) = a.downcast_ref::<Msg>() {
        enc(x)
    } else if let Some(x) = a.downcast_ref::<Grant>() {
        enc(x)
    } else if let Some(x) = a.downcast_ref::<Req>() {
        enc(x)
    } else if let Some(x) = a.downcast_ref::<Rep>() {
        enc(x)
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
        export(
            &cc,
            &bottom_program(),
            &header("x4"),
            &a3_a2_encoders(),
            &path,
        )
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
        export(
            &cc,
            &bottom_program(),
            &header("x4"),
            &a3_a2_encoders(),
            &fresh,
        )
    }));
    assert!(r.is_err());
    assert!(!fresh.exists() && !dir.join("x4-none.jsonl.tmp").exists());
}

// =========================================================================
// The reader: T11–T15, T17 (scratch files)
// =========================================================================

const AB: &str = r#"{"format":1,"tool":"t","program":"p","size":"s","visible":["a","b"],"model":"p2p","enumeration":"complete","encoding":1}"#;

/// A header with `enumeration` set (and the rest as `AB`).
fn head_with(enumeration: &str) -> String {
    AB.replace("\"complete\"", &format!("\"{enumeration}\""))
}

/// Writes `lines` under `head` to `dir/name`.
fn file<S: AsRef<str>>(dir: &Path, name: &str, head: &str, lines: &[S]) -> PathBuf {
    let p = dir.join(name);
    let mut text = format!("{head}\n");
    for l in lines {
        text.push_str(l.as_ref());
        text.push('\n');
    }
    std::fs::write(&p, text).unwrap();
    p
}

/// A line over names `a`, `b`: `a` sends `Acq(0)`, `b` receives it; `ab` the
/// count of `a`'s events before `b`'s receive.
fn ab_line(ab: u32) -> String {
    format!(
        r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{{"s":{{"t":"Acq","f":[0]}}}}],"b":[{{"r":{{"t":"Acq","f":[0]}}}}]}},"counts":[0,{ab}]}}"#
    )
}

fn join_ok(spec: &Path, imp: &Path) -> JoinReport {
    conf_join(spec, imp).unwrap_or_else(|e| panic!("conformance: J3: refused: {e}"))
}

fn join_err(spec: &Path, imp: &Path) -> String {
    match conf_join(spec, imp) {
        Err(e) => e.to_string(),
        Ok(r) => panic!("conformance: J3: accepted: {}", r.render()),
    }
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

/// **T12** (R1, R2; rulings Q8, Q9): the reader's refusals, each on a scratch
/// file, each naming the file (and the line where one is at fault); the two
/// messages of Q9 distinct. Failing direction: a refusal removed (the case
/// accepted).
#[test]
fn t12_the_readers_refusals() {
    let dir = scratch("t12");
    let ok = ab_line(1);
    let spec = file(&dir, "spec.jsonl", AB, &[&ok]);
    let line = |name: &str, l: &str| file(&dir, name, AB, &[l]);
    let cases: Vec<(&str, PathBuf, PathBuf, &str)> = vec![
        (
            "format 2",
            spec.clone(),
            file(
                &dir,
                "f2.jsonl",
                &AB.replace("\"format\":1", "\"format\":2"),
                &[&ok],
            ),
            "`format` is not 1",
        ),
        (
            "encoding 2",
            spec.clone(),
            file(
                &dir,
                "e2.jsonl",
                &AB.replace("\"encoding\":1", "\"encoding\":2"),
                &[&ok],
            ),
            "`encoding` is not 1",
        ),
        (
            "unequal visible",
            spec.clone(),
            file(
                &dir,
                "v.jsonl",
                &AB.replace(r#"["a","b"]"#, r#"["a","c"]"#),
                &[] as &[&str],
            ),
            "`visible` lists differ",
        ),
        (
            "a sampled specification",
            file(&dir, "ss.jsonl", &head_with("sampled"), &[&ok]),
            spec.clone(),
            "not `complete`",
        ),
        (
            "a bounded specification",
            file(&dir, "sb.jsonl", &head_with("bounded"), &[&ok]),
            spec.clone(),
            "not `complete`",
        ),
        (
            "an aborted specification",
            file(&dir, "sa.jsonl", &head_with("aborted"), &[&ok]),
            spec.clone(),
            "not `complete`",
        ),
        (
            "a missing name key",
            spec.clone(),
            line(
                "mk.jsonl",
                &ok.replace(r#""b":"done""#, "")
                    .replace("{\"a\":\"done\",}", "{\"a\":\"done\"}"),
            ),
            "not the visible names",
        ),
        (
            "an extra name key",
            spec.clone(),
            line(
                "xk.jsonl",
                &ok.replace(r#""b":"done"}"#, r#""b":"done","c":"done"}"#),
            ),
            "not the visible names",
        ),
        (
            "an unknown status",
            spec.clone(),
            line(
                "us.jsonl",
                &ok.replace(r#""a":"done""#, r#""a":"finished""#),
            ),
            "unknown status",
        ),
        (
            "an observation key",
            spec.clone(),
            line("ok.jsonl", &ok.replace(r#"{"s":{"t""#, r#"{"x":{"t""#)),
            "is not {\"s\":V}",
        ),
        (
            "counts too short",
            spec.clone(),
            line("cs.jsonl", &ok.replace("[0,1]", "[0]")),
            "`counts` has 1 entries, not 2",
        ),
        (
            "counts too long",
            spec.clone(),
            line("cl.jsonl", &ok.replace("[0,1]", "[0,1,0]")),
            "`counts` has 3 entries, not 2",
        ),
        (
            "a count above the word",
            spec.clone(),
            line("ca.jsonl", &ok.replace("[0,1]", "[0,2]")),
            "exceeds the length 1",
        ),
        (
            "a float",
            spec.clone(),
            line("fl.jsonl", &ok.replace(r#"[0]}}],"b""#, r#"[0.5]}}],"b""#)),
            "invalid in format version 1",
        ),
        (
            "1.0",
            spec.clone(),
            line("f1.jsonl", &ok.replace(r#"[0]}}],"b""#, r#"[1.0]}}],"b""#)),
            "invalid in format version 1",
        ),
        (
            "null as a value",
            spec.clone(),
            line(
                "nu.jsonl",
                &ok.replace(r#"{"s":{"t":"Acq","f":[0]}}"#, r#"{"s":null}"#),
            ),
            "is not {\"s\":V}",
        ),
        (
            "null inside a value",
            spec.clone(),
            line("ni.jsonl", &ok.replace(r#"[0]}}],"b""#, r#"[null]}}],"b""#)),
            "`null` other than ⊥ is invalid in format version 1",
        ),
        (
            "an object without t",
            spec.clone(),
            line(
                "ot.jsonl",
                &ok.replace(r#"{"s":{"t":"Acq","f":[0]}}"#, r#"{"s":{"f":[0]}}"#),
            ),
            "invalid in format version 1",
        ),
        (
            "a map",
            spec.clone(),
            line(
                "mp.jsonl",
                &ok.replace(
                    r#"{"s":{"t":"Acq","f":[0]}}"#,
                    r#"{"s":{"t":"Acq","f":[0],"k":1}}"#,
                ),
            ),
            "invalid in format version 1",
        ),
        (
            "a string",
            spec.clone(),
            line("st.jsonl", &ok.replace(r#"[0]}}],"b""#, r#"["x"]}}],"b""#)),
            "a string is not supported by J3",
        ),
        (
            "a boolean",
            spec.clone(),
            line("bo.jsonl", &ok.replace(r#"[0]}}],"b""#, r#"[true]}}],"b""#)),
            "a boolean is not supported by J3",
        ),
        (
            "a list",
            spec.clone(),
            line("li.jsonl", &ok.replace(r#"[0]}}],"b""#, r#"[[0]]}}],"b""#)),
            "a list is not supported by J3",
        ),
        (
            "an integer above i64",
            spec.clone(),
            line(
                "ib.jsonl",
                &ok.replace(r#"[0]}}],"b""#, r#"[9223372036854775808]}}],"b""#),
            ),
            "invalid in format version 1",
        ),
        ("not JSON", spec.clone(), line("nj.jsonl", "{"), "not JSON"),
        (
            "an empty file",
            spec.clone(),
            {
                let p = dir.join("empty.jsonl");
                std::fs::write(&p, "").unwrap();
                p
            },
            "the file is empty",
        ),
    ];
    let mut seen_messages = BTreeSet::new();
    for (what, s, i, want) in &cases {
        let e = join_err(s, i);
        assert!(
            e.contains(want),
            "conformance: J3: {what}: `{e}` lacks `{want}`"
        );
        if *what != "unequal visible" {
            let blamed = if e.contains(&s.display().to_string()) {
                s
            } else {
                i
            };
            assert!(
                e.starts_with(&blamed.display().to_string()),
                "conformance: J3: {what}: no file named: {e}"
            );
        }
        if *what != "unequal visible"
            && !what.ends_with("specification")
            && *what != "an empty file"
        {
            assert!(
                e.contains(": line "),
                "conformance: J3: {what}: no line number: {e}"
            );
        }
        seen_messages.insert(want.to_string());
    }
    assert!(seen_messages
        .iter()
        .any(|m| m.contains("not supported by J3")));
    assert!(seen_messages
        .iter()
        .any(|m| m.contains("invalid in format version 1")));
}

/// The six cases of T13 and of T16 (c)–(h): a `sampled`, `bounded` or `aborted`
/// implementation, all covered or with one uncovered line, against a
/// specification holding `ab_line(1)`: (name, spec, impl, the verdict line, the
/// uncovered lines, the exit code).
fn label_cases(dir: &Path) -> Vec<(String, PathBuf, PathBuf, String, Vec<String>, u8)> {
    let spec = file(dir, "lspec.jsonl", AB, &[&ab_line(1)]);
    let mut out = Vec::new();
    for (en, suffix) in [
        ("sampled", " (sampled)"),
        ("bounded", " (partial)"),
        ("aborted", " (partial)"),
    ] {
        let covered = file(
            dir,
            &format!("{en}-covered.jsonl"),
            &head_with(en),
            &[&ab_line(1)],
        );
        let word = if en == "sampled" {
            "no verdict"
        } else {
            "conforms"
        };
        out.push((
            format!("{en} covered"),
            spec.clone(),
            covered,
            format!("verdict: {word}{suffix}"),
            vec![],
            0,
        ));
        let unc = file(
            dir,
            &format!("{en}-uncovered.jsonl"),
            &head_with(en),
            &[&ab_line(1), &ab_line(0)],
        );
        out.push((
            format!("{en} uncovered"),
            spec.clone(),
            unc,
            format!("verdict: violation{suffix}"),
            vec![format!("not-found {}", ab_line(0))],
            1,
        ));
    }
    out
}

/// **T13** (R1): through the library, the six cases' verdict, label, uncovered
/// lines and exit code. Failing directions: a sampled all-covered result read
/// `conforms`; the `(partial)` label dropped for `aborted`.
#[test]
fn t13_the_sampled_and_partial_labels() {
    let dir = scratch("t13");
    for (name, spec, imp, verdict, uncovered, exit) in label_cases(&dir) {
        let r = join_ok(&spec, &imp);
        let text = r.render();
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines[2], verdict, "conformance: J3: {name}");
        assert_eq!(
            lines[3],
            format!("uncovered: {}", uncovered.len()),
            "conformance: J3: {name}"
        );
        let got: Vec<String> = lines[4..].iter().map(|s| (*s).to_owned()).collect();
        assert_eq!(got, uncovered, "conformance: J3: {name}");
        assert_eq!(r.exit_code(), exit, "conformance: J3: {name}");
        assert_eq!(
            r.verdict == Verdict::Conforms,
            verdict.starts_with("verdict: conforms")
        );
    }
}

/// **T14** (R4, ruling Q4): the result does not depend on the lines' order or
/// on `n`; a repeated line is refused naming both line numbers — once byte-equal,
/// once differing only by `n`. Failing directions: the duplicate check removed;
/// one line number reported.
#[test]
fn t14_set_semantics_and_the_duplicate_refusal() {
    let dir = scratch("t14");
    let l1 = ab_line(1);
    let l0 = ab_line(0);
    let spec = file(&dir, "spec.jsonl", AB, &[&l1]);
    let a = join_ok(&spec, &file(&dir, "i1.jsonl", AB, &[&l1, &l0]));
    let b = join_ok(&spec, &file(&dir, "i2.jsonl", AB, &[&l0, &l1]));
    let with_n = |l: &str, n: u32| format!("{},\"n\":{n}}}", &l[..l.len() - 1]);
    let c = join_ok(
        &spec,
        &file(&dir, "i3.jsonl", AB, &[&with_n(&l0, 7), &with_n(&l1, 3)]),
    );
    let set = |r: &JoinReport| {
        r.uncovered
            .iter()
            .map(|(c, l)| (c.name(), l.clone()))
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(
        (a.verdict, set(&a)),
        (b.verdict, set(&b)),
        "conformance: J3: R4 order"
    );
    assert_eq!(
        (a.verdict, set(&a)),
        (c.verdict, set(&c)),
        "conformance: J3: R4 n"
    );
    // the specification's order and `n` likewise
    let spec2 = file(&dir, "spec2.jsonl", AB, &[&with_n(&l1, 99)]);
    assert_eq!(
        set(&join_ok(&spec2, &file(&dir, "i4.jsonl", AB, &[&l1, &l0]))),
        set(&a)
    );
    // duplicates: byte-equal, and differing only by `n`
    for (name, lines) in [
        ("byte-equal", vec![l1.clone(), l0.clone(), l1.clone()]),
        (
            "by n only",
            vec![with_n(&l1, 1), l0.clone(), with_n(&l1, 2)],
        ),
    ] {
        let refs: Vec<&str> = lines.iter().map(String::as_str).collect();
        let imp = file(
            &dir,
            &format!("dup-{}.jsonl", name.replace(' ', "-")),
            AB,
            &refs,
        );
        let e = join_err(&spec, &imp);
        assert!(
            e.contains("line 4") && e.contains("repeats line 2"),
            "conformance: J3: Q4 {name}: {e}"
        );
        let in_spec = file(
            &dir,
            &format!("dups-{}.jsonl", name.replace(' ', "-")),
            AB,
            &refs,
        );
        let e = join_err(&in_spec, &spec);
        assert!(
            e.contains("line 4") && e.contains("repeats line 2"),
            "conformance: J3: Q4 {name} (spec): {e}"
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
