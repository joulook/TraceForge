//! The default-build half of the interchange tests (`H`, ruling Q15: the split
//! of `interchange_tests.rs` by the tester): J3's reader tests T12–T14 and G1's
//! generic tests (G-T1, T2, T6, T-P, T7, T7b, T7c, T8, T9), which use no
//! fixture (`Prog` reads `program::Entry`), and H's default-build tests (A1, A2,
//! F, G; `criteria/H.md` H-2). The fixture-based rest stays in
//! `interchange_tests.rs` behind `fixture-tests` and imports the shared helpers
//! from here.

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use serde_json::Value;
use crate::{thread, Config, ConsType};
use crate::conformance::config::{ConfBuilder, ConfConfig, Engine, IndexKind};
use crate::conformance::interchange::{conf_join, encode_generic, export, model_name, normal_line, ExportError, ExportHeader, ExportStats, JoinReport, ThreadName, ThreadNames, Verdict};
use crate::msg::Val;
use crate::program::{run_cli, Entry, Program};

/// Writes a line to stderr (the closed `s5_tests` emission scan forbids the
/// print macros in every file under `conformance/` but its test-only list).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

/// A recreated scratch directory under the system temp dir (`TMPDIR`).
pub(super) fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("j3-tests-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("conformance: J3: a scratch directory");
    d
}
pub(super) fn named<F: FnOnce() + Send + 'static>(n: &str, f: F) -> thread::JoinHandle<()> {
    thread::Builder::new().name(n.to_string()).spawn(f).unwrap()
}
/// A file's header and its summary lines as written.
pub(super) fn read_jsonl(path: &Path) -> (Value, Vec<String>) {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("conformance: J3: {}: {e}", path.display()));
    let mut it = text.lines();
    let head: Value = serde_json::from_str(it.next().expect("conformance: J3: a header"))
        .unwrap_or_else(|e| panic!("conformance: J3: {}: the header: {e}", path.display()));
    (head, it.map(str::to_owned).collect())
}
pub(super) fn visible_of(head: &Value) -> Vec<String> {
    head["visible"]
        .as_array()
        .expect("conformance: J3: a visible list")
        .iter()
        .map(|v| v.as_str().unwrap().to_owned())
        .collect()
}
/// `G1` stage B: the generic export of a `Entry` (J3's hand path is removed).
pub(super) fn ex(
    cc: &ConfConfig,
    p: &Entry,
    h: &ExportHeader,
    path: &Path,
) -> Result<ExportStats, ExportError> {
    let p = Arc::clone(p);
    export(cc, move || p(), h, path)
}
// =========================================================================
// Small programs: T3 (E5), T4 (⊥, U16), T5 (the header), T7 (X4)
// =========================================================================

/// A configuration for a small program: FIFO, seed 0, the given names, the
/// stateful engine under `Set`.
pub(super) fn small_cc(names: &[&str], model: ConsType) -> ConfConfig {
    ConfBuilder::new()
        .config(Config::builder().with_cons_type(model).with_seed(0).build())
        .visible_threads(names.iter().map(|s| (*s).to_owned()))
        .engine(Engine::Stateful)
        .index(IndexKind::Set)
        .build()
        .expect("conformance: J3: a small configuration")
}
pub(super) fn header(program: &str) -> ExportHeader {
    ExportHeader {
        program: program.to_owned(),
        size: "k1".to_owned(),
    }
}
// =========================================================================
// The reader: T11–T15, T17 (scratch files)
// =========================================================================

pub(super) const AB: &str = r#"{"format":1,"tool":"t","program":"p","size":"s","visible":["a","b"],"model":"p2p","enumeration":"complete","encoding":1}"#;
/// A header with `enumeration` set (and the rest as `AB`).
pub(super) fn head_with(enumeration: &str) -> String {
    AB.replace("\"complete\"", &format!("\"{enumeration}\""))
}
/// Writes `lines` under `head` to `dir/name`.
pub(super) fn file<S: AsRef<str>>(dir: &Path, name: &str, head: &str, lines: &[S]) -> PathBuf {
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
pub(super) fn ab_line(ab: u32) -> String {
    format!(
        r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{{"s":{{"t":"Acq","f":[0]}}}}],"b":[{{"r":{{"t":"Acq","f":[0]}}}}]}},"counts":[0,{ab}]}}"#
    )
}
pub(super) fn join_ok(spec: &Path, imp: &Path) -> JoinReport {
    conf_join(spec, imp).unwrap_or_else(|e| panic!("conformance: J3: refused: {e}"))
}
pub(super) fn join_err(spec: &Path, imp: &Path) -> String {
    match conf_join(spec, imp) {
        Err(e) => e.to_string(),
        Ok(r) => panic!("conformance: J3: accepted: {}", r.render()),
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
        // G1-2: a string, a boolean and a list are accepted now (G-T9).
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
        .any(|m| m.contains("invalid in format version 1")));
}
/// The six cases of T13 and of T16 (c)–(h): a `sampled`, `bounded` or `aborted`
/// implementation, all covered or with one uncovered line, against a
/// specification holding `ab_line(1)`: (name, spec, impl, the verdict line, the
/// uncovered lines, the exit code).
pub(super) fn label_cases(dir: &Path) -> Vec<(String, PathBuf, PathBuf, String, Vec<String>, u8)> {
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
// =========================================================================
// G1 (the tester's; `criteria/G1.md` G1-7, `log/dev/G1.derived.md` addendum A)
// =========================================================================
//
// The generic path beside J3's hand path (stage A): the grammar, the
// refusals, hand = generic, `ThreadId`, the preconditions, the shared main,
// the models, the reader's extension; gates (1) and (2) on the 74 (ignored).

fn gen(v: Val) -> Result<String, ExportError> {
    encode_generic(&v, &ThreadNames::new())
}
fn gen_ok<T: crate::msg::Message + 'static>(x: T) -> String {
    let v = Val::new(x);
    let text = format!("{:?}", &*v.val);
    gen(v).unwrap_or_else(|e| panic!("conformance: G1: `{text}` refused: {e}"))
}
#[derive(Clone, Debug, PartialEq)]
struct GUnit;
#[derive(Clone, Debug, PartialEq)]
struct GTup(i32, u8);
#[derive(Clone, Debug, PartialEq)]
struct GRec {
    a: i64,
    b: bool,
}
#[derive(Clone, Debug, PartialEq)]
enum GE {
    U,
    T(String),
    S { x: Vec<u8>, y: Option<u8> },
}
#[derive(Clone, Debug, PartialEq)]
struct GW<T> {
    v: T,
}
#[derive(Clone, Debug, PartialEq)]
struct GSets {
    o: std::collections::BTreeSet<u32>,
    h: HashSet<String>,
}
/// **G-T1** (G1-1): the grammar on real `Debug` renderings, each expected by
/// hand (addendum A3). Failing directions: MU1 (`\u{…}` decoded as code + 1),
/// MU2 (`\0` read as `0`), MU5 (a set left in `Debug` order), MU12 (fields
/// reversed).
#[test]
fn g1_t1_the_grammar() {
    let cases: Vec<(String, &str)> = vec![
        (gen_ok(GUnit), r#"{"t":"GUnit","f":[]}"#),
        (gen_ok(GTup(-3, 7)), r#"{"t":"GTup","f":[-3,7]}"#),
        (
            gen_ok(GRec { a: i64::MIN, b: true }),
            r#"{"t":"GRec","f":[-9223372036854775808,true]}"#,
        ),
        (
            gen_ok(GRec { a: i64::MAX, b: false }),
            r#"{"t":"GRec","f":[9223372036854775807,false]}"#,
        ),
        (gen_ok(GE::U), r#"{"t":"U","f":[]}"#),
        (gen_ok(GE::T("x".to_owned())), r#"{"t":"T","f":["x"]}"#),
        (
            gen_ok(GE::S { x: vec![1, 2], y: None }),
            r#"{"t":"S","f":[[1,2],{"t":"None","f":[]}]}"#,
        ),
        (
            gen_ok(GE::S { x: vec![], y: Some(9) }),
            r#"{"t":"S","f":[[],{"t":"Some","f":[9]}]}"#,
        ),
        (gen_ok(Some(9u8)), r#"{"t":"Some","f":[9]}"#),
        (gen_ok(None::<u8>), r#"{"t":"None","f":[]}"#),
        (gen_ok([1u8, 2, 3]), "[1,2,3]"),
        (gen_ok(VecDeque::from(vec![3i16, 4])), "[3,4]"),
        (gen_ok(Vec::<u8>::new()), "[]"),
        (gen_ok(true), "true"),
        (gen_ok(-5i8), "-5"),
        (gen_ok(Box::new(GTup(1, 0))), r#"{"t":"GTup","f":[1,0]}"#),
        (gen_ok(Arc::new(GE::U)), r#"{"t":"U","f":[]}"#),
        (
            gen_ok(GW { v: GRec { a: 1, b: true } }),
            r#"{"t":"GW","f":[{"t":"GRec","f":[1,true]}]}"#,
        ),
        // sets: by the encoded bytes ("10" < "2"), not by `Ord`
        (
            gen_ok(GSets {
                o: [2u32, 10].into_iter().collect(),
                h: ["b", "a", "c"].iter().map(|s| s.to_string()).collect(),
            }),
            r#"{"t":"GSets","f":[[10,2],["a","b","c"]]}"#,
        ),
    ];
    for (got, want) in &cases {
        assert_eq!(got, want, "conformance: G1: grammar");
    }
    // strings: the expected bytes are serde_json's rendering of the original
    let strings = [
        "a\"b\\c\nd\te\rf\0g'h",
        "\u{1}\u{7f}\u{200b}x",
        "\u{301}x",
        "x\u{301}",
        "é\u{1F600}",
        "",
    ];
    for s in strings {
        let dbg = format!("{s:?}");
        let want = serde_json::to_string(s).unwrap();
        assert_eq!(
            gen_ok(s.to_owned()),
            want,
            "conformance: G1: the string {dbg}"
        );
        assert_eq!(gen_ok(s), want, "conformance: G1: the &str {dbg}");
    }
    // pins: the escapes the grammar names are really exercised (rustc 1.98.1)
    let d = format!("{:?}", "\u{1}\u{7f}\u{200b}x");
    assert!(
        d.contains("\\u{1}") && d.contains("\\u{7f}"),
        "conformance: G1: pin: {d}"
    );
    let d0 = format!("{:?}", "a\"b\\c\nd\te\rf\0g'h");
    assert!(
        d0.contains("\\0") && d0.contains("\\\"") && d0.contains("\\\\") && d0.contains("\\n"),
        "conformance: G1: pin: {d0}"
    );
    note!(
        "G-T1\t{} cases\t\\u{{200b}} renders {:?}\tleading U+301 renders {:?}",
        cases.len() + 2 * strings.len(),
        format!("{:?}", "\u{200b}"),
        format!("{:?}", "\u{301}x")
    );
}
/// A value whose `Debug` is the given text verbatim (a hand-written `Debug`).
#[derive(Clone, PartialEq)]
struct Raw(&'static str);
impl std::fmt::Debug for Raw {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
/// `finish_non_exhaustive`, as a hand `Debug` might use it.
#[derive(Clone, PartialEq)]
struct Hidden {
    a: i32,
    b: i32,
}
impl std::fmt::Debug for Hidden {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let _ = self.b;
        f.debug_struct("Hidden").field("a", &self.a).finish_non_exhaustive()
    }
}
#[derive(Clone, Debug, PartialEq)]
struct Holder {
    k: u8,
    m: HashMap<u8, u8>,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Pair2(u8);
/// Two values that render alike: `Debug` ignores the field `PartialEq` and
/// `Hash` compare (P3).
#[derive(Clone, PartialEq, Eq, Hash)]
struct Same(u8);
impl std::fmt::Debug for Same {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let _ = self.0;
        f.write_str("Same")
    }
}
/// The kind of a refusal: `Refused` with its `what`, `Unparsed`, or another.
fn refusal(v: Val) -> String {
    let text = format!("{:?}", &*v.val);
    let ty = v.type_name.clone();
    match gen(v) {
        Ok(s) => panic!("conformance: G1: `{text}` accepted as {s}"),
        Err(ExportError::Refused {
            type_name,
            rendering,
            what,
        }) => {
            assert_eq!(type_name, ty, "conformance: G1: the type named");
            assert_eq!(rendering, text, "conformance: G1: the text named");
            format!("refused: {what}")
        }
        Err(ExportError::Unparsed {
            type_name,
            rendering,
            at,
        }) => {
            assert_eq!(type_name, ty, "conformance: G1: the type named");
            assert_eq!(rendering, text, "conformance: G1: the text named");
            assert!(at <= text.len());
            "unparsed".to_owned()
        }
        Err(e) => format!("other: {e:?}"),
    }
}
/// **G-T2** (G1-1): the refusals, each naming the type and the text.
/// Failing directions: MU3 (unknown escapes accepted), MU4 (a map read as a
/// set, values dropped), MU6 (equal encodings in a set), MU7 (`..` skipped),
/// MU8 (a char read as a string), MU9 (a tuple read as a list), MU10 (a float
/// read as an integer), MU11 (the i64 bound removed).
#[test]
fn g1_t2_the_refusals() {
    let mut one = HashMap::new();
    one.insert(1u8, 2u8);
    let cases: Vec<(&str, Val, &str)> = vec![
        ("a map nested in a struct", Val::new(Holder { k: 1, m: one.clone() }), "refused: a map"),
        ("a map", Val::new(one), "refused: a map"),
        ("1.5", Val::new(1.5f64), "refused: a float"),
        ("1e-7", Val::new(1e-7f64), "refused: a float"),
        ("NaN", Val::new(f64::NAN), "refused: a float"),
        ("inf", Val::new(f64::INFINITY), "refused: a float"),
        ("-inf", Val::new(f64::NEG_INFINITY), "refused: a float"),
        ("a float in a struct", Val::new(GW { v: 2.0f32 }), "refused: a float"),
        ("a char", Val::new('x'), "refused: a char"),
        ("a char in a struct", Val::new(GW { v: 'y' }), "refused: a char"),
        ("a tuple", Val::new((1u8, 2u8)), "refused: an anonymous tuple"),
        ("the unit", Val::new(()), "refused: an anonymous tuple"),
        ("a tuple in a variant", Val::new(Some((1u8, 2u8))), "refused: an anonymous tuple"),
        (
            "finish_non_exhaustive",
            Val::new(Hidden { a: 1, b: 2 }),
            "refused: `..` (a non-exhaustive rendering)",
        ),
        (
            "an empty finish_non_exhaustive",
            Val::new(Raw("Hidden { .. }")),
            "refused: `..` (a non-exhaustive rendering)",
        ),
        ("PhantomData", Val::new(std::marker::PhantomData::<u8>), "unparsed"),
        ("a Duration", Val::new(std::time::Duration::from_millis(1500)), "refused: a float"),
        ("a range", Val::new(0..5i32), "refused: a range"),
        ("a hand Debug", Val::new(Raw("<x>")), "unparsed"),
        ("a \\x escape", Val::new(Raw(r#"S("\x01")"#)), "unparsed"),
        ("an empty \\u{}", Val::new(Raw(r#"S("\u{}")"#)), "unparsed"),
        ("a surrogate", Val::new(Raw(r#"S("\u{d800}")"#)), "unparsed"),
        ("above U+10FFFF", Val::new(Raw(r#"S("\u{110000}")"#)), "unparsed"),
        ("seven hex digits", Val::new(Raw(r#"S("\u{0000041}")"#)), "unparsed"),
        ("a path", Val::new(Raw("a::b")), "unparsed"),
        ("u64::MAX", Val::new(u64::MAX), "refused: an integer outside signed 64 bits"),
        ("i64::MAX + 1", Val::new(i64::MAX as u64 + 1), "refused: an integer outside signed 64 bits"),
        ("u128::MAX", Val::new(u128::MAX), "refused: an integer outside signed 64 bits"),
        ("i128::MIN", Val::new(i128::MIN), "refused: an integer outside signed 64 bits"),
        (
            "a set with two equal encodings",
            Val::new([Same(1), Same(2)].into_iter().collect::<HashSet<Same>>()),
            "refused: a set with two equal encodings",
        ),
    ];
    let mut bad = Vec::new();
    for (what, v, want) in cases {
        let got = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| refusal(v)))
            .unwrap_or_else(|p| {
                p.downcast_ref::<String>()
                    .cloned()
                    .unwrap_or_else(|| "a panic".to_owned())
            });
        if got != want {
            bad.push(format!("{what}: {got} (want {want})"));
        }
    }
    // the control: a set of distinct encodings is accepted
    assert_eq!(
        gen_ok([Pair2(2), Pair2(1)].into_iter().collect::<HashSet<Pair2>>()),
        r#"[{"t":"Pair2","f":[1]},{"t":"Pair2","f":[2]}]"#
    );
    assert!(bad.is_empty(), "conformance: G1: refusals:\n  {}", bad.join("\n  "));
}
// ------------------------------------------------------------ ThreadId --

#[derive(Clone, Debug, PartialEq)]
struct Who(crate::ThreadId);
fn tid(n: u32) -> crate::ThreadId {
    crate::ThreadId::try_from(format!("t{n}"))
        .unwrap_or_else(|_| panic!("conformance: G1: t{n} is no ThreadId"))
}
mod lookalike {
    /// A user type with the reserved shape (P2).
    #[derive(Clone, Debug, PartialEq)]
    pub(super) struct ThreadId {
        pub(super) opaque_id: u32,
    }
}
/// `b` receives a `Who` from `a`, which names thread `who(…)` (chosen in main).
fn who_program<F>(prefix: F, payload: fn(crate::ThreadId, Option<crate::ThreadId>) -> Who) -> Entry
where
    F: Fn() -> Option<crate::ThreadId> + Send + Sync + 'static,
{
    Arc::new(move || {
        let extra = prefix();
        let b = named("b", || {
            let _: Who = crate::recv_msg_block();
        });
        let tb = b.thread().id();
        named("a", move || {
            crate::send_msg(tb, payload(thread::current().id(), extra));
        });
    })
}
/// **G-T6** (G1-1, P2): `ThreadId` becomes the thread's name. (a) unit level:
/// a name, and the three refusals; (b) the F41 shape: the implementation
/// spawns an invisible thread first, so `a`'s raw id differs (pinned by the
/// stateful engine's report), and the two exports' bodies are equal; (c) one id
/// named `x` or `y` by a `nondet()`; (d) an unnamed thread; (e) an id absent
/// from the run. Failing directions: MU13 (an absent id rendered as its
/// number), MU14 (the unnamed check removed), MU15 (the conflict check removed),
/// MU20 (every id rendered as its number).
#[test]
fn g1_t6_thread_ids() {
    // (a)
    let mut names = ThreadNames::new();
    names.insert(3, ThreadName::Named("c0".to_owned()));
    names.insert(4, ThreadName::Unnamed);
    names.insert(5, ThreadName::Conflict("x".to_owned(), "y".to_owned()));
    assert_eq!(
        encode_generic(&Val::new(tid(3)), &names).unwrap(),
        r#""c0""#
    );
    assert_eq!(
        encode_generic(&Val::new(Who(tid(3))), &names).unwrap(),
        r#"{"t":"Who","f":["c0"]}"#
    );
    let reason = |n: u32| match encode_generic(&Val::new(Who(tid(n))), &names) {
        Err(ExportError::Thread { type_name, reason }) => {
            assert!(type_name.ends_with("Who"), "conformance: G1: {type_name}");
            reason
        }
        other => panic!("conformance: G1: t{n}: {other:?}"),
    };
    assert!(
        reason(4).contains("has no name"),
        "conformance: G1: {}",
        reason(4)
    );
    assert!(reason(5).contains("named `x` in one graph and `y` in another"));
    assert!(reason(9).contains("is not a thread of the run"));
    // P2: the lookalike is read as a thread identity
    assert!(matches!(
        encode_generic(&Val::new(lookalike::ThreadId { opaque_id: 99 }), &names),
        Err(ExportError::Thread { .. })
    ));
    assert_eq!(
        encode_generic(&Val::new(lookalike::ThreadId { opaque_id: 3 }), &names).unwrap(),
        r#""c0""#,
        "conformance: G1: P2's undetectable case"
    );

    // (b) the F41 shape
    let spec = who_program(|| None, |me, _| Who(me));
    let imp = who_program(
        || {
            let _ = thread::spawn(|| {});
            None
        },
        |me, _| Who(me),
    );
    let cc = small_cc(&["a", "b"], ConsType::FIFO);
    let typed = crate::conformance::stateful::run_with(&cc, &imp, &spec, false);
    assert!(
        typed.counters.reports > 0,
        "conformance: G1: pin: the raw ids must differ (F41 shape)"
    );
    let dir = scratch("g1-t6");
    let (ps, pi) = (dir.join("s.jsonl"), dir.join("i.jsonl"));
    let (s2, i2) = (spec.clone(), imp.clone());
    export(&cc, move || s2(), &header("t6s"), &ps).expect("conformance: G1: (b) spec");
    export(&cc, move || i2(), &header("t6i"), &pi).expect("conformance: G1: (b) impl");
    let (_, ls) = read_jsonl(&ps);
    let (_, li) = read_jsonl(&pi);
    assert_eq!(ls, li, "conformance: G1: the F41 shape exports equal bodies");
    assert_eq!(ls.len(), 1);
    assert!(
        ls[0].contains(r#"{"s":{"t":"Who","f":["a"]}}"#),
        "conformance: G1: {}",
        ls[0]
    );
    assert!(matches!(join_ok(&ps, &pi).verdict, Verdict::Conforms));

    // (c) one id, two names
    let conflict = who_program(
        || {
            let nm = if crate::nondet() { "x" } else { "y" };
            Some(named(nm, || {}).thread().id())
        },
        |_, extra| Who(extra.unwrap()),
    );
    // (d) an unnamed thread
    let unnamed = who_program(
        || Some(thread::spawn(|| {}).thread().id()),
        |_, extra| Who(extra.unwrap()),
    );
    // (e) an id absent from the run
    let absent = who_program(|| None, |_, _| Who(tid(99)));
    for (what, p, want) in [
        ("(c)", conflict, "in one graph and"),
        ("(d)", unnamed, "has no name"),
        ("(e)", absent, "t99 is not a thread of the run"),
    ] {
        let path = dir.join("r.jsonl");
        let r = export(&cc, move || p(), &header("t6"), &path);
        match r {
            Err(ExportError::Thread { reason, .. }) => {
                assert!(reason.contains(want), "conformance: G1: {what}: {reason}")
            }
            other => panic!("conformance: G1: {what}: {other:?}"),
        }
        assert!(!path.exists(), "conformance: G1: {what}: a file after a refusal");
    }
}
// --------------------------------------------------------- preconditions --

#[derive(Clone, Debug, PartialEq)]
struct GMaps {
    m: HashMap<u8, u8>,
    s: HashSet<u8>,
}
/// Distinct values (by `PartialEq`) that render alike (P3a).
#[derive(Clone, PartialEq)]
struct Alike(u8);
impl std::fmt::Debug for Alike {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let _ = self.0;
        f.write_str("Alike")
    }
}
/// Equal values (by `PartialEq`, which ignores `b`) that render differently
/// (P3b).
#[derive(Clone, Debug)]
struct Loose {
    a: u8,
    b: u8,
}
impl PartialEq for Loose {
    fn eq(&self, o: &Self) -> bool {
        self.a == o.a
    }
}
/// `a` sends `make(nondet())` to `b`.
fn choice_program<M: crate::msg::Message + Clone + 'static>(make: fn(bool) -> M) -> Entry {
    Arc::new(move || {
        let b = named("b", || {
            let _: M = crate::recv_msg_block();
        });
        let tb = b.thread().id();
        named("a", move || crate::send_msg(tb, make(crate::nondet())));
    })
}
/// **G-T-P** (G1-1 P1–P3): P1, a nested empty map encodes as `[]` (the stated
/// consequence); P2 in G-T6; P3a, two distinct values rendering alike refuse
/// the export (`Collision`); P3b, a `PartialEq` that ignores a rendered field
/// makes the line depend on which branch Must explores first (the stated
/// consequence). Failing direction: MU16 (the `Collision` check removed).
#[test]
fn g1_tp_the_preconditions() {
    // P1
    assert_eq!(
        gen_ok(GMaps {
            m: HashMap::new(),
            s: HashSet::new()
        }),
        r#"{"t":"GMaps","f":[[],[]]}"#
    );
    let cc = small_cc(&["a", "b"], ConsType::FIFO);
    let dir = scratch("g1-tp");
    // P3a
    let path = dir.join("c.jsonl");
    let p = choice_program(|c| Alike(if c { 1 } else { 2 }));
    match export(&cc, move || p(), &header("p3a"), &path) {
        Err(ExportError::Collision { line }) => {
            assert!(line.contains("Alike"), "conformance: G1: {line}")
        }
        other => panic!("conformance: G1: P3a: {other:?}"),
    }
    assert!(!path.exists(), "conformance: G1: P3a: a file after a refusal");
    // P3b
    let (p1, p2) = (dir.join("l1.jsonl"), dir.join("l2.jsonl"));
    let a = choice_program(|c| Loose { a: 1, b: if c { 1 } else { 2 } });
    let b = choice_program(|c| Loose { a: 1, b: if c { 2 } else { 1 } });
    let s1 = export(&cc, move || a(), &header("p3b"), &p1).expect("conformance: G1: P3b");
    let s2 = export(&cc, move || b(), &header("p3b"), &p2).expect("conformance: G1: P3b");
    assert_eq!((s1.lines, s2.lines, s1.spec_graphs, s2.spec_graphs), (1, 1, 2, 2));
    let (_, l1) = read_jsonl(&p1);
    let (_, l2) = read_jsonl(&p2);
    assert_ne!(
        l1, l2,
        "conformance: G1: P3b: the representative follows the exploration order"
    );
    note!("G-T-P\tP3b\t{}\t{}", l1[0], l2[0]);
}
// ------------------------------------------------------- the shared main --

#[derive(Clone, Debug, PartialEq)]
enum PcMsg {
    Item(i32),
}
/// The template's program (producer–consumer, CIVL): the specification's
/// channel is FIFO by construction, the implementation's takes the run's model.
fn pc(k: usize, fifo_by_construction: bool) {
    let (tx, rx) = if fifo_by_construction {
        crate::channel::Builder::<PcMsg>::new()
            .with_comm(crate::loc::CommunicationModel::LocalOrder)
            .build()
    } else {
        crate::channel::Builder::<PcMsg>::new().build()
    };
    let c = named("consumer", move || {
        for _ in 0..=k {
            let PcMsg::Item(x) = rx.recv_msg_block();
            if x == 0 {
                return;
            }
        }
    });
    let p = named("producer", move || {
        for x in 1..=k as i32 {
            if crate::nondet() {
                tx.send_msg(PcMsg::Item(x));
            } else {
                tx.send_msg(PcMsg::Item(0));
                return;
            }
        }
        tx.send_msg(PcMsg::Item(0));
    });
    c.join().unwrap();
    p.join().unwrap();
}
fn cli(p: &Program, args: &[&str]) -> (String, u8) {
    let a: Vec<String> = args.iter().map(|s| (*s).to_owned()).collect();
    run_cli(p, &a)
}
/// **G-T7** (G1-5): the shared main through `run_cli` on the template's
/// program. Failing directions: MU17 (the program's arguments not passed),
/// MU18 (`stateful` above one thread stays Stateful).
#[test]
fn g1_t7_the_shared_main() {
    let k_of = |a: &[String]| -> usize { a.first().and_then(|s| s.parse().ok()).unwrap_or(2) };
    let spec = move |a: &[String]| -> Entry {
        let k = k_of(a);
        Arc::new(move || pc(k, true))
    };
    let imp = move |a: &[String]| -> Entry {
        let k = k_of(a);
        Arc::new(move || pc(k, false))
    };
    let p = Program {
        visible: &|_| vec!["consumer".to_owned(), "producer".to_owned()],
        spec: &spec,
        imp: &imp,
    };
    assert_eq!(cli(&p, &["count", "spec", "1"]), ("execs=2 blocked=0\n".to_owned(), 0));
    assert_eq!(cli(&p, &["count", "spec", "3"]), ("execs=4 blocked=0\n".to_owned(), 0));
    assert_eq!(
        cli(&p, &["count", "impl", "--model", "bag", "2"]),
        ("execs=8 blocked=0\n".to_owned(), 0)
    );
    let dir = scratch("g1-t7");
    let f = dir.join("s.jsonl");
    let fs = f.to_string_lossy().into_owned();
    assert_eq!(
        cli(&p, &["export", "spec", "--out", &fs, "2"]),
        (format!("exported: 3 lines from 3 graphs to {fs}\n"), 0)
    );
    let (head, lines) = read_jsonl(&f);
    assert_eq!(head["program"], "program:spec");
    assert_eq!(head["size"], "2");
    assert_eq!(head["model"], "p2p");
    assert_eq!(visible_of(&head), vec!["consumer", "producer"]);
    assert_eq!(lines.len(), 3);
    for (args, text) in [
        (vec!["conf", "2"], "(thm:stateful), and both"),
        (vec!["conf", "--threads", "2", "2"], "(thm:stateful, the partitioned form)"),
        (vec!["conf", "--engine", "stateless", "2"], "a sweep (thm:cfirst)"),
        (
            vec!["conf", "--engine", "stateless", "--threads", "2", "2"],
            "(thm:cfirst, the partitioned form)",
        ),
    ] {
        let (out, code) = cli(&p, &args);
        assert_eq!(code, 0, "conformance: G1: {args:?}: {out}");
        assert!(out.contains(text), "conformance: G1: {args:?} lacks `{text}`: {out}");
    }
    let (out, code) = cli(&p, &["conf", "--model", "bag", "2"]);
    assert_eq!(code, 1, "conformance: G1: bag reports: {out}");
    // `C` implements `online`: with no `--spec` it is a usage error (exit 2).
    let (out, code) = cli(&p, &["online"]);
    assert!(
        code == 2 && out.contains("online needs --spec") && out.contains("usage:"),
        "conformance: G1: {out}"
    );
    let (out, code) = cli(&p, &["frob"]);
    assert!(code == 2 && out.contains("usage:"), "conformance: G1: {out}");
}
/// `k` clients `c0 … c{k-1}`, each sending `Item(i)` to an invisible server `s`
/// that receives all `k`: the visible set depends on the program's argument.
fn clients(k: usize) {
    let srv = named("s", move || {
        for _ in 0..k {
            let _: PcMsg = crate::recv_msg_block();
        }
    });
    let ts = srv.thread().id();
    for i in 0..k {
        named(&format!("c{i}"), move || crate::send_msg(ts, PcMsg::Item(i as i32)));
    }
}
/// **G-T7b** (G1-5, `Program.visible` from the arguments; H's Q1): a program
/// whose visible set is `c0 … c{k-1}`, run by `run_cli` at k = 1 and k = 2.
/// Expected by hand: k = 1, one graph and one line over `["c0"]`; k = 2, the
/// server's two receive orders give two graphs whose summaries are equal (the
/// two clients' sends are porf-unrelated and only the clients are visible),
/// so one line over `["c0","c1"]`; `count` gives `execs=1` and `execs=2`; `conf`
/// conforms at both sizes. Failing direction: MU21 (the visible set computed
/// from no arguments: at k = 1 the run declares `c1`, which is never spawned).
#[test]
fn g1_t7b_a_visible_set_from_the_arguments() {
    let k_of = |a: &[String]| -> usize { a.first().and_then(|s| s.parse().ok()).unwrap_or(2) };
    let vis = move |a: &[String]| -> Vec<String> { (0..k_of(a)).map(|i| format!("c{i}")).collect() };
    let side = move |a: &[String]| -> Entry {
        let k = k_of(a);
        Arc::new(move || clients(k))
    };
    let p = Program {
        visible: &vis,
        spec: &side,
        imp: &side,
    };
    let dir = scratch("g1-t7b");
    for (k, names, graphs) in [("1", vec!["c0"], 1), ("2", vec!["c0", "c1"], 2)] {
        assert_eq!(
            cli(&p, &["count", "spec", k]),
            (format!("execs={graphs} blocked=0\n"), 0),
            "conformance: G1: count at k = {k}"
        );
        let f = dir.join(format!("k{k}.jsonl"));
        let fs = f.to_string_lossy().into_owned();
        assert_eq!(
            cli(&p, &["export", "spec", "--out", &fs, k]),
            (format!("exported: 1 lines from {graphs} graphs to {fs}\n"), 0),
            "conformance: G1: export at k = {k}"
        );
        let (head, lines) = read_jsonl(&f);
        assert_eq!(visible_of(&head), names, "conformance: G1: visible at k = {k}");
        assert_eq!(lines.len(), 1);
        let (out, code) = cli(&p, &["conf", k]);
        assert_eq!(code, 0, "conformance: G1: conf at k = {k}: {out}");
    }
}
/// `a` asserts `!(x && y)` over two `nondet()`s: one execution in four fails.
fn asserting_pair() {
    named("a", || {
        let x = crate::nondet();
        let y = crate::nondet();
        crate::assert(!(x && y));
    });
}
/// **G-T7c** (G1-5, `count` past an assertion failure; H's Q12, the owner's G3):
/// `count` explores past a failed assertion as the plain-Must baseline does, so
/// on `asserting_pair` it reports what `crate::verify` with
/// `keep_going_after_error = true` reports on the same program: all four
/// executions (derived as `execs=3 blocked=1`; measured `execs=4 blocked=0` —
/// Must counts the execution that ends on its failed assertion as finished, so
/// the test pins the total, four, and the equality). Failing direction: MU22
/// (`count` without the setting: the failed assertion panics the run).
#[test]
fn g1_t7c_count_explores_past_a_failure() {
    let entry = |_: &[String]| -> Entry { Arc::new(asserting_pair) };
    let p = Program {
        visible: &|_| vec!["a".to_owned()],
        spec: &entry,
        imp: &entry,
    };
    let reference = crate::verify(
        Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_keep_going_after_error(true)
            .with_verbose(0)
            .build(),
        asserting_pair,
    );
    assert_eq!(
        reference.execs + reference.block,
        4,
        "conformance: G1: the reference explores all four executions"
    );
    for side in ["spec", "impl"] {
        assert_eq!(
            cli(&p, &["count", side]),
            (
                format!("execs={} blocked={}\n", reference.execs, reference.block),
                0
            ),
            "conformance: G1: count {side} past the failure"
        );
    }
}
/// **G-T8** (G1-4): the models. Failing direction: MU19 (Bag → `p2p`).
#[test]
#[allow(deprecated)]
fn g1_t8_the_models() {
    assert_eq!(model_name(ConsType::FIFO), Ok("p2p"));
    assert_eq!(model_name(ConsType::Bag), Ok("asyn"));
    assert_eq!(model_name(ConsType::Causal), Ok("cd"));
    assert_eq!(model_name(ConsType::CD), Ok("cd"));
    for c in [ConsType::MO, ConsType::WB, ConsType::Mailbox] {
        assert!(
            matches!(model_name(c), Err(ExportError::Model(_))),
            "conformance: G1: {c:?} has no model"
        );
    }
}
// ------------------------------------------------------------ the reader --

/// A line over `a`, `b`: `a` sends the value, `b` receives it.
fn vline(v: &str) -> String {
    format!(
        r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{{"s":{v}}}],"b":[{{"r":{v}}}]}},"counts":[0,1]}}"#
    )
}
#[derive(Clone, Debug, PartialEq)]
struct Note {
    s: String,
    b: bool,
    l: Vec<u8>,
}
/// **G-T9** (G1-2): the reader accepts strings (in `serde_json`'s escaping),
/// booleans and lists; the generic writer's lines are already in the reader's
/// normal form; floats, `null` and other objects stay invalid. Failing
/// directions: MR1 (the reader renders a string with Rust's escaping), MR2 (the
/// reader refuses lists again).
#[test]
fn g1_t9_the_readers_extension() {
    let names = ["a".to_owned(), "b".to_owned()];
    let n = |v: &str| normal_line(&vline(v), &names);
    assert_eq!(n(r#""é""#), n(r#""é""#));
    assert_eq!(n(r#""é""#).unwrap(), vline(r#""é""#));
    assert_eq!(n(r#""a\"b\\c\n\u0001""#).unwrap(), vline(r#""a\"b\\c\n\u0001""#));
    assert_eq!(n("true").unwrap(), vline("true"));
    assert_eq!(n("[ [1, 2] , [] ]").unwrap(), vline("[[1,2],[]]"));
    for bad in ["1.5", "[null]", r#"{"x":1}"#] {
        let e = n(bad).unwrap_err();
        assert!(e.contains("invalid in format version 1"), "conformance: G1: {bad}: {e}");
    }
    let dir = scratch("g1-t9");
    let s = file(&dir, "s.jsonl", AB, &[vline(r#""é""#)]);
    let i = file(&dir, "i.jsonl", AB, &[vline(r#""é""#)]);
    assert!(matches!(join_ok(&s, &i).verdict, Verdict::Conforms));
    // the generic writer's lines are normal
    let cc = small_cc(&["a", "b"], ConsType::FIFO);
    let p = choice_program(|c| {
        if c {
            Note {
                s: "q\"\\\u{1}é\n".to_owned(),
                b: true,
                l: vec![1, 2],
            }
        } else {
            Note {
                s: String::new(),
                b: false,
                l: vec![],
            }
        }
    });
    let path = dir.join("n.jsonl");
    let st = export(&cc, move || p(), &header("t9"), &path).expect("conformance: G1: t9");
    assert_eq!(st.lines, 2);
    let (_, lines) = read_jsonl(&path);
    for l in &lines {
        assert_eq!(normal_line(l, &names).unwrap(), *l, "conformance: G1: normal");
    }
    assert!(lines.iter().any(|l| l.contains(r#""q\"\\\u0001é\n""#)), "{lines:?}");
    assert!(matches!(join_ok(&path, &path).verdict, Verdict::Conforms));
}

// =========================================================================
// H (the tester's; `criteria/H.md` H-2 A1, A2, F, G; `log/dev/H.md` §2.0)
// =========================================================================

use crate::conformance::record::{self, Subject};

/// `cluster/schema8-header.csv` (md5 9ac763f3…, = Daavar's `scripts/`): the 262
/// names in order, unquoted and comma-joined (the record's own header).
const SCHEMA8_HEADER: &str = concat!(
    "key,run_kind,profile,commit,rep,tier,end_class,censor_via,censored,proc_wall_ms,pid,",
    "rss_sampled_hwm_kb,rss_child_hwm_kb,run_dir,diag_keys,diag_bytes_est,family,knobs,k1,k2,",
    "k3,k4,variant,twin_key,cut,inner_order,comm_model,cache,carry,direction,fixture,engine,",
    "selector,stop,gated_mode,policy,memo,budget,precheck,instrumented,cover,flat_calls,",
    "flat_visits,flat_nd_branches,wall_ms,vm_hwm_kb_before,vm_hwm_kb_after,tainted_at_start,",
    "stack_mib,reports,exhaustions,diagnostics,end,skipped_gates,inert_gates,seed,spec_error,",
    "outer_graphs(execs+block),gate_invocations,gate_skipped_inert,gate_skipped_replay,",
    "gate_skipped_pruned,gate_skipped_disabled,gate_skipped_aborted,cover_calls,",
    "cover_exhaustions,rebuilds_taken,rebuilds_skipped_initial_seed,",
    "rebuilds_skipped_exhausted_seed,spec_visit_calls,spec_visit_calls_extend,",
    "spec_visit_calls_rebuild,memo_hits,per_cover,distinct_keys_run_wide,",
    "f63_distinct_run_wide,explored_complete_keys,report_keys,max_paper_events_per_execution,",
    "paper_events_at_first_report,executions,engine_wall_time_ms,per_cover_detail,impl_end,",
    "spec_end,spec_errors,impl_notes,max_paper_events,kept_impl_graphs,kept_spec_graphs,",
    "spec_graphs,impl_graphs,sig_key_buckets,signatures,orders_held,lookups,",
    "lookups_signature_miss,lookups_containment_tested,lookups_succeeded,",
    "lookups_failed_after_tests,containment_tests,counter_reports,spec_wall_time_ms,",
    "impl_wall_time_ms,cut_reports_list,aborted,witness_cache_len,sweep_ends,",
    "paper_events_at_first_report(grid),cache_probes,cache_hits,cache_tests,sweeps,",
    "sweeps_successful,sweeps_failing,sweeps_aborted,sweep_sizes,sweep_graphs,",
    "sweep_graphs_max,witnesses,admissions,evictions,readmissions,wall_ms_at_first_report,",
    "vmhwm_kb_at_first_report,witness_duplicates,cut_reports,precheck_ran,",
    "precheck_wall_time_ms,outer_wall_time_ms,sweep_wall_time_ms,reports_at_gates,",
    "reports_at_completion,abort_gate_at,first_failure_mode,gates,gates_inert,",
    "gates_skipped_replay,gates_skipped_certified,gates_declined,c1_tests_carried,",
    "carried_hits,c1_tests_cache,gate_cache_hits,c1_tests_sweep,gate_sweeps,",
    "gate_sweeps_successful,gate_sweeps_failing,gate_sweeps_budgeted,gate_sweeps_aborted,",
    "gate_sweep_sizes,certificates_set,certificate_resets,states_pushed,",
    "certified_states_revisited,reports_certified,reports_by_completion_test,",
    "completion_probes,completion_cache_hits,completion_cache_tests,completion_sweeps,",
    "completion_sweeps_successful,completion_sweeps_failing,completion_sweeps_aborted,",
    "completion_sweep_sizes,verdict,notes,rendered_engine,spec_errfree,communication_flat,",
    "thread_flat,spec_graphs_scanned,first_invisible,refused_at,payload,cap_ms,",
    "flat_source_branches,flat_source_recursions,flat_send_kills,flat_slot_kills,",
    "flat_source_kills,flat_done_kills,flat_witnesses,flat_max_depth,flat_wall_time_ms,",
    "impl_distinct_summaries,index_kind,impl_phase_wall_ms,antichain_effective,entries,",
    "buckets,bucket_max,admitted,duplicates,antichain_dropped_new,antichain_dropped_old,",
    "insert_tests,summary_bytes,sig_bytes_est,signatures_seen,sig_tests,sig_aliases,",
    "coordinates_compared,inverted_used,inverted_words,trie_nodes_visited,memo_on,",
    "memo_entries,memo_clears,threads,flush_entries,iterations_until_split,warmup,",
    "state_batch_size,freeze_wall_time_ms,spec_vmhwm_kb,freeze_vmhwm_kb,impl_vmhwm_kb,",
    "vmhwm_kb_max,phase_peaks,vm_peak_kb,spec_complete,spec_blocked,impl_complete,",
    "impl_blocked,spec_tasks,impl_tasks,spec_tasks_nonempty,impl_tasks_nonempty,spec_flushes,",
    "impl_flushes,spec_merge_lock_held_ms,spec_merge_lock_wait_ms,impl_merge_lock_held_ms,",
    "impl_merge_lock_wait_ms,spec_flush_entries,spec_worker_duplicates,spec_merge_duplicates,",
    "impl_seen_flush_entries,impl_seen_worker_duplicates,exact_hits,uncovered_distinct,",
    "uncovered_multiplicity,uncovered_flush_entries,uncovered_worker_duplicates,",
    "uncovered_merge_duplicates,stopped_early,uncovered_at_stop,spawned_at_stop,",
    "redundant_sweeps,unadmitted_after_cancel,unprobed_after_cancel,signature_syncs,",
    "admission_lock_held_ms,admission_lock_wait_ms,sweeps_in_warmup,sweeps_in_root_loop,",
    "sweeps_in_tasks,sweeps_abandoned,watch_probes,cpu_user_ms,cpu_sys_ms",
);

/// **H A1** (H-2 A): the library's header is schema 8's, 262 names in order.
/// Failing direction: MA1 (two header columns swapped, a scratch mutant).
#[test]
fn h_a1_the_header_is_schema_8s() {
    let want: Vec<&str> = SCHEMA8_HEADER.split(',').collect();
    assert_eq!(want.len(), 262, "conformance: H: the embedded header");
    let got = record::header();
    assert_eq!(got.len(), 262, "conformance: H: the library header's length");
    assert_eq!(got, want, "conformance: H: the library header");
    assert_eq!(record::SCHEMA_VERSION, 8, "conformance: H: schema 8");
}

/// The 14 label forms of the cluster's smoke rows (`cluster/smoke.rows`).
const SMOKE_LABELS: [&str; 14] = [
    "Stateful/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set",
    "SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=1",
    "SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=16",
    "SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=32",
    "CompleteFirst/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set",
    "CFirstP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=1",
    "CFirstP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=16",
    "SverifyP/Plain/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set/threads=64",
    "CompleteFirst/Plain/stop=true/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/w=inf/quiet=false/index=set",
    "Gated/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep",
    "Enumerator/Ltr/stop=false/Exhaustive/Always/memo=true/Unlimited/precheck=false/instr=false/cut=false/cover=Sweep",
    "Explore/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep",
    "ExploreP/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/threads=1",
    "ExploreP/Ltr/stop=false/Exhaustive/Always/memo=false/Default/precheck=false/instr=false/cut=false/cover=Sweep/threads=16",
];

/// **H A2** (H-2 A): each of the 14 label forms parses and prints itself; two
/// misspelled forms are refused. Failing direction: MA2 (the printer drops
/// `/threads=`, a scratch mutant).
#[test]
fn h_a2_the_14_label_forms_round_trip() {
    let distinct: BTreeSet<&str> = SMOKE_LABELS.iter().copied().collect();
    assert_eq!(distinct.len(), 14, "conformance: H: 14 distinct forms");
    for l in SMOKE_LABELS {
        let c = record::parse_label(l)
            .unwrap_or_else(|| panic!("conformance: H: `{l}` does not parse"));
        assert_eq!(c.label(), l, "conformance: H: the label prints itself");
    }
    let bad_stop = SMOKE_LABELS[0].replace("stop=false", "stop=maybe");
    let bad_threads = SMOKE_LABELS[1].replace("threads=1", "threads=x");
    for bad in [bad_stop, bad_threads] {
        assert!(
            record::parse_label(&bad).is_none(),
            "conformance: H: `{bad}` must be refused"
        );
    }
}

#[derive(Clone, Debug, PartialEq)]
enum FMsg {
    V(i32),
}

/// `a` sends `V(x)` to `b`, `x` one of `values` chosen by `nondet()`; `b`
/// receives it (a pair that is no benchmark: H-2 F).
fn f_program(values: [i32; 2]) -> Entry {
    Arc::new(move || {
        let b = named("b", || {
            let _: FMsg = crate::recv_msg_block();
        });
        let tb = b.thread().id();
        named("a", move || {
            let x = if crate::nondet() { values[0] } else { values[1] };
            crate::send_msg(tb, FMsg::V(x));
        });
    })
}

/// The subject of an F row: FIFO, seed 0, visible `a`, `b`; the specification
/// sends {1, 2}, the implementation `imp`.
fn f_subject(name: &str, imp: [i32; 2]) -> Subject {
    Subject {
        name: name.to_owned(),
        config: Config::builder()
            .with_cons_type(ConsType::FIFO)
            .with_seed(0)
            .build(),
        visible: vec!["a".to_owned(), "b".to_owned()],
        implementation: f_program(imp),
        specification: f_program([1, 2]),
    }
}

/// A row's `EVAL_ROW` JSON with the smoke rows' fields and the given label.
fn f_json(name: &str, label: &str) -> String {
    format!(
        r#"{{"fixture":"{name}","label":"{label}","rep":0,"tier":{{"name":"c1h","wall_ms":3600000,"mem_kb":262144000}},"run_kind":"timed","family":"f","knobs":"","k":[null,null,null,null],"variant":"conforming","twin_key":""}}"#
    )
}

/// An all-quoted RFC 4180 record (the sentinel stripped), split into cells.
pub(super) fn record_cells(line: &str) -> Vec<String> {
    let body = line
        .strip_prefix(record::SENTINEL)
        .unwrap_or_else(|| panic!("conformance: H: no sentinel in {line}"))
        .trim_end_matches('\n');
    let mut cells = Vec::new();
    let mut cur = String::new();
    let mut chars = body.chars().peekable();
    let mut quoted = false;
    while let Some(c) = chars.next() {
        match (quoted, c) {
            (false, '"') => quoted = true,
            (true, '"') if chars.peek() == Some(&'"') => {
                chars.next();
                cur.push('"');
            }
            (true, '"') => quoted = false,
            (false, ',') => cells.push(std::mem::take(&mut cur)),
            (_, c) => cur.push(c),
        }
    }
    cells.push(cur);
    cells
}

/// One F row: the record by header name.
fn f_row(name: &str, label: &str, imp: [i32; 2]) -> HashMap<String, String> {
    let lines = record::run_row(&f_json(name, label), "F", |n| f_subject(n, imp))
        .unwrap_or_else(|e| panic!("conformance: H: F: {label}: refused: {e}"));
    let cells = record_cells(&lines.record);
    let header = record::header();
    assert_eq!(cells.len(), header.len(), "conformance: H: F: 262 cells");
    header
        .iter()
        .map(|h| (*h).to_owned())
        .zip(cells)
        .collect()
}

/// The F row of `rows` whose label starts with `prefix`, has `stop=false` and,
/// if given, ends with `/threads=<threads>`.
fn f_by<'a>(
    rows: &'a [(String, HashMap<String, String>)],
    prefix: &str,
    threads: Option<&str>,
) -> &'a HashMap<String, String> {
    &rows
        .iter()
        .find(|(l, _)| {
            l.starts_with(prefix)
                && l.contains("stop=false")
                && threads.is_none_or(|t| l.ends_with(&format!("/threads={t}")))
        })
        .unwrap_or_else(|| panic!("conformance: H: F: no {prefix} row"))
        .1
}

/// H-1's core list (the cells compared across engines in F where both fill them).
const CORE: [&str; 18] = [
    "verdict",
    "end_class",
    "end",
    "spec_end",
    "impl_end",
    "reports",
    "spec_errors",
    "executions",
    "spec_graphs",
    "impl_graphs",
    "spec_complete",
    "spec_blocked",
    "impl_complete",
    "impl_blocked",
    "impl_distinct_summaries",
    "uncovered_distinct",
    "signatures",
    "orders_held",
];

/// **H F** (H-2 F, generic engine gating, default build): a conforming and a
/// violating inline pair under the 14 label forms and SverifyP/CFirstP at two
/// threads. Every row ends `ok`; every conformance engine reports 0 on the
/// conforming pair and more than 0 on the violating one; SverifyP at t = 1, 2
/// equals Stateful, and CFirstP at t = 1, 2 equals CompleteFirst, on every core
/// cell both fill (at least 4 per comparison); ExploreP t1's split equals
/// `count`. Failing direction: a CFirstP label with the selector `Ltr` is
/// refused with no record.
#[test]
fn h_f_generic_engine_gating() {
    let mut labels: Vec<String> = SMOKE_LABELS.iter().map(|s| (*s).to_owned()).collect();
    labels.push(SMOKE_LABELS[1].replace("threads=1", "threads=2"));
    labels.push(SMOKE_LABELS[5].replace("threads=1", "threads=2"));
    let mut compared = 0;
    for (pair, imp, violates) in [("f-conf", [1, 2], false), ("f-viol", [1, 3], true)] {
        let rows: Vec<(String, HashMap<String, String>)> = labels
            .iter()
            .map(|l| (l.clone(), f_row(pair, l, imp)))
            .collect();
        for (l, r) in &rows {
            assert_eq!(r["end_class"], "ok", "conformance: H: F: {pair} {l}: {r:?}");
            assert_eq!(r["fixture"], pair, "conformance: H: F: the opaque name");
            let engine = l.split('/').next().unwrap();
            if !matches!(engine, "Explore" | "ExploreP") {
                let reports: u64 = r["reports"]
                    .parse()
                    .unwrap_or_else(|_| panic!("conformance: H: F: {pair} {l}: reports"));
                assert_eq!(
                    reports > 0,
                    violates,
                    "conformance: H: F: {pair} {l}: reports {reports}"
                );
            }
        }
        for (base, par) in [("Stateful/", "SverifyP/"), ("CompleteFirst/", "CFirstP/")] {
            for t in ["1", "2"] {
                let (a, b) = (f_by(&rows, base, None), f_by(&rows, par, Some(t)));
                let mut both = 0;
                for c in CORE {
                    if !a[c].is_empty() && !b[c].is_empty() {
                        assert_eq!(
                            a[c], b[c],
                            "conformance: H: F: {pair}: {base} vs {par} t{t}: `{c}`"
                        );
                        both += 1;
                    }
                }
                assert!(
                    both >= 4,
                    "conformance: H: F: {pair}: {base} vs {par} t{t}: only {both} core cells"
                );
                compared += both;
            }
        }
        // ExploreP t1's split against `count`
        let xp = f_by(&rows, "ExploreP/", Some("1"));
        let imp_entry = move |_: &[String]| -> Entry { f_program(imp) };
        let spec_entry = |_: &[String]| -> Entry { f_program([1, 2]) };
        let p = Program {
            visible: &|_| vec!["a".to_owned(), "b".to_owned()],
            spec: &spec_entry,
            imp: &imp_entry,
        };
        for side in ["spec", "impl"] {
            let (out, code) = run_cli(&p, &["count".to_owned(), side.to_owned()]);
            assert_eq!(code, 0, "conformance: H: F: count {side}");
            let want = format!(
                "execs={} blocked={}\n",
                xp[&format!("{side}_complete")],
                xp[&format!("{side}_blocked")]
            );
            assert_eq!(out, want, "conformance: H: F: {pair}: ExploreP t1 vs count {side}");
        }
    }
    assert!(compared >= 32, "conformance: H: F: {compared} core cells compared");
    // the refusal: a CFirstP row with a legacy selector field
    let legacy = SMOKE_LABELS[5].replace("CFirstP/Plain/", "CFirstP/Ltr/");
    assert!(
        record::run_row(&f_json("f-legacy", &legacy), "F", |n| f_subject(n, [1, 2])).is_err(),
        "conformance: H: F: `{legacy}` must be refused"
    );
}

/// `b` receives twice; `a` sends `V(1)` and, by `nondet()`, `V(2)`: one graph
/// ends with `b` blocked on its second receive.
fn h_blocked_program() -> Entry {
    Arc::new(|| {
        let b = named("b", || {
            let _: FMsg = crate::recv_msg_block();
            let _: FMsg = crate::recv_msg_block();
        });
        let tb = b.thread().id();
        named("a", move || {
            crate::send_msg(tb, FMsg::V(1));
            if crate::nondet() {
                crate::send_msg(tb, FMsg::V(2));
            }
        });
    })
}

/// **H B's `spec_blocked` control input** (H-1 rev 1.4; ignored): a SverifyP
/// row at two threads of an inline program whose specification has a blocked
/// graph; its record is written to `H_B_OUT` for the comparison's control, and
/// `spec_blocked > 0` is asserted. A no-op without `H_B_OUT`.
#[test]
#[ignore]
fn h_b_blocked_spec_record() {
    let Some(out) = std::env::var_os("H_B_OUT") else {
        return;
    };
    let label = SMOKE_LABELS[1].replace("threads=1", "threads=2");
    let lines = record::run_row(&f_json("h-blocked-spec", &label), "H_COMMIT_PENDING", |n| {
        Subject {
            name: n.to_owned(),
            config: Config::builder()
                .with_cons_type(ConsType::FIFO)
                .with_seed(0)
                .build(),
            visible: vec!["a".to_owned(), "b".to_owned()],
            implementation: h_blocked_program(),
            specification: h_blocked_program(),
        }
    })
    .unwrap_or_else(|e| panic!("conformance: H: B: refused: {e}"));
    let cells = record_cells(&lines.record);
    let header = record::header();
    let i = header.iter().position(|h| *h == "spec_blocked").unwrap();
    let blocked: u64 = cells[i]
        .parse()
        .unwrap_or_else(|_| panic!("conformance: H: B: spec_blocked `{}`", cells[i]));
    assert!(blocked > 0, "conformance: H: B: no blocked specification graph");
    std::fs::write(out, &lines.record).unwrap_or_else(|e| panic!("conformance: H: B: {e}"));
}

/// The scan's patterns (derivation §5 G), each written split so that this file
/// does not hit itself.
fn g_patterns() -> Vec<String> {
    let parts: [&[&str]; 35] = [
        &["fixture", "_by_name"],
        &["fixture", "_domain"],
        &["all", "_fixtures"],
        &["_fix", "tures("],
        &["app", "tab_"],
        &["Apptab", "Pair"],
        &["regis", "try("],
        &["struct ", "Fixture"],
        &["Synth", "Point"],
        &["\"ap", "ps/"],
        &["\"syn", "th/"],
        &["\"2p", "c/"],
        &["\"ex:", "naive/"],
        &["\"ev", "al/"],
        &["\"cor", "pus/"],
        &["A3", "Lock"],
        &["A2", "Store"],
        &["a1", "_impl"],
        &["a2", "_pb"],
        &["a2", "_sh"],
        &["a3", "_impl"],
        &["a4", "_impl"],
        &["le", "_impl"],
        &["ring", "_impl"],
        &["share", "_impl"],
        &["commit", "_prog"],
        &["chain", "_prog"],
        &["reset", "_prog"],
        &["width", "_prog"],
        &["A1", "Coord"],
        &["A2", "Pb"],
        &["A3", "Coord"],
        &["A4", "Policy"],
        &["Summary", "Encode"],
        &["a3_a2", "_encoders"],
    ];
    parts.iter().map(|p| p.concat()).collect()
}

/// The source root the scan reads: `H_SCAN_SRC`, or this crate's `src`.
fn g_root() -> PathBuf {
    std::env::var_os("H_SCAN_SRC")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("src"))
}

/// The modules of `conformance/mod.rs` declared under `feature =
/// "fixture-tests"` (read from its `cfg` lines, not listed here).
fn g_flagged(mod_rs: &str) -> BTreeSet<String> {
    let lines: Vec<&str> = mod_rs.lines().collect();
    let mut out = BTreeSet::new();
    for (i, l) in lines.iter().enumerate() {
        let t = l.trim();
        let decl = t
            .strip_prefix("pub(crate) mod ")
            .or_else(|| t.strip_prefix("mod "))
            .and_then(|r| r.strip_suffix(';'));
        let Some(name) = decl else { continue };
        let mut j = i;
        while j > 0 && lines[j - 1].trim().starts_with("#[") {
            j -= 1;
            if lines[j].contains("feature = \"fixture-tests\"") {
                out.insert(name.to_owned());
            }
        }
    }
    out
}

fn g_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("conformance: H: G: {}: {e}", dir.display()))
    {
        let p = e.unwrap().path();
        if p.is_dir() {
            g_rs_files(&p, out);
        } else if p.extension().and_then(|x| x.to_str()) == Some("rs") {
            out.push(p);
        }
    }
}

/// The hits of the patterns in one file: (line number, pattern), with the two
/// exemptions (Q16 and the flag's own declarations in `mod.rs`).
fn g_hits(text: &str, is_mod_rs: bool, flagged: &BTreeSet<String>, pats: &[String]) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    for (n, l) in text.lines().enumerate() {
        let t = l.trim();
        if is_mod_rs {
            let decl = t
                .strip_prefix("pub(crate) mod ")
                .or_else(|| t.strip_prefix("mod "))
                .and_then(|r| r.strip_suffix(';'));
            if decl.is_some_and(|d| flagged.contains(d)) {
                continue;
            }
        }
        for p in pats {
            if l.contains(p.as_str()) {
                out.push((n + 1, p.clone()));
            }
        }
    }
    out
}

/// **H G** (H-2 G, the scan): no catalogue identifier, fixture-name literal,
/// family constructor or encoder name in any source the default build reaches
/// — every `src/**.rs` but the modules `mod.rs` declares under
/// `fixture-tests` (`program.rs` and `src/bin` included); upstream `tests/` and
/// `examples/` are outside `src` (Q16), and `naive_d` is not a pattern (Q16).
/// The positive control: the patterns hit `grid.rs`, `eval.rs` and every
/// flagged `*_tests.rs`. Failing directions: `H_SCAN_SRC` on a scratch copy
/// with a fixture name in `program.rs`, or with `mod grid;`'s `cfg` removed.
#[test]
fn h_g_the_scan() {
    let root = g_root();
    let mod_rs = std::fs::read_to_string(root.join("conformance/mod.rs"))
        .unwrap_or_else(|e| panic!("conformance: H: G: mod.rs: {e}"));
    let flagged = g_flagged(&mod_rs);
    for m in ["grid", "eval", "interchange_tests"] {
        assert!(flagged.contains(m), "conformance: H: G: `{m}` is not flagged");
    }
    let pats = g_patterns();
    let mut files = Vec::new();
    g_rs_files(&root, &mut files);
    files.sort();
    let (mut scanned, mut controls, mut bad) = (0, 0, Vec::new());
    for f in &files {
        let rel = f.strip_prefix(&root).unwrap().to_string_lossy().into_owned();
        let stem = f.file_stem().unwrap().to_string_lossy().into_owned();
        let text = std::fs::read_to_string(f).unwrap();
        let in_conf = rel.starts_with("conformance/");
        let is_flagged = in_conf && flagged.contains(&stem);
        let hits = g_hits(&text, rel == "conformance/mod.rs", &flagged, &pats);
        if is_flagged {
            if stem == "grid" || stem == "eval" || stem.ends_with("_tests") {
                assert!(!hits.is_empty(), "conformance: H: G: the control misses {rel}");
                controls += 1;
            }
        } else {
            scanned += 1;
            for (n, p) in hits {
                bad.push(format!("{rel}:{n}: {p}"));
            }
        }
    }
    assert!(
        bad.is_empty(),
        "conformance: H: G: fixture-specific text in the default build:\n  {}",
        bad.join("\n  ")
    );
    assert!(scanned >= 60, "conformance: H: G: only {scanned} files scanned");
    assert!(
        files.iter().any(|f| f.ends_with("program.rs")) && files.iter().any(|f| f.ends_with("bin/conf-join.rs")),
        "conformance: H: G: program.rs and src/bin are in scope"
    );
    assert_eq!(controls, 16, "conformance: H: G: the positive control's files");
    note!("H-G\tscanned {scanned}\tcontrols {controls}\tpatterns {}", pats.len());
}
