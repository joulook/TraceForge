//! Empty `{}` in exported values: a set where the message type's declared shape says so, refused
//! where it says map or where nothing is declared. Tiny programs exported through `<bin> export`,
//! and the shapes `#[derive(SummaryShape)]` produces.
mod wg_common;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use traceforge::conformance::{declare, Shape, SummaryShape};
use traceforge::program::{run_cli, Program};
use wg_common::*;

#[derive(Clone, Debug, PartialEq, SummaryShape)]
enum Msg {
    S(BTreeSet<u32>),
    Nested(Vec<BTreeSet<u32>>),
    Opt(Option<HashSet<u32>>),
    M(HashMap<u32, u32>),
}

/// Never declared.
#[derive(Clone, Debug, PartialEq)]
struct Und(BTreeSet<u32>);

/// Never declared; used only by the text-witness test.
#[derive(Clone, Debug, PartialEq)]
struct Inv(BTreeSet<u32>);

#[derive(Clone, Debug, PartialEq, SummaryShape)]
enum Either {
    A(HashMap<u32, u32>),
    B(HashSet<u32>),
}

#[derive(Clone, Debug, PartialEq, SummaryShape)]
struct Wrap<T>(T);

#[derive(Clone, Debug, PartialEq, SummaryShape)]
enum Tree {
    Leaf,
    Node(Vec<Tree>),
    Tag(BTreeSet<u32>),
}

#[derive(Clone, Debug, PartialEq, SummaryShape)]
struct Unit;

#[derive(Clone, Debug, PartialEq, SummaryShape)]
struct Tup(u8, BTreeSet<u8>);

#[derive(Clone, Debug, PartialEq, SummaryShape)]
struct Rec {
    a: u8,
    b: BTreeSet<u8>,
}

/// Raw identifiers: derived `Debug` prints them without `r#`, and so must the tags.
#[allow(non_camel_case_types)]
#[derive(Clone, Debug, PartialEq, SummaryShape)]
struct r#type(BTreeSet<u8>);

#[allow(non_camel_case_types)]
#[derive(Clone, Debug, PartialEq, SummaryShape)]
enum RawVariant {
    r#match(BTreeSet<u8>),
}

/// Holds `()`: it compiles with the derive only if `()` implements `SummaryShape`.
#[derive(Clone, Debug, PartialEq, SummaryShape)]
struct Res(Result<BTreeSet<u8>, ()>);

fn declare_all() {
    declare::<r#type>();
    declare::<RawVariant>();
    declare::<Res>();
    declare::<Msg>();
    declare::<Either>();
    declare::<Wrap<BTreeSet<u32>>>();
    declare::<Wrap<HashMap<u32, u32>>>();
    declare::<Tree>();
    declare::<Unit>();
    declare::<Tup>();
    declare::<Rec>();
}

/// The visible thread `v` sends the variant's one value to itself.
fn body(variant: &str) {
    fn send<T: traceforge::msg::Message + 'static>(m: T) {
        named("v", move || traceforge::send_msg(me(), m)).join().unwrap();
    }
    let one = || { let mut m = HashMap::new(); m.insert(1u32, 2u32); m };
    match variant {
        "set" => send(Msg::S(BTreeSet::new())),
        "nested" => send(Msg::Nested(vec![BTreeSet::new()])),
        "opt" => send(Msg::Opt(Some(HashSet::new()))),
        "map" => send(Msg::M(HashMap::new())),
        "map1" => send(Msg::M(one())),
        "und" => send(Und(BTreeSet::new())),
        "und1" => send(Und(BTreeSet::from([1]))),
        "either-a" => send(Either::A(HashMap::new())),
        "either-b" => send(Either::B(HashSet::new())),
        "wrap-set" => send(Wrap(BTreeSet::<u32>::new())),
        "wrap-map" => send(Wrap(HashMap::<u32, u32>::new())),
        // An undeclared instance of the generic: `Wrap<HashSet<u32>>`.
        "wrap-und" => send(Wrap(HashSet::<u32>::new())),
        "tree" => send(Tree::Node(vec![Tree::Node(vec![Tree::Leaf, Tree::Tag(BTreeSet::new())])])),
        "unit" => send(Unit),
        "tup" => send(Tup(1, BTreeSet::new())),
        "rec" => send(Rec { a: 1, b: BTreeSet::new() }),
        "raw-type" => send(r#type(BTreeSet::new())),
        "raw-variant" => send(RawVariant::r#match(BTreeSet::new())),
        "res-ok" => send(Res(Ok(BTreeSet::new()))),
        "res-err" => send(Res(Err(()))),
        // The text witness: `v` sends nothing (spec), or 1 while the invisible `h` sends an
        // undeclared empty set to itself (impl); `wit-vis`: `v` itself sends the undeclared set.
        "wit-spec" => named("v", || {}).join().unwrap(),
        "wit-imp" => {
            let h = named("h", || traceforge::send_msg(me(), Inv(BTreeSet::new())));
            named("v", || traceforge::send_msg(me(), 1usize)).join().unwrap();
            h.join().unwrap();
        }
        "wit-vis" => send(Inv(BTreeSet::new())),
        other => panic!("unknown variant {other}"),
    }
}

fn program() -> Program<'static> {
    Program {
        visible: &|_| vec!["v".to_owned()],
        spec: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
        imp: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
    }
}

/// `export spec` of `variant`: (CLI text, code, the exported file's text).
fn export(variant: &str) -> (String, u8, String) {
    declare_all();
    let dir = scratch();
    let out = dir.join(format!("{variant}.jsonl"));
    let args: Vec<String> = ["export", "spec", "--out", out.to_str().unwrap(), "--", variant]
        .iter().map(|s| s.to_string()).collect();
    let (t, c) = run_cli(&program(), &args);
    let file = std::fs::read_to_string(&out).unwrap_or_default();
    println!("export {variant}: exit {c}\n{t}--- file\n{file}---");
    (t, c, file)
}

/// The exported line of `v`'s one send of `enc`.
fn line(enc: &str) -> String {
    format!("{{\"statuses\":{{\"v\":\"done\"}},\"words\":{{\"v\":[{{\"s\":{enc}}}]}},\"counts\":[]}}")
}

fn accepted(variant: &str, enc: &str) {
    let (t, c, file) = export(variant);
    assert_eq!(c, 0, "{variant}: {t}");
    let lines: Vec<&str> = file.lines().skip(1).collect();
    assert_eq!(lines, vec![line(enc).as_str()], "{variant}");
}

fn refused<T>(variant: &str, what: &str, rendering: &str) {
    let (t, c, _) = export(variant);
    assert_eq!(c, 2, "{variant}: {t}");
    let want = format!(
        "program: export refused: a value of type `{}` holds {what}, which the format refuses: {rendering}",
        std::any::type_name::<T>()
    );
    assert_eq!(t.lines().next(), Some(want.as_str()), "{variant}: {t}");
    assert!(t.contains("\n--- measurements\n"), "{variant}: the refused block");
}

const UNDECLARED: &str = "an empty `{}` whose type is not declared a set (an empty set and an empty map \
    print alike: derive `SummaryShape` for the message type and call `traceforge::conformance::declare`)";

#[test]
fn declared_empty_sets_are_exported_as_empty_lists() {
    accepted("set", r#"{"t":"S","f":[[]]}"#);
    accepted("nested", r#"{"t":"Nested","f":[[[]]]}"#);
    accepted("opt", r#"{"t":"Opt","f":[{"t":"Some","f":[[]]}]}"#);
}

#[test]
fn maps_are_refused_empty_or_not() {
    refused::<Msg>("map", "a map", "M({})");
    refused::<Msg>("map1", "a map", "M({1: 2})");
}

#[test]
fn an_undeclared_type_is_refused_only_for_an_empty_brace() {
    refused::<Und>("und", UNDECLARED, "Und({})");
    // No `{}`: no declaration needed.
    accepted("und1", r#"{"t":"Und","f":[[1]]}"#);
}

#[test]
fn the_variant_decides_set_or_map() {
    refused::<Either>("either-a", "a map", "A({})");
    accepted("either-b", r#"{"t":"B","f":[[]]}"#);
}

#[test]
fn derive_generic_structs_per_instance() {
    accepted("wrap-set", r#"{"t":"Wrap","f":[[]]}"#);
    refused::<Wrap<HashMap<u32, u32>>>("wrap-map", "a map", "Wrap({})");
    // Declaring two instances does not declare a third.
    refused::<Wrap<HashSet<u32>>>("wrap-und", UNDECLARED, "Wrap({})");
}

#[test]
fn derive_recursive_type_terminates() {
    accepted("tree", r#"{"t":"Node","f":[[{"t":"Node","f":[[{"t":"Leaf","f":[]},{"t":"Tag","f":[[]]}]]}]]}"#);
    let Shape::Variants(vs) = Tree::shape() else { panic!("Tree: not Variants") };
    let names: Vec<(&str, usize)> = vs.iter().map(|(n, fs)| (*n, fs.len())).collect();
    assert_eq!(names, vec![("Leaf", 0), ("Node", 1), ("Tag", 1)]);
    // Node's field is a list of trees, whose shape is Tree's again.
    let Shape::List(elem) = (vs[1].1[0])() else { panic!("Node: not List") };
    assert!(matches!(elem(), Shape::Variants(v) if v.len() == 3));
}

#[test]
fn derive_unit_tuple_and_named_structs() {
    accepted("unit", r#"{"t":"Unit","f":[]}"#);
    accepted("tup", r#"{"t":"Tup","f":[1,[]]}"#);
    accepted("rec", r#"{"t":"Rec","f":[1,[]]}"#);
    assert!(matches!(Unit::shape(), Shape::Record("Unit", f) if f.is_empty()));
    let Shape::Record("Tup", f) = Tup::shape() else { panic!("Tup") };
    assert!(matches!(((f[0])(), (f[1])()), (Shape::Scalar, Shape::Set(_))));
    let Shape::Record("Rec", f) = Rec::shape() else { panic!("Rec") };
    assert!(matches!(((f[0])(), (f[1])()), (Shape::Scalar, Shape::Set(_))));
    assert!(matches!(<Wrap<HashMap<u8, u8>>>::shape(), Shape::Record("Wrap", f) if matches!((f[0])(), Shape::Map)));
}

fn cli(args: &[&str]) -> (String, u8) {
    declare_all();
    let (t, c) = run_cli(&program(), &args.iter().map(|s| s.to_string()).collect::<Vec<_>>());
    println!("{args:?}: exit {c}\n{t}---");
    (t, c)
}

/// The text witness prints every send. An invisible send's undeclared `{}` is written as an empty
/// set; a visible one still refuses the export and the online run.
#[test]
fn the_text_witness_writes_an_invisible_undeclared_empty_set() {
    let dir = scratch();
    let spec = dir.join("spec.jsonl");
    let (t, c) = cli(&["export", "spec", "--out", spec.to_str().unwrap(), "--", "wit-spec"]);
    assert_eq!(c, 0, "{t}");
    let w = format!("{}/w/", dir.display());
    let (t, c) = cli(&["online", "--spec", spec.to_str().unwrap(), "--witness", &w, "--seed", "0", "--", "wit-imp"]);
    assert_ne!(c, 2, "{t}");
    let text = std::fs::read_to_string(format!("{w}witness-1.txt")).unwrap_or_default();
    println!("--- witness-1.txt\n{text}---");
    assert_eq!(
        text.lines().next(),
        Some(concat!("uncovered summary (iteration 1): ",
            r#"{"statuses":{"v":"done"},"words":{"v":[{"s":1}]},"counts":[]}"#))
    );
    let sends: Vec<&str> = text.lines().filter(|l| l.contains("SEND(")).map(|l| l.split_once(": ").unwrap().1).collect();
    let mut sends = sends;
    sends.sort();
    assert_eq!(sends, vec![r#"SEND(h, {"t":"Inv","f":[[]]})"#, "SEND(v, 1)"]);
    // The same type sent by the visible thread: refused by the export and by the online run.
    refused::<Inv>("wit-vis", UNDECLARED, "Inv({})");
    let (t, c) = cli(&["online", "--spec", spec.to_str().unwrap(), "--", "wit-vis"]);
    // The online run reports a refused value as its failure: exit 1, verdict partial.
    assert_eq!(c, 1, "{t}");
    let want = format!("FAILED:     a value of type `{}` holds {UNDECLARED}, which the format refuses: Inv({{}})",
        std::any::type_name::<Inv>());
    assert!(t.lines().any(|l| l == want), "{t}");
    assert!(t.contains("\nverdict:    partial\n"), "{t}");
}

#[test]
fn derive_raw_identifiers_tag_without_the_prefix() {
    accepted("raw-type", r#"{"t":"type","f":[[]]}"#);
    accepted("raw-variant", r#"{"t":"match","f":[[]]}"#);
    assert!(matches!(<r#type>::shape(), Shape::Record("type", _)));
    let Shape::Variants(vs) = RawVariant::shape() else { panic!("RawVariant") };
    assert_eq!(vs.iter().map(|(n, _)| *n).collect::<Vec<_>>(), vec!["match"]);
}

/// `()` has a shape (Opaque), so a type holding it derives and can be declared; its `Debug` form
/// is still refused as an anonymous tuple.
#[test]
fn derive_a_type_holding_unit() {
    accepted("res-ok", r#"{"t":"Res","f":[{"t":"Ok","f":[[]]}]}"#);
    refused::<Res>("res-err", "an anonymous tuple", "Res(Err(()))");
    assert!(matches!(<()>::shape(), Shape::Opaque));
    assert!(matches!(<(u8, BTreeSet<u8>)>::shape(), Shape::Opaque));
}
