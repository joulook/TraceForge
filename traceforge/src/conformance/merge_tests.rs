//! `SORTED-JOIN` (2026-11-02): `conf_join_merge` against `conf_join` on scratch
//! files (the helpers of `interchange_default_tests`): agreement of verdict,
//! classes and uncovered set; the refusals of an unsorted or repeated line, of
//! a malformed line after a violation and after the other stream's end; the
//! three miss classes with the specification's shape after the miss in byte
//! order; a large group answered by the scan; the sequential exporter's order.

use crate::conformance::compact::{Covers, SetIndex};
use crate::conformance::config::{ConfBuilder, ConfConfig, Engine, IndexKind};
use crate::conformance::export_p::export_partitioned;
use crate::conformance::interchange::{
    conf_join, conf_join_merge, export, normal_line, parse_line, ExportError, ExportHeader,
    JoinReport, MissClass, Verdict,
};
use crate::conformance::interchange_default_tests::{
    ab_line, file, head_with, named, read_jsonl, scratch, AB,
};
use crate::conformance::online::{self, Mode, OnlineOpts, OnlineOut};
use crate::conformance::online_p::online_partitioned;
use crate::{Config, ConsType};
use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// The lines of a file sorted bytewise (a test-side sorter for fixtures written
/// in any order).
fn sorted_file(dir: &Path, name: &str, head: &str, lines: &[String]) -> PathBuf {
    let mut l = lines.to_vec();
    l.sort_unstable();
    file(dir, name, head, &l)
}
fn classes(r: &JoinReport) -> Vec<(MissClass, String)> {
    r.uncovered.clone()
}
fn same(spec: &Path, imp: &Path) -> (JoinReport, JoinReport) {
    let a =
        conf_join(spec, imp).unwrap_or_else(|e| panic!("conformance: SJ: old join refused: {e}"));
    let b = conf_join_merge(spec, imp)
        .unwrap_or_else(|e| panic!("conformance: SJ: merge join refused: {e}"));
    assert_eq!(a.verdict, b.verdict, "conformance: SJ: verdict");
    assert_eq!(a.exit_code(), b.exit_code(), "conformance: SJ: exit code");
    let mut ca = classes(&a);
    let mut cb = classes(&b);
    ca.sort();
    cb.sort();
    assert_eq!(ca, cb, "conformance: SJ: uncovered (class, line) set");
    assert_eq!(a.spec_lines, b.spec_lines);
    assert_eq!(a.impl_lines, b.impl_lines);
    (a, b)
}
/// A line over `a`, `b` with `a` sending `Acq(v)`: a second signature.
fn ab_v(v: u32, ab: u32) -> String {
    ab_line(ab).replace("\"f\":[0]", &format!("\"f\":[{v}]"))
}
/// A line with `b` blocked and no receive: another shape.
fn blocked_line() -> String {
    concat!(
        r#"{"statuses":{"a":"done","b":"blocked"},"#,
        r#""words":{"a":[{"s":{"t":"Acq","f":[0]}}],"b":[]},"counts":[0]}"#
    )
    .to_owned()
}

/// **M1**: agreement on conforming, violating and sampled pairs, with several
/// signatures and orders per signature.
#[test]
fn m1_agreement_with_the_in_memory_join() {
    let dir = scratch("m1");
    let spec = sorted_file(
        &dir,
        "spec.jsonl",
        AB,
        &[ab_line(0), ab_line(1), ab_v(1, 0), blocked_line()],
    );
    let conf = sorted_file(&dir, "conf.jsonl", AB, &[ab_line(1), ab_v(1, 1)]);
    let (a, b) = same(&spec, &conf);
    assert_eq!(a.verdict, Verdict::Conforms);
    assert_eq!(b.merge.unwrap().spec_groups, 3);
    assert_eq!(b.merge.unwrap().max_group_lines, 2);
    let viol = sorted_file(
        &dir,
        "viol.jsonl",
        AB,
        &[ab_line(1), ab_v(2, 0), ab_v(1, 1)],
    );
    let (a, _) = same(&spec, &viol);
    assert_eq!(a.verdict, Verdict::Violation);
    assert_eq!(classes(&a).len(), 1);
    let head = AB.replace("\"complete\"", "\"sampled\"");
    let sampled = sorted_file(&dir, "sampled.jsonl", &head, &[ab_line(1)]);
    let (a, _) = same(&spec, &sampled);
    assert_eq!(a.verdict, Verdict::NoVerdict);
}

/// **M2**: the refusals: an unsorted file, a repeated line, a malformed line
/// after the implementation ended, a malformed implementation line after a
/// violation, a non-complete specification.
#[test]
fn m2_the_refusals() {
    let dir = scratch("m2");
    let spec = sorted_file(&dir, "spec.jsonl", AB, &[ab_line(0), ab_line(1)]);
    let unsorted = file(&dir, "unsorted.jsonl", AB, &[ab_line(1), ab_line(0)]);
    let e = conf_join_merge(&spec, &unsorted).unwrap_err().to_string();
    assert!(
        e.contains("not sorted") && e.contains("line 3"),
        "conformance: SJ: {e}"
    );
    let repeat = file(&dir, "repeat.jsonl", AB, &[ab_line(0), ab_line(0)]);
    let e = conf_join_merge(&spec, &repeat).unwrap_err().to_string();
    assert!(e.contains("repeats line 2"), "conformance: SJ: {e}");
    // the specification has a malformed line after every implementation line was consumed
    let bad_tail = file(
        &dir,
        "badtail.jsonl",
        AB,
        &[ab_line(0), "{\"oops\":1}".to_owned()],
    );
    let imp = sorted_file(&dir, "imp.jsonl", AB, &[ab_line(0)]);
    assert!(
        conf_join_merge(&bad_tail, &imp).is_err(),
        "conformance: SJ: a malformed specification tail is refused"
    );
    // a violation, then a malformed implementation line
    let imp_bad = file(
        &dir,
        "impbad.jsonl",
        AB,
        &[ab_v(2, 0), "{\"oops\":1}".to_owned()],
    );
    assert!(
        conf_join_merge(&spec, &imp_bad).is_err(),
        "conformance: SJ: a malformed line after a violation is refused"
    );
    let head = AB.replace("\"complete\"", "\"bounded\"");
    let bounded = sorted_file(&dir, "bounded.jsonl", &head, &[ab_line(0)]);
    assert!(conf_join_merge(&bounded, &imp)
        .unwrap_err()
        .to_string()
        .contains("not `complete`"));
}

/// **M3**: the miss classes, with the specification's line of the same shape
/// after the missing signature in byte order (no-slot needs the whole file).
#[test]
fn m3_the_miss_classes() {
    let dir = scratch("m3");
    // spec: Acq(5) only (its shape = a sends, b receives, both done)
    let spec = sorted_file(&dir, "spec.jsonl", AB, &[ab_v(5, 1)]);
    // impl: Acq(1) (same shape, no slot: sorts before Acq(5)), the blocked shape (no bucket),
    // Acq(5) with count 0 (not found)
    let imp = sorted_file(
        &dir,
        "imp.jsonl",
        AB,
        &[ab_v(1, 1), blocked_line(), ab_v(5, 0)],
    );
    let (a, b) = same(&spec, &imp);
    let mut cs: Vec<MissClass> = classes(&b).into_iter().map(|(c, _)| c).collect();
    cs.sort();
    assert_eq!(
        cs,
        vec![MissClass::NoBucket, MissClass::NoSlot, MissClass::NotFound]
    );
    assert_eq!(classes(&a).len(), 3);
}

/// **M4**: one signature with thousands of orders is one group; an exact order
/// is a hit, a larger one is covered by the scan, a smaller one is not found.
#[test]
fn m4_a_large_group() {
    let dir = scratch("m4");
    // one signature: `a` sends Acq(0) twelve times, `b` receives once; an order = for each of
    // a's sends whether b's receive is before it (0/1), and for b's receive how many of a's
    // sends are before (0..12)
    const L: usize = 12;
    let line = |bits: u32, k: u32| -> String {
        let a_word = (0..L)
            .map(|_| r#"{"s":{"t":"Acq","f":[0]}}"#)
            .collect::<Vec<_>>()
            .join(",");
        let mut counts: Vec<String> = (0..L).map(|i| ((bits >> i) & 1).to_string()).collect();
        counts.push(k.to_string());
        format!(
            concat!(
                r#"{{"statuses":{{"a":"done","b":"done"}},"#,
                r#""words":{{"a":[{a_word}],"b":[{{"r":{{"t":"Acq","f":[0]}}}}]}},"#,
                r#""counts":[{counts}]}}"#
            ),
            a_word = a_word,
            counts = counts.join(",")
        )
    };
    // the specification holds orders with k >= 1 only (3000 of them)
    let mut spec_lines = Vec::new();
    'outer: for k in 1..=L as u32 {
        for bits in 0..(1u32 << L) {
            spec_lines.push(line(bits, k));
            if spec_lines.len() == 3000 {
                break 'outer;
            }
        }
    }
    let spec = sorted_file(&dir, "spec.jsonl", AB, &spec_lines);
    // impl: an exact held order (hit), a larger order (covered by the scan), an order with
    // k = 0 and no bits (not found)
    let imp = sorted_file(
        &dir,
        "imp.jsonl",
        AB,
        &[line(0, 0), line(5, 1), line((1 << L) - 1, L as u32)],
    );
    let (a, b) = same(&spec, &imp);
    assert_eq!(a.verdict, Verdict::Violation);
    assert_eq!(classes(&b), vec![(MissClass::NotFound, line(0, 0))]);
    let m = b.merge.unwrap();
    assert_eq!((m.spec_groups, m.max_group_lines), (1, 3000));
}

// =========================================================================
// The tester's: criteria SJ-1; derivation `log/dev/SORTED-JOIN.derived.md`
// =========================================================================

/// Writes a line to stderr (the `s5_tests` emission scan forbids the print macros).
macro_rules! note {
    ($($arg:tt)*) => {{
        use std::io::Write as _;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

/// The block's lines but its timers, by this file's own reading.
fn untimed(block: &str) -> Vec<String> {
    block
        .lines()
        .filter(|l| {
            let k = l.split(':').next().unwrap_or("");
            !k.ends_with("_ms") && !k.contains("rss")
        })
        .map(str::to_owned)
        .collect()
}

/// SJ-0.4 in full, on a valid sorted pair: verdict, exit, the (class, line) list in file order,
/// the line counts, the shape; the text but the `merge:` line; the block but its timers.
fn agree(spec: &Path, imp: &Path, what: &str) -> (JoinReport, JoinReport) {
    let a = conf_join(spec, imp).unwrap_or_else(|e| panic!("conformance: SJ: {what}: {e}"));
    let b = conf_join_merge(spec, imp)
        .unwrap_or_else(|e| panic!("conformance: SJ: {what}: merge: {e}"));
    assert_eq!(a.verdict, b.verdict, "conformance: SJ: {what}: verdict");
    assert_eq!(
        a.exit_code(),
        b.exit_code(),
        "conformance: SJ: {what}: exit"
    );
    assert_eq!(
        a.uncovered, b.uncovered,
        "conformance: SJ: {what}: uncovered"
    );
    assert_eq!(
        a.spec_lines, b.spec_lines,
        "conformance: SJ: {what}: spec lines"
    );
    assert_eq!(
        a.impl_lines, b.impl_lines,
        "conformance: SJ: {what}: impl lines"
    );
    assert_eq!(a.shape, b.shape, "conformance: SJ: {what}: shape");
    assert!(
        a.merge.is_none(),
        "conformance: SJ: {what}: merge stats on the in-memory join"
    );
    let (ta, tb) = (a.render(), b.render());
    assert!(!ta.contains("\nmerge: "), "conformance: SJ: {what}: {ta}");
    let m = b.merge.expect("conformance: SJ: merge stats");
    let want = format!(
        "merge: spec_groups={} impl_lines={} max_group_lines={}\n",
        m.spec_groups, b.impl_lines, m.max_group_lines
    );
    assert!(tb.contains(&want), "conformance: SJ: {what}: {tb}");
    assert_eq!(
        ta,
        tb.replacen(&want, "", 1),
        "conformance: SJ: {what}: the text"
    );
    assert_eq!(
        untimed(&a.measurements(0).to_string()),
        untimed(&b.measurements(0).to_string()),
        "conformance: SJ: {what}: the block"
    );
    (a, b)
}

fn classes_of(r: &JoinReport) -> Vec<MissClass> {
    r.uncovered.iter().map(|(c, _)| *c).collect()
}

fn lines_of(path: &Path) -> Vec<String> {
    read_jsonl(path).1
}

/// A line over `a`, `b`: `a` sends `Acq(v)` `n` times, `b` receives `Acq(0)`; the counts zero.
fn sends(v: u32, n: usize) -> String {
    let w = vec![format!(r#"{{"s":{{"t":"Acq","f":[{v}]}}}}"#); n].join(",");
    let c = vec!["0"; n + 1].join(",");
    format!(
        concat!(
            r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{w}],"#,
            r#""b":[{{"r":{{"t":"Acq","f":[0]}}}}]}},"counts":[{c}]}}"#
        ),
        w = w,
        c = c
    )
}

/// SJ-1.1: empty bodies on either side, an implementation ending before several groups, absent
/// signatures before, between and after held groups.
#[test]
fn sj1_the_edges() {
    let d = scratch("sj1a");
    let none: &[String] = &[];
    let one = |n: &str, l: &[String]| sorted_file(&d, n, AB, l);
    let (empty, g1) = (one("empty", none), one("g1", &[ab_v(1, 1)]));
    let (a, b) = agree(&empty, &empty, "both empty");
    assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ");
    assert_eq!(b.merge.unwrap().spec_groups, 0, "conformance: SJ");
    let (a, _) = agree(&g1, &empty, "implementation empty");
    assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ");
    let (a, _) = agree(&empty, &g1, "specification empty");
    assert_eq!(classes_of(&a), vec![MissClass::NoBucket], "conformance: SJ");

    let six: Vec<String> = (1..=6).map(|v| ab_v(v, 1)).collect();
    let (a, b) = agree(&one("six", &six), &g1, "the implementation ends first");
    assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ");
    assert_eq!(a.spec_lines, 6, "conformance: SJ");
    let m = b.merge.unwrap();
    assert_eq!(
        (m.spec_groups, m.max_group_lines),
        (6, 1),
        "conformance: SJ"
    );

    let spec = one("two-four", &[ab_v(2, 1), ab_v(4, 1)]);
    let imp: Vec<String> = (1..=5).map(|v| ab_v(v, 1)).collect();
    let (a, _) = agree(&spec, &one("five", &imp), "absent before, between, after");
    assert_eq!(
        a.uncovered,
        vec![
            (MissClass::NoSlot, ab_v(1, 1)),
            (MissClass::NoSlot, ab_v(3, 1)),
            (MissClass::NoSlot, ab_v(5, 1))
        ],
        "conformance: SJ"
    );
    // Several lines of one signature probing one group, a repeated group across a gap.
    let spec = one("orders", &[ab_v(2, 0), ab_v(2, 1), ab_v(4, 1)]);
    let imp = one("probes", &[ab_v(2, 0), ab_v(2, 1), ab_v(4, 0), ab_v(4, 1)]);
    let (a, _) = agree(&spec, &imp, "several probes per group");
    assert_eq!(
        a.uncovered,
        vec![(MissClass::NotFound, ab_v(4, 0))],
        "conformance: SJ"
    );
}

/// The implementation's enumeration against the verdict, with and without a miss.
#[test]
fn sj1_a_partial_implementation() {
    let d = scratch("sj1b");
    let spec = sorted_file(&d, "spec", AB, &[ab_v(1, 1)]);
    for (e, want) in [
        ("bounded", Verdict::Conforms),
        ("sampled", Verdict::NoVerdict),
        ("aborted", Verdict::Conforms),
    ] {
        let h = head_with(e);
        let fine = sorted_file(&d, "fine", &h, &[ab_v(1, 1)]);
        let (a, _) = agree(&spec, &fine, e);
        assert_eq!(a.verdict, want, "conformance: SJ: {e}");
        let miss = sorted_file(&d, "miss", &h, &[ab_v(2, 1)]);
        let (a, _) = agree(&spec, &miss, e);
        assert_eq!(a.verdict, Verdict::Violation, "conformance: SJ: {e}");
    }
}

/// A file sorted by normal form, its lines as they are; `file` in another directory if asked.
fn sorted_copy(from: &Path, to: &Path) {
    let (h, lines) = read_jsonl(from);
    let visible: Vec<String> = h["visible"]
        .as_array()
        .unwrap()
        .iter()
        .map(|x| x.as_str().unwrap().to_owned())
        .collect();
    let mut keyed: Vec<(String, String)> = lines
        .into_iter()
        .map(|l| {
            (
                normal_line(&l, &visible).expect("conformance: SJ: a golden line"),
                l,
            )
        })
        .collect();
    keyed.sort_unstable();
    let text = std::fs::read_to_string(from).unwrap();
    let mut out = format!("{}\n", text.lines().next().unwrap());
    for (_, l) in keyed {
        out.push_str(&l);
        out.push('\n');
    }
    std::fs::write(to, out).unwrap();
}

/// SJ-1.1 on JMC's golden files and J3's exports, each sorted by the helper: the four pairs of
/// each implementation row and its specification, a specification against itself, and each
/// row's sampled file. Ignored, as T10: `J3_GOLDEN` and `J3_OUT` name the directories. The raw
/// JMC files, unsorted, are refused (difference (c)) where they have a descent.
#[test]
#[ignore]
fn sj1_the_golden_pairs() {
    let gold = PathBuf::from(std::env::var_os("J3_GOLDEN").expect("conformance: SJ: J3_GOLDEN"));
    let tf = PathBuf::from(std::env::var_os("J3_OUT").expect("conformance: SJ: J3_OUT"));
    let d = scratch("sj1g");
    let sorted = |p: PathBuf, n: &str| {
        let to = d.join(n);
        sorted_copy(&p, &to);
        to
    };
    let mut rows: Vec<String> = std::fs::read_dir(&gold)
        .unwrap()
        .filter_map(|e| {
            let n = e.unwrap().file_name().into_string().unwrap();
            n.strip_suffix(".must.jsonl").map(str::to_owned)
        })
        .collect();
    rows.sort();
    let (mut pairs, mut refused, mut sampled, mut viol) = (0, 0, 0, 0);
    for row in &rows {
        // The row's size is its trailing numbers: k, q and, on a shard row, s.
        let parts: Vec<&str> = row.split('-').collect();
        let tail = parts
            .iter()
            .rev()
            .take_while(|p| p.parse::<u32>().is_ok())
            .count();
        let (fam, k, q) = (
            parts[0],
            parts[parts.len() - tail],
            parts[parts.len() - tail + 1],
        );
        let sr = format!("{fam}-spec-{k}-{q}");
        let g = |r: &str| gold.join(format!("{r}.must.jsonl"));
        let t = |r: &str| tf.join(format!("{r}.traceforge.jsonl"));
        let (gs, ts) = (sorted(g(&sr), "gs"), sorted(t(&sr), "ts"));
        let (gi, ti) = (sorted(g(row), "gi"), sorted(t(row), "ti"));
        for (what, s, i) in [
            ("JMC spec, JMC impl", &gs, &gi),
            ("JMC spec, TF impl", &gs, &ti),
            ("TF spec, JMC impl", &ts, &gi),
            ("TF spec, TF impl", &ts, &ti),
        ] {
            let (a, _) = agree(s, i, &format!("{row}: {what}"));
            viol += usize::from(a.verdict == Verdict::Violation);
            pairs += 1;
        }
        let rnd = sorted(gold.join(format!("{row}.random.jsonl")), "ri");
        let (a, _) = agree(&gs, &rnd, &format!("{row}: sampled"));
        assert_ne!(
            a.verdict,
            Verdict::Conforms,
            "conformance: SJ: {row}: a sampled file"
        );
        sampled += 1;
        // Difference (c): a raw JMC file with a descent is refused; the helper's copy is not.
        let raw = lines_of(&g(row));
        if raw.windows(2).any(|w| w[0] > w[1]) {
            let e = conf_join_merge(&gs, &g(row)).unwrap_err().to_string();
            assert!(e.contains("not sorted"), "conformance: SJ: {row}: {e}");
            refused += 1;
        }
    }
    let n = rows.len();
    note!("SJ: golden: {n} rows, {pairs} pairs, {viol} violating, {sampled} sampled");
    note!("SJ: golden: {refused} raw files refused");
    assert_eq!(rows.len(), 74, "conformance: SJ: the rows");
    assert!(refused > 0 && viol > 0, "conformance: SJ: both kinds");
}

/// SJ-1.3: the classes, with the shape in each place it can be.
#[test]
fn sj3_the_miss_classes() {
    let d = scratch("sj3");
    let f = |n: &str, l: &[String]| sorted_file(&d, n, AB, l);
    let miss = [ab_v(2, 1)];
    let imp = f("imp", &miss);
    // The shape only after the miss in byte order: met when the first group is loaded.
    let (a, _) = agree(&f("after", &[ab_v(5, 1)]), &imp, "shape after");
    assert_eq!(classes_of(&a), vec![MissClass::NoSlot], "conformance: SJ");
    // The shape only before it.
    let (a, _) = agree(&f("before", &[ab_v(1, 1)]), &imp, "shape before");
    assert_eq!(classes_of(&a), vec![MissClass::NoSlot], "conformance: SJ");
    // The shape only past the implementation's end: a group of another shape sits between, so
    // only the final drain reaches it.
    let between = sends(3, 2);
    assert!(
        ab_v(2, 1) < between && between < ab_v(5, 1),
        "conformance: SJ: the fixture"
    );
    let (a, _) = agree(
        &f("drain", &[between.clone(), ab_v(5, 1)]),
        &imp,
        "shape in the drain",
    );
    assert_eq!(classes_of(&a), vec![MissClass::NoSlot], "conformance: SJ");
    // No shape: the other shape alone.
    let (a, _) = agree(&f("other", &[between]), &imp, "no shape");
    assert_eq!(classes_of(&a), vec![MissClass::NoBucket], "conformance: SJ");
    // A held signature, no order.
    let (a, _) = agree(
        &f("hi", &[ab_v(2, 1)]),
        &f("lo", &[ab_v(2, 0)]),
        "not found",
    );
    assert_eq!(classes_of(&a), vec![MissClass::NotFound], "conformance: SJ");
    // A header alone.
    let (a, _) = agree(&f("head", &[] as &[String]), &imp, "a header");
    assert_eq!(classes_of(&a), vec![MissClass::NoBucket], "conformance: SJ");
    // All of them in one list, in file order.
    let spec = f("mix", &[ab_v(3, 1), ab_v(5, 1)]);
    let i = f(
        "mixi",
        &[
            blocked_line(),
            ab_v(1, 1),
            ab_v(3, 0),
            ab_v(5, 1),
            ab_v(6, 1),
        ],
    );
    let (a, _) = agree(&spec, &i, "mixed");
    assert_eq!(
        classes_of(&a),
        vec![
            MissClass::NoBucket,
            MissClass::NoSlot,
            MissClass::NotFound,
            MissClass::NoSlot
        ],
        "conformance: SJ: {:?}",
        a.uncovered
    );
}

fn refused_by_merge(spec: &Path, imp: &Path, what: &str, want: &str) -> String {
    let e = conf_join_merge(spec, imp)
        .err()
        .unwrap_or_else(|| panic!("conformance: SJ: {what}: the merge accepted"))
        .to_string();
    assert!(e.contains(want), "conformance: SJ: {what}: {e}");
    e
}

fn refused_by_both(spec: &Path, imp: &Path, what: &str, want: &str) -> (String, String) {
    let m = refused_by_merge(spec, imp, what, want);
    let o = conf_join(spec, imp)
        .err()
        .unwrap_or_else(|| panic!("conformance: SJ: {what}: the in-memory join accepted"))
        .to_string();
    (m, o)
}

/// Each refusal, each side, with its message.
#[test]
fn sj4_a_descent_on_either_side() {
    let d = scratch("sj4a");
    let ok = file(&d, "ok", AB, &[ab_v(1, 0), ab_v(1, 1), ab_v(2, 1)]);
    for (what, lines, at) in [
        ("across groups", vec![ab_v(2, 1), ab_v(1, 1)], "line 3"),
        ("within a group", vec![ab_v(1, 1), ab_v(1, 0)], "line 3"),
        (
            "later on",
            vec![ab_v(1, 0), ab_v(3, 1), ab_v(2, 1)],
            "line 4",
        ),
    ] {
        let bad = file(&d, "bad", AB, &lines);
        let e = refused_by_merge(&ok, &bad, what, "not sorted");
        assert!(
            e.contains(at) && e.contains("bad"),
            "conformance: SJ: {what}: {e}"
        );
        let e = refused_by_merge(&bad, &ok, what, "not sorted");
        assert!(
            e.contains(at) && e.contains("bad"),
            "conformance: SJ: {what}: {e}"
        );
        // Difference (c): the in-memory join takes it.
        assert!(conf_join(&ok, &bad).is_ok(), "conformance: SJ: {what}");
        assert!(conf_join(&bad, &ok).is_ok(), "conformance: SJ: {what}");
    }
}

/// A repeat, in the normal form, whatever its text: whitespace, member order, `n`.
#[test]
fn sj4_a_normalised_duplicate_on_either_side() {
    let d = scratch("sj4b");
    let l = ab_v(1, 1);
    let ok = file(&d, "ok", AB, &[l.clone()]);
    let parts = l.strip_prefix('{').unwrap().strip_suffix('}').unwrap();
    let (st, rest) = parts.split_once(",\"words\"").unwrap();
    let reordered = format!("{{\"words\"{rest},{st}}}");
    for (what, other) in [
        ("whitespace", format!("{{ {parts} }}")),
        ("member order", reordered),
        ("n", format!("{{{parts},\"n\":3}}")),
        ("an escape", l.replace("\"Acq\"", "\"\\u0041cq\"")),
        ("the same text", l.clone()),
    ] {
        let dup = file(&d, "dup", AB, &[l.clone(), other.clone()]);
        let (_, o) = refused_by_both(&ok, &dup, what, "repeats line 2");
        assert!(o.contains("repeats line 2"), "conformance: SJ: {what}: {o}");
        let (_, o) = refused_by_both(&dup, &ok, what, "repeats line 2");
        assert!(o.contains("repeats line 2"), "conformance: SJ: {what}: {o}");
    }
}

/// A line reached only in the final drain, past the implementation's end; a malformed
/// implementation line past a violation; a header refusal; an empty file.
#[test]
fn sj4_the_drain_and_the_rest() {
    let d = scratch("sj4c");
    let bad = "{\"oops\":1}".to_owned();
    let imp = file(&d, "imp", AB, &[ab_v(1, 1)]);
    // [G1, G2, malformed] against [G1]: G2 is the lookahead when the implementation ends.
    let s = file(&d, "s1", AB, &[ab_v(1, 1), ab_v(2, 1), bad.clone()]);
    refused_by_both(
        &s,
        &imp,
        "malformed in the drain",
        "line 4: unknown key `oops`",
    );
    let s = file(&d, "s2", AB, &[ab_v(1, 1), ab_v(3, 1), ab_v(2, 1)]);
    refused_by_merge(
        &s,
        &imp,
        "a descent in the drain",
        "line 4: the file is not sorted",
    );
    let s = file(&d, "s3", AB, &[ab_v(1, 1), ab_v(2, 1), ab_v(2, 1)]);
    refused_by_both(
        &s,
        &imp,
        "a repeat in the drain",
        "line 4: the line repeats line 3",
    );
    // With an implementation of a header only.
    let none = file(&d, "none", AB, &[] as &[String]);
    let s = file(&d, "s4", AB, &[ab_v(1, 1), ab_v(2, 1), bad.clone()]);
    refused_by_both(&s, &none, "the drain alone", "line 4: unknown key `oops`");
    // A violation, then a malformed line on the implementation's side.
    let spec = file(&d, "spec", AB, &[ab_v(1, 1)]);
    let i = file(&d, "i2", AB, &[ab_v(2, 1), bad.clone()]);
    refused_by_both(&spec, &i, "past a violation", "line 3: unknown key `oops`");
    // The header's refusals.
    let bounded = file(&d, "bounded", &head_with("bounded"), &[ab_v(1, 1)]);
    refused_by_both(&bounded, &imp, "non-complete", "not `complete`");
    let other = AB.replace(r#"["a","b"]"#, r#"["a","c"]"#);
    let v = file(&d, "v", &other, &[] as &[String]);
    refused_by_both(&spec, &v, "visible", "`visible` lists differ");
    refused_by_both(&v, &spec, "visible, reversed", "`visible` lists differ");
    // The same names in another order: refused alike, as the lists are compared as they are.
    let swapped = AB.replace(r#"["a","b"]"#, r#"["b","a"]"#);
    let v = file(&d, "swapped", &swapped, &[ab_v(1, 1)]);
    refused_by_both(
        &spec,
        &v,
        "visible in another order",
        "`visible` lists differ",
    );
    // An empty file, either side.
    let e = d.join("empty");
    std::fs::write(&e, "").unwrap();
    refused_by_both(&e, &spec, "empty specification", "the file is empty");
    refused_by_both(&spec, &e, "empty implementation", "the file is empty");
    let gone = d.join("gone");
    refused_by_both(&gone, &spec, "no specification", "gone");
    refused_by_both(&spec, &gone, "no implementation", "gone");
}

/// The line forms that a stream and a whole-file read could treat apart.
#[test]
fn sj4_what_lies_between_the_lines() {
    let d = scratch("sj4d");
    let spec = file(&d, "spec", AB, &[ab_v(1, 1)]);
    let write = |n: &str, bytes: Vec<u8>| {
        let p = d.join(n);
        std::fs::write(&p, bytes).unwrap();
        p
    };
    let body = format!("{AB}\n{}", ab_v(1, 1));
    // No final newline; CRLF; a CR at the very end: all accepted alike.
    let p = write("nonl", body.clone().into_bytes());
    agree(&spec, &p, "no final newline");
    let p = write("crlf", format!("{AB}\r\n{}\r\n", ab_v(1, 1)).into_bytes());
    agree(&spec, &p, "CRLF");
    let p = write("cr", format!("{body}\r").into_bytes());
    agree(&spec, &p, "a final CR");
    // A blank line; invalid UTF-8; both refused.
    let p = write("blank", format!("{body}\n\n").into_bytes());
    refused_by_both(&spec, &p, "a blank line", "not JSON");
    let mut b = format!("{body}\n").into_bytes();
    b.extend_from_slice(&[0xff, 0xfe, b'\n']);
    let p = write("utf8", b);
    refused_by_both(&spec, &p, "invalid UTF-8", "utf8");
    let p = write("bom", format!("\u{feff}{body}\n").into_bytes());
    refused_by_both(&spec, &p, "a BOM", "header");
}

/// Difference (e): each refused by both, each with its own message.
#[test]
fn sj4_difference_e() {
    let d = scratch("sj4e");
    let bad = "{\"oops\":1}".to_owned();
    // A bounded specification with a malformed body.
    let s = file(&d, "s", &head_with("bounded"), &[ab_v(1, 1), bad.clone()]);
    let i = file(&d, "i", AB, &[ab_v(1, 1)]);
    let (m, o) = refused_by_both(&s, &i, "bounded, malformed", "not `complete`");
    assert!(o.contains("unknown key `oops`"), "conformance: SJ: {o}");
    note!("SJ: (e) bounded: merge `{m}`; in-memory `{o}`");
    // Unequal `visible` lists with malformed bodies.
    let other = AB.replace(r#"["a","b"]"#, r#"["a","c"]"#);
    let s = file(&d, "s2", AB, &[bad.clone()]);
    let i = file(&d, "i2", &other, &[bad.clone()]);
    let (m, o) = refused_by_both(&s, &i, "visible, malformed", "`visible` lists differ");
    assert!(o.contains("unknown key `oops`"), "conformance: SJ: {o}");
    note!("SJ: (e) visible: merge `{m}`; in-memory `{o}`");
    // A compatible pair: the implementation's malformed line first, a later specification's.
    let s = file(
        &d,
        "s3",
        AB,
        &[ab_v(1, 1), ab_v(2, 1), ab_v(3, 1), bad.clone()],
    );
    let i = file(&d, "i3", AB, &[bad.clone()]);
    let (m, o) = refused_by_both(&s, &i, "both bodies", "i3");
    assert!(m.contains("unknown key `oops`"), "conformance: SJ: {m}");
    assert!(
        o.contains("s3") && o.contains("unknown key `oops`"),
        "conformance: SJ: {o}"
    );
    note!("SJ: (e) both: merge `{m}`; in-memory `{o}`");
}

/// A line of one value `x` sent by `a`, received as `y` by `b`.
fn valued(x: &str, y: &str) -> String {
    format!(
        concat!(
            r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{{"s":{x}}}],"#,
            r#""b":[{{"r":{y}}}]}},"counts":[0,1]}}"#
        ),
        x = x,
        y = y
    )
}

/// SJ-1.5: values whose text could confuse the group key or the order.
#[test]
fn sj5_the_values() {
    let d = scratch("sj5");
    let vals: Vec<&str> = vec![
        "1",
        "10",
        "-1",
        "\"\"",
        "\"a\"",
        "\"a\\\"b\"",
        "\"a\\\\\"",
        "\"\\n\\t\"",
        "\"\\u0000\"",
        "\"\u{e9}\"",
        "\"\u{1F600}\"",
        "\",\\\"counts\\\":[0]\"",
        "\",\"",
        "true",
        "false",
        "[]",
        "[1,2]",
        "[2,1]",
        "[[1],[2]]",
        r#"{"t":"Acq","f":[]}"#,
        r#"{"t":"Acq","f":[1,{"t":"N","f":[[2,"x"]]}]}"#,
        r#"{"t":"counts","f":[0]}"#,
    ];
    // Every other value in the specification, every value in the implementation, with `{"r":null}`.
    let lines: Vec<String> = vals.iter().map(|v| valued(v, "1")).collect();
    let spec: Vec<String> = lines.iter().step_by(2).cloned().collect();
    let (s, i) = (
        sorted_file(&d, "s", AB, &spec),
        sorted_file(&d, "i", AB, &lines),
    );
    let (a, _) = agree(&s, &i, "values");
    assert_eq!(
        a.uncovered.len(),
        lines.len() - spec.len(),
        "conformance: SJ"
    );
    let (a, _) = agree(&i, &i, "values against themselves");
    assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ");
    let recv = sorted_file(&d, "r", AB, &[valued("1", "null"), valued("1", "2")]);
    let (a, _) = agree(&recv, &recv, "a receive of nothing");
    assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ");
    // The two spellings of a value: one normal form, one signature, one group.
    let spelt = file(&d, "spelt", AB, &[valued("\"\\u0041\"", "1")]);
    let plain = file(&d, "plain", AB, &[valued("\"A\"", "1")]);
    let (a, _) = agree(&spelt, &plain, "two spellings");
    assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ");
    // Numbers version 1 forbids, on the side the reader meets them.
    for n in ["1.0", "1e0", "-0", "18446744073709551615"] {
        let bad = file(&d, "bad", AB, &[valued(n, "1")]);
        refused_by_both(&s, &bad, n, "version 1");
    }
}

const COUNTS_HEAD: &str = concat!(
    r#"{"format":1,"tool":"t","program":"p","size":"s","visible":["a","b","counts"],"#,
    r#""model":"p2p","enumeration":"complete","encoding":1}"#
);

/// A role named `counts`, so `,"counts":` occurs inside the signature text too.
fn role_counts(v: u32, c: u32) -> String {
    format!(
        concat!(
            r#"{{"statuses":{{"a":"done","b":"done","counts":"done"}},"#,
            r#""words":{{"a":[{{"s":{v}}}],"b":[],"counts":[{{"r":{v}}}]}},"#,
            r#""counts":[0,0,{c},0]}}"#
        ),
        v = v,
        c = c
    )
}

/// Roles named so that one is a prefix of another, and a role named `counts`.
#[test]
fn sj5_the_roles() {
    let d = scratch("sj5b");
    let l: Vec<String> = [(1, 0), (1, 1), (2, 1), (3, 1)]
        .map(|(v, c)| role_counts(v, c))
        .to_vec();
    let s = sorted_file(&d, "s", COUNTS_HEAD, &[l[1].clone(), l[3].clone()]);
    let i = sorted_file(&d, "i", COUNTS_HEAD, &l);
    let (a, b) = agree(&s, &i, "a role named counts");
    let mut got = classes_of(&a);
    got.sort();
    assert_eq!(
        got,
        vec![MissClass::NoSlot, MissClass::NotFound],
        "conformance: SJ"
    );
    assert_eq!(b.merge.unwrap().spec_groups, 2, "conformance: SJ");
    let head = AB.replace(r#"["a","b"]"#, r#"["a","ab"]"#);
    let line = |v: u32| ab_v(v, 1).replace("\"b\":", "\"ab\":");
    let s = sorted_file(&d, "s2", &head, &[line(2)]);
    let i = sorted_file(&d, "i2", &head, &[line(1), line(2), line(3)]);
    let (a, _) = agree(&s, &i, "a role prefix of another");
    assert_eq!(a.uncovered.len(), 2, "conformance: SJ");
}

/// A line of `n` sends and a count at `c`, for counts above 255 and word lengths around it.
fn wide(n: usize, c: usize) -> String {
    let w = vec![r#"{"s":1}"#; n].join(",");
    let mut cs = vec!["0".to_owned(); n];
    cs.push(c.to_string());
    format!(
        concat!(
            r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{w}],"b":[{{"r":1}}]}},"#,
            r#""counts":[{c}]}}"#
        ),
        w = w,
        c = cs.join(",")
    )
}

#[test]
fn sj5_counts_above_255() {
    let d = scratch("sj5c");
    for n in [255usize, 256, 300] {
        let s = sorted_file(&d, "s", AB, &[wide(n, 200), wide(n, n)]);
        let i = sorted_file(
            &d,
            "i",
            AB,
            &[wide(n, 199), wide(n, 200), wide(n, n - 1), wide(n, n)],
        );
        let (a, _) = agree(&s, &i, &format!("{n} events"));
        assert_eq!(
            a.uncovered,
            vec![(MissClass::NotFound, wide(n, 199))],
            "conformance: SJ"
        );
    }
    // A count past the word's length, refused alike.
    let s = file(&d, "s", AB, &[wide(300, 300)]);
    let bad = file(&d, "bad", AB, &[wide(300, 301)]);
    refused_by_both(&s, &bad, "a count past the word", "exceeds the length");
    // A width that differs inside one group cannot be: the width is the signature's.
    let m = sorted_file(&d, "m", AB, &[wide(255, 255), wide(256, 256)]);
    let (a, b) = agree(&m, &m, "two widths");
    assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ");
    assert_eq!(b.merge.unwrap().spec_groups, 2, "conformance: SJ");
}

/// `a` sends 12 sends' line, as M4's: one signature, thousands of orders.
fn big_order(bits: u32, k: u32) -> String {
    const L: usize = 12;
    let w = vec![r#"{"s":0}"#; L].join(",");
    let mut c: Vec<String> = (0..L).map(|i| ((bits >> i) & 1).to_string()).collect();
    c.push(k.to_string());
    format!(
        concat!(
            r#"{{"statuses":{{"a":"done","b":"done"}},"words":{{"a":[{w}],"b":[{{"r":0}}]}},"#,
            r#""counts":[{c}]}}"#
        ),
        w = w,
        c = c.join(",")
    )
}

/// SJ-1.6: thousands of orders. The merge's `Found` hides which path answered, so the group's
/// index, built in file order as the merge builds it, tells an exact hit from a scan.
#[test]
fn sj6_a_large_group() {
    let d = scratch("sj6");
    let mut lines = Vec::new();
    'all: for k in 1..=12 {
        for bits in 0..(1u32 << 12) {
            lines.push(big_order(bits, k));
            if lines.len() == 5000 {
                break 'all;
            }
        }
    }
    let s = sorted_file(&d, "s", AB, &lines);
    let exact = big_order(5, 1);
    let scan = big_order((1 << 12) - 1, 12);
    let none = big_order(0, 0);
    let i = sorted_file(&d, "i", AB, &[exact.clone(), scan.clone(), none.clone()]);
    let (a, b) = agree(&s, &i, "large");
    assert_eq!(
        a.uncovered,
        vec![(MissClass::NotFound, none.clone())],
        "conformance: SJ"
    );
    let m = b.merge.unwrap();
    assert_eq!(
        (m.spec_groups, m.max_group_lines),
        (1, 5000),
        "conformance: SJ"
    );
    let names = vec!["a".to_owned(), "b".to_owned()];
    let mut sorted = lines.clone();
    sorted.sort_unstable();
    let mut index = SetIndex::new();
    for l in &sorted {
        index.insert(&parse_line(l, &names).unwrap().1);
    }
    let q = |t: &str| parse_line(t, &names).unwrap().1;
    let before = (index.stats().exact_hits, index.stats().containment_tests);
    assert!(
        matches!(index.covers(&q(&exact)).1, Covers::Found(_)),
        "conformance: SJ"
    );
    let after = (index.stats().exact_hits, index.stats().containment_tests);
    assert_eq!(
        after,
        (before.0 + 1, before.1),
        "conformance: SJ: an exact hit"
    );
    assert!(
        matches!(index.covers(&q(&scan)).1, Covers::Found(_)),
        "conformance: SJ"
    );
    let scanned = (index.stats().exact_hits, index.stats().containment_tests);
    assert_eq!(
        scanned.0, after.0,
        "conformance: SJ: a scan is no exact hit"
    );
    assert!(scanned.1 > after.1, "conformance: SJ: a scan tests");
    assert!(
        matches!(index.covers(&q(&none)).1, Covers::NotFound),
        "conformance: SJ"
    );
}

/// SJ-1.7 in-process: the load time isn't counted twice (Codex 1). One implementation line past
/// every group, so all the specification is loaded inside one probe.
#[test]
fn sj7_the_timers() {
    let d = scratch("sj7");
    let spec: Vec<String> = (0..30000u32).map(|v| ab_v(v + 100_000, 1)).collect();
    let s = sorted_file(&d, "s", AB, &spec);
    let i = sorted_file(&d, "i", AB, &[ab_v(999_999, 1)]);
    let r = conf_join_merge(&s, &i).unwrap();
    note!(
        "SJ: index {} lookup {} join {}",
        r.index_ms,
        r.lookup_ms,
        r.join_ms
    );
    assert!(
        r.index_ms >= 10,
        "conformance: SJ: the fixture: index {}",
        r.index_ms
    );
    assert!(
        r.index_ms + r.lookup_ms <= r.join_ms + 2,
        "conformance: SJ: index {} + lookup {} against join {}",
        r.index_ms,
        r.lookup_ms,
        r.join_ms
    );
}

// =========================================================================
// SJ-1.2, 1.8: the exporters
// =========================================================================

#[derive(Clone, Debug, PartialEq)]
struct Fielded {
    a: i32,
    b: String,
}

#[derive(Clone, Debug, PartialEq)]
enum E {
    S(String),
    I(i64),
    N(Option<i32>),
    L(Vec<i32>),
    B(bool),
    F(Fielded),
    Set(BTreeSet<i32>),
    Nest(Box<E>),
    Unit,
}

fn awkward() -> Vec<E> {
    let s = |t: &str| E::S(t.to_owned());
    vec![
        s("plain"),
        s("q\"uote\\"),
        s("line\nbreak\ttab\r"),
        s("\u{e9}"),
        s("\u{301}"),
        s("\u{7f}"),
        s("\u{200b}"),
        s("\u{1F600}"),
        s("\u{0}"),
        s(",\"counts\":[0]"),
        E::I(i64::MIN),
        E::I(i64::MAX),
        E::I(-1),
        E::I(10),
        E::I(9),
        E::N(None),
        E::N(Some(-5)),
        E::I(100),
        E::I(-100),
        E::I(0),
        E::I(1),
        E::L(vec![]),
        E::L(vec![3, 1]),
        E::B(true),
        E::F(Fielded {
            a: 1,
            b: "b".to_owned(),
        }),
        E::Set(BTreeSet::from([3, 1, 2])),
        E::Set(BTreeSet::new()),
        E::Nest(Box::new(E::Nest(Box::new(E::Unit)))),
        E::Unit,
        s("zz"),
        s(""),
        s(" "),
    ]
}

/// `v` sends the value at an index of `nondet`s: 32 graphs, 32 lines, in the DFS's order.
fn sends_one_of(values: Vec<E>) {
    let mut i = 0;
    for _ in 0..5 {
        i = 2 * i + usize::from(crate::nondet());
    }
    let (tx, _rx) = crate::channel::Builder::<E>::new().build();
    let v = named("v", move || tx.send_msg(values[i % values.len()].clone()));
    v.join().unwrap();
}

fn cc_of(engine: Engine, visible: &[&str]) -> ConfConfig {
    let mut b = ConfBuilder::new()
        .config(
            Config::builder()
                .with_cons_type(ConsType::Bag)
                .with_seed(0)
                .build(),
        )
        .visible_threads(visible.iter().map(|s| (*s).to_owned()))
        .engine(engine)
        .index(IndexKind::Set);
    if matches!(engine, Engine::SverifyP) {
        b = b.threads(2);
    }
    b.build().expect("conformance: SJ: a configuration")
}

fn head(program: &str) -> ExportHeader {
    ExportHeader {
        program: program.to_owned(),
        size: "s".to_owned(),
    }
}

/// Byte order, by this file's own comparison on the raw bytes, and each line its normal form.
fn in_order(path: &Path, visible: &[&str], what: &str) -> Vec<String> {
    let bytes = std::fs::read(path).unwrap();
    assert_eq!(
        bytes.last(),
        Some(&b'\n'),
        "conformance: SJ: {what}: the last newline"
    );
    let lines: Vec<&[u8]> = bytes[..bytes.len() - 1]
        .split(|b| *b == b'\n')
        .skip(1)
        .collect();
    assert!(
        lines.windows(2).all(|w| w[0] < w[1]),
        "conformance: SJ: {what}: not strictly increasing bytes"
    );
    let names: Vec<String> = visible.iter().map(|s| (*s).to_owned()).collect();
    let ls = lines_of(path);
    for l in &ls {
        assert_eq!(
            &normal_line(l, &names).unwrap(),
            l,
            "conformance: SJ: {what}: not normal"
        );
    }
    ls
}

/// Both exporters, on values whose text could differ from the reader's normal form, or sort
/// otherwise: their own files in byte order, normal, equal, and joined all four ways.
#[test]
fn sj2_both_exporters_on_awkward_values() {
    let d = scratch("sj2a");
    let all = awkward();
    let half: Vec<E> = all.iter().step_by(2).cloned().collect();
    let vis = ["v"];
    let (a1, a2) = (all.clone(), all.clone());
    let (ss, ps) = (d.join("ss"), d.join("ps"));
    let gs = export(
        &cc_of(Engine::Stateful, &vis),
        move || sends_one_of(a1.clone()),
        &head("s"),
        &ss,
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: sequential: {e}"));
    export_partitioned(
        &cc_of(Engine::SverifyP, &vis),
        move || sends_one_of(a2.clone()),
        &head("s"),
        &ps,
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: parallel: {e}"));
    assert_eq!(gs.lines, 32, "conformance: SJ: the lines");
    let (ls, lp) = (in_order(&ss, &vis, "seq"), in_order(&ps, &vis, "par"));
    assert_eq!(ls, lp, "conformance: SJ: the two exporters' lines");
    assert_eq!(
        std::fs::read(&ss).unwrap(),
        std::fs::read(&ps).unwrap(),
        "conformance: SJ: the whole file"
    );
    let (h1, h2) = (half.clone(), half.clone());
    let (si, pi) = (d.join("si"), d.join("pi"));
    export(
        &cc_of(Engine::Stateful, &vis),
        move || sends_one_of(h1.clone()),
        &head("i"),
        &si,
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: sequential: {e}"));
    export_partitioned(
        &cc_of(Engine::SverifyP, &vis),
        move || sends_one_of(h2.clone()),
        &head("i"),
        &pi,
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: parallel: {e}"));
    // All lines against half: a miss for each of the rest; half against all: none.
    for (s, i, tag) in [
        (&ss, &si, "ss"),
        (&ss, &pi, "sp"),
        (&ps, &si, "ps"),
        (&ps, &pi, "pp"),
    ] {
        let (a, _) = agree(s, i, &format!("{tag} conforming"));
        assert_eq!(a.verdict, Verdict::Conforms, "conformance: SJ: {tag}");
        let (a, _) = agree(i, s, &format!("{tag} violating"));
        assert_eq!(a.verdict, Verdict::Violation, "conformance: SJ: {tag}");
        assert_eq!(a.uncovered.len(), 16, "conformance: SJ: {tag}");
    }
}

/// `D`'s `Debug` hides its field, so two values render one line; `Bad` can't be parsed.
#[derive(Clone, PartialEq)]
enum D {
    Alike(i32),
    Zlike(i32),
    Bad,
}

impl std::fmt::Debug for D {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            D::Alike(_) => write!(f, "Alike"),
            D::Zlike(_) => write!(f, "Zlike"),
            D::Bad => write!(f, "@@"),
        }
    }
}

fn sends_d(values: Vec<D>) {
    let x = usize::from(crate::nondet());
    let y = usize::from(crate::nondet());
    let (tx, _rx) = crate::channel::Builder::<D>::new().build();
    let v = named("v", move || {
        tx.send_msg(values[(2 * x + y) % values.len()].clone())
    });
    v.join().unwrap();
}

/// SJ-1.8: `Collision` refused before any file; difference (b): an encoding refusal comes first
/// wherever it falls, and the `Collision`'s line is the smallest colliding; a failed write
/// leaves no temporary.
#[test]
fn sj8_collision_and_difference_b() {
    let d = scratch("sj8a");
    let run = |vals: Vec<D>, name: &str| {
        let p = d.join(name);
        std::fs::write(&p, "earlier\n").unwrap();
        let r = export(
            &cc_of(Engine::Stateful, &["v"]),
            move || sends_d(vals.clone()),
            &head("c"),
            &p,
        );
        assert_eq!(
            std::fs::read_to_string(&p).unwrap(),
            "earlier\n",
            "conformance: SJ: {name}"
        );
        assert!(
            !d.join(format!("{name}.tmp")).exists(),
            "conformance: SJ: {name}: a .tmp"
        );
        r
    };
    // A collision alone, in either arrangement.
    for (name, vals) in [
        (
            "c1",
            vec![D::Alike(1), D::Alike(2), D::Zlike(1), D::Zlike(2)],
        ),
        (
            "c2",
            vec![D::Zlike(1), D::Zlike(2), D::Alike(1), D::Alike(2)],
        ),
        (
            "c3",
            vec![D::Zlike(1), D::Alike(1), D::Zlike(2), D::Alike(2)],
        ),
    ] {
        match run(vals, name) {
            Err(ExportError::Collision { line }) => {
                assert!(
                    line.contains("Alike"),
                    "conformance: SJ: {name}: the smallest: {line}"
                )
            }
            other => panic!("conformance: SJ: {name}: {other:?}"),
        }
    }
    // A collision and an encoding refusal, in each place: the encoding refusal.
    for (name, vals) in [
        ("b1", vec![D::Alike(1), D::Alike(2), D::Bad, D::Zlike(1)]),
        ("b2", vec![D::Bad, D::Alike(1), D::Alike(2), D::Zlike(1)]),
        ("b3", vec![D::Alike(1), D::Bad, D::Alike(2), D::Zlike(1)]),
    ] {
        match run(vals, name) {
            Err(ExportError::Collision { line }) => {
                panic!("conformance: SJ: {name}: the collision came first: {line}")
            }
            Err(e) => {
                let t = e.to_string();
                assert!(t.contains("@@"), "conformance: SJ: {name}: {t}");
            }
            Ok(_) => panic!("conformance: SJ: {name}: written"),
        }
    }
    // A failed write: the target is a directory, so the rename fails.
    let target = d.join("adir");
    std::fs::create_dir(&target).unwrap();
    let r = export(
        &cc_of(Engine::Stateful, &["v"]),
        || sends_one_of(awkward()),
        &head("w"),
        &target,
    );
    assert!(
        matches!(r, Err(ExportError::Io(_))),
        "conformance: SJ: {r:?}"
    );
    assert!(
        !d.join("adir.tmp").exists(),
        "conformance: SJ: a .tmp behind"
    );
    // A replacing write over an earlier file; no temporary.
    let p = d.join("over");
    std::fs::write(&p, "earlier\n").unwrap();
    export(
        &cc_of(Engine::Stateful, &["v"]),
        || sends_one_of(awkward()),
        &head("w"),
        &p,
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: {e}"));
    assert_eq!(lines_of(&p).len(), 32, "conformance: SJ: replaced");
    assert!(
        !d.join("over.tmp").exists(),
        "conformance: SJ: a .tmp behind"
    );
}

/// `online --out`, both paths: it reads under `--merge`, and the join agrees with the run.
#[test]
fn sj8_online_out_reads_under_merge() {
    let d = scratch("sj8b");
    let spec = d.join("spec");
    let all = awkward();
    let half: Vec<E> = all.iter().step_by(2).cloned().collect();
    let cfg = Config::builder()
        .with_cons_type(ConsType::Bag)
        .with_seed(0)
        .build();
    let vis = vec!["v".to_owned()];
    let h = half.clone();
    export(
        &cc_of(Engine::Stateful, &["v"]),
        move || sends_one_of(h.clone()),
        &head("s"),
        &spec,
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: {e}"));
    let out = |p: &Path| OnlineOut {
        path: p.to_owned(),
        header: head("i"),
    };
    let (so, po) = (d.join("so"), d.join("po"));
    let a2 = all.clone();
    let r = online::online(
        &cfg,
        &vis,
        Arc::new(move || sends_one_of(a2.clone())),
        &spec,
        OnlineOpts::new(Mode::Full, None, Some(out(&so))),
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: {e:?}"));
    let a3 = all.clone();
    let q = online_partitioned(
        &cfg,
        2,
        &vis,
        Arc::new(move || sends_one_of(a3.clone())),
        &spec,
        Some(out(&po)),
    )
    .unwrap_or_else(|e| panic!("conformance: SJ: {e:?}"));
    for (f, rep, tag) in [(&so, &r, "sequential"), (&po, &q, "parallel")] {
        let ls = in_order(f, &["v"], tag);
        assert_eq!(ls.len(), rep.impl_lines, "conformance: SJ: {tag}");
        let (a, _) = agree(&spec, f, tag);
        assert_eq!(
            a.uncovered.len(),
            rep.uncovered_distinct,
            "conformance: SJ: {tag}"
        );
    }
}

/// `HashSet` is used by the awkward list's neighbours only through the join; keep the import
/// honest with one set-valued check of the classes.
#[test]
fn sj3_the_uncovered_set_is_the_lines_missing() {
    let d = scratch("sj3b");
    let s = sorted_file(&d, "s", AB, &[ab_v(2, 1)]);
    let i = sorted_file(&d, "i", AB, &[ab_v(1, 1), ab_v(2, 1), ab_v(3, 1)]);
    let (a, _) = agree(&s, &i, "set");
    let got: HashSet<String> = a.uncovered.iter().map(|(_, l)| l.clone()).collect();
    assert_eq!(
        got,
        HashSet::from([ab_v(1, 1), ab_v(3, 1)]),
        "conformance: SJ"
    );
}
