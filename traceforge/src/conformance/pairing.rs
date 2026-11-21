//! The pairing check: before two summary files are compared, verify the
//! restrictions a meaningful join needs, each reported with its row (`C2` …
//! `C18`) of the release-1 comparison contract between JMC's and TraceForge's
//! summary files.
//!
//! The rows checked here, on the files alone:
//! - **C2**: `visible` and, when both headers carry it, `roles` are byte-sorted
//!   lists of distinct names, and equal on both sides.
//! - **C3**: the two `model`s are equal and in the supported set `p2p`, `asyn`.
//! - **C4**: the specification's `enumeration` is `complete`.
//! - **C6**: each file's lines are distinct (by their normal form); under
//!   `--merge` they are also in byte order.
//! - **C10**: every count is at most 2^31−1 (the bound both readers accept) and
//!   every word has at most 2^31−1 events. Under `--decide` a count above 65535
//!   is a warning: Decide refuses it only in a line it classifies. C10 reads the
//!   raw line, before it is parsed: a count above the bound is reported even in
//!   a line the reader would also refuse (a count longer than its word).
//! - **C13**: a tag used on both sides is used with the same field arities on
//!   both. A tag seen on one side only is a warning, never a failure: a
//!   specification-only tag is one the implementation never sends, and an
//!   implementation-only tag is left to the join, which reports its lines as
//!   uncovered.
//! - **C18**: identities are role names. A role name is a JSON string and
//!   cannot be told from any other string, and a tag name does not establish a
//!   type, so C18 cannot fail on the files alone: it is the programs'
//!   obligation. A value tagged `ThreadId` or `Tid` (the names of the two tools'
//!   identity types) is a warning that it may be a raw identity.
//!
//! A header the join's reader refuses (a missing or ill-typed field, an invalid,
//! unsorted or repeated role name, `roles` omitting a visible name) or a line
//! that does not parse as a summary is not a pairing failure: the check skips
//! the header rows for that file, or the line's tags (C13, C18), and the join
//! refuses it with its own message. Such a line still counts for C6, by its
//! text, and for C10. A file that cannot be read, or a header or line that is
//! not a JSON object, is refused here as in the join.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::io::{BufRead, BufReader};
use std::path::Path;

use serde_json::Value;

use crate::conformance::interchange::{parse_line, sorted_names, JoinError};

/// The largest count either reader accepts (JMC reads counts as `int`).
const COUNT_MAX: u64 = (1 << 31) - 1;
/// The largest count `--decide` classifies.
const DECIDE_COUNT_MAX: u64 = u16::MAX as u64;
/// The longest word, in events, whose counts stay within [`COUNT_MAX`].
const WORD_MAX: u64 = COUNT_MAX;

/// How the files will be joined, which decides the C6 and C10 rules.
#[derive(Clone, Copy, Debug, Default)]
pub struct PairingOpts {
    /// `--merge`: the lines must be in byte order.
    pub merge: bool,
    /// `--decide`: a count above 65535 is warned about.
    pub decide: bool,
}

/// One failed or warned row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingItem {
    /// The contract row, `C2` … `C18`.
    pub row: &'static str,
    pub what: String,
}

/// The check's result: the failures (the join must not run) and the warnings
/// (it may).
#[derive(Clone, Debug, Default)]
pub struct PairingReport {
    pub failures: Vec<PairingItem>,
    pub warnings: Vec<PairingItem>,
}

impl PairingReport {
    pub fn passed(&self) -> bool {
        self.failures.is_empty()
    }

    /// One line per failure, then one per warning, then the outcome:
    /// `pairing: C<n>: …`, `pairing: warning: C<n>: …`, `pairing: ok` or
    /// `pairing: failed (<k> checks)`.
    pub fn render(&self) -> String {
        let mut out = String::new();
        for f in &self.failures {
            out.push_str(&format!("pairing: {}: {}\n", f.row, f.what));
        }
        for w in &self.warnings {
            out.push_str(&format!("pairing: warning: {}: {}\n", w.row, w.what));
        }
        if self.passed() {
            out.push_str("pairing: ok\n");
        } else {
            out.push_str(&format!("pairing: failed ({} checks)\n", self.failures.len()));
        }
        out
    }
}

/// What one file contributes to the check.
struct Side {
    visible: Option<Vec<String>>,
    roles: Option<Vec<String>>,
    model: Option<String>,
    enumeration: Option<String>,
    /// Tag → the field arities it is used with.
    tags: BTreeMap<String, BTreeSet<usize>>,
}

/// Verifies the pairing restrictions of `spec` and `imp` (see the module
/// documentation). `Err` only for a file that cannot be read or whose header or
/// a line is not a JSON object.
pub fn check_pairing(spec: &Path, imp: &Path, opts: PairingOpts) -> Result<PairingReport, JoinError> {
    let mut report = PairingReport::default();
    let s = read_side(spec, opts, &mut report)?;
    let i = read_side(imp, opts, &mut report)?;
    let fail = |r: &mut PairingReport, row, what: String| r.failures.push(PairingItem { row, what });

    // C2: equal lists (each list's own order was checked while reading).
    if let (Some(a), Some(b)) = (&s.visible, &i.visible) {
        if a != b {
            fail(&mut report, "C2", format!("the two `visible` lists differ: {a:?} and {b:?}"));
        }
    }
    if let (Some(a), Some(b)) = (&s.roles, &i.roles) {
        if a != b {
            fail(&mut report, "C2", format!("the two `roles` lists differ: {a:?} and {b:?}"));
        }
    }
    // C3.
    match (&s.model, &i.model) {
        (Some(a), Some(b)) => {
            if a != b {
                fail(&mut report, "C3", format!("the two models differ: {a} and {b}"));
            }
            for (m, side) in [(a, "specification"), (b, "implementation")] {
                if m != "p2p" && m != "asyn" {
                    fail(
                        &mut report,
                        "C3",
                        format!("the {side}'s model `{m}` is not supported for a join (p2p or asyn)"),
                    );
                }
            }
        }
        // A missing model is the join's refusal.
        _ => {}
    }
    // C4.
    match s.enumeration.as_deref() {
        Some("complete") => {}
        Some(e) => fail(&mut report, "C4", format!("the specification is `{e}`, not `complete`")),
        // A missing enumeration is the join's refusal.
        None => {}
    }
    // C13.
    for (tag, sa) in &s.tags {
        match i.tags.get(tag) {
            Some(ia) if ia != sa => fail(
                &mut report,
                "C13",
                format!(
                    "the tag {} has the field arities {sa:?} in the specification and {ia:?} \
                     in the implementation",
                    crate::conformance::interchange::json_string(tag)
                ),
            ),
            Some(_) => {}
            None => report.warnings.push(PairingItem {
                row: "C13",
                what: format!(
                    "the tag {} (arities {sa:?}) occurs only in the specification; the \
                     implementation never sends it, which the join does not count against it",
                    crate::conformance::interchange::json_string(tag)
                ),
            }),
        }
    }
    for (tag, ia) in &i.tags {
        if !s.tags.contains_key(tag) {
            report.warnings.push(PairingItem {
                row: "C13",
                what: format!(
                    "the tag {} (arities {ia:?}) occurs only in the implementation; the join \
                     reports the lines that carry it as uncovered",
                    crate::conformance::interchange::json_string(tag)
                ),
            });
        }
    }
    Ok(report)
}

fn read_side(
    path: &Path,
    opts: PairingOpts,
    report: &mut PairingReport,
) -> Result<Side, JoinError> {
    let at = |line: Option<usize>, what: String| {
        JoinError(match line {
            Some(n) => format!("{}: line {n}: {what}", path.display()),
            None => format!("{}: {what}", path.display()),
        })
    };
    let file = fs::File::open(path).map_err(|e| at(None, e.to_string()))?;
    let mut lines = BufReader::new(file).lines();
    let first = match lines.next() {
        Some(l) => l.map_err(|e| at(None, e.to_string()))?,
        None => return Err(at(None, "the file is empty".into())),
    };
    let head: Value =
        serde_json::from_str(&first).map_err(|e| at(Some(1), format!("the header is not JSON: {e}")))?;
    let Value::Object(mut h) = head else {
        return Err(at(Some(1), "the header is not a JSON object".into()));
    };
    let fail = |r: &mut PairingReport, row, what: String| {
        r.failures.push(PairingItem { row, what: format!("{}: {what}", path.display()) })
    };
    let warn = |r: &mut PairingReport, row, what: String| {
        r.warnings.push(PairingItem { row, what: format!("{}: {what}", path.display()) })
    };
    // A list of strings, else `None` (malformed: the join's refusal).
    // A header the reader refuses contributes nothing to C2, C3 and C4.
    if crate::conformance::interchange::header_of(&first).is_err() {
        h.clear();
    }
    let names = |key: &str, report: &mut PairingReport| -> Option<Vec<String>> {
        let Some(Value::Array(items)) = h.get(key) else {
            return None;
        };
        let out: Option<Vec<String>> = items.iter().map(|x| x.as_str().map(str::to_owned)).collect();
        let out = out?;
        if out.windows(2).any(|w| w[0].as_bytes() >= w[1].as_bytes()) {
            fail(
                report,
                "C2",
                format!("line 1: the `{key}` list {out:?} is not byte-sorted with distinct names"),
            );
        }
        Some(out)
    };
    let visible = names("visible", report);
    let roles = names("roles", report);
    let string = |k: &str| h.get(k).and_then(Value::as_str).map(str::to_owned);
    let mut out = Side {
        visible,
        roles,
        model: string("model"),
        enumeration: string("enumeration"),
        tags: BTreeMap::new(),
    };
    let sorted = sorted_names(out.visible.as_deref().unwrap_or(&[]));

    // The lines: C6, C10, C13, C18.
    let mut seen: HashSet<String> = HashSet::new();
    let mut last: Option<(usize, String)> = None;
    for (k, l) in lines.enumerate() {
        let number = k + 2;
        let l = l.map_err(|e| at(Some(number), e.to_string()))?;
        let v: Value = serde_json::from_str(&l).map_err(|e| at(Some(number), format!("not JSON: {e}")))?;
        let Value::Object(m) = &v else {
            return Err(at(Some(number), "the line is not a JSON object".into()));
        };
        // C10.
        if let Some(Value::Array(cs)) = m.get("counts") {
            if let Some(c) = cs.iter().filter_map(Value::as_u64).find(|&c| c > COUNT_MAX) {
                fail(
                    report,
                    "C10",
                    format!("line {number}: the count {c} is out of bounds (both readers accept counts up to 2^31-1)"),
                );
            } else if let Some(c) =
                cs.iter().filter_map(Value::as_u64).find(|&c| opts.decide && c > DECIDE_COUNT_MAX)
            {
                warn(
                    report,
                    "C10",
                    format!(
                        "line {number}: the count {c} exceeds 65535; --decide refuses the join if it \
                         classifies this line"
                    ),
                );
            }
        }
        if let Some(Value::Object(wm)) = m.get("words") {
            for (n, w) in wm {
                if let Value::Array(obs) = w {
                    if obs.len() as u64 > WORD_MAX {
                        fail(
                            report,
                            "C10",
                            format!("line {number}: the word of `{n}` has {} events (at most 2^31-1)", obs.len()),
                        );
                    }
                }
            }
        }
        // C13 and C18 only from a line the reader accepts.
        let parsed = parse_line(&l, &sorted).map(|(key, _)| key);
        if parsed.is_ok() {
            if let Some(Value::Object(wm)) = m.get("words") {
                for obs in wm.values().filter_map(Value::as_array) {
                    for x in obs.iter().filter_map(Value::as_object).flat_map(|om| om.values()) {
                        walk(x, &mut out.tags, &mut |what| {
                            warn(report, "C18", format!("line {number}: {what}"))
                        });
                    }
                }
            }
        }
        // C6, on the normal form when the line parses, else on its text.
        let key = parsed.unwrap_or(l);
        if opts.merge {
            if let Some((prev, pkey)) = &last {
                match key.as_bytes().cmp(pkey.as_bytes()) {
                    std::cmp::Ordering::Equal => {
                        fail(report, "C6", format!("line {number} repeats line {prev}"))
                    }
                    std::cmp::Ordering::Less => fail(
                        report,
                        "C6",
                        format!("line {number} precedes line {prev} in byte order (--merge needs sorted files)"),
                    ),
                    std::cmp::Ordering::Greater => {}
                }
            }
            last = Some((number, key));
        } else if !seen.insert(key) {
            fail(report, "C6", format!("line {number} repeats an earlier line"));
        }
    }
    Ok(out)
}

/// Records every tag of `v` with its arity, and warns about tags that name an
/// identity type (C18).
fn walk(v: &Value, tags: &mut BTreeMap<String, BTreeSet<usize>>, c18: &mut dyn FnMut(String)) {
    match v {
        Value::Array(items) => {
            for x in items {
                walk(x, tags, c18);
            }
        }
        Value::Object(m) => {
            if let (Some(Value::String(t)), Some(Value::Array(f))) = (m.get("t"), m.get("f")) {
                if t == "ThreadId" || t == "Tid" {
                    c18(format!(
                        "a value is tagged {}, the name of an identity type; if it is a process \
                         identity, the programs must send its role name instead",
                        crate::conformance::interchange::json_string(t)
                    ));
                }
                tags.entry(t.clone()).or_default().insert(f.len());
                for x in f {
                    walk(x, tags, c18);
                }
            }
        }
        _ => {}
    }
}
