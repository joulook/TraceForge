//! `conf-join --witness-dir D`: the witness graphs of a join's uncovered lines.
//!
//! The graphs are looked up, by the bytes of the uncovered line, in the graph store written beside
//! the implementation's export (`export --graphs`), and, for the nearest specification lines that
//! Decide names, in the specification's store. Each graph found is checked on reading (validity
//! rules G1-G8 and G10-G12 of witness format 1; the projection rule G9 is the renderer's) and
//! written as `D/<n>.graph.json`, `n` the line's rank in the printed order, with `join` and
//! `nearest` filled in. `D/index.tsv` lists every uncovered line with what became of it. Nothing
//! is ever overwritten, and the join's verdict and exit code do not change.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::{BufRead, BufReader, Read, Seek, SeekFrom, Write};
use std::ops::Range;
use std::path::{Path, PathBuf};

use serde_json::Value;

use super::decide::Outcome;
use super::interchange::{json_string, JoinError, JoinReport, MissClass};
use super::witness_graph::TOOL_COMMIT;

/// The online check's header fields, which a store's `export` and a graph's `against` leave out.
pub(crate) const ONLINE_FIELDS: [&str; 3] = ["first_miss_iteration", "first_miss_wall_ms", "uncovered_total"];

/// `--witness-dir` and its options.
#[derive(Clone, Debug)]
pub struct WitnessJoinOpts {
    pub dir: PathBuf,
    /// `--impl-graphs P`; else `<impl.jsonl>.graphs.jsonl` if it exists.
    pub impl_graphs: Option<PathBuf>,
    /// `--spec-graphs Q`; else `<spec.jsonl>.graphs.jsonl` if it exists.
    pub spec_graphs: Option<PathBuf>,
    /// `--witness-limit N`; `None` is `all`.
    pub limit: Option<usize>,
    /// `--witness-nearest N`.
    pub nearest: usize,
    /// `--merge`: the join's `mode` is `merge`.
    pub merge: bool,
}

impl WitnessJoinOpts {
    /// The defaults: limit 20, nearest 3.
    pub fn new(dir: PathBuf) -> Self {
        WitnessJoinOpts { dir, impl_graphs: None, spec_graphs: None, limit: Some(20), nearest: 3, merge: false }
    }
}

/// What the witness pass did, for the report's rendering.
#[derive(Clone, Debug, Default)]
pub(crate) struct WitnessSummary {
    /// Per uncovered line, in order: `<n>.graph.json` or `- (<reason>)`.
    pub(crate) graphs: Vec<String>,
    pub(crate) written: usize,
    pub(crate) missing: usize,
    pub(crate) refused: usize,
}

fn refused(what: impl Into<String>) -> JoinError {
    JoinError(what.into())
}

/// `D` must not exist or must be empty (checked before the join runs).
pub fn check_witness_dir(dir: &Path) -> Result<(), JoinError> {
    match fs::read_dir(dir) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(refused(format!("{}: {e}", dir.display()))),
        Ok(mut entries) => {
            if entries.next().is_some() {
                Err(refused(format!("{}: the witness directory is not empty", dir.display())))
            } else {
                Ok(())
            }
        }
    }
}

// ------------------------------------------------------------ top-level JSON fields --

/// One member of a JSON object's top level: its key, the byte range of the key as written
/// (quotes included) and of its value.
struct Field {
    key: String,
    raw_key: Range<usize>,
    value: Range<usize>,
}

/// The top-level members of the JSON object `t`, in order, with their byte ranges; `None` if
/// `t` is not one JSON object (only the structure is scanned here).
fn top_fields(t: &str) -> Option<Vec<Field>> {
    let b = t.as_bytes();
    let mut i = 0;
    let ws = |i: &mut usize| {
        while *i < b.len() && matches!(b[*i], b' ' | b'\t' | b'\n' | b'\r') {
            *i += 1;
        }
    };
    // The end of the string starting at `i` (at its quote), past the closing quote.
    let string_end = |mut i: usize| -> Option<usize> {
        i += 1;
        while i < b.len() {
            match b[i] {
                b'\\' => i += 2,
                b'"' => return Some(i + 1),
                _ => i += 1,
            }
        }
        None
    };
    ws(&mut i);
    if b.get(i) != Some(&b'{') {
        return None;
    }
    i += 1;
    let mut out = Vec::new();
    loop {
        ws(&mut i);
        if b.get(i) == Some(&b'}') && out.is_empty() {
            i += 1;
            break;
        }
        if b.get(i) != Some(&b'"') {
            return None;
        }
        let k0 = i;
        i = string_end(i)?;
        let k1 = i;
        let key: String = serde_json::from_str(&t[k0..k1]).ok()?;
        ws(&mut i);
        if b.get(i) != Some(&b':') {
            return None;
        }
        i += 1;
        ws(&mut i);
        let v0 = i;
        let mut depth = 0usize;
        while i < b.len() {
            match b[i] {
                b'"' => {
                    i = string_end(i)?;
                    continue;
                }
                b'{' | b'[' => depth += 1,
                b'}' | b']' if depth > 0 => depth -= 1,
                b',' | b'}' if depth == 0 => break,
                _ => {}
            }
            i += 1;
        }
        let mut v1 = i;
        while v1 > v0 && matches!(b[v1 - 1], b' ' | b'\t' | b'\n' | b'\r') {
            v1 -= 1;
        }
        if v1 == v0 {
            return None;
        }
        out.push(Field { key, raw_key: k0..k1, value: v0..v1 });
        match b.get(i) {
            Some(b',') => i += 1,
            Some(b'}') => {
                i += 1;
                break;
            }
            _ => return None,
        }
    }
    ws(&mut i);
    (i == b.len()).then_some(out)
}

/// `t` with the top-level members named in `drop` removed. The kept members' bytes, the bytes
/// before the first member and after the last, and the separator that followed each kept member
/// are kept as written; `t` itself when nothing is dropped.
pub(crate) fn without_fields(t: &str, drop: &[&str]) -> Option<String> {
    let fields = top_fields(t)?;
    if !fields.iter().any(|f| drop.contains(&f.key.as_str())) {
        return Some(t.to_owned());
    }
    let (Some(first), Some(last)) = (fields.first(), fields.last()) else {
        return Some(t.to_owned());
    };
    let kept: Vec<usize> = (0..fields.len()).filter(|&i| !drop.contains(&fields[i].key.as_str())).collect();
    let mut out = String::from(&t[..first.raw_key.start]);
    for (j, &i) in kept.iter().enumerate() {
        if j > 0 {
            // The separator written after the previous kept member.
            let p = kept[j - 1];
            out.push_str(&t[fields[p].value.end..fields[p + 1].raw_key.start]);
        }
        out.push_str(&t[fields[i].raw_key.start..fields[i].value.end]);
    }
    out.push_str(&t[last.value.end..]);
    Some(out)
}

/// The first line of a file, without its newline.
fn first_line(path: &Path) -> Result<String, JoinError> {
    let f = fs::File::open(path).map_err(|e| refused(format!("{}: {e}", path.display())))?;
    let mut line = String::new();
    BufReader::new(f)
        .read_line(&mut line)
        .map_err(|e| refused(format!("{}: {e}", path.display())))?;
    Ok(line.trim_end_matches(['\n', '\r']).to_owned())
}

// ------------------------------------------------------------------------- the store --

/// A graph store, indexed in memory by its graphs' lines (a signature of each line to the byte
/// ranges of the graph lines that may carry it; a hit is confirmed by the bytes of `line`).
struct Store {
    path: PathBuf,
    file: fs::File,
    /// The identity line's `run`, verbatim.
    run: String,
    index: HashMap<u64, Vec<(u64, usize)>>,
}

fn signature(line: &str) -> u64 {
    let mut h = DefaultHasher::new();
    line.hash(&mut h);
    h.finish()
}

/// The `line` of a graph line, if it has one.
fn line_of_graph(text: &str) -> Option<String> {
    let fields = top_fields(text)?;
    let f = fields.iter().find(|f| f.key == "line")?;
    serde_json::from_str(&text[f.value.clone()]).ok()
}

impl Store {
    /// Opens the store at `path` for the export whose header line is `header`. Refused (an
    /// unusable store) when it is not a store, belongs to another export, or holds a line twice.
    fn open(path: &Path, header: &str) -> Result<Store, JoinError> {
        let bad = |what: &str| refused(format!("{}: {what}", path.display()));
        let file = fs::File::open(path).map_err(|e| bad(&e.to_string()))?;
        let mut r = BufReader::new(file.try_clone().map_err(|e| bad(&e.to_string()))?);
        let mut first = String::new();
        let mut at = r.read_line(&mut first).map_err(|e| bad(&e.to_string()))? as u64;
        let first = first.trim_end_matches('\n');
        let fields = top_fields(first).ok_or_else(|| bad("the first line is not a store's identity line"))?;
        let keys: Vec<&str> = fields.iter().map(|f| f.key.as_str()).collect();
        if keys != ["witness_store", "export", "run"] || &first[fields[0].value.clone()] != "1" {
            return Err(bad("the first line is not a store's identity line (witness_store 1)"));
        }
        super::witness_json::check_store_run(first).map_err(|e| bad(&e))?;
        let export: Value = serde_json::from_str(&first[fields[1].value.clone()])
            .map_err(|_| bad("the store's export is not JSON"))?;
        let mut want: Value = serde_json::from_str(header).map_err(|_| bad("the export's header is not JSON"))?;
        if let Value::Object(m) = &mut want {
            for k in ONLINE_FIELDS {
                m.remove(k);
            }
        }
        if export != want {
            return Err(bad("the graph store belongs to another export"));
        }
        let run = first[fields[2].value.clone()].to_owned();
        let mut index: HashMap<u64, Vec<(u64, usize)>> = HashMap::new();
        let mut seen: HashSet<String> = HashSet::new();
        let mut buf = String::new();
        let mut number = 1usize;
        loop {
            buf.clear();
            let n = r.read_line(&mut buf).map_err(|e| bad(&e.to_string()))?;
            if n == 0 {
                break;
            }
            number += 1;
            let text = buf.trim_end_matches('\n');
            let line = line_of_graph(text)
                .ok_or_else(|| bad(&format!("line {number} is not a graph with a `line`")))?;
            if !seen.insert(line.clone()) {
                return Err(bad(&format!("line {number} repeats a summary line")));
            }
            index.entry(signature(&line)).or_default().push((at, text.len()));
            at += n as u64;
        }
        Ok(Store { path: path.to_path_buf(), file, run, index })
    }

    /// The graph line whose `line` is `line`, byte for byte.
    fn get(&mut self, line: &str) -> Result<Option<String>, JoinError> {
        let Some(cands) = self.index.get(&signature(line)) else {
            return Ok(None);
        };
        for &(at, len) in cands {
            let mut text = vec![0u8; len];
            self.file
                .seek(SeekFrom::Start(at))
                .and_then(|_| self.file.read_exact(&mut text))
                .map_err(|e| refused(format!("{}: {e}", self.path.display())))?;
            let text = String::from_utf8(text)
                .map_err(|_| refused(format!("{}: a line is not UTF-8", self.path.display())))?;
            if line_of_graph(&text).as_deref() == Some(line) {
                return Ok(Some(text));
            }
        }
        Ok(None)
    }
}

/// The store at `explicit`, or at `<export>.graphs.jsonl` when that exists; `None` without one.
fn open_store(explicit: &Option<PathBuf>, export: &Path, header: &str) -> Result<Option<Store>, JoinError> {
    let path = match explicit {
        Some(p) => p.clone(),
        None => {
            let mut p = export.as_os_str().to_owned();
            p.push(".graphs.jsonl");
            let p = PathBuf::from(p);
            if !p.exists() {
                return Ok(None);
            }
            p
        }
    };
    Store::open(&path, header).map(Some)
}

// ------------------------------------------------------------------ checks on reading --

/// G1-G8 and G10-G12 of witness format 1 on one graph line (see [`super::witness_json`]).
pub(crate) fn check_graph(text: &str) -> Result<(), String> {
    super::witness_json::check_graph(text).map(|_| ())
}

/// `text` (a checked graph line) with its `join` and `nearest` values replaced.
fn with_join(text: &str, join: &str, nearest: &str) -> Option<String> {
    let f = top_fields(text)?;
    let (j, n) = (f.iter().find(|x| x.key == "join")?, f.iter().find(|x| x.key == "nearest")?);
    Some(format!(
        "{}{join}{}{nearest}{}",
        &text[..j.value.start],
        &text[j.value.end..n.value.start],
        &text[n.value.end..]
    ))
}

/// Writes `text` and a newline to the new file `path`; an existing file is never replaced.
fn write_new(path: &Path, text: &str) -> Result<(), JoinError> {
    let mut f = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|e| refused(format!("{}: {e}", path.display())))?;
    f.write_all(text.as_bytes())
        .and_then(|()| f.write_all(b"\n"))
        .map_err(|e| refused(format!("{}: {e}", path.display())))
}

// ------------------------------------------------------------------------- the pass --

/// Writes the witness graphs of `report`'s uncovered lines (the join of `imp` against `spec`)
/// into `o.dir` and records the outcome in the report. Refused (exit 2) only for an unusable
/// store or a file that cannot be written; a single graph that fails its check is counted.
pub fn write_join_witnesses(
    report: &mut JoinReport, spec: &Path, imp: &Path, o: &WitnessJoinOpts,
) -> Result<(), JoinError> {
    let spec_header = first_line(spec)?;
    let impl_header = first_line(imp)?;
    let mut impl_store = open_store(&o.impl_graphs, imp, &impl_header)?;
    let mut spec_store = open_store(&o.spec_graphs, spec, &spec_header)?;
    let against = without_fields(&spec_header, &ONLINE_FIELDS)
        .ok_or_else(|| refused(format!("{}: the header is not a JSON object", spec.display())))?;
    // `against` goes into every graph written, so it must pass the graph format's own check.
    super::witness_json::check_against(&against)
        .map_err(|e| refused(format!("{}: the header cannot be a witness graph's `against`: {e}", spec.display())))?;
    let against_run = spec_store.as_ref().map_or_else(|| "null".to_owned(), |s| s.run.clone());
    let mode = if o.merge { "merge" } else { "plain" };
    fs::create_dir_all(&o.dir).map_err(|e| refused(format!("{}: {e}", o.dir.display())))?;
    let mut summary = WitnessSummary::default();
    let mut index = String::from("n\tclass\tdecide\tgraph\treason\tline\n");
    let mut eligible = 0usize;
    for (j, (class, line)) in report.uncovered.iter().enumerate() {
        let n = j + 1;
        let entry = report.decide.as_ref().and_then(|d| d.entries.get(j));
        let word = entry.map_or("-", |e| e.decision.outcome.word());
        let decide_json = match entry {
            None => "null".to_owned(),
            Some(e) => {
                let d = &e.decision;
                let witness = match &d.outcome {
                    Outcome::Violation(w) => {
                        let names = super::interchange::sorted_names(&report.imp.visible);
                        let ps: Vec<String> =
                            w.iter().map(|&(t, i)| format!("[{},{i}]", json_string(&names[t]))).collect();
                        format!("[{}]", ps.join(","))
                    }
                    _ => "null".to_owned(),
                };
                format!(
                    "{{\"outcome\":\"{}\",\"k\":{},\"k_min\":{},\"states\":{},\"witness\":{witness}}}",
                    d.outcome.word(),
                    d.group,
                    d.effective,
                    d.states
                )
            }
        };
        let mut outcome = |reason: &str, graph: Option<String>, summary: &mut WitnessSummary| {
            let g = graph.clone().unwrap_or_else(|| "-".to_owned());
            index.push_str(&format!("{n}\t{}\t{word}\t{g}\t{reason}\t{line}\n", class.name()));
            summary.graphs.push(match graph {
                Some(g) => g,
                None => format!("- ({reason})"),
            });
        };
        if entry.is_some_and(|e| matches!(e.decision.outcome, Outcome::FalseAlarm)) {
            outcome("false-alarm", None, &mut summary);
            continue;
        }
        if o.limit.is_some_and(|l| eligible >= l) {
            outcome("limit", None, &mut summary);
            continue;
        }
        eligible += 1;
        let Some(store) = impl_store.as_mut() else {
            summary.missing += 1;
            outcome("no-store", None, &mut summary);
            continue;
        };
        let Some(text) = store.get(line)? else {
            summary.missing += 1;
            outcome("no-graph", None, &mut summary);
            continue;
        };
        if check_graph(&text).is_err() {
            summary.refused += 1;
            outcome("refused", None, &mut summary);
            continue;
        }
        // The nearest specification lines (Decide's effective group, `not-found` only).
        let nearest = match (*class, entry) {
            (MissClass::NotFound, Some(e)) => {
                let mut items = Vec::new();
                for (k, nl) in e.nearest.iter().take(o.nearest).enumerate() {
                    let name = format!("{n}.nearest-{}.graph.json", k + 1);
                    let found = match spec_store.as_mut() {
                        Some(s) => s.get(nl)?.filter(|t| check_graph(t).is_ok()),
                        None => None,
                    };
                    let graph = match found {
                        Some(t) => {
                            write_new(&o.dir.join(&name), &t)?;
                            json_string(&name)
                        }
                        None => "null".to_owned(),
                    };
                    items.push(format!("{{\"line\":{},\"graph\":{graph}}}", json_string(nl)));
                }
                format!("[{}]", items.join(","))
            }
            _ => "null".to_owned(),
        };
        let join = format!(
            "{{\"tool\":\"traceforge\",\"tool_commit\":{},\"mode\":\"{mode}\",\"class\":\"{}\",\
             \"decide\":{decide_json},\"against\":{against},\"against_run\":{against_run}}}",
            json_string(TOOL_COMMIT),
            class.name()
        );
        let name = format!("{n}.graph.json");
        let out = with_join(&text, &join, &nearest).expect("conformance: a checked graph has join and nearest");
        write_new(&o.dir.join(&name), &out)?;
        summary.written += 1;
        outcome("ok", Some(name), &mut summary);
    }
    write_new(&o.dir.join("index.tsv"), index.trim_end_matches('\n'))?;
    report.witness = Some(summary);
    Ok(())
}
