//! Reading witness graph files exactly: a JSON reader that keeps every object's key order and
//! every number's digits, and the validity check of witness format 1 (rules G1-G8 and G10-G12;
//! the projection rule G9 is the renderer's) built on it. The check returns the graph's parts that
//! conf-join and the replay use.

use std::collections::{HashMap, HashSet};

use serde_json::Value;

use super::interchange::normal_value;

/// A JSON value with its objects' keys in written order and its numbers as written.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum J {
    Null,
    Bool(bool),
    Num(String),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

struct Reader<'a> {
    b: &'a [u8],
    t: &'a str,
    i: usize,
}

impl Reader<'_> {
    fn ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }

    fn string(&mut self) -> Option<String> {
        let s0 = self.i;
        if self.b.get(self.i) != Some(&b'"') {
            return None;
        }
        self.i += 1;
        while self.i < self.b.len() {
            match self.b[self.i] {
                b'\\' => self.i += 2,
                b'"' => {
                    self.i += 1;
                    return serde_json::from_str(&self.t[s0..self.i]).ok();
                }
                _ => self.i += 1,
            }
        }
        None
    }

    fn value(&mut self, depth: usize) -> Option<J> {
        if depth > 256 {
            return None;
        }
        self.ws();
        let c = *self.b.get(self.i)?;
        Some(match c {
            b'{' => {
                self.i += 1;
                let mut out: Vec<(String, J)> = Vec::new();
                self.ws();
                if self.b.get(self.i) == Some(&b'}') {
                    self.i += 1;
                    return Some(J::Obj(out));
                }
                loop {
                    self.ws();
                    let k = self.string()?;
                    if out.iter().any(|(x, _)| *x == k) {
                        return None;
                    }
                    self.ws();
                    if self.b.get(self.i) != Some(&b':') {
                        return None;
                    }
                    self.i += 1;
                    let v = self.value(depth + 1)?;
                    out.push((k, v));
                    self.ws();
                    match self.b.get(self.i)? {
                        b',' => self.i += 1,
                        b'}' => {
                            self.i += 1;
                            break J::Obj(out);
                        }
                        _ => return None,
                    }
                }
            }
            b'[' => {
                self.i += 1;
                let mut out = Vec::new();
                self.ws();
                if self.b.get(self.i) == Some(&b']') {
                    self.i += 1;
                    return Some(J::Arr(out));
                }
                loop {
                    out.push(self.value(depth + 1)?);
                    self.ws();
                    match self.b.get(self.i)? {
                        b',' => self.i += 1,
                        b']' => {
                            self.i += 1;
                            break J::Arr(out);
                        }
                        _ => return None,
                    }
                }
            }
            b'"' => J::Str(self.string()?),
            b't' if self.t[self.i..].starts_with("true") => {
                self.i += 4;
                J::Bool(true)
            }
            b'f' if self.t[self.i..].starts_with("false") => {
                self.i += 5;
                J::Bool(false)
            }
            b'n' if self.t[self.i..].starts_with("null") => {
                self.i += 4;
                J::Null
            }
            b'-' | b'0'..=b'9' => {
                let s0 = self.i;
                while self.i < self.b.len() && matches!(self.b[self.i], b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9') {
                    self.i += 1;
                }
                let n = &self.t[s0..self.i];
                serde_json::from_str::<Value>(n).ok().filter(Value::is_number)?;
                J::Num(n.to_owned())
            }
            _ => return None,
        })
    }
}

/// `t` as one JSON value, or `None`.
pub(crate) fn parse(t: &str) -> Option<J> {
    let mut r = Reader { b: t.as_bytes(), t, i: 0 };
    let v = r.value(0)?;
    r.ws();
    (r.i == r.b.len()).then_some(v)
}

impl J {
    fn get(&self, k: &str) -> Option<&J> {
        match self {
            J::Obj(m) => m.iter().find(|(x, _)| x == k).map(|(_, v)| v),
            _ => None,
        }
    }

    fn keys(&self) -> Vec<&str> {
        match self {
            J::Obj(m) => m.iter().map(|(k, _)| k.as_str()).collect(),
            _ => Vec::new(),
        }
    }

    fn str(&self) -> Option<&str> {
        match self {
            J::Str(s) => Some(s),
            _ => None,
        }
    }

    /// A non-negative integer written without sign, fraction or exponent.
    fn uint(&self) -> Option<u128> {
        match self {
            J::Num(n) if n.bytes().all(|b| b.is_ascii_digit()) && (n == "0" || !n.starts_with('0')) => n.parse().ok(),
            _ => None,
        }
    }

    /// As a `serde_json` value (numbers through their digits), for the P5 value check.
    fn to_value(&self) -> Value {
        match self {
            J::Null => Value::Null,
            J::Bool(b) => Value::Bool(*b),
            J::Num(n) => serde_json::from_str(n).unwrap_or(Value::Null),
            J::Str(s) => Value::String(s.clone()),
            J::Arr(a) => Value::Array(a.iter().map(J::to_value).collect()),
            J::Obj(m) => Value::Object(m.iter().map(|(k, v)| (k.clone(), v.to_value())).collect()),
        }
    }
}

/// One recorded event of a checked graph.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Ev {
    Begin,
    End,
    Blk,
    Error(String),
    TCreate(usize),
    TJoin(usize),
    /// `v` in P5 normal form, or `None` for an opaque value.
    Send { to: usize, v: Option<String> },
    Recv { try_: bool, rf: Option<(usize, usize)> },
    /// `n` may be 2^64 (a choice over every `usize`), so it is kept wide.
    Nondet { n: u128, i: u128, lo: Option<u64> },
}

/// The source identity: the manifest's files, or unknown.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Source {
    Unknown,
    Known { root: String, files: Vec<(String, String)> },
}

/// A checked graph's parts.
#[derive(Clone, Debug)]
pub(crate) struct Graph {
    pub(crate) tool: String,
    pub(crate) tool_commit: String,
    pub(crate) entry: String,
    pub(crate) side: Option<String>,
    pub(crate) args: Vec<String>,
    pub(crate) model: Option<String>,
    pub(crate) seed: Option<u64>,
    pub(crate) threshold: Option<u32>,
    pub(crate) source: Source,
    pub(crate) names: Vec<Option<String>>,
    pub(crate) events: Vec<Vec<Ev>>,
}

fn obj_keys(v: &J, want: &[&str], what: &str) -> Result<(), String> {
    if !matches!(v, J::Obj(_)) || v.keys() != want {
        return Err(format!("G1: {what} has the keys {:?}, not {want:?}", v.keys()));
    }
    Ok(())
}

/// `source` from its JSON text (a `run.source` value, or the producer's own manifest object).
pub(crate) fn parse_source(text: &str) -> Result<Source, String> {
    source_of(&parse(text).ok_or("G1: run.source is not JSON")?)
}

/// The source manifest files map of `run.source`.
fn source_of(v: &J) -> Result<Source, String> {
    match v {
        J::Str(s) if s == "unknown" => Ok(Source::Unknown),
        J::Obj(_) => {
            obj_keys(v, &["root", "files"], "run.source")?;
            let root = v.get("root").and_then(J::str).ok_or("G1: run.source.root")?.to_owned();
            let J::Obj(files) = v.get("files").unwrap() else {
                return Err("G1: run.source.files".into());
            };
            let mut out = Vec::new();
            for (p, d) in files {
                let d = d.str().filter(|d| d.len() == 32 && d.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)))
                    .ok_or("G1: a run.source digest is not 32 lowercase hex digits")?;
                out.push((p.clone(), d.to_owned()));
            }
            if out.windows(2).any(|w| w[0].0.as_bytes() >= w[1].0.as_bytes()) {
                return Err("G1: run.source.files is not sorted by bytes".into());
            }
            Ok(Source::Known { root, files: out })
        }
        _ => Err("G1: run.source".into()),
    }
}

/// G1-G8 and G10-G12 of witness format 1 on one graph line.
pub(crate) fn check_graph(text: &str) -> Result<Graph, String> {
    let g = parse(text).ok_or("G1: not one JSON object")?;
    obj_keys(&g, &["witness", "line", "export", "run", "join", "nearest", "threads"], "the graph")?;
    if g.get("witness").and_then(J::uint) != Some(1) {
        return Err("G1: witness is not 1".into());
    }
    if g.get("line").and_then(J::str).is_none() {
        return Err("G1: line is not a string".into());
    }
    // G1 (export), G10
    let export = g.get("export").unwrap();
    check_export(export, "export")?;
    let names = |k: &str| -> Result<Vec<String>, String> {
        let J::Arr(a) = export.get(k).ok_or(format!("G10: export.{k}"))? else {
            return Err(format!("G10: export.{k}"));
        };
        let v: Vec<String> = a.iter().map(|x| x.str().map(str::to_owned)).collect::<Option<_>>()
            .ok_or(format!("G10: export.{k} holds a non-string"))?;
        if v.windows(2).any(|w| w[0] >= w[1]) {
            return Err(format!("G10: export.{k} is not sorted and distinct"));
        }
        Ok(v)
    };
    let visible = names("visible")?;
    if export.get("roles").is_some() {
        let roles = names("roles")?;
        if visible.iter().any(|v| !roles.contains(v)) {
            return Err("G10: a visible name is not a role".into());
        }
    }
    if !matches!(export.get("model").and_then(J::str), Some("p2p" | "asyn" | "cd")) {
        return Err("G10: export.model".into());
    }
    // G1 (run), G12
    let r = check_run(g.get("run").unwrap(), "run", true)?;
    let (tool, tool_commit, entry, side, args, model, seed, threshold, source) =
        (r.tool, r.tool_commit, r.entry, r.side, r.args, r.model, r.seed, r.threshold, r.source);
    check_join(g.get("join").unwrap())?;
    check_nearest(g.get("nearest").unwrap())?;
    // G2, G11
    let J::Arr(threads) = g.get("threads").unwrap() else { return Err("G2: threads is not an array".into()) };
    if threads.is_empty() {
        return Err("G2: no thread".into());
    }
    let mut tnames: Vec<Option<String>> = Vec::new();
    let mut raw_events: Vec<&Vec<J>> = Vec::new();
    for th in threads {
        obj_keys(th, &["name", "daemon", "events"], "a thread")?;
        let name = match th.get("name").unwrap() {
            J::Null => None,
            J::Str(s) => Some(s.clone()),
            _ => return Err("G1: a thread name".into()),
        };
        if !matches!(th.get("daemon"), Some(J::Bool(_))) {
            return Err("G1: a thread's daemon".into());
        }
        if name.as_ref().is_some_and(|n| n.chars().any(|c| c.is_control() || matches!(c, '\u{2028}' | '\u{2029}'))) {
            return Err("G11: a thread name holds a control character".into());
        }
        let J::Arr(evs) = th.get("events").unwrap() else { return Err("G1: events is not an array".into()) };
        tnames.push(name);
        raw_events.push(evs);
    }
    if tnames[0].as_deref() != Some("main") || threads[0].get("daemon") != Some(&J::Bool(false)) {
        return Err("G2: thread 0 is not main".into());
    }
    for v in &visible {
        if tnames.iter().filter(|n| n.as_deref() == Some(v.as_str())).count() != 1 {
            return Err(format!("G2: the visible name {v:?} is not one thread's"));
        }
    }
    let tcount = threads.len();
    let vis_t: HashSet<usize> =
        (0..tcount).filter(|&t| tnames[t].as_ref().is_some_and(|n| visible.contains(n))).collect();
    // Event shapes (G1, key order included), G3, G7, G8 (encodings)
    let mut events: Vec<Vec<Ev>> = Vec::new();
    for (t, evs) in raw_events.iter().enumerate() {
        if evs.is_empty() {
            return Err(format!("G3: thread {t} has no event"));
        }
        let mut out = Vec::new();
        for (k, e) in evs.iter().enumerate() {
            let kind = e.get("e").and_then(J::str).ok_or(format!("G1: event ({t}, {k}) has no kind"))?;
            let at = || format!("({t}, {k})");
            let index = |v: Option<&J>, what: &str| -> Result<usize, String> {
                v.and_then(J::uint)
                    .and_then(|x| usize::try_from(x).ok())
                    .filter(|&x| x < tcount)
                    .ok_or(format!("G4: {what} at {}", at()))
            };
            let ev = match kind {
                "BEGIN" => { obj_keys(e, &["e"], "an event")?; Ev::Begin }
                "END" => { obj_keys(e, &["e"], "an event")?; Ev::End }
                "BLK" => { obj_keys(e, &["e"], "an event")?; Ev::Blk }
                "ERROR" => {
                    obj_keys(e, &["e", "msg"], "an event")?;
                    Ev::Error(e.get("msg").and_then(J::str).ok_or("G1: ERROR msg")?.to_owned())
                }
                "TCREATE" => { obj_keys(e, &["e", "child"], "an event")?; Ev::TCreate(index(e.get("child"), "a created thread")?) }
                "TJOIN" => { obj_keys(e, &["e", "child"], "an event")?; Ev::TJoin(index(e.get("child"), "a joined thread")?) }
                "SEND" => {
                    obj_keys(e, &["e", "to", "v"], "an event")?;
                    let to = index(e.get("to"), "a destination")?;
                    let v = e.get("v").unwrap();
                    let opaque = matches!(v, J::Obj(m) if m.len() == 1 && m[0].0 == "opaque" && matches!(m[0].1, J::Str(_)));
                    let v = if opaque {
                        None
                    } else {
                        Some(normal_value(&v.to_value()).map_err(|e| format!("G8: the value at {}: {e}", at()))?)
                    };
                    Ev::Send { to, v }
                }
                "RECV" => {
                    obj_keys(e, &["e", "mode", "rf"], "an event")?;
                    let try_ = match e.get("mode").and_then(J::str) {
                        Some("try") => true,
                        Some("block") => false,
                        _ => return Err(format!("G1: the receive mode at {}", at())),
                    };
                    let rf = match e.get("rf").unwrap() {
                        J::Null if try_ => None,
                        J::Arr(a) if a.len() == 2 => Some((
                            a[0].uint().and_then(|x| usize::try_from(x).ok()).ok_or(format!("G5: rf at {}", at()))?,
                            a[1].uint().and_then(|x| usize::try_from(x).ok()).ok_or(format!("G5: rf at {}", at()))?,
                        )),
                        _ => return Err(format!("G5: rf at {}", at())),
                    };
                    Ev::Recv { try_, rf }
                }
                "NONDET" => {
                    let lo = if e.get("lo").is_some() {
                        obj_keys(e, &["e", "n", "i", "lo"], "an event")?;
                        if tool != "traceforge" {
                            return Err(format!("G7: lo at {} in a {tool} graph", at()));
                        }
                        Some(e.get("lo").and_then(J::uint).and_then(|x| u64::try_from(x).ok()).ok_or(format!("G7: lo at {}", at()))?)
                    } else {
                        obj_keys(e, &["e", "n", "i"], "an event")?;
                        None
                    };
                    let n = e.get("n").and_then(J::uint).ok_or(format!("G7: n at {}", at()))?;
                    let i = e.get("i").and_then(J::uint).ok_or(format!("G7: i at {}", at()))?;
                    if n < 2 || i >= n || n > (1u128 << 64) {
                        return Err(format!("G7: event {}", at()));
                    }
                    Ev::Nondet { n, i, lo }
                }
                other => return Err(format!("G1: unknown event {other:?} at {}", at())),
            };
            let terminal = matches!(ev, Ev::End | Ev::Blk | Ev::Error(_));
            if (k == 0) != matches!(ev, Ev::Begin) || (k + 1 == evs.len()) != terminal {
                return Err(format!("G3: event {}", at()));
            }
            out.push(ev);
        }
        events.push(out);
    }
    // G4, G5, G8 (visibility of opaque values)
    let mut created = vec![0usize; tcount];
    let mut read: HashMap<(usize, usize), usize> = HashMap::new();
    for (t, evs) in events.iter().enumerate() {
        for (k, e) in evs.iter().enumerate() {
            match e {
                Ev::TCreate(c) => {
                    if *c == 0 || *c == t {
                        return Err(format!("G4: event ({t}, {k}) creates thread {c}"));
                    }
                    created[*c] += 1;
                }
                Ev::TJoin(c) => {
                    if *c == 0 || !matches!(events[*c].last(), Some(Ev::End)) {
                        return Err(format!("G4: thread {c} is joined but does not end"));
                    }
                }
                Ev::Recv { rf: Some((st, sk)), .. } => {
                    match events.get(*st).and_then(|x| x.get(*sk)) {
                        Some(Ev::Send { to, .. }) if *to == t => {}
                        _ => return Err(format!("G5: rf at ({t}, {k}) is not a send to this thread")),
                    }
                    if read.insert((*st, *sk), t).is_some() {
                        return Err(format!("G5: the send ({st}, {sk}) is read twice"));
                    }
                }
                _ => {}
            }
        }
    }
    for (t, &c) in created.iter().enumerate().skip(1) {
        if c != 1 {
            return Err(format!("G4: thread {t} is created {c} times"));
        }
    }
    for (t, evs) in events.iter().enumerate() {
        for (k, e) in evs.iter().enumerate() {
            if let Ev::Send { v: None, .. } = e {
                if vis_t.contains(&t) || read.get(&(t, k)).is_some_and(|r| vis_t.contains(r)) {
                    return Err(format!("G8: an opaque value at ({t}, {k}) is visible"));
                }
            }
        }
    }
    // G6: porf acyclic (Kahn over po, rf, create, join).
    let base: Vec<usize> = events.iter().scan(0, |acc, e| { let b = *acc; *acc += e.len(); Some(b) }).collect();
    let total: usize = events.iter().map(Vec::len).sum();
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); total];
    let mut indeg = vec![0usize; total];
    let mut edge = |a: usize, b: usize| {
        succ[a].push(b);
        indeg[b] += 1;
    };
    for (t, evs) in events.iter().enumerate() {
        for (k, e) in evs.iter().enumerate() {
            if k > 0 {
                edge(base[t] + k - 1, base[t] + k);
            }
            match e {
                Ev::Recv { rf: Some((st, sk)), .. } => edge(base[*st] + sk, base[t] + k),
                Ev::TCreate(c) => edge(base[t] + k, base[*c]),
                Ev::TJoin(c) => edge(base[*c] + events[*c].len() - 1, base[t] + k),
                _ => {}
            }
        }
    }
    let mut ready: Vec<usize> = (0..total).filter(|&x| indeg[x] == 0).collect();
    let mut done = 0;
    while let Some(x) = ready.pop() {
        done += 1;
        for &y in &succ[x] {
            indeg[y] -= 1;
            if indeg[y] == 0 {
                ready.push(y);
            }
        }
    }
    if done != total {
        return Err("G6: porf has a cycle".into());
    }
    Ok(Graph { tool, tool_commit, entry, side, args, model, seed, threshold, source, names: tnames, events })
}

/// The parts of a checked `run` object.
pub(crate) struct RunParts {
    pub(crate) tool: String,
    pub(crate) tool_commit: String,
    pub(crate) entry: String,
    pub(crate) side: Option<String>,
    pub(crate) args: Vec<String>,
    pub(crate) model: Option<String>,
    pub(crate) seed: Option<u64>,
    pub(crate) threshold: Option<u32>,
    pub(crate) source: Source,
}

/// A `run` object (§1.2): its members in order, with their types and each tool's values. `own`:
/// the graph's own run (G12 applies), not a store's identity run named by `join.against_run`.
fn check_run(run: &J, where_: &str, own: bool) -> Result<RunParts, String> {
    obj_keys(
        run,
        &["tool", "tool_commit", "entry", "side", "args", "model", "options", "source", "iteration", "producer", "order"],
        where_,
    )?;
    let rs = |k: &str| run.get(k).and_then(J::str).map(str::to_owned).ok_or(format!("G1: {where_}.{k} is not a string"));
    let tool = rs("tool")?;
    if tool != "jmc" && tool != "traceforge" {
        return Err("G1: run.tool".into());
    }
    let tool_commit = rs("tool_commit")?;
    let entry = rs("entry")?;
    let side = match run.get("side").unwrap() {
        J::Null => None,
        J::Str(s) if s == "spec" || s == "impl" => Some(s.clone()),
        _ => return Err("G1: run.side".into()),
    };
    let J::Arr(args) = run.get("args").unwrap() else { return Err("G1: run.args".into()) };
    let args: Vec<String> = args.iter().map(|a| a.str().map(str::to_owned)).collect::<Option<_>>()
        .ok_or("G1: run.args holds a non-string")?;
    // The tool's own values: TraceForge records its side and runner model, JMC neither.
    let model = match (tool.as_str(), run.get("model").unwrap()) {
        ("jmc", J::Null) => None,
        ("traceforge", J::Str(s)) if matches!(s.as_str(), "fifo" | "bag" | "causal") => Some(s.clone()),
        _ => return Err("G1: run.model".into()),
    };
    if (tool == "jmc") != side.is_none() {
        return Err("G1: run.side".into());
    }
    let options = run.get("options").unwrap();
    if !matches!(options, J::Obj(_)) {
        return Err("G1: run.options".into());
    }
    let seed = match options.get("seed") {
        None => None,
        Some(v) => Some(v.uint().and_then(|s| u64::try_from(s).ok()).ok_or("G1: run.options.seed")?),
    };
    let threshold = match options.get("threshold") {
        None => None,
        Some(v) => Some(v.uint().and_then(|s| u32::try_from(s).ok()).ok_or("G1: run.options.threshold")?),
    };
    let source = source_of(run.get("source").unwrap())?;
    let order = rs("order")?;
    if order != "first" && order != "smallest" {
        return Err("G12: run.order".into());
    }
    let producer = rs("producer")?;
    if !matches!(producer.as_str(), "export" | "online" | "conf") {
        return Err("G1: run.producer".into());
    }
    match run.get("iteration").unwrap() {
        // A graph's own run has an iteration unless G12 allows none; a store's identity run has none.
        J::Null if !own || order == "smallest" || producer == "online" => {}
        J::Null => return Err("G12: iteration is null".into()),
        v if v.uint().is_some_and(|i| i >= 1) => {}
        _ => return Err("G1: run.iteration".into()),
    }
    Ok(RunParts { tool, tool_commit, entry, side, args, model, seed, threshold, source })
}

/// A P5 header object (`export`, `join.against`): known keys only, in header order, the required
/// ones present, with their types; no online field.
fn check_export(ex: &J, where_: &str) -> Result<(), String> {
    const ORDER: [&str; 12] =
        ["format", "minor", "tool", "program", "size", "visible", "roles", "model", "enumeration", "seed", "iterations", "encoding"];
    const REQUIRED: [&str; 8] = ["format", "tool", "program", "size", "visible", "model", "enumeration", "encoding"];
    let J::Obj(m) = ex else { return Err(format!("G1: {where_} is not an object")) };
    let keys: Vec<&str> = m.iter().map(|(k, _)| k.as_str()).collect();
    if keys.iter().any(|k| !ORDER.contains(k)) {
        return Err(format!("G1: {where_} holds an unknown or online key: {keys:?}"));
    }
    let ordered: Vec<&str> = ORDER.iter().copied().filter(|k| keys.contains(k)).collect();
    if keys != ordered || REQUIRED.iter().any(|k| !keys.contains(k)) {
        return Err(format!("G1: {where_} keys {keys:?}"));
    }
    if ex.get("format").and_then(J::uint) != Some(1) {
        return Err(format!("G1: {where_}.format is not 1"));
    }
    let minor = match ex.get("minor") {
        None => 0,
        Some(v) => v.uint().ok_or(format!("G1: {where_}.minor"))?,
    };
    if minor >= 1 && ex.get("roles").is_none() {
        return Err(format!("G1: {where_} is minor {minor} and has no roles"));
    }
    for k in ["tool", "program", "size", "model", "enumeration"] {
        if ex.get(k).and_then(J::str).is_none() {
            return Err(format!("G1: {where_}.{k} is not a string"));
        }
    }
    for k in ["visible", "roles"] {
        if let Some(v) = ex.get(k) {
            if !matches!(v, J::Arr(a) if a.iter().all(|x| x.str().is_some())) {
                return Err(format!("G1: {where_}.{k} is not a list of strings"));
            }
        }
    }
    for k in ["seed", "iterations", "encoding"] {
        if ex.get(k).is_some_and(|v| v.uint().is_none()) {
            return Err(format!("G1: {where_}.{k} is not an integer"));
        }
    }
    Ok(())
}

/// `join` (§1.5): `null`, or an object whose known members come in the contract's order with
/// their types and values; other members are ignored.
fn check_join(j: &J) -> Result<(), String> {
    let J::Obj(m) = j else {
        return if matches!(j, J::Null) { Ok(()) } else { Err("G1: join".into()) };
    };
    let order = ["tool", "tool_commit", "mode", "class", "decide", "against", "against_run"];
    let known: Vec<&str> = m.iter().map(|(k, _)| k.as_str()).filter(|k| order.contains(k)).collect();
    if known != order {
        return Err(format!("G1: join has the members {known:?}, not {order:?}"));
    }
    let bad = |what: &str| Err(format!("G1: join.{what}"));
    if !matches!(j.get("tool").and_then(J::str), Some("jmc" | "traceforge")) {
        return bad("tool");
    }
    if j.get("tool_commit").and_then(J::str).is_none() {
        return bad("tool_commit");
    }
    let mode = j.get("mode").and_then(J::str);
    if !matches!(mode, Some("plain" | "merge" | "online")) {
        return bad("mode");
    }
    // An online check has no miss class and no Decide.
    match (mode, j.get("class").unwrap()) {
        (Some("online"), J::Null) if matches!(j.get("decide"), Some(J::Null)) => {}
        (Some("plain" | "merge"), J::Str(c)) if matches!(c.as_str(), "no-bucket" | "no-slot" | "not-found") => {}
        _ => return bad("class"),
    }
    match j.get("decide").unwrap() {
        J::Null => {}
        d @ J::Obj(_) => {
            obj_keys(d, &["outcome", "k", "k_min", "states", "witness"], "join.decide")?;
            let outcome = d.get("outcome").and_then(J::str);
            if !matches!(outcome, Some("violation" | "unresolved")) {
                return bad("decide.outcome");
            }
            if ["k", "k_min", "states"].iter().any(|k| d.get(k).and_then(J::uint).is_none()) {
                return bad("decide counts");
            }
            match (outcome, d.get("witness").unwrap()) {
                (Some("unresolved"), J::Null) => {}
                (Some("violation"), J::Arr(w)) => {
                    let pos_ok = |p: &J| matches!(p, J::Arr(x) if x.len() == 2 && x[0].str().is_some() && x[1].uint().is_some());
                    if !w.iter().all(pos_ok) {
                        return bad("decide.witness");
                    }
                }
                _ => return bad("decide.witness"),
            }
        }
        _ => return bad("decide"),
    }
    match j.get("against").unwrap() {
        J::Null => {}
        a => check_export(a, "join.against")?,
    }
    match j.get("against_run").unwrap() {
        J::Null => {}
        r => {
            check_run(r, "join.against_run", false)?;
        }
    }
    Ok(())
}

/// `nearest` (§1.5): `null`, or a list of `{"line":<string>,"graph":<string|null>}`.
fn check_nearest(n: &J) -> Result<(), String> {
    match n {
        J::Null => Ok(()),
        J::Arr(items) => {
            for it in items {
                obj_keys(it, &["line", "graph"], "a nearest item")?;
                if it.get("line").and_then(J::str).is_none() || !matches!(it.get("graph"), Some(J::Null | J::Str(_))) {
                    return Err("G1: a nearest item".into());
                }
            }
            Ok(())
        }
        _ => Err("G1: nearest".into()),
    }
}

/// A header `h` as the graph format's `join.against` must hold it (`check_export`).
pub(crate) fn check_against(h: &str) -> Result<(), String> {
    check_export(&parse(h).ok_or("G1: the header is not JSON")?, "join.against")
}

/// A store's identity line: one JSON object whose `run` is a valid `run` (its `iteration` may be
/// `null`), since that `run` is copied into the graphs a join writes as `against_run`.
pub(crate) fn check_store_run(t: &str) -> Result<(), String> {
    let v = parse(t).ok_or("the identity line is not JSON")?;
    let run = v.get("run").ok_or("the identity line has no run")?;
    check_run(run, "the store's run", false).map(|_| ())
}
