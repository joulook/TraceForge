//! `J3` and `G1`: TraceForge's side of the compact summary interchange format,
//! version 1 (`plan/jmc-must/SUMMARY-FORMAT.md`), for any Must program.
//!
//! - **The generic encoder** (G1-1): a value's canonical form is parsed from its
//!   derived `Debug` rendering ([`encode_generic`]): a struct, tuple struct or
//!   variant becomes `{"t":<name>,"f":[…]}`, lists, sets (sorted), integers,
//!   strings and booleans as the format says, a `ThreadId` its role name;
//!   anything else is refused with the value's type. Preconditions P1–P3 of
//!   `criteria/G1.md`: no map-typed value; the text `ThreadId { opaque_id: N }`
//!   reserved; a value's `Debug` agrees with its `PartialEq`. No per-program
//!   encoder exists.
//! - **The exporter** (G1-3): [`export`] enumerates the program once as a
//!   specification with its own sink, which fills a `SetIndex` exactly as the
//!   stateful engine's specification sink does and records the thread names;
//!   after the run every entry is encoded and written, `n` omitted. No engine
//!   changes.
//! - **The reader and the join** (J3-3): [`conf_join`] reads two files, inserts
//!   the specification's summaries into a `SetIndex` and queries each
//!   implementation summary with `SetIndex::covers`; the command `conf-join`
//!   (`src/bin/conf-join.rs`) prints its [`JoinReport`].
//!
//! The writer and the reader render a summary line through one function
//! ([`render_line`]), so a file TraceForge writes is in the reader's normal form
//! (ruling Q8). The text a user reads — the errors' `Display`, the decoded
//! value's, and `JoinReport::render` — is in `report.rs`, the one rendering
//! module (S5 criterion 1).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;

use serde_json::Value;

use crate::conformance::compact::{CompactSummary, Covers, OrdCounts, SetIndex};
use crate::conformance::config::{ConfConfig, IndexKind};
use crate::conformance::ctx::{CompletionSink, ConfMode, DiagnosticReason, SinkVerdict};
use crate::conformance::morphism::Status;
use crate::conformance::obs::Obs;
use crate::conformance::report::SearchEnd;
use crate::conformance::sig::Sig;
use crate::conformance::stateful;
use crate::exec_graph::ExecutionGraph;
use crate::msg::Val;
use crate::must::MustState;
use crate::ConsType;

// ---------------------------------------------------------------- encoder --

/// A JSON string literal, `serde_json`'s escaping.
pub(crate) fn json_string(s: &str) -> String {
    serde_json::to_string(s).expect("conformance: a string always serialises")
}

// -------------------------------------------------------- generic encoder --

/// `G1`: a run's thread names, by the number of `ThreadId` (its `Display` is
/// `t<N>`, its derived `Debug` `ThreadId { opaque_id: N }`), recorded by the
/// export's sink from every explored graph.
pub(crate) type ThreadNames = HashMap<u32, ThreadName>;

/// What the explored graphs say about one thread's name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ThreadName {
    Named(String),
    Unnamed,
    /// Two graphs named the thread differently.
    Conflict(String, String),
}

/// Records every thread of `g` into `names`.
pub(crate) fn record_thread_names(g: &ExecutionGraph, names: &mut ThreadNames) {
    for tid in g.thread_ids() {
        let Some(n) = tid
            .to_string()
            .strip_prefix('t')
            .and_then(|d| d.parse::<u32>().ok())
        else {
            continue;
        };
        let seen = match g.thread_name(tid) {
            Some(s) => ThreadName::Named(s.to_string()),
            None => ThreadName::Unnamed,
        };
        match names.get(&n) {
            None => {
                names.insert(n, seen);
            }
            Some(old) if *old == seen => {}
            Some(ThreadName::Conflict(..)) => {}
            Some(old) => {
                let label = |t: &ThreadName| match t {
                    ThreadName::Named(s) => s.clone(),
                    _ => "(unnamed)".to_string(),
                };
                let c = ThreadName::Conflict(label(old), label(&seen));
                names.insert(n, c);
            }
        }
    }
}

/// A value parsed from its derived `Debug` rendering (G1-1).
enum DbgVal {
    Int(i128),
    Bool(bool),
    Str(String),
    /// A struct, a tuple struct or an enum variant; a unit one has no fields.
    Named(String, Vec<DbgVal>),
    List(Vec<DbgVal>),
    /// `{a, b}`; also an empty `{}`, which an empty map prints too (P1).
    Set(Vec<DbgVal>),
    /// The reserved shape `ThreadId { opaque_id: N }` (P2).
    Thread(u32),
}

/// Why a rendering has no canonical form.
enum DbgError {
    /// Text outside the derived-`Debug` grammar, at this byte offset.
    Unparsed(usize),
    /// A form the format refuses, named.
    Refused(&'static str),
    /// A `ThreadId` without a role name in this run.
    Thread(String),
}

/// The parser of derived `Debug` text: its separators are exactly `", "` and
/// `": "`, a braced body is `" { "` … `" }"`; anything else refuses.
struct DbgParser<'a> {
    s: &'a str,
    pos: usize,
}

impl<'a> DbgParser<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.pos..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn eat(&mut self, lit: &str) -> bool {
        if self.rest().starts_with(lit) {
            self.pos += lit.len();
            true
        } else {
            false
        }
    }

    fn want(&mut self, lit: &str) -> Result<(), DbgError> {
        if self.eat(lit) {
            Ok(())
        } else {
            Err(DbgError::Unparsed(self.pos))
        }
    }

    /// The length of the identifier at the cursor (0 if none).
    fn ident_len(&self) -> usize {
        let mut chars = self.rest().char_indices();
        match chars.next() {
            Some((_, c)) if c == '_' || c.is_alphabetic() => {}
            _ => return 0,
        }
        chars
            .find(|(_, c)| !(*c == '_' || c.is_alphanumeric()))
            .map_or(self.rest().len(), |(i, _)| i)
    }

    fn value(&mut self) -> Result<DbgVal, DbgError> {
        match self.peek() {
            Some('"') => self.string().map(DbgVal::Str),
            Some('\'') => Err(DbgError::Refused("a char")),
            Some('[') => {
                self.pos += 1;
                self.seq("]").map(DbgVal::List)
            }
            Some('{') => self.brace(),
            Some('(') => Err(DbgError::Refused("an anonymous tuple")),
            Some(c) if c == '-' || c.is_ascii_digit() => self.number(),
            Some(c) if c == '_' || c.is_alphabetic() => self.named(),
            _ => Err(DbgError::Unparsed(self.pos)),
        }
    }

    /// `value (", " value)*` up to `close`, or nothing.
    fn seq(&mut self, close: &str) -> Result<Vec<DbgVal>, DbgError> {
        let mut out = Vec::new();
        if self.eat(close) {
            return Ok(out);
        }
        loop {
            out.push(self.value()?);
            if self.eat(close) {
                return Ok(out);
            }
            self.want(", ")?;
        }
    }

    fn brace(&mut self) -> Result<DbgVal, DbgError> {
        self.pos += 1;
        if self.eat("}") {
            // P1: an empty set and an empty map print alike.
            return Ok(DbgVal::Set(Vec::new()));
        }
        let first = self.value()?;
        if self.rest().starts_with(": ") {
            return Err(DbgError::Refused("a map"));
        }
        let mut out = vec![first];
        loop {
            if self.eat("}") {
                return Ok(DbgVal::Set(out));
            }
            self.want(", ")?;
            out.push(self.value()?);
        }
    }

    fn number(&mut self) -> Result<DbgVal, DbgError> {
        let start = self.pos;
        if self.rest().starts_with("-inf") {
            return Err(DbgError::Refused("a float"));
        }
        self.eat("-");
        let digits = self.rest().bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 {
            return Err(DbgError::Unparsed(self.pos));
        }
        self.pos += digits;
        if self.rest().starts_with("..") {
            return Err(DbgError::Refused("a range"));
        }
        if matches!(self.peek(), Some('.' | 'e' | 'E')) {
            return Err(DbgError::Refused("a float"));
        }
        self.s[start..self.pos]
            .parse::<i128>()
            .map(DbgVal::Int)
            .map_err(|_| DbgError::Refused("an integer outside signed 64 bits"))
    }

    fn named(&mut self) -> Result<DbgVal, DbgError> {
        let len = self.ident_len();
        let ident = &self.s[self.pos..self.pos + len];
        self.pos += len;
        match ident {
            "true" => return Ok(DbgVal::Bool(true)),
            "false" => return Ok(DbgVal::Bool(false)),
            "NaN" | "inf" => return Err(DbgError::Refused("a float")),
            _ => {}
        }
        if self.eat("(") {
            let fields = self.seq(")")?;
            return Ok(DbgVal::Named(ident.to_string(), fields));
        }
        if self.eat(" { ") {
            let mut names = Vec::new();
            let mut fields = Vec::new();
            loop {
                if self.rest().starts_with("..") {
                    return Err(DbgError::Refused("`..` (a non-exhaustive rendering)"));
                }
                let flen = self.ident_len();
                if flen == 0 {
                    return Err(DbgError::Unparsed(self.pos));
                }
                names.push(&self.s[self.pos..self.pos + flen]);
                self.pos += flen;
                self.want(": ")?;
                fields.push(self.value()?);
                if self.eat(" }") {
                    break;
                }
                self.want(", ")?;
            }
            if ident == "ThreadId" && names == ["opaque_id"] {
                // P2: the reserved shape of TraceForge's `ThreadId`.
                return match fields.as_slice() {
                    [DbgVal::Int(n)] => u32::try_from(*n)
                        .map(DbgVal::Thread)
                        .map_err(|_| DbgError::Unparsed(self.pos)),
                    _ => Err(DbgError::Unparsed(self.pos)),
                };
            }
            return Ok(DbgVal::Named(ident.to_string(), fields));
        }
        if matches!(self.peek(), Some('<' | ':')) {
            return Err(DbgError::Unparsed(self.pos));
        }
        Ok(DbgVal::Named(ident.to_string(), Vec::new()))
    }

    /// A derived-`Debug` string: the escapes `\0 \t \r \n \\ \" \' \u{…}`
    /// (rustc renders every other non-printable character as `\u{…}`).
    fn string(&mut self) -> Result<String, DbgError> {
        self.pos += 1;
        let mut out = String::new();
        loop {
            let at = self.pos;
            let c = self.peek().ok_or(DbgError::Unparsed(at))?;
            self.pos += c.len_utf8();
            match c {
                '"' => return Ok(out),
                '\\' => {
                    let e = self.peek().ok_or(DbgError::Unparsed(at))?;
                    self.pos += e.len_utf8();
                    match e {
                        '0' => out.push('\0'),
                        't' => out.push('\t'),
                        'r' => out.push('\r'),
                        'n' => out.push('\n'),
                        '\\' => out.push('\\'),
                        '"' => out.push('"'),
                        '\'' => out.push('\''),
                        'u' => {
                            self.want("{").map_err(|_| DbgError::Unparsed(at))?;
                            let hex = self
                                .rest()
                                .bytes()
                                .take_while(u8::is_ascii_hexdigit)
                                .count();
                            if !(1..=6).contains(&hex) {
                                return Err(DbgError::Unparsed(at));
                            }
                            let code = u32::from_str_radix(&self.s[self.pos..self.pos + hex], 16)
                                .map_err(|_| DbgError::Unparsed(at))?;
                            self.pos += hex;
                            self.want("}").map_err(|_| DbgError::Unparsed(at))?;
                            out.push(char::from_u32(code).ok_or(DbgError::Unparsed(at))?);
                        }
                        _ => return Err(DbgError::Unparsed(at)),
                    }
                }
                c => out.push(c),
            }
        }
    }
}

/// The canonical bytes of a parsed value (G1-1).
fn render_dbg(v: &DbgVal, threads: &ThreadNames, out: &mut String) -> Result<(), DbgError> {
    match v {
        DbgVal::Int(i) => {
            let i = i64::try_from(*i)
                .map_err(|_| DbgError::Refused("an integer outside signed 64 bits"))?;
            out.push_str(&i.to_string());
        }
        DbgVal::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        DbgVal::Str(s) => out.push_str(&json_string(s)),
        DbgVal::Named(tag, fields) => {
            out.push_str("{\"t\":");
            out.push_str(&json_string(tag));
            out.push_str(",\"f\":[");
            for (i, f) in fields.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                render_dbg(f, threads, out)?;
            }
            out.push_str("]}");
        }
        DbgVal::List(items) => {
            out.push('[');
            for (i, x) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                render_dbg(x, threads, out)?;
            }
            out.push(']');
        }
        DbgVal::Set(items) => {
            let mut enc = Vec::with_capacity(items.len());
            for x in items {
                let mut s = String::new();
                render_dbg(x, threads, &mut s)?;
                enc.push(s);
            }
            // Sorted by the encoded bytes; two equal encodings break P3.
            enc.sort_unstable();
            if enc.windows(2).any(|w| w[0] == w[1]) {
                return Err(DbgError::Refused("a set with two equal encodings"));
            }
            out.push('[');
            out.push_str(&enc.join(","));
            out.push(']');
        }
        DbgVal::Thread(n) => match threads.get(n) {
            Some(ThreadName::Named(name)) => out.push_str(&json_string(name)),
            Some(ThreadName::Unnamed) => {
                return Err(DbgError::Thread(format!("thread t{n} has no name")));
            }
            Some(ThreadName::Conflict(a, b)) => {
                return Err(DbgError::Thread(format!(
                    "thread t{n} is named `{a}` in one graph and `{b}` in another"
                )));
            }
            None => {
                return Err(DbgError::Thread(format!("t{n} is not a thread of the run")));
            }
        },
    }
    Ok(())
}

/// `G1`: a value's canonical bytes from its derived `Debug` rendering (G1-1);
/// refused with the value's type and the offending text.
pub(crate) fn encode_generic(v: &Val, threads: &ThreadNames) -> Result<String, ExportError> {
    let text = format!("{:?}", &*v.val);
    let mut p = DbgParser { s: &text, pos: 0 };
    let parsed = p.value().and_then(|x| {
        if p.pos == text.len() {
            Ok(x)
        } else {
            Err(DbgError::Unparsed(p.pos))
        }
    });
    let mut out = String::new();
    let rendered = parsed.and_then(|x| render_dbg(&x, threads, &mut out));
    match rendered {
        Ok(()) => Ok(out),
        Err(DbgError::Unparsed(at)) => Err(ExportError::Unparsed {
            type_name: v.type_name.clone(),
            rendering: text,
            at,
        }),
        Err(DbgError::Refused(what)) => Err(ExportError::Refused {
            type_name: v.type_name.clone(),
            rendering: text,
            what: what.to_string(),
        }),
        Err(DbgError::Thread(reason)) => Err(ExportError::Thread {
            type_name: v.type_name.clone(),
            reason,
        }),
    }
}

// ------------------------------------------------------- the line, shared --

/// One observation as text: a send, or a receive of a value or of ⊥ (`None`).
#[derive(Clone, Debug)]
enum ObsText {
    Send(String),
    Recv(Option<String>),
}

fn status_name(s: Status) -> &'static str {
    match s {
        Status::Done => "done",
        Status::Blocked => "blocked",
        Status::Errored => "err",
    }
}

fn status_of(name: &str) -> Option<Status> {
    match name {
        "done" => Some(Status::Done),
        "blocked" => Some(Status::Blocked),
        "err" => Some(Status::Errored),
        _ => None,
    }
}

/// A summary line in the normal form both sides share (X2, R2): `statuses`,
/// then `words`, then `counts`; the names in sorted order; no `n`; no
/// whitespace. `statuses` and `words` are aligned with `names`.
fn render_line(
    names: &[String],
    statuses: &[Status],
    words: &[Vec<ObsText>],
    counts: &[u16],
) -> String {
    let mut out = String::from("{\"statuses\":{");
    for (i, (n, s)) in names.iter().zip(statuses).enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{}:\"{}\"", json_string(n), status_name(*s));
    }
    out.push_str("},\"words\":{");
    for (i, (n, w)) in names.iter().zip(words).enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{}:[", json_string(n));
        for (j, o) in w.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            match o {
                ObsText::Send(v) => {
                    let _ = write!(out, "{{\"s\":{v}}}");
                }
                ObsText::Recv(Some(v)) => {
                    let _ = write!(out, "{{\"r\":{v}}}");
                }
                ObsText::Recv(None) => out.push_str("{\"r\":null}"),
            }
        }
        out.push(']');
    }
    out.push_str("},\"counts\":[");
    for (i, c) in counts.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{c}");
    }
    out.push_str("]}");
    out
}

/// The declared names, sorted (byte order, as `OrdCounts::of`) and deduplicated.
pub(crate) fn sorted_names(visible: &[String]) -> Vec<String> {
    let mut names = visible.to_vec();
    names.sort_unstable();
    names.dedup();
    names
}

// --------------------------------------------------------------- exporter --

/// The header fields the caller names (X3): `program` and `size`, printed by
/// the join and never compared.
#[derive(Clone, Debug)]
pub struct ExportHeader {
    pub program: String,
    pub size: String,
}

/// What an export wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExportStats {
    /// The summary lines written (the header not counted).
    pub lines: usize,
    /// The index's held orders, which `lines` equals (X1).
    pub orders_held: usize,
    /// The specification's explored graphs.
    pub spec_graphs: usize,
}

/// Why an export was refused; no file is written (X4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportError {
    /// The configuration's index is not `Set`.
    NotSet,
    /// The configuration's `ConsType` has no format `model` (G1-4).
    Model(String),
    /// A value's `Debug` rendering outside the derived grammar (G1-1).
    Unparsed {
        type_name: String,
        rendering: String,
        at: usize,
    },
    /// A value holding a form the format refuses (G1-1), named.
    Refused {
        type_name: String,
        rendering: String,
        what: String,
    },
    /// A `ThreadId` with no role name in the run (G1-1).
    Thread { type_name: String, reason: String },
    /// Two entries rendering one line: their `Debug` and `PartialEq` disagree (P3).
    Collision { line: String },
    /// The specification run did not exhaust.
    NotExhausted(String),
    /// The program raised assertions (the format's specification side raises none).
    SpecErrors(usize),
    /// Writing the file failed.
    Io(String),
}

/// `G1-4`: the format's `model` of a `ConsType`: FIFO → `p2p`, Bag → `asyn`,
/// Causal (and the deprecated CD) → `cd`; the others have none.
#[allow(deprecated)]
pub fn model_name(c: ConsType) -> Result<&'static str, ExportError> {
    match c {
        ConsType::FIFO => Ok("p2p"),
        ConsType::Bag => Ok("asyn"),
        ConsType::Causal | ConsType::CD => Ok("cd"),
        other => Err(ExportError::Model(format!("{other:?}"))),
    }
}

fn header_line(h: &ExportHeader, names: &[String], model: &str) -> String {
    let visible: Vec<String> = names.iter().map(|n| json_string(n)).collect();
    format!(
        "{{\"format\":1,\"tool\":\"traceforge\",\"program\":{},\"size\":{},\"visible\":[{}],\
         \"model\":{},\"enumeration\":\"complete\",\"encoding\":1}}",
        json_string(&h.program),
        json_string(&h.size),
        visible.join(","),
        json_string(model)
    )
}

/// The line of one entry of the specification's index (X2), its values encoded
/// by `enc`.
pub(crate) fn line_of(
    sig: &Sig,
    ord: &OrdCounts,
    names: &[String],
    enc: &dyn Fn(&Val) -> Result<String, ExportError>,
) -> Result<String, ExportError> {
    let mut statuses = Vec::with_capacity(names.len());
    let mut words = Vec::with_capacity(names.len());
    for n in names {
        statuses.push(
            sig.status(n)
                .expect("conformance: a summary has a status per declared name"),
        );
        let mut w = Vec::with_capacity(sig.word(n).len());
        for o in sig.word(n) {
            w.push(match o {
                Obs::Send(v) => ObsText::Send(enc(v)?),
                Obs::Recv(Some(v)) => ObsText::Recv(Some(enc(v)?)),
                Obs::Recv(None) => ObsText::Recv(None),
            });
        }
        words.push(w);
    }
    let counts: Vec<u16> = match ord {
        OrdCounts::U8(c) => c.iter().map(|&x| u16::from(x)).collect(),
        OrdCounts::U16(c) => c.clone(),
    };
    Ok(render_line(names, &statuses, &words, &counts))
}

/// X4: the text goes to `<path>.tmp`, which is renamed into place, so the path
/// holds its earlier content or the whole export, and no `.tmp` stays behind.
pub(crate) fn write_replacing(path: &Path, text: &str) -> Result<(), ExportError> {
    let mut tmp = path.as_os_str().to_owned();
    tmp.push(".tmp");
    let tmp = PathBuf::from(tmp);
    let written = fs::File::create(&tmp)
        .and_then(|mut f| {
            f.write_all(text.as_bytes())?;
            f.sync_all()
        })
        .and_then(|()| fs::rename(&tmp, path));
    written.map_err(|e| {
        let _ = fs::remove_file(&tmp);
        ExportError::Io(format!("{}: {e}", path.display()))
    })
}

/// `G1`: the export (G1-3). `program` is enumerated once as a specification
/// under `cc` (whose index must be `Set`) with this function's own completion
/// sink, which fills a `SetIndex` exactly as the stateful engine's specification
/// sink does (the same configuration with no bound, the same visible names,
/// `CompactSummary::at_completion` inserted at every completion) and records the
/// thread names. After the run every entry is encoded by its values' derived
/// `Debug` rendering and the file is written: the header, then one line per
/// entry in `entries()` order. Every refusal comes before the write.
pub fn export<P>(
    cc: &ConfConfig,
    program: P,
    header: &ExportHeader,
    path: &Path,
) -> Result<ExportStats, ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    if cc.index != IndexKind::Set {
        return Err(ExportError::NotSet);
    }
    let model = model_name(cc.config.cons_type)?;
    let names = sorted_names(&cc.visible);
    let program: Arc<dyn Fn() + Send + Sync> = Arc::new(program);
    let mut config = cc.config.clone();
    config.max_iterations = None;
    let state = Rc::new(RefCell::new((SetIndex::new(), ThreadNames::new(), 0usize)));
    let sink: CompletionSink = {
        let state = Rc::clone(&state);
        let visible = cc.visible.clone();
        Box::new(move |g: &ExecutionGraph, _: &MustState| {
            let s = CompactSummary::at_completion(g, &visible, "specification");
            let mut st = state.borrow_mut();
            st.0.insert(&s);
            record_thread_names(g, &mut st.1);
            st.2 += 1;
            SinkVerdict::Continue
        })
    };
    let run = stateful::enumerate(
        stateful::EnumRun {
            config,
            visible: cc.visible.clone(),
            mode: ConfMode::Enumerate,
            sink,
            cut: false,
            stop_at_first_report: false,
            gate_sink: None,
            paper_events: false,
        },
        &program,
    );
    let errors = run.visible_errors.len()
        + run
            .diagnostics
            .iter()
            .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
            .count();
    if errors > 0 {
        return Err(ExportError::SpecErrors(errors));
    }
    if run.end != SearchEnd::StateSpaceExhausted {
        return Err(ExportError::NotExhausted(format!("{:?}", run.end)));
    }
    let st = state.borrow();
    let (index, threads, graphs) = (&st.0, &st.1, st.2);
    let mut text = header_line(header, &names, model);
    text.push('\n');
    let mut seen = HashSet::new();
    let mut lines = 0;
    for (_, sig, _, ord) in index.entries() {
        let line = line_of(sig, ord, &names, &|v| encode_generic(v, threads))?;
        if !seen.insert(line.clone()) {
            return Err(ExportError::Collision { line });
        }
        text.push_str(&line);
        text.push('\n');
        lines += 1;
    }
    write_replacing(path, &text)?;
    Ok(ExportStats {
        lines,
        orders_held: index.stats().entries,
        spec_graphs: graphs,
    })
}

// ------------------------------------------------------ reader and join --

/// A decoded value: its canonical bytes. Equality is byte equality, the
/// format's comparison (J1); every decoded value has this one concrete type, so
/// equal decoded signatures share `Sig::hash128`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DecVal(pub(crate) String);

/// A file's `enumeration` (R1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Enumeration {
    Complete,
    Sampled,
    Bounded,
    Aborted,
}

impl Enumeration {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Enumeration::Complete => "complete",
            Enumeration::Sampled => "sampled",
            Enumeration::Bounded => "bounded",
            Enumeration::Aborted => "aborted",
        }
    }
}

/// A file's header as the join prints it (R1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FileHead {
    pub(crate) tool: String,
    pub(crate) program: String,
    pub(crate) size: String,
    pub(crate) model: String,
    pub(crate) visible: Vec<String>,
    pub(crate) enumeration: Enumeration,
}

/// Why an implementation line is not covered (J4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MissClass {
    /// No specification line has the shape (kinds, lengths, statuses).
    NoBucket,
    /// The shape is held, not these values.
    NoSlot,
    /// The signature is held; no order of it is `≤` the line's.
    NotFound,
}

impl MissClass {
    pub(crate) fn name(self) -> &'static str {
        match self {
            MissClass::NoBucket => "no-bucket",
            MissClass::NoSlot => "no-slot",
            MissClass::NotFound => "not-found",
        }
    }
}

/// The join's verdict (J3-3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Verdict {
    Conforms,
    Violation,
    /// A `sampled` implementation with every line covered.
    NoVerdict,
}

/// What `conf-join` found (J3-3).
#[derive(Clone, Debug)]
pub struct JoinReport {
    pub(crate) spec: FileHead,
    pub(crate) imp: FileHead,
    pub(crate) verdict: Verdict,
    /// The uncovered implementation lines, normalised, in the file's order.
    pub(crate) uncovered: Vec<(MissClass, String)>,
}

impl JoinReport {
    /// 0 for conforms or no verdict (partial or not), 1 for a violation.
    pub fn exit_code(&self) -> u8 {
        match self.verdict {
            Verdict::Violation => 1,
            Verdict::Conforms | Verdict::NoVerdict => 0,
        }
    }
}

/// Why `conf-join` refused its input (exit 2): the file, the line where one is
/// at fault, and what is wrong.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JoinError(pub(crate) String);

impl std::error::Error for JoinError {}

/// A value's normal form (R2, ruling Q8; G1-2 widened Q9): integers, strings,
/// booleans, lists and `{t, f}` objects; `Err` names a value version 1 forbids.
fn normal_value(v: &Value) -> Result<String, String> {
    match v {
        Value::Number(n) => match n.as_i64() {
            Some(i) => Ok(i.to_string()),
            None => Err(invalid(
                "a number other than an integer within signed 64 bits",
            )),
        },
        Value::Object(m) => {
            let (Some(Value::String(tag)), Some(Value::Array(fields)), 2) =
                (m.get("t"), m.get("f"), m.len())
            else {
                return Err(invalid("an object other than {\"t\":…,\"f\":[…]}"));
            };
            let mut out = format!("{{\"t\":{},\"f\":[", json_string(tag));
            for (i, x) in fields.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&normal_value(x)?);
            }
            out.push_str("]}");
            Ok(out)
        }
        Value::Null => Err(invalid("`null` other than ⊥")),
        // `G1-2`: strings, booleans and lists, as JMC's reader (J3's Q9 superseded).
        Value::String(s) => Ok(json_string(s)),
        Value::Bool(b) => Ok(if *b { "true" } else { "false" }.to_string()),
        Value::Array(items) => {
            let mut out = String::from("[");
            for (i, x) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&normal_value(x)?);
            }
            out.push(']');
            Ok(out)
        }
    }
}

fn invalid(what: &str) -> String {
    format!("{what} is invalid in format version 1")
}

/// An object's keys, which must be exactly the declared names.
fn exact_keys(
    m: &serde_json::Map<String, Value>,
    names: &[String],
    what: &str,
) -> Result<(), String> {
    let mut keys: Vec<&str> = m.keys().map(String::as_str).collect();
    keys.sort_unstable();
    let want: Vec<&str> = names.iter().map(String::as_str).collect();
    if keys != want {
        return Err(format!(
            "`{what}` has the keys {keys:?}, not the visible names {want:?}"
        ));
    }
    Ok(())
}

/// One summary line (R2, R3): its normal form, which is also the duplicate
/// key, and its summary for the index. `names` are the header's, sorted.
pub(crate) fn parse_line(text: &str, names: &[String]) -> Result<(String, CompactSummary), String> {
    let v: Value = serde_json::from_str(text).map_err(|e| format!("not JSON: {e}"))?;
    let Value::Object(m) = v else {
        return Err("the line is not a JSON object".to_string());
    };
    if let Some(k) = m
        .keys()
        .find(|k| !matches!(k.as_str(), "statuses" | "words" | "counts" | "n"))
    {
        return Err(format!("unknown key `{k}`"));
    }
    let Some(Value::Object(sm)) = m.get("statuses") else {
        return Err("no `statuses` object".to_string());
    };
    let Some(Value::Object(wm)) = m.get("words") else {
        return Err("no `words` object".to_string());
    };
    let Some(Value::Array(cs)) = m.get("counts") else {
        return Err("no `counts` array".to_string());
    };
    exact_keys(sm, names, "statuses")?;
    exact_keys(wm, names, "words")?;

    let mut statuses = Vec::with_capacity(names.len());
    let mut words: Vec<Vec<ObsText>> = Vec::with_capacity(names.len());
    for n in names {
        let Value::String(s) = &sm[n] else {
            return Err(format!("the status of `{n}` is not a string"));
        };
        statuses.push(status_of(s).ok_or_else(|| format!("unknown status `{s}`"))?);
        let Value::Array(obs) = &wm[n] else {
            return Err(format!("the word of `{n}` is not an array"));
        };
        if obs.len() > u16::MAX as usize {
            return Err(format!(
                "the word of `{n}` has more than {} events",
                u16::MAX
            ));
        }
        let mut w = Vec::with_capacity(obs.len());
        for o in obs {
            let one = match o {
                Value::Object(om) if om.len() == 1 => om.iter().next(),
                _ => None,
            };
            w.push(match one {
                Some((k, x)) if k == "s" && !x.is_null() => ObsText::Send(normal_value(x)?),
                Some((k, Value::Null)) if k == "r" => ObsText::Recv(None),
                Some((k, x)) if k == "r" => ObsText::Recv(Some(normal_value(x)?)),
                _ => {
                    return Err(format!(
                        "an observation of `{n}` is not {{\"s\":V}}, {{\"r\":V}} or {{\"r\":null}}"
                    ))
                }
            });
        }
        words.push(w);
    }

    // `counts` (R2): Σ_t |w_t| · (T − 1) entries, event-major, each bounded by
    // the other thread's word length.
    let t = names.len();
    let total: usize = words.iter().map(Vec::len).sum();
    let want = total * t.saturating_sub(1);
    if cs.len() != want {
        return Err(format!("`counts` has {} entries, not {want}", cs.len()));
    }
    let mut counts = Vec::with_capacity(want);
    let mut it = cs.iter();
    for (ti, w) in words.iter().enumerate() {
        for _ in w {
            for (tj, other) in words.iter().enumerate() {
                if tj == ti {
                    continue;
                }
                let c = it.next().expect("conformance: the length was checked");
                let c = c
                    .as_u64()
                    .ok_or_else(|| "a count is not a non-negative integer".to_string())?;
                if c > other.len() as u64 {
                    return Err(format!(
                        "a count {c} exceeds the length {} of `{}`'s word",
                        other.len(),
                        names[tj]
                    ));
                }
                counts.push(c as u16);
            }
        }
    }

    let key = render_line(names, &statuses, &words, &counts);

    // The summary (R3): `U16` iff some word exceeds 255 events, as `OrdCounts::of`.
    let wide = words.iter().any(|w| w.len() > 255);
    let ord = if wide {
        OrdCounts::U16(counts)
    } else {
        OrdCounts::U8(counts.into_iter().map(|c| c as u8).collect())
    };
    let mut sig_statuses = BTreeMap::new();
    let mut sig_words = BTreeMap::new();
    for ((n, s), w) in names.iter().zip(&statuses).zip(&words) {
        sig_statuses.insert(n.clone(), *s);
        let decoded: Vec<Obs> = w
            .iter()
            .map(|o| match o {
                ObsText::Send(v) => Obs::Send(Val::new(DecVal(v.clone()))),
                ObsText::Recv(Some(v)) => Obs::Recv(Some(Val::new(DecVal(v.clone())))),
                ObsText::Recv(None) => Obs::Recv(None),
            })
            .collect();
        sig_words.insert(n.clone(), decoded);
    }
    let sig = Sig::from_words(sig_statuses, sig_words);
    let summary = CompactSummary {
        hash: sig.hash128(),
        sig,
        sig_est: 32 * total + 16 * t,
        ord,
    };
    Ok((key, summary))
}

/// A line's normal form (ruling Q8), for the test that JMC's lines are already
/// in it; `visible` as the file's header gives it.
pub(crate) fn normal_line(text: &str, visible: &[String]) -> Result<String, String> {
    parse_line(text, &sorted_names(visible)).map(|(key, _)| key)
}

fn header_of(text: &str) -> Result<FileHead, String> {
    let v: Value =
        serde_json::from_str(text).map_err(|e| format!("the header is not JSON: {e}"))?;
    let Value::Object(m) = v else {
        return Err("the header is not a JSON object".to_string());
    };
    let int = |k: &str| m.get(k).and_then(Value::as_i64);
    let string = |k: &str| -> Result<String, String> {
        match m.get(k) {
            Some(Value::String(s)) => Ok(s.clone()),
            _ => Err(format!("the header has no string `{k}`")),
        }
    };
    if int("format") != Some(1) {
        return Err("the header's `format` is not 1".to_string());
    }
    if int("encoding") != Some(1) {
        return Err("the header's `encoding` is not 1".to_string());
    }
    let Some(Value::Array(vis)) = m.get("visible") else {
        return Err("the header has no `visible` list".to_string());
    };
    let mut visible = Vec::with_capacity(vis.len());
    for x in vis {
        let Value::String(n) = x else {
            return Err("a `visible` name is not a string".to_string());
        };
        visible.push(n.clone());
    }
    if sorted_names(&visible).len() != visible.len() {
        return Err("the header's `visible` list names a role twice".to_string());
    }
    let enumeration = match string("enumeration")?.as_str() {
        "complete" => Enumeration::Complete,
        "sampled" => Enumeration::Sampled,
        "bounded" => Enumeration::Bounded,
        "aborted" => Enumeration::Aborted,
        other => return Err(format!("unknown `enumeration` `{other}`")),
    };
    Ok(FileHead {
        tool: string("tool")?,
        program: string("program")?,
        size: string("size")?,
        model: string("model")?,
        visible,
        enumeration,
    })
}

/// A file read whole: its header and, per line, its number, its normal form
/// and its summary. A duplicate line is refused (R4, ruling Q4).
pub(crate) struct ReadFile {
    pub(crate) head: FileHead,
    pub(crate) lines: Vec<(usize, String, CompactSummary)>,
}

pub(crate) fn read_file(path: &Path) -> Result<ReadFile, JoinError> {
    let at = |line: Option<usize>, what: String| {
        JoinError(match line {
            Some(n) => format!("{}: line {n}: {what}", path.display()),
            None => format!("{}: {what}", path.display()),
        })
    };
    let text = fs::read_to_string(path).map_err(|e| at(None, e.to_string()))?;
    let mut raw = text.lines();
    let first = raw
        .next()
        .ok_or_else(|| at(None, "the file is empty".to_string()))?;
    let head = header_of(first).map_err(|e| at(Some(1), e))?;
    let names = sorted_names(&head.visible);
    let mut seen: HashMap<String, usize> = HashMap::new();
    let mut lines = Vec::new();
    for (i, l) in raw.enumerate() {
        let number = i + 2;
        let (key, summary) = parse_line(l, &names).map_err(|e| at(Some(number), e))?;
        if let Some(earlier) = seen.insert(key.clone(), number) {
            return Err(at(
                Some(number),
                format!("the line repeats line {earlier} (each line is one distinct summary)"),
            ));
        }
        lines.push((number, key, summary));
    }
    Ok(ReadFile { head, lines })
}

/// `conf-join spec.jsonl impl.jsonl` (J3-3): the specification's lines into a
/// `SetIndex`, each implementation line queried with `covers`. Refused (`Err`):
/// a file that does not parse (R1, R2), a duplicate line (R4), unequal
/// `visible` lists, a specification whose `enumeration` is not `complete`.
/// `model` is printed, never compared (ruling Q3).
pub fn conf_join(spec: &Path, imp: &Path) -> Result<JoinReport, JoinError> {
    let s = read_file(spec)?;
    let i = read_file(imp)?;
    if s.head.enumeration != Enumeration::Complete {
        return Err(JoinError(format!(
            "{}: the specification is `{}`, not `complete`",
            spec.display(),
            s.head.enumeration.name()
        )));
    }
    if s.head.visible != i.head.visible {
        return Err(JoinError(format!(
            "the two files' `visible` lists differ: {:?} and {:?}",
            s.head.visible, i.head.visible
        )));
    }
    let mut index = SetIndex::new();
    for (_, _, summary) in &s.lines {
        index.insert(summary);
    }
    let mut uncovered = Vec::new();
    for (_, key, summary) in &i.lines {
        let class = match index.covers(summary).1 {
            Covers::Found(_) => continue,
            Covers::NoBucket => MissClass::NoBucket,
            Covers::NoSig => MissClass::NoSlot,
            Covers::NotFound => MissClass::NotFound,
        };
        uncovered.push((class, key.clone()));
    }
    let verdict = if !uncovered.is_empty() {
        Verdict::Violation
    } else if i.head.enumeration == Enumeration::Sampled {
        Verdict::NoVerdict
    } else {
        Verdict::Conforms
    };
    Ok(JoinReport {
        spec: s.head,
        imp: i.head,
        verdict,
        uncovered,
    })
}
