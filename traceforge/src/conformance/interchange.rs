//! `J3` and `G1`: TraceForge's side of the compact summary interchange format,
//! version 1 (`plan/jmc-must/SUMMARY-FORMAT.md`), for any Must program.
//!
//! - **The generic encoder** (G1-1): a value's canonical form is parsed from its
//!   derived `Debug` rendering ([`encode_generic`]): a struct, tuple struct or
//!   variant becomes `{"t":<name>,"f":[…]}`, lists, sets (sorted), integers,
//!   strings and booleans as the format says, a `ThreadId` its role name;
//!   anything else is refused with the value's type. Maps are refused; an
//!   empty `{}` (an empty set or an empty map) is a set only where the message
//!   type's declared shape says so (`conformance::shape`). Preconditions: the
//!   text `ThreadId { opaque_id: N }` is reserved; a value's `Debug` agrees with
//!   its `PartialEq`. No per-program encoder exists.
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
    /// `{a, b}`; also an empty `{}`, which an empty map prints too: the
    /// declared shape decides ([`check_braces`]).
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
    /// A visible payload violates its declared role restrictions.
    PayloadThread(String),
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
            // An empty set and an empty map print alike: `check_braces` decides.
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
fn render_dbg(
    v: &DbgVal, threads: &ThreadNames, out: &mut String,
) -> Result<(), DbgError> {
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
            Some(ThreadName::Named(name)) => {
                out.push_str(&json_string(name));
            }
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

/// Whether `v` holds a `{}`, which needs the declared shape.
fn has_empty_brace(v: &DbgVal) -> bool {
    match v {
        DbgVal::Set(items) if items.is_empty() => true,
        DbgVal::Set(items) | DbgVal::List(items) | DbgVal::Named(_, items) => {
            items.iter().any(has_empty_brace)
        }
        _ => false,
    }
}

/// The refusal of a `{}` the declared shape does not make a set.
const UNDECLARED_BRACE: &str = "an empty `{}` whose type is not declared a set (an empty set and an \
     empty map print alike: derive `SummaryShape` for the message type and call \
     `traceforge::conformance::declare`)";

/// Each `{}` in `v` against the declared shape `s`: an empty set where `s` has a
/// set, refused where it has a map ("a map", as every map) or nothing known.
/// Where the parsed value and the shape disagree (a hand-written `Debug`), the
/// rest is unknown.
///
/// `undeclared_as_set`: an undescribed `{}` is an empty set instead of refused.
fn check_braces(
    v: &DbgVal, s: &crate::conformance::shape::Shape, undeclared_as_set: bool,
) -> Result<(), DbgError> {
    use crate::conformance::shape::Shape;
    let each = |items: &[DbgVal], f: &dyn Fn(usize) -> Shape| -> Result<(), DbgError> {
        for (k, x) in items.iter().enumerate() {
            if has_empty_brace(x) {
                check_braces(x, &f(k), undeclared_as_set)?;
            }
        }
        Ok(())
    };
    match v {
        DbgVal::Set(items) => match s {
            Shape::Set(elem) => each(items, &|_| elem()),
            Shape::Map => Err(DbgError::Refused("a map")),
            _ if items.is_empty() && !undeclared_as_set => Err(DbgError::Refused(UNDECLARED_BRACE)),
            _ if items.is_empty() => Ok(()),
            _ => each(items, &|_| Shape::Opaque),
        },
        DbgVal::List(items) => match s {
            Shape::List(elem) => each(items, &|_| elem()),
            _ => each(items, &|_| Shape::Opaque),
        },
        DbgVal::Named(tag, fields) => {
            let declared = match s {
                Shape::Record(name, fs) if *name == tag.as_str() && fs.len() == fields.len() => Some(fs),
                Shape::Variants(vs) => vs
                    .iter()
                    .find(|(name, fs)| *name == tag.as_str() && fs.len() == fields.len())
                    .map(|(_, fs)| fs),
                _ => None,
            };
            match declared {
                Some(fs) => each(fields, &|k| fs[k]()),
                None => each(fields, &|_| Shape::Opaque),
            }
        }
        _ => Ok(()),
    }
}

/// Check only the new restrictions, using the execution that holds this payload.
/// Unknown and unnamed identities are left to the legacy encoder.
fn check_payload(v: &DbgVal, g: &ExecutionGraph, roles: &[String]) -> Result<(), DbgError> {
    match v {
        DbgVal::Thread(n) if *n != 0 => {
            if let Some(tid) = g.thread_ids().into_iter().find(|t| u32::from(*t) == *n) {
                if g.is_thread_daemon(tid) {
                    return Err(DbgError::PayloadThread(format!("thread t{n} is a daemon")));
                }
                if let Some(name) = g.thread_name(tid) {
                    if !roles.iter().any(|r| r == name) {
                        return Err(DbgError::PayloadThread(format!(
                            "thread t{n} named `{name}` is not declared payload-nameable"
                        )));
                    }
                }
            }
        }
        DbgVal::Named(_, fields) | DbgVal::List(fields) | DbgVal::Set(fields) => {
            for f in fields {
                check_payload(f, g, roles)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Sequential export validates before deduplication loses the execution context.
/// It does not render values or lines; legacy encoding errors remain deferred.
fn check_payloads(
    sig: &Sig, g: &ExecutionGraph, visible: &[String], roles: &[String],
) -> Result<(), ExportError> {
    for name in visible {
        for obs in sig.word(name) {
            let v = match obs {
                Obs::Send(v) | Obs::Recv(Some(v)) => v,
                Obs::Recv(None) => continue,
            };
            let text = format!("{:?}", &*v.val);
            let mut p = DbgParser { s: &text, pos: 0 };
            if let Ok(parsed) = p.value() {
                if p.pos == text.len() {
                    if let Err(DbgError::PayloadThread(reason)) = check_payload(&parsed, g, roles) {
                        return Err(ExportError::PayloadThread {
                            type_name: v.type_name.clone(),
                            reason,
                        });
                    }
                }
            }
        }
    }
    Ok(())
}

/// `G1`: a value's canonical bytes from its derived `Debug` rendering (G1-1);
/// refused with the value's type and the offending text.
pub(crate) fn encode_generic(v: &Val, threads: &ThreadNames) -> Result<String, ExportError> {
    encode_declared(v, threads, None)
}

pub(crate) fn encode_declared(
    v: &Val, threads: &ThreadNames, context: Option<(&ExecutionGraph, &[String])>,
) -> Result<String, ExportError> {
    encode_with(v, threads, context, false)
}

/// The text witness's encoding of a send (`execution_witness`): as
/// [`encode_generic`], except that a `{}` the message type does not declare is
/// written as an empty set, as before shapes existed. The witness prints every
/// send, invisible ones included, whose values are never summarised or
/// compared; a visible value's `{}` has already been checked strictly when its
/// summary line was encoded. A declared map is still refused.
pub(crate) fn encode_witness_value(v: &Val, threads: &ThreadNames) -> Result<String, ExportError> {
    encode_with(v, threads, None, true)
}

fn encode_with(
    v: &Val, threads: &ThreadNames, context: Option<(&ExecutionGraph, &[String])>,
    undeclared_as_set: bool,
) -> Result<String, ExportError> {
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
    let rendered = parsed.and_then(|x| {
        render_dbg(&x, threads, &mut out)?;
        if has_empty_brace(&x) {
            let id = std::any::Any::type_id(v.val.msg_as_any_ref());
            check_braces(&x, &crate::conformance::shape::declared(id), undeclared_as_set)?;
        }
        if let Some((g, roles)) = context {
            check_payload(&x, g, roles)?;
        }
        Ok(())
    });
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
        Err(DbgError::PayloadThread(reason)) => Err(ExportError::PayloadThread {
            type_name: v.type_name.clone(),
            reason,
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
    counts: &[u32],
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

/// Export/online declarations; in-process conformance keeps its own name rules.
pub(crate) fn checked_names(visible: &[String]) -> Result<Vec<String>, ExportError> {
    for n in visible {
        if n.is_empty() || n == "main" || n.starts_with('~') || !n.is_ascii() {
            return Err(ExportError::Names(format!("invalid declared visible name: {n:?}")));
        }
    }
    let names = sorted_names(visible);
    if names.len() != visible.len() {
        return Err(ExportError::Names("a visible name is declared twice".to_string()));
    }
    Ok(names)
}

/// The union is independent of which identities an execution happens to send.
pub(crate) fn declared_roles(
    visible: &[String], payload: &[String],
) -> Result<Vec<String>, ExportError> {
    let mut roles = checked_names(visible)?;
    let extra = checked_names(payload)?;
    for name in extra {
        if roles.contains(&name) {
            return Err(ExportError::Names(format!("role is declared twice: {name:?}")));
        }
        roles.push(name);
    }
    roles.sort_unstable();
    Ok(roles)
}

fn check_named_graph(
    g: &ExecutionGraph,
    visible: &[String],
    kind: &str,
) -> Result<(), ExportError> {
    for tid in g.thread_ids() {
        if g.is_thread_daemon(tid) {
            if let Some(n) = g.thread_name(tid) {
                if visible.iter().any(|v| v == n) {
                    return Err(ExportError::Names(format!(
                        "declared {kind} name is a daemon: {n:?}"
                    )));
                }
            }
        }
    }
    Ok(())
}

pub(crate) fn check_roles_graph(
    g: &ExecutionGraph, visible: &[String], roles: &[String],
) -> Result<(), ExportError> {
    check_named_graph(g, visible, "visible")?;
    check_named_graph(g, roles, "payload-nameable")
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
    /// The distinct summaries held: the index's orders, which `lines` equals
    /// (X1); on the partitioned path, where the line is the identity, the lines.
    pub orders_held: usize,
    /// The specification's explored graphs.
    pub spec_graphs: usize,
    /// `B` (MEAS-1 K2): the run's executions, its phases in milliseconds
    /// (`explore_ms` = the run's wall − `summarise_ms`; `export_ms` = encode +
    /// write), the completion classes and the shape counters.
    pub(crate) executions: usize,
    pub(crate) explore_ms: u128,
    pub(crate) summarise_ms: u128,
    pub(crate) export_ms: u128,
    pub(crate) graphs_complete: usize,
    pub(crate) graphs_blocked: usize,
    pub(crate) shape: crate::conformance::measure::Shape,
}

/// `B`'s test seams for [`export_with`] (MEAS-2); inert outside tests.
#[derive(Clone, Copy, Default)]
pub(crate) struct ExportSeams {
    /// Sleep this long inside the export phase (encode + write).
    #[cfg(test)]
    pub(crate) export_delay: Option<std::time::Duration>,
}

/// `B`'s test seams for [`conf_join_with`] (MEAS-2); inert outside tests.
#[derive(Clone, Copy, Default)]
pub(crate) struct JoinSeams {
    /// Sleep this long inside the index phase.
    #[cfg(test)]
    pub(crate) index_delay: Option<std::time::Duration>,
    /// Sleep this long inside the lookup phase.
    #[cfg(test)]
    pub(crate) lookup_delay: Option<std::time::Duration>,
}

/// Why an export was refused; no file is written (X4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportError {
    Threshold(crate::ThresholdStop),
    /// The configuration's index is not `Set`.
    NotSet,
    /// The configuration's `ConsType` has no format `model` (G1-4).
    Model(String),
    /// An invalid export/online declaration.
    Names(String),
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
    /// An unnamed, unknown or genuinely conflicting `ThreadId` in the run (G1-1).
    Thread { type_name: String, reason: String },
    /// A daemon or undeclared identity in a visible payload.
    PayloadThread { type_name: String, reason: String },
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

pub(crate) fn header_line(
    h: &ExportHeader, names: &[String], roles: &[String], model: &str,
) -> String {
    let visible: Vec<String> = names.iter().map(|n| json_string(n)).collect();
    let roles: Vec<String> = roles.iter().map(|n| json_string(n)).collect();
    format!(
        "{{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":{},\
         \"size\":{},\"visible\":[{}],\
         \"roles\":[{}],\"model\":{},\"enumeration\":\"complete\",\"encoding\":1}}",
        json_string(&h.program),
        json_string(&h.size),
        visible.join(","),
        roles.join(","),
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
    let counts: Vec<u32> = match ord {
        OrdCounts::U8(c) => c.iter().map(|&x| u32::from(x)).collect(),
        OrdCounts::U16(c) => c.iter().map(|&x| u32::from(x)).collect(),
        OrdCounts::U32(c) => c.clone(),
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
/// entry in byte order. Every refusal comes before the write.
pub fn export<P>(
    cc: &ConfConfig,
    program: P,
    header: &ExportHeader,
    path: &Path,
) -> Result<ExportStats, ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    export_with(cc, program, header, path, ExportSeams::default())
}

/// [`export`] with `B`'s test seams.
pub(crate) fn export_with<P>(
    cc: &ConfConfig,
    program: P,
    header: &ExportHeader,
    path: &Path,
    seams: ExportSeams,
) -> Result<ExportStats, ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    export_with_store(cc, program, header, path, seams, None).0
}

/// [`export_with`] that also writes a graph store (`--graphs`) when `store` is given: one graph
/// per distinct line, from the line's first execution, written after the export succeeded. The
/// second result is `None` without a store, else the store's report or its write error.
#[allow(clippy::type_complexity)]
pub(crate) fn export_with_store<P>(
    cc: &ConfConfig,
    program: P,
    header: &ExportHeader,
    path: &Path,
    seams: ExportSeams,
    store: Option<crate::conformance::witness_graph::GraphStoreOpts>,
) -> (
    Result<ExportStats, ExportError>,
    Option<Result<crate::conformance::witness_graph::StoreReport, String>>,
)
where
    P: Fn() + Send + Sync + 'static,
{
    let wanted = store.is_some();
    let store = Rc::new(RefCell::new(
        store.map(|o| crate::conformance::witness_graph::StoreBuilder::new(o, &cc.visible)),
    ));
    let r = export_inner(cc, program, header, path, seams, &store);
    let report = match (&r, wanted) {
        (_, false) => None,
        (Err(_), true) => None,
        (Ok((_, text, sorted)), true) => {
            let b = store.borrow_mut().take().expect("conformance: the store builder is kept");
            Some(b.finish(text, sorted))
        }
    };
    (r.map(|(stats, _, _)| stats), report)
}

#[allow(clippy::type_complexity)]
fn export_inner<P>(
    cc: &ConfConfig,
    program: P,
    header: &ExportHeader,
    path: &Path,
    seams: ExportSeams,
    store: &Rc<RefCell<Option<crate::conformance::witness_graph::StoreBuilder>>>,
) -> Result<(ExportStats, String, Vec<String>), ExportError>
where
    P: Fn() + Send + Sync + 'static,
{
    use crate::conformance::compact::Inserted;
    use crate::conformance::measure::Shape;
    use std::time::{Duration, Instant};
    let _ = &seams;
    if cc.index != IndexKind::Set {
        return Err(ExportError::NotSet);
    }
    let model = model_name(cc.config.cons_type)?;
    let names = checked_names(&cc.visible)?;
    let roles = declared_roles(&names, &cc.payload_names)?;
    let program: Arc<dyn Fn() + Send + Sync> = Arc::new(program);
    let mut config = cc.config.clone();
    config.max_iterations = None;
    let state = Rc::new(RefCell::new((SetIndex::new(), ThreadNames::new(), 0usize)));
    // `B` (MEAS-1 K2): the summarise phase, the completion classes, the shape.
    let probe = Rc::new(RefCell::new((
        Duration::ZERO,
        0usize,
        0usize,
        Shape::default(),
    )));
    let refusal = Rc::new(RefCell::new(None));
    let payload_refusal = Rc::new(RefCell::new(None));
    let sink: CompletionSink = {
        let refusal = Rc::clone(&refusal);
        let payload_refusal = Rc::clone(&payload_refusal);
        let state = Rc::clone(&state);
        let probe = Rc::clone(&probe);
        let audit = cc.config.graph_audit.clone();
        let visible = cc.visible.clone();
        let names = names.clone();
        let roles = roles.clone();
        let store = Rc::clone(store);
        Box::new(move |g: &ExecutionGraph, _: &MustState| {
            if let Err(e) = check_roles_graph(g, &visible, &roles) {
                *refusal.borrow_mut() = Some(e);
                return SinkVerdict::Stop;
            }
            let (events, messages) = Shape::graph_counts(g);
            let blocked = g.check_blocked().is_some();
            let t = Instant::now();
            let s = CompactSummary::at_completion(g, &visible, "specification");
            if let Err(e) = check_payloads(&s.sig, g, &visible, &roles) {
                payload_refusal.borrow_mut().get_or_insert(e);
            }
            let mut st = state.borrow_mut();
            let new = matches!(st.0.insert(&s).1, Inserted::Stored(_));
            record_thread_names(g, &mut st.1);
            st.2 += 1;
            // `--graphs`: the first execution of a new line, while the limit allows. Its time is
            // the store's, kept out of the summarise phase here and out of exploration below.
            let mut graph_time = Duration::ZERO;
            if new {
                if let Some(b) = store.borrow_mut().as_mut().filter(|b| b.wants()) {
                    let tg = Instant::now();
                    // A line that does not encode is refused by the export itself, later.
                    if let Ok(line) = line_of(&s.sig, &s.ord, &names, &|v| encode_generic(v, &st.1)) {
                        b.add(g, line, st.2);
                    }
                    graph_time = tg.elapsed();
                    b.time_line(graph_time);
                }
            }
            let mut pr = probe.borrow_mut();
            // Word lengths need no encoding; payload names are resolved after enumeration.
            pr.3.add_summary(&s, &names, 0);
            pr.0 += t.elapsed().saturating_sub(graph_time);
            if blocked {
                pr.2 += 1;
            } else {
                pr.1 += 1;
            }
            pr.3.add_graph_counts(events, messages);
            super::graph_audit::record(&audit, g, &visible);
            SinkVerdict::Continue
        })
    };
    let run_started = Instant::now();
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
    // The graphs' walk and encoding are not exploration.
    let run_wall = run_started
        .elapsed()
        .saturating_sub(store.borrow().as_ref().map_or(Duration::ZERO, |b| b.time));
    if let Some(e) = refusal.borrow_mut().take() {
        return Err(e);
    }
    let errors = run.visible_errors.len()
        + run
            .diagnostics
            .iter()
            .filter(|d| d.reason == DiagnosticReason::InvisibleThread)
            .count();
    if let SearchEnd::Threshold(reason) = run.end.clone() {
        return Err(ExportError::Threshold(reason));
    }
    if errors > 0 {
        return Err(ExportError::SpecErrors(errors));
    }
    if run.end != SearchEnd::StateSpaceExhausted {
        return Err(ExportError::NotExhausted(format!("{:?}", run.end)));
    }
    let st = state.borrow();
    let (index, threads, graphs) = (&st.0, &st.1, st.2);
    let (summarise, complete, blocked, mut shape) = probe.borrow().clone();
    let export_started = Instant::now();
    let text = header_line(header, &names, &roles, model);
    let mut sorted: Vec<String> = Vec::with_capacity(index.stats().entries);
    for (_, sig, _, ord) in index.entries() {
        let line = line_of(sig, ord, &names, &|v| encode_generic(v, threads))?;
        shape.add_summary_bytes(line.len());
        sorted.push(line);
    }
    // Preserve legacy encoding errors, including conflicts learned later in the run.
    if let Some(e) = payload_refusal.borrow_mut().take() {
        return Err(e);
    }
    // `SORTED-JOIN`: the lines in byte order, as `export --threads N` writes
    // them, so `conf-join --merge` can read either file as a sorted stream. Two
    // entries rendering one line (P3's collision) are adjacent after the sort,
    // so the refusal needs no set of the lines.
    sorted.sort_unstable();
    if let Some(w) = sorted.windows(2).find(|w| w[0] == w[1]) {
        return Err(ExportError::Collision { line: w[0].clone() });
    }
    let lines = sorted.len();
    // The export seam sits just before the write, so a timer that stops before
    // the write would miss it (B's gate-3 finding).
    #[cfg(test)]
    if let Some(d) = seams.export_delay {
        std::thread::sleep(d);
    }
    let kept = if store.borrow().is_some() {
        crate::conformance::export_p::write_lines(path, &text, sorted.iter().cloned())?;
        sorted
    } else {
        crate::conformance::export_p::write_lines(path, &text, sorted.into_iter())?;
        Vec::new()
    };
    let export_ms = export_started.elapsed().as_millis();
    let stats = ExportStats {
        lines,
        orders_held: index.stats().entries,
        spec_graphs: graphs,
        executions: run.executions,
        explore_ms: run_wall.saturating_sub(summarise).as_millis(),
        summarise_ms: summarise.as_millis(),
        export_ms,
        graphs_complete: complete,
        graphs_blocked: blocked,
        shape,
    };
    Ok((stats, text, kept))
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
    pub(crate) roles: Option<Vec<String>>,
    pub(crate) enumeration: Enumeration,
}

/// Why an implementation line is not covered (J4).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    /// `JOIN-TOTAL`: Σ `n` over the uncovered implementation lines (0 with
    /// none); `None` when one of them carries no `n` (TraceForge omits it).
    pub(crate) uncovered_total: Option<u128>,
    /// `B` (MEAS-1 K3): the specification's read + inserts, the `covers`
    /// loop, the whole call, in milliseconds; the two files' line counts; the
    /// shape counters over the implementation's lines.
    pub(crate) index_ms: u128,
    pub(crate) lookup_ms: u128,
    pub(crate) join_ms: u128,
    pub(crate) spec_lines: usize,
    pub(crate) impl_lines: usize,
    pub(crate) shape: crate::conformance::measure::Shape,
    /// `SORTED-JOIN`: the merge's counters (`None` for the in-memory join).
    pub(crate) merge: Option<MergeStats>,
    /// `DECIDE`: the post-pass's classifications (`None` without `--decide`).
    pub(crate) decide: Option<DecideReport>,
    /// `--witness-dir`: what became of each uncovered line's graph (`None` without it).
    pub(crate) witness: Option<crate::conformance::witness_join::WitnessSummary>,
}

/// `DECIDE`: one uncovered line's classification and its witness, rendered.
#[derive(Clone, Debug)]
pub(crate) struct DecideEntry {
    pub(crate) decision: crate::conformance::decide::Decision,
    /// For a violation: the labelled word (`<role>:<observation>` in the
    /// witness's order), then the statuses.
    pub(crate) witness: Option<String>,
    /// The specification lines of the effective group (`k_min` of them), in normal form: the
    /// candidate's statuses and words with each effective order's counts.
    pub(crate) nearest: Vec<String>,
}

/// `DECIDE`: the classifications of the uncovered lines, `entries` in the
/// order of `JoinReport::uncovered`, and the counters.
#[derive(Clone, Debug, Default)]
pub(crate) struct DecideReport {
    pub(crate) entries: Vec<DecideEntry>,
    pub(crate) violations: usize,
    pub(crate) false_alarms: usize,
    pub(crate) unresolved: usize,
    /// The largest `k` (specification orders of the candidate's signature).
    pub(crate) max_group: usize,
    /// Search states over all candidates.
    pub(crate) states: u64,
    pub(crate) budget: u64,
    pub(crate) ms: u128,
}

impl DecideReport {
    fn new(budget: u64) -> Self {
        DecideReport { budget, ..DecideReport::default() }
    }

    fn push(&mut self, e: DecideEntry) {
        use crate::conformance::decide::Outcome;
        match e.decision.outcome {
            Outcome::Violation(_) => self.violations += 1,
            Outcome::FalseAlarm => self.false_alarms += 1,
            Outcome::Unresolved => self.unresolved += 1,
        }
        self.max_group = self.max_group.max(e.decision.group);
        self.states += e.decision.states;
        self.entries.push(e);
    }
}

/// DECIDE: convert only orders in a signature group used by a miss.
fn ord_u16(o: &OrdCounts, path: &Path, line: usize) -> Result<Vec<u16>, JoinError> {
    match o {
        OrdCounts::U8(v) => Ok(v.iter().map(|c| u16::from(*c)).collect()),
        OrdCounts::U16(v) => Ok(v.clone()),
        OrdCounts::U32(v) => v.iter()
            .map(|&c| {
                u16::try_from(c).map_err(|_| JoinError(format!(
                    "decide: {}: line {line}: count {c} exceeds 65535", path.display()
                )))
            })
            .collect(),
    }
}

/// `DECIDE`: classifies the uncovered line `key` (a normal form over the
/// sorted `names`) against `group`, the count vectors of the specification's
/// lines of its signature (empty for `no-bucket` and `no-slot`).
fn decide_entry(
    key: &str,
    names: &[String],
    group: &[Vec<u16>],
    budget: u64,
) -> Result<DecideEntry, JoinError> {
    use crate::conformance::decide::{decide, Outcome};
    let bad = |what: &str| JoinError(format!("decide: a normal-form line: {what}: {key}"));
    let v: Value = serde_json::from_str(key).map_err(|_| bad("not JSON"))?;
    let (Some(Value::Object(sm)), Some(Value::Object(wm)), Some(Value::Array(cs))) =
        (v.get("statuses"), v.get("words"), v.get("counts"))
    else {
        return Err(bad("no statuses, words or counts"));
    };
    let mut statuses = Vec::with_capacity(names.len());
    let mut obs: Vec<Vec<String>> = Vec::with_capacity(names.len());
    for n in names {
        statuses.push(sm.get(n).and_then(Value::as_str).ok_or_else(|| bad("a status"))?);
        let Some(Value::Array(w)) = wm.get(n) else {
            return Err(bad("a word"));
        };
        let mut texts = Vec::with_capacity(w.len());
        for o in w {
            let Some((k, x)) = o.as_object().and_then(|m| m.iter().next()) else {
                return Err(bad("an observation"));
            };
            let x = if x.is_null() {
                "null".to_string()
            } else {
                normal_value(x).map_err(|e| bad(&e))?
            };
            texts.push(format!("{{{}:{x}}}", json_string(k)));
        }
        obs.push(texts);
    }
    let counts: Vec<u16> = cs
        .iter()
        .map(|c| {
            let c = c.as_u64().ok_or_else(|| bad("a count"))?;
            u16::try_from(c).map_err(|_| bad(&format!("count {c} exceeds 65535")))
        })
        .collect::<Result<_, _>>()?;
    let lens: Vec<usize> = obs.iter().map(Vec::len).collect();
    let decision = decide(&lens, &counts, group, budget);
    let witness = match &decision.outcome {
        Outcome::Violation(w) => {
            let mut out = String::new();
            for (j, &(t, i)) in w.iter().enumerate() {
                if j > 0 {
                    out.push(' ');
                }
                let _ = write!(out, "{}:{}", names[t], obs[t][i]);
            }
            out.push_str(" ; statuses:");
            for (n, st) in names.iter().zip(&statuses) {
                let _ = write!(out, " {n}={st}");
            }
            Some(out)
        }
        Outcome::FalseAlarm | Outcome::Unresolved => None,
    };
    // The nearest specification lines: the same signature, the effective orders' counts. The
    // counts are the normal form's last key, and nothing after them holds a string.
    let at = key.rfind(",\"counts\":[").ok_or_else(|| bad("no counts"))?;
    let nearest = crate::conformance::decide::effective_group(&lens, &counts, group)
        .into_iter()
        .map(|j| {
            let c: Vec<String> = group[j].iter().map(u16::to_string).collect();
            format!("{},\"counts\":[{}]}}", &key[..at], c.join(","))
        })
        .collect();
    Ok(DecideEntry { decision, witness, nearest })
}

/// `SORTED-JOIN`: what the merge over two sorted files held at most.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MergeStats {
    /// Signature groups of the specification file.
    pub spec_groups: usize,
    /// The largest specification group's line count (the index held at most).
    pub max_group_lines: usize,
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
pub(crate) fn normal_value(v: &Value) -> Result<String, String> {
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
pub(crate) fn parse_line(
    text: &str,
    names: &[String],
) -> Result<(String, CompactSummary), String> {
    parse_line_n(text, names).map(|(key, summary, _)| (key, summary))
}

/// [`parse_line`] and the line's `n` (`JOIN-TOTAL`): `Some` for an integer in
/// 1 ..= `i64::MAX`, `None` for no `n` or any other value. `n` is information
/// only: it is outside the normal form, and its value refuses the line only
/// outside the file's common domain ([`common_domain`]).
pub(crate) fn parse_line_n(
    text: &str,
    names: &[String],
) -> Result<(String, CompactSummary, Option<u64>), String> {
    let v: Value = serde_json::from_str(text).map_err(|e| format!("not JSON: {e}"))?;
    let Value::Object(m) = v else {
        return Err("the line is not a JSON object".to_string());
    };
    let n = m.get("n").and_then(Value::as_i64).filter(|&n| n >= 1).map(|n| n as u64);
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
        if obs.len() as u64 > u64::from(u32::MAX) {
            return Err(format!(
                "the visible thread `{n}` has {} visible events; counts support at most {}",
                obs.len(), u32::MAX
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
                counts.push(c as u32);
            }
        }
    }

    let key = render_line(names, &statuses, &words, &counts);
    writer_form(text, &key, m.get("n"))?;

    // The summary uses the longest word's width, as `OrdCounts::of`.
    let longest = words.iter().map(Vec::len).max().unwrap_or(0);
    let ord = if longest > u16::MAX as usize {
        OrdCounts::U32(counts)
    } else if longest > u8::MAX as usize {
        OrdCounts::U16(counts.into_iter().map(|c| c as u16).collect())
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
    Ok((key, summary, n))
}

/// A summary line is accepted only in the form both writers emit: its normal
/// form, optionally followed by an `n` member (JMC's execution count) as the
/// last member, compact. This refuses what a writer never writes: a repeated
/// key, members or `t`/`f` out of order, whitespace, other spellings of a value.
/// The value of `n` is checked only as every value of the file is
/// ([`common_domain`]): `n` is information only, and one that is not a positive
/// integer empties the join's total without refusing the line. `key` is the
/// line's normal form, `n` its `n` member.
fn writer_form(text: &str, key: &str, n: Option<&Value>) -> Result<(), String> {
    let expected = match n {
        None => key.to_owned(),
        Some(v) => {
            // `n` is compared by its own text, compact: a number outside u64
            // (2^64, say) has no exact re-rendering.
            let head = format!("{},\"n\":", &key[..key.len() - 1]);
            if let Some(raw) = text.strip_prefix(&head).and_then(|r| r.strip_suffix('}')) {
                if compact_json(raw) && serde_json::from_str::<Value>(raw).is_ok() {
                    return common_domain(raw);
                }
            }
            format!("{head}{v}}}")
        }
    };
    if text == expected {
        return Ok(());
    }
    let at = text.bytes().zip(expected.bytes()).take_while(|(a, b)| a == b).count();
    Err(format!(
        "the line is not in the form the writers emit (the normal form, then `n` if any; \
         compact, each key once, in order): it differs at byte {at}"
    ))
}

/// The domain every value of a file shares with JMC's reader, checked on the
/// text of `raw`, a valid compact JSON value: each number an integer literal
/// (no fraction or exponent), not `-0`, within signed 64 bits; no object with a
/// repeated key. The parsed value cannot show these: a fraction and an integer
/// above `u64::MAX` both parse as floats, and a repeated key keeps its last
/// value. The messages are JMC's, a repeated key decoded between plain quotes.
fn common_domain(raw: &str) -> Result<(), String> {
    let bytes = raw.as_bytes();
    // One entry per open object (its keys so far) or array (`None`), and
    // whether the next string in the innermost object is a key.
    let mut open: Vec<Option<HashSet<String>>> = Vec::new();
    let mut key_next = false;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                let start = i;
                i += 1;
                while bytes[i] != b'"' {
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
                if key_next {
                    let key: String = serde_json::from_str(&raw[start..=i])
                        .map_err(|e| format!("not JSON: {e}"))?;
                    if let Some(Some(keys)) = open.last_mut() {
                        if !keys.insert(key.clone()) {
                            return Err(format!("duplicate key \"{key}\" in an object"));
                        }
                    }
                    key_next = false;
                }
                i += 1;
            }
            b'{' => {
                open.push(Some(HashSet::new()));
                key_next = true;
                i += 1;
            }
            b'[' => {
                open.push(None);
                i += 1;
            }
            b'}' | b']' => {
                open.pop();
                i += 1;
            }
            b',' => {
                key_next = matches!(open.last(), Some(Some(_)));
                i += 1;
            }
            b'-' | b'0'..=b'9' => {
                let start = i;
                while i < bytes.len() && matches!(bytes[i], b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9') {
                    i += 1;
                }
                let lit = &raw[start..i];
                if lit.bytes().any(|b| matches!(b, b'.' | b'e' | b'E' | b'+')) {
                    return Err(format!(
                        "number {lit} is not an integer literal (the format refuses floating-point values)"
                    ));
                }
                if lit == "-0" {
                    return Err("number -0 is not the canonical encoding of 0".to_string());
                }
                if lit.parse::<i64>().is_err() {
                    return Err(format!("integer {lit} is outside signed 64 bits"));
                }
            }
            _ => i += 1,
        }
    }
    Ok(())
}

/// Whether `raw` has no whitespace outside its JSON strings (escapes respected).
fn compact_json(raw: &str) -> bool {
    let (mut in_string, mut escaped) = (false, false);
    for b in raw.bytes() {
        if in_string {
            match (escaped, b) {
                (true, _) => escaped = false,
                (false, b'\\') => escaped = true,
                (false, b'"') => in_string = false,
                _ => {}
            }
        } else if b == b'"' {
            in_string = true;
        } else if b.is_ascii_whitespace() {
            return false;
        }
    }
    true
}

/// The header keys, in the order the writers emit them; each is optional here,
/// and [`header_of`] checks which must be present.
const HEADER_KEYS: [&str; 15] = [
    "format", "minor", "tool", "program", "size", "visible", "roles", "model", "enumeration",
    "seed", "iterations", "first_miss_iteration", "first_miss_wall_ms", "uncovered_total",
    "encoding",
];

/// A header is accepted only in the form both writers emit: the known keys, in
/// [`HEADER_KEYS`] order, each once, compact; `minor` absent (minor 0) or 1, and
/// `roles` exactly with `minor`; `seed` and `iterations` integers and only in a
/// `sampled` file (JMC writes them there); the three online fields together and
/// integers (JMC may write -1). The other fields' types are [`header_of`]'s.
fn header_writer_form(text: &str, m: &serde_json::Map<String, Value>) -> Result<(), String> {
    if let Some(k) = m.keys().find(|k| !HEADER_KEYS.contains(&k.as_str())) {
        return Err(format!("unknown header key `{k}` (neither writer emits it)"));
    }
    if m.get("minor").is_some_and(|v| v.as_u64() == Some(0)) {
        return Err("the header has `\"minor\":0`; a minor-0 header has no `minor` key".to_string());
    }
    if m.contains_key("roles") != m.contains_key("minor") {
        return Err("the header has `roles` without `minor` or `minor` without `roles`".to_string());
    }
    let integer = |v: &Value| v.is_i64() || v.is_u64();
    for k in ["seed", "iterations"] {
        if let Some(v) = m.get(k) {
            if m.get("enumeration").and_then(Value::as_str) != Some("sampled") {
                return Err(format!("the header has `{k}` in a file that is not `sampled`"));
            }
            if !integer(v) {
                return Err(format!("the header's `{k}` is {v}, not an integer"));
            }
        }
    }
    let online = ["first_miss_iteration", "first_miss_wall_ms", "uncovered_total"];
    let present = online.iter().filter(|k| m.contains_key(**k)).count();
    if present != 0 && present != online.len() {
        return Err("the header has some of the online fields (first_miss_iteration, \
             first_miss_wall_ms, uncovered_total) but not all three"
            .to_string());
    }
    for k in online {
        if let Some(v) = m.get(k).filter(|v| !integer(v)) {
            return Err(format!("the header's `{k}` is {v}, not an integer"));
        }
    }
    let mut expected = String::from("{");
    for k in HEADER_KEYS {
        if let Some(v) = m.get(k) {
            if expected.len() > 1 {
                expected.push(',');
            }
            expected.push_str(&json_string(k));
            expected.push(':');
            expected.push_str(&v.to_string());
        }
    }
    expected.push('}');
    if text == expected {
        return Ok(());
    }
    let at = text.bytes().zip(expected.bytes()).take_while(|(a, b)| a == b).count();
    Err(format!(
        "the header is not in the form the writers emit (compact, each key once, in the order \
         format, minor, tool, program, size, visible, roles, model, enumeration, seed, iterations, \
         the online fields, encoding): it differs at byte {at}"
    ))
}

/// `JOIN-TOTAL`: the sum with one more uncovered line's `n`; `None` from the
/// first line that carries none.
fn add_n(total: Option<u128>, n: Option<u64>) -> Option<u128> {
    Some(total? + u128::from(n?))
}

/// A line's normal form (ruling Q8), for the test that JMC's lines are already
/// in it; `visible` as the file's header gives it.
pub(crate) fn normal_line(text: &str, visible: &[String]) -> Result<String, String> {
    parse_line(text, &sorted_names(visible)).map(|(key, _)| key)
}

pub(crate) fn header_of(text: &str) -> Result<FileHead, String> {
    let v: Value =
        serde_json::from_str(text).map_err(|e| format!("the header is not JSON: {e}"))?;
    let Value::Object(m) = v else {
        return Err("the header is not a JSON object".to_string());
    };
    header_writer_form(text, &m)?;
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
    let roles = match m.get("minor") {
        None => None,
        Some(v) if v.as_u64() == Some(1) => {
            let Some(Value::Array(items)) = m.get("roles") else {
                return Err("the minor-1 header has no `roles` list".to_string());
            };
            let mut roles = Vec::with_capacity(items.len());
            for item in items {
                let Some(name) = item.as_str() else {
                    return Err("a `roles` name is not a string".to_string());
                };
                if name.is_empty() || name == "main" || name.starts_with('~') || !name.is_ascii() {
                    return Err(format!("invalid declared role name: {name:?}"));
                }
                roles.push(name.to_string());
            }
            if roles.windows(2).any(|w| w[0] >= w[1]) {
                return Err("the header's `roles` list is not sorted and unique".to_string());
            }
            if visible.iter().any(|n| !roles.contains(n)) {
                return Err("the header's `roles` list omits a visible name".to_string());
            }
            Some(roles)
        }
        Some(_) => return Err("unsupported header `minor` (expected 1, or no `minor` for minor 0)".to_string()),
    };
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
        roles,
        enumeration,
    })
}

/// Minor 0 remains readable, but cannot establish equality of declarations.
pub(crate) fn compare_roles(
    spec: Option<&[String]>, imp: Option<&[String]>,
) -> Result<(), String> {
    match (spec, imp) {
        (Some(a), Some(b)) if a != b => {
            Err(format!("the two roles lists differ: {a:?} and {b:?}"))
        }
        (Some(_), Some(_)) => Ok(()),
        _ => {
            crate::conformance::report::warn_uncompared_roles();
            Ok(())
        }
    }
}

/// A file read whole: its header and, per line, its number, its normal form
/// and its summary. A duplicate line is refused (R4, ruling Q4).
pub(crate) struct ReadFile {
    pub(crate) head: FileHead,
    pub(crate) lines: Vec<(usize, String, CompactSummary)>,
    /// `JOIN-TOTAL`: each line's `n`, in line order.
    pub(crate) ns: Vec<Option<u64>>,
}

/// One line of a sorted file: its number, its normal form, its summary and
/// its `n`.
type ReadLine = (usize, String, CompactSummary, Option<u64>);

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
    let mut ns = Vec::new();
    for (i, l) in raw.enumerate() {
        let number = i + 2;
        let (key, summary, n) = parse_line_n(l, &names).map_err(|e| at(Some(number), e))?;
        if let Some(earlier) = seen.insert(key.clone(), number) {
            return Err(at(
                Some(number),
                format!("the line repeats line {earlier} (each line is one distinct summary)"),
            ));
        }
        lines.push((number, key, summary));
        ns.push(n);
    }
    Ok(ReadFile { head, lines, ns })
}

/// `conf-join spec.jsonl impl.jsonl` (J3-3): the specification's lines into a
/// `SetIndex`, each implementation line queried with `covers`. Refused (`Err`):
/// a file that does not parse (R1, R2), a duplicate line (R4), unequal
/// `visible` lists, a specification whose `enumeration` is not `complete`.
/// `model` must agree.
pub fn conf_join(spec: &Path, imp: &Path) -> Result<JoinReport, JoinError> {
    conf_join_with(spec, imp, JoinSeams::default())
}

/// `DECIDE`: [`conf_join`], then every uncovered line classified (violation,
/// false alarm, unresolved) under the state budget `budget` per line. The
/// verdict and the exit code are [`conf_join`]'s.
pub fn conf_join_decide(spec: &Path, imp: &Path, budget: u64) -> Result<JoinReport, JoinError> {
    conf_join_inner(spec, imp, JoinSeams::default(), Some(budget))
}

/// [`conf_join`] with `B`'s test seams.
pub(crate) fn conf_join_with(
    spec: &Path,
    imp: &Path,
    seams: JoinSeams,
) -> Result<JoinReport, JoinError> {
    conf_join_inner(spec, imp, seams, None)
}

fn conf_join_inner(
    spec: &Path,
    imp: &Path,
    seams: JoinSeams,
    decide: Option<u64>,
) -> Result<JoinReport, JoinError> {
    use std::time::{Duration, Instant};
    let _ = &seams;
    let join_started = Instant::now();
    let t = Instant::now();
    let s = read_file(spec)?;
    let mut index_wall: Duration = t.elapsed();
    let i = read_file(imp)?;
    if s.head.enumeration != Enumeration::Complete {
        return Err(JoinError(format!(
            "{}: the specification is `{}`, not `complete`",
            spec.display(),
            s.head.enumeration.name()
        )));
    }
    if s.head.model != i.head.model {
        return Err(JoinError(format!(
            "the two models differ: {} and {}",
            s.head.model, i.head.model
        )));
    }
    if s.head.visible != i.head.visible {
        return Err(JoinError(format!(
            "the two files' `visible` lists differ: {:?} and {:?}",
            s.head.visible, i.head.visible
        )));
    }
    compare_roles(s.head.roles.as_deref(), i.head.roles.as_deref()).map_err(JoinError)?;
    let t = Instant::now();
    #[cfg(test)]
    if let Some(d) = seams.index_delay {
        std::thread::sleep(d);
    }
    let mut index = SetIndex::new();
    for (_, _, summary) in &s.lines {
        index.insert(summary);
    }
    index_wall += t.elapsed();
    let t = Instant::now();
    #[cfg(test)]
    if let Some(d) = seams.lookup_delay {
        std::thread::sleep(d);
    }
    let mut uncovered = Vec::new();
    let mut uncovered_total = Some(0);
    for ((_, key, summary), n) in i.lines.iter().zip(&i.ns) {
        let class = match index.covers(summary).1 {
            Covers::Found(_) => continue,
            Covers::NoBucket => MissClass::NoBucket,
            Covers::NoSig => MissClass::NoSlot,
            Covers::NotFound => MissClass::NotFound,
        };
        uncovered.push((class, key.clone()));
        uncovered_total = add_n(uncovered_total, *n);
    }
    let lookup_wall = t.elapsed();
    let mut shape = crate::conformance::measure::Shape::default();
    let names = sorted_names(&i.head.visible);
    for (_, key, summary) in &i.lines {
        let (v, b, m, p) = crate::conformance::measure::Shape::summary_counts(
            &summary.sig,
            &summary.ord,
            &names,
            key.len(),
        );
        shape.add_summary_counts(v, b, m, p);
    }
    let verdict = if !uncovered.is_empty() {
        Verdict::Violation
    } else if i.head.enumeration == Enumeration::Sampled {
        Verdict::NoVerdict
    } else {
        Verdict::Conforms
    };
    let mut report = JoinReport {
        spec_lines: s.lines.len(),
        impl_lines: i.lines.len(),
        spec: s.head,
        imp: i.head,
        verdict,
        uncovered,
        uncovered_total,
        index_ms: index_wall.as_millis(),
        lookup_ms: lookup_wall.as_millis(),
        join_ms: join_started.elapsed().as_millis(),
        shape,
        merge: None,
        decide: None,
        witness: None,
    };
    // `DECIDE`: after the join, outside its timings; the specification's
    // orders of the `not-found` lines' signatures only.
    if let Some(budget) = decide {
        let t = Instant::now();
        let wanted: HashSet<&str> = report
            .uncovered
            .iter()
            .filter(|(c, _)| *c == MissClass::NotFound)
            .map(|(_, k)| sig_key(k))
            .collect();
        let mut groups: HashMap<&str, Vec<Vec<u16>>> = HashMap::new();
        for (number, key, summary) in &s.lines {
            let g = sig_key(key);
            if wanted.contains(g) {
                groups.entry(g).or_default().push(ord_u16(&summary.ord, spec, *number)?);
            }
        }
        let mut d = DecideReport::new(budget);
        for (class, key) in &report.uncovered {
            let group = match class {
                MissClass::NotFound => groups.get(sig_key(key)).map_or(&[][..], Vec::as_slice),
                MissClass::NoBucket | MissClass::NoSlot => &[],
            };
            d.push(decide_entry(key, &names, group, budget)?);
        }
        d.ms = t.elapsed().as_millis();
        report.decide = Some(d);
    }
    Ok(report)
}

// ------------------------------------------------------------ sorted merge --

/// `SORTED-JOIN` (owner's decision, 2026-11-02): one summary file read as a
/// stream of lines in byte order of their normal form (the order both
/// exporters write), each line parsed and checked against the previous one:
/// a repeat is the duplicate refusal, a descent the "not sorted" refusal.
struct SortedReader {
    path: PathBuf,
    names: Vec<String>,
    lines: std::io::Lines<std::io::BufReader<fs::File>>,
    /// The number of the last line handed out (the header is line 1).
    number: usize,
    last_key: Option<String>,
    /// Lines handed out so far (the file's summary count at EOF).
    count: usize,
}

impl SortedReader {
    fn open(path: &Path) -> Result<(FileHead, SortedReader), JoinError> {
        use std::io::BufRead as _;
        let at = |line: Option<usize>, what: String| {
            JoinError(match line {
                Some(n) => format!("{}: line {n}: {what}", path.display()),
                None => format!("{}: {what}", path.display()),
            })
        };
        let f = fs::File::open(path).map_err(|e| at(None, e.to_string()))?;
        let mut lines = std::io::BufReader::new(f).lines();
        let first = match lines.next() {
            Some(Ok(l)) => l,
            Some(Err(e)) => return Err(at(Some(1), e.to_string())),
            None => return Err(at(None, "the file is empty".to_string())),
        };
        let head = header_of(&first).map_err(|e| at(Some(1), e))?;
        let names = sorted_names(&head.visible);
        Ok((
            head,
            SortedReader {
                path: path.to_path_buf(),
                names,
                lines,
                number: 1,
                last_key: None,
                count: 0,
            },
        ))
    }

    fn at(&self, what: String) -> JoinError {
        JoinError(format!("{}: line {}: {what}", self.path.display(), self.number))
    }

    /// The next line: its number, its normal form, its summary and its `n`;
    /// `None` at EOF.
    fn next(&mut self) -> Result<Option<ReadLine>, JoinError> {
        let Some(l) = self.lines.next() else {
            return Ok(None);
        };
        self.number += 1;
        let l = l.map_err(|e| self.at(e.to_string()))?;
        let (key, summary, n) = parse_line_n(&l, &self.names).map_err(|e| self.at(e))?;
        if let Some(prev) = &self.last_key {
            match key.as_str().cmp(prev.as_str()) {
                std::cmp::Ordering::Equal => {
                    return Err(self.at(format!(
                        "the line repeats line {} (each line is one distinct summary)",
                        self.number - 1
                    )));
                }
                std::cmp::Ordering::Less => {
                    return Err(self.at(format!(
                        "the file is not sorted: the line precedes line {} in byte order \
                         (re-export it, or join without --merge)",
                        self.number - 1
                    )));
                }
                std::cmp::Ordering::Greater => {}
            }
        }
        self.last_key = Some(key.clone());
        self.count += 1;
        Ok(Some((self.number, key, summary, n)))
    }
}

/// The signature part of a normal-form line: the text before its `"counts"`
/// member (the statuses and the words), which `render_line` writes last and
/// follows only with numbers, so the last occurrence of `,"counts":` is the
/// member's (an earlier one can only come from a role named `counts`). Signature
/// keys are prefix-free, as a key ends where the `words` object closes, so byte
/// order of the lines and byte order of their keys agree: the merge's advance
/// loop rests on this.
fn sig_key(key: &str) -> &str {
    match key.rfind(",\"counts\":") {
        Some(i) => &key[..i],
        None => key,
    }
}

/// A group of specification lines of one signature, as the index the old join
/// would hold for that signature alone.
struct SpecGroup {
    key: String,
    index: SetIndex,
    lines: usize,
    /// DECIDE: line numbers and full-width orders, converted only for a NotFound miss.
    /// Empty without `--decide`.
    orders: Vec<(usize, OrdCounts)>,
}

/// `SORTED-JOIN`: `conf-join --merge spec.jsonl impl.jsonl`, the same verdict,
/// classes and report as [`conf_join`], with both files read as sorted
/// streams: one specification group (one signature's orders in a [`SetIndex`])
/// is held at a time, and every implementation line is one probe against the
/// group of its signature. Memory: the largest group, the read buffers and
/// lookahead, the distinct shape hashes of the specification (16 bytes each
/// plus the table's overhead), and each miss's class, hash and line (the
/// report's output). A report comes only after both files are read to their
/// end, whatever the verdict so far, so a pair with a malformed or repeated line
/// anywhere is refused, as the in-memory join refuses it; an out-of-order line
/// is this reader's own refusal. The first refusal met returns at once.
pub fn conf_join_merge(spec: &Path, imp: &Path) -> Result<JoinReport, JoinError> {
    conf_join_merge_inner(spec, imp, None)
}

/// `DECIDE`: [`conf_join_merge`] with every uncovered line classified as by
/// [`conf_join_decide`], each against the group in hand when it misses (the
/// decision's time is excluded from the lookup and join timings).
pub fn conf_join_merge_decide(
    spec: &Path,
    imp: &Path,
    budget: u64,
) -> Result<JoinReport, JoinError> {
    conf_join_merge_inner(spec, imp, Some(budget))
}

fn conf_join_merge_inner(
    spec: &Path,
    imp: &Path,
    decide: Option<u64>,
) -> Result<JoinReport, JoinError> {
    use std::time::{Duration, Instant};
    let keep = decide.is_some();
    let mut decided = decide.map(DecideReport::new);
    let mut decide_wall = Duration::ZERO;
    let join_started = Instant::now();
    let (shead, mut sr) = SortedReader::open(spec)?;
    let (ihead, mut ir) = SortedReader::open(imp)?;
    if shead.enumeration != Enumeration::Complete {
        return Err(JoinError(format!(
            "{}: the specification is `{}`, not `complete`",
            spec.display(),
            shead.enumeration.name()
        )));
    }
    if shead.model != ihead.model {
        return Err(JoinError(format!(
            "the two models differ: {} and {}",
            shead.model, ihead.model
        )));
    }
    if shead.visible != ihead.visible {
        return Err(JoinError(format!(
            "the two files' `visible` lists differ: {:?} and {:?}",
            shead.visible, ihead.visible
        )));
    }
    compare_roles(shead.roles.as_deref(), ihead.roles.as_deref()).map_err(JoinError)?;
    let names = sorted_names(&ihead.visible);
    let mut index_wall = Duration::ZERO;
    let mut lookup_wall = Duration::ZERO;
    let mut shapes: HashSet<crate::conformance::compact::SigHash> = HashSet::new();
    let mut spec_groups = 0usize;
    let mut max_group = 0usize;
    // The specification's lookahead line and current group.
    let t = Instant::now();
    let mut ahead = sr.next()?;
    index_wall += t.elapsed();
    let mut group: Option<SpecGroup> = None;
    // Loads the next group from the lookahead; `None` at EOF. `DECIDE`: the
    // time spent keeping the group's count vectors is added to `prep` (it is
    // charged to `decide_ms`, not to the index phase).
    let load = |ahead: &mut Option<ReadLine>,
                    sr: &mut SortedReader,
                    shapes: &mut HashSet<crate::conformance::compact::SigHash>,
                    prep: &mut Duration|
     -> Result<Option<SpecGroup>, JoinError> {
        let Some((number, key, summary, _)) = ahead.take() else {
            return Ok(None);
        };
        let gk = sig_key(&key).to_owned();
        let mut index = SetIndex::new();
        let mut orders = Vec::new();
        shapes.insert(summary.hash);
        index.insert(&summary);
        if keep {
            let t = Instant::now();
            orders.push((number, summary.ord.clone()));
            *prep += t.elapsed();
        }
        let mut lines = 1usize;
        loop {
            match sr.next()? {
                None => break,
                Some((n, k, s, sn)) => {
                    if sig_key(&k) == gk {
                        shapes.insert(s.hash);
                        index.insert(&s);
                        if keep {
                            let t = Instant::now();
                            orders.push((n, s.ord.clone()));
                            *prep += t.elapsed();
                        }
                        lines += 1;
                    } else {
                        *ahead = Some((n, k, s, sn));
                        break;
                    }
                }
            }
        }
        Ok(Some(SpecGroup { key: gk, index, lines, orders }))
    };
    // The misses in file order, their class decided at the end where it
    // depends on the whole specification (no-bucket vs no-slot).
    let mut misses: Vec<(Option<MissClass>, crate::conformance::compact::SigHash, String)> =
        Vec::new();
    let mut uncovered_total = Some(0);
    let mut shape = crate::conformance::measure::Shape::default();
    let mut impl_lines = 0usize;
    loop {
        let t = Instant::now();
        let line = ir.next()?;
        let Some((_, key, summary, n)) = line else {
            lookup_wall += t.elapsed();
            break;
        };
        impl_lines += 1;
        let (v, b, m, p) = crate::conformance::measure::Shape::summary_counts(
            &summary.sig,
            &summary.ord,
            &names,
            key.len(),
        );
        shape.add_summary_counts(v, b, m, p);
        let ik = sig_key(&key);
        // Advance the specification to the first group whose key is >= ik (its
        // loading time counts for the index phase, not the lookup phase).
        let mut loaded = Duration::ZERO;
        let mut found: Option<Covers> = None;
        loop {
            match &group {
                Some(g) if g.key.as_str() < ik => {
                    group = None;
                }
                Some(g) if g.key.as_str() == ik => {
                    found = Some(g.index.covers(&summary).1);
                    break;
                }
                Some(_) => break,
                None => {
                    let t2 = Instant::now();
                    let mut prep = Duration::ZERO;
                    let next = load(&mut ahead, &mut sr, &mut shapes, &mut prep)?;
                    let d = t2.elapsed();
                    index_wall += d.saturating_sub(prep);
                    loaded += d;
                    decide_wall += prep;
                    match next {
                        Some(g) => {
                            spec_groups += 1;
                            max_group = max_group.max(g.lines);
                            group = Some(g);
                        }
                        None => break,
                    }
                }
            }
        }
        // `DECIDE`: a miss is decided here, against the group in hand (none
        // for a missing group: `k = 0`).
        let mut decided_ms = Duration::ZERO;
        if let (Some(d), Some(budget)) = (decided.as_mut(), decide) {
            if !matches!(found, Some(Covers::Found(_))) {
                let t2 = Instant::now();
                let group = match (&found, &group) {
                    (Some(Covers::NotFound), Some(g)) => g.orders.iter()
                        .map(|(n, o)| ord_u16(o, spec, *n))
                        .collect::<Result<Vec<_>, _>>()?,
                    _ => Vec::new(),
                };
                d.push(decide_entry(&key, &names, &group, budget)?);
                decided_ms = t2.elapsed();
                decide_wall += decided_ms;
            }
        }
        match found {
            Some(Covers::Found(_)) => {}
            Some(Covers::NotFound) => {
                misses.push((Some(MissClass::NotFound), summary.hash, key));
                uncovered_total = add_n(uncovered_total, n);
            }
            // The group is built from this signature, so its own index holds it.
            Some(Covers::NoBucket) | Some(Covers::NoSig) => {
                unreachable!("conformance: a group's index holds its own signature")
            }
            // A missing group: the class is decided at the end.
            None => {
                misses.push((None, summary.hash, key));
                uncovered_total = add_n(uncovered_total, n);
            }
        }
        lookup_wall += t.elapsed().saturating_sub(loaded + decided_ms);
    }
    // Drain the specification: the remaining groups are read (their order and
    // uniqueness checked, their shapes recorded) and dropped.
    let t = Instant::now();
    drop(group.take());
    let mut prep = Duration::ZERO;
    while let Some(g) = load(&mut ahead, &mut sr, &mut shapes, &mut prep)? {
        spec_groups += 1;
        max_group = max_group.max(g.lines);
    }
    index_wall += t.elapsed().saturating_sub(prep);
    decide_wall += prep;
    let uncovered: Vec<(MissClass, String)> = misses
        .into_iter()
        .map(|(c, h, key)| {
            (
                c.unwrap_or(if shapes.contains(&h) {
                    MissClass::NoSlot
                } else {
                    MissClass::NoBucket
                }),
                key,
            )
        })
        .collect();
    let verdict = if !uncovered.is_empty() {
        Verdict::Violation
    } else if ihead.enumeration == Enumeration::Sampled {
        Verdict::NoVerdict
    } else {
        Verdict::Conforms
    };
    Ok(JoinReport {
        spec_lines: sr.count,
        impl_lines,
        spec: shead,
        imp: ihead,
        verdict,
        uncovered,
        uncovered_total,
        index_ms: index_wall.as_millis(),
        lookup_ms: lookup_wall.as_millis(),
        join_ms: join_started.elapsed().saturating_sub(decide_wall).as_millis(),
        shape,
        merge: Some(MergeStats { spec_groups, max_group_lines: max_group }),
        decide: decided.map(|mut d| {
            d.ms = decide_wall.as_millis();
            d
        }),
        witness: None,
    })
}
