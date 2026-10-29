//! `J3` (batch cross-tool checking): TraceForge's side of the compact summary
//! interchange format, version 1 (`plan/jmc-must/SUMMARY-FORMAT.md`).
//!
//! - **The encoder** (J3-1): [`SummaryEncode`], an opt-in trait a message type
//!   implements to give its values the format's canonical form — integers and
//!   tagged values only ([`EncVal`]; ruling Q9). An [`Encoders`] registry, keyed
//!   by the concrete type, is what the exporter consults; no engine reads it.
//! - **The exporter** (J3-2): [`export`] runs the program as the stateful
//!   engine's specification under `IndexKind::Set` — and as its implementation,
//!   so the run checks the program against itself (ruling Q5) — and writes one
//!   line per entry of the specification's `SetIndex` after the run; `n` is
//!   omitted. No engine changes.
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

use std::any::{Any, TypeId};
use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Write as _};
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use serde_json::Value;

use crate::conformance::compact::{CompactSummary, Covers, OrdCounts, SetIndex};
use crate::conformance::config::{ConfConfig, IndexKind};
use crate::conformance::morphism::Status;
use crate::conformance::obs::Obs;
use crate::conformance::sig::Sig;
use crate::conformance::stateful;
use crate::msg::Val;
use crate::ConsType;

// ---------------------------------------------------------------- encoder --

/// A value in the format's canonical form (J3-1): an integer within signed 64
/// bits, or a tagged value `{"t":<tag>,"f":[…]}` — a record, a tuple struct or
/// an enum variant, its fields in declaration order; a unit variant has none.
/// J3 implements no other kind (ruling Q9).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum EncVal {
    Int(i64),
    Tagged(String, Vec<EncVal>),
}

/// Why a value has no canonical form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum EncodeError {
    /// An integer outside signed 64 bits (E4), as `Display` writes it.
    OutOfRange(String),
}

impl EncVal {
    /// An integer, refused outside signed 64 bits (E4).
    pub(crate) fn int<T>(v: T) -> Result<Self, EncodeError>
    where
        T: TryInto<i64> + Copy + fmt::Display,
    {
        v.try_into()
            .map(EncVal::Int)
            .map_err(|_| EncodeError::OutOfRange(v.to_string()))
    }

    /// A tagged value, its fields in declaration order (`[]` for a unit variant).
    pub(crate) fn tagged(tag: &str, fields: Vec<EncVal>) -> Self {
        EncVal::Tagged(tag.to_string(), fields)
    }

    /// The canonical bytes: `t` before `f`, no whitespace, integers in decimal.
    pub(crate) fn render(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out
    }

    fn write(&self, out: &mut String) {
        match self {
            EncVal::Int(i) => out.push_str(&i.to_string()),
            EncVal::Tagged(tag, fields) => {
                out.push_str("{\"t\":");
                out.push_str(&json_string(tag));
                out.push_str(",\"f\":[");
                for (i, v) in fields.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    v.write(out);
                }
                out.push_str("]}");
            }
        }
    }
}

/// The encoder (J3-1, ruling 1): opt-in, implemented by a message type that
/// takes part in an export; not a bound on `Message`. Equal values (the type's
/// `PartialEq`, which `msg_equals` uses) must encode to equal bytes and unequal
/// values to unequal bytes (E2, E3), so a slot's representative signature
/// encodes as any member of the slot would.
pub(crate) trait SummaryEncode: 'static {
    fn encode(&self) -> Result<EncVal, EncodeError>;
}

type EncodeFn = fn(&dyn Any) -> Result<EncVal, EncodeError>;

fn encode_as<T: SummaryEncode>(v: &dyn Any) -> Result<EncVal, EncodeError> {
    v.downcast_ref::<T>()
        .expect("conformance: the registry maps a type to its own encoder")
        .encode()
}

/// The encoders an export may use, by concrete type (J3-1). A visible value
/// of a type not registered here refuses the export (E5).
#[derive(Clone, Default)]
pub(crate) struct Encoders {
    by_type: HashMap<TypeId, EncodeFn>,
}

impl Encoders {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Registers `T`'s encoder.
    pub(crate) fn register<T: SummaryEncode>(mut self) -> Self {
        self.by_type.insert(TypeId::of::<T>(), encode_as::<T>);
        self
    }

    /// The value's canonical bytes; an unregistered type is refused by name.
    fn encode(&self, v: &Val) -> Result<String, ExportError> {
        let any = v.as_any_ref();
        let f = self
            .by_type
            .get(&any.type_id())
            .ok_or_else(|| ExportError::Unregistered {
                type_name: v.type_name.clone(),
            })?;
        f(any).map(|e| e.render()).map_err(ExportError::Encode)
    }
}

/// A JSON string literal, `serde_json`'s escaping.
fn json_string(s: &str) -> String {
    serde_json::to_string(s).expect("conformance: a string always serialises")
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
fn sorted_names(visible: &[String]) -> Vec<String> {
    let mut names = visible.to_vec();
    names.sort_unstable();
    names.dedup();
    names
}

// --------------------------------------------------------------- exporter --

/// The header fields the caller names (X3, ruling Q6): `program`, TraceForge's
/// name for the program, and `size`, the JMC row's size string.
#[derive(Clone, Debug)]
pub(crate) struct ExportHeader {
    pub(crate) program: String,
    pub(crate) size: String,
}

/// What an export wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExportStats {
    /// The summary lines written (the header not counted).
    pub(crate) lines: usize,
    /// The run's `orders_held`, which `lines` equals (X1).
    pub(crate) orders_held: usize,
    /// The specification's complete graphs.
    pub(crate) spec_graphs: usize,
}

/// Why an export was refused; no file is written (X4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExportError {
    /// The configuration's index is not `Set` (ruling 2).
    NotSet,
    /// The configuration's `ConsType` has no `model` (X3, ruling Q7).
    Model(String),
    /// A visible value of a type with no registered encoder (E5).
    Unregistered { type_name: String },
    /// A value with no canonical form (E4).
    Encode(EncodeError),
    /// The program raised assertions (the format's specification side raises none).
    SpecErrors(usize),
    /// The run of the program against itself reported (ruling Q5: 0 required).
    NotReflexive { reports: usize },
    /// Writing the file failed.
    Io(String),
}

/// The `model` of a configuration's `ConsType` (X3, ruling Q7): one entry.
pub(crate) fn model_of(c: ConsType) -> Result<&'static str, ExportError> {
    match c {
        ConsType::FIFO => Ok("p2p"),
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

/// The line of one entry of the specification's index (X2).
fn line_of(
    sig: &Sig,
    ord: &OrdCounts,
    names: &[String],
    enc: &Encoders,
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
                Obs::Send(v) => ObsText::Send(enc.encode(v)?),
                Obs::Recv(Some(v)) => ObsText::Recv(Some(enc.encode(v)?)),
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
fn write_replacing(path: &Path, text: &str) -> Result<(), ExportError> {
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

/// The export (J3-2): `program` run by `stateful::run_with` as the
/// specification and as the implementation under `cc` (whose index must be
/// `Set`), then the file written from the specification's `SetIndex` entries
/// after the run — the header, then one line per entry, in `entries()` order.
/// Every refusal comes before the file is written.
pub(crate) fn export(
    cc: &ConfConfig,
    program: &Arc<dyn Fn() + Send + Sync>,
    header: &ExportHeader,
    enc: &Encoders,
    path: &Path,
) -> Result<ExportStats, ExportError> {
    if cc.index != IndexKind::Set {
        return Err(ExportError::NotSet);
    }
    let model = model_of(cc.config.cons_type)?;
    let names = sorted_names(&cc.visible);
    let out = stateful::run_with(cc, program, program, false);
    if !out.spec_errors.is_empty() {
        return Err(ExportError::SpecErrors(out.spec_errors.len()));
    }
    if out.counters.reports != 0 {
        return Err(ExportError::NotReflexive {
            reports: out.counters.reports,
        });
    }
    let index = out
        .set_index
        .as_ref()
        .expect("conformance: `run_with` under `Set` returns its set index");
    let mut text = header_line(header, &names, model);
    text.push('\n');
    let mut lines = 0;
    for (_, sig, _, ord) in index.entries() {
        text.push_str(&line_of(sig, ord, &names, enc)?);
        text.push('\n');
        lines += 1;
    }
    assert_eq!(
        lines, out.counters.orders_held,
        "conformance: an export's lines are its index's entries (X1)"
    );
    write_replacing(path, &text)?;
    Ok(ExportStats {
        lines,
        orders_held: out.counters.orders_held,
        spec_graphs: out.counters.spec_graphs,
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

/// A value's normal form (R2, rulings Q8 and Q9): `Err` names a kind J3 does
/// not support, or a value version 1 forbids — two distinct messages.
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
        Value::String(_) => Err(unsupported("a string")),
        Value::Bool(_) => Err(unsupported("a boolean")),
        Value::Array(_) => Err(unsupported("a list")),
    }
}

fn invalid(what: &str) -> String {
    format!("{what} is invalid in format version 1")
}

fn unsupported(what: &str) -> String {
    format!("{what} is not supported by J3")
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
fn parse_line(text: &str, names: &[String]) -> Result<(String, CompactSummary), String> {
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
struct ReadFile {
    head: FileHead,
    lines: Vec<(usize, String, CompactSummary)>,
}

fn read_file(path: &Path) -> Result<ReadFile, JoinError> {
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
