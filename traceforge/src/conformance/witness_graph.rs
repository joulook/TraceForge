//! Witness graphs (format 1) and the graph store written at export.
//!
//! A graph is one execution as JSON: every thread in creation order, and per thread the same
//! events, at the same positions, as the text witness ([`super::execution_witness`]), with the
//! destination and value of each send, the send each receive read, and the raw index of each
//! choice. The store (`export --graphs PATH`) holds, after an identity line, one graph per
//! distinct summary line of the export, taken from the first execution that produced the line.
//! A graph is keyed by its summary line's bytes; no hash is written.
//!
//! Identity: `tool_commit` is fixed when this crate is built (`build.rs`); `source` is copied from
//! the manifest `<binary>.SOURCE.md5` that the build script writes beside the binary, and is
//! `"unknown"` without one. Nothing is hashed here.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;

use super::execution_witness::{event_lines, EventLine};
use super::interchange::{encode_generic, json_string, record_thread_names, ThreadName, ThreadNames};

/// The commit of this TraceForge build (`build.rs`).
pub(crate) const TOOL_COMMIT: &str = env!("TRACEFORGE_TOOL_COMMIT");

/// What the store records about the run that produced its executions (`run`, without
/// `iteration`, which each graph adds).
#[derive(Clone, Debug)]
pub(crate) struct RunIdentity {
    pub(crate) side: String,
    pub(crate) args: Vec<String>,
    /// The runner model: `fifo`, `bag` or `causal`.
    pub(crate) model: String,
    pub(crate) seed: Option<u64>,
    pub(crate) threshold: Option<u32>,
    /// The file name of `argv[0]`.
    pub(crate) entry: String,
    /// `source` as JSON text: the manifest object, or `"unknown"`.
    pub(crate) source: String,
    /// Why an existing manifest was not used, for the caller to print.
    pub(crate) warning: Option<String>,
}

impl RunIdentity {
    /// The identity of this process's run. Reads the manifest beside the running binary; a
    /// malformed one gives `"unknown"` and a `warning` line for the caller to print.
    pub(crate) fn of_process(
        side: &str, args: &[String], model: &str, seed: Option<u64>, threshold: Option<u32>,
    ) -> Self {
        let entry = std::env::args_os()
            .next()
            .and_then(|a| Path::new(&a).file_name().map(|f| f.to_string_lossy().into_owned()))
            .unwrap_or_default();
        let mut warning = None;
        let source = match std::env::current_exe() {
            Ok(exe) => {
                let mut m = exe.into_os_string();
                m.push(".SOURCE.md5");
                let m = PathBuf::from(m);
                match source_of_manifest(&m) {
                    Ok(Some(s)) => s,
                    Ok(None) => "\"unknown\"".to_owned(),
                    Err(e) => {
                        warning = Some(format!("graphs: manifest {}: {e}", m.display()));
                        "\"unknown\"".to_owned()
                    }
                }
            }
            Err(_) => "\"unknown\"".to_owned(),
        };
        RunIdentity {
            side: side.to_owned(),
            args: args.to_vec(),
            model: model.to_owned(),
            seed,
            threshold,
            entry,
            source,
            warning,
        }
    }

    /// `run` as JSON text, keys in the contract's order.
    pub(crate) fn json(&self, iteration: Option<usize>) -> String {
        let args: Vec<String> = self.args.iter().map(|a| json_string(a)).collect();
        let mut options = Vec::new();
        if let Some(s) = self.seed {
            options.push(format!("\"seed\":{s}"));
        }
        if let Some(t) = self.threshold {
            options.push(format!("\"threshold\":{t}"));
        }
        let iteration = iteration.map_or_else(|| "null".to_owned(), |i| i.to_string());
        format!(
            "{{\"tool\":\"traceforge\",\"tool_commit\":{},\"entry\":{},\"side\":{},\"args\":[{}],\
             \"model\":{},\"options\":{{{}}},\"source\":{},\"iteration\":{},\
             \"producer\":\"export\",\"order\":\"first\"}}",
            json_string(TOOL_COMMIT),
            json_string(&self.entry),
            json_string(&self.side),
            args.join(","),
            json_string(&self.model),
            options.join(","),
            self.source,
            iteration
        )
    }
}

/// The runner model's name in `run.model`.
pub(crate) fn model_label(c: crate::ConsType) -> String {
    match c {
        crate::ConsType::FIFO => "fifo".to_owned(),
        crate::ConsType::Bag => "bag".to_owned(),
        #[allow(deprecated)]
        crate::ConsType::Causal | crate::ConsType::CD => "causal".to_owned(),
        other => format!("{other:?}").to_lowercase(),
    }
}

/// `source` from a manifest: `# root <dir>`, then `<md5>  <path>` lines. `Ok(None)` when the
/// file does not exist; `Err` when it exists and is not a manifest.
pub(crate) fn source_of_manifest(path: &Path) -> Result<Option<String>, String> {
    let text = match fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e.to_string()),
    };
    // `lines` drops one final newline; every other line must be a manifest line.
    let mut lines = text.lines();
    let root = lines
        .next()
        .and_then(|l| l.strip_prefix("# root "))
        .filter(|r| !r.is_empty())
        .ok_or("the first line is not `# root <dir>`")?;
    let mut files: Vec<(String, String)> = Vec::new();
    let mut seen = HashSet::new();
    for (k, l) in lines.enumerate() {
        let bad = || format!("line {} is not `<md5>  <path>`", k + 2);
        let (md5, file) = l.split_once("  ").ok_or_else(bad)?;
        if md5.len() != 32 || !md5.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || file.is_empty()
        {
            return Err(bad());
        }
        if !seen.insert(file.to_owned()) {
            return Err(format!("the path {file:?} is listed twice"));
        }
        files.push((file.to_owned(), md5.to_owned()));
    }
    if files.is_empty() {
        return Err("no file is listed".to_owned());
    }
    files.sort_unstable_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    let files: Vec<String> =
        files.iter().map(|(f, m)| format!("{}:{}", json_string(f), json_string(m))).collect();
    Ok(Some(format!("{{\"root\":{},\"files\":{{{}}}}}", json_string(root), files.join(","))))
}

/// Why a graph is not written.
fn refused<T>(why: impl Into<String>) -> Result<T, String> {
    Err(why.into())
}

/// `threads` of the execution `g` as JSON text, or why it cannot be written. `visible` are the
/// export's visible names.
pub(crate) fn threads_json(g: &ExecutionGraph, visible: &[String]) -> Result<String, String> {
    let tids: Vec<crate::ThreadId> = g.thread_ids().into_iter().collect();
    let index: HashMap<crate::ThreadId, usize> =
        tids.iter().enumerate().map(|(t, &tid)| (tid, t)).collect();
    // Labels with no JSON form, anywhere in the graph (also those the walk omits).
    for &tid in &tids {
        for k in 0..g.thread_size(tid) {
            match g.label(Event::new(tid, k as u32)) {
                LabelEnum::Sample(_) => return refused("unsupported event Sample"),
                LabelEnum::Inbox(_) => return refused("unsupported event Inbox"),
                #[cfg(feature = "symbolic")]
                LabelEnum::SymbolicVar(_) | LabelEnum::ConstraintEval(_) => {
                    return refused("unsupported event symbolic")
                }
                _ => {}
            }
        }
    }
    // Thread names for encoding values, as the text witness has them.
    let mut names = ThreadNames::new();
    record_thread_names(g, &mut names);
    let mut visible_tids = HashSet::new();
    for &tid in &tids {
        if let Some(n) = g.thread_name(tid) {
            if n.chars().any(|c| c.is_control() || matches!(c, '\u{2028}' | '\u{2029}')) {
                return refused("a thread name contains a control character or line separator");
            }
            names.insert(tid.to_number(), ThreadName::Named(n.to_owned()));
            if visible.iter().any(|v| v == n) {
                visible_tids.insert(tid);
            }
        }
    }
    // Positions: (t, k) of every written event; the sends a visible thread reads.
    let mut positions: HashMap<Event, usize> = HashMap::new();
    let mut read_by_visible: HashSet<Event> = HashSet::new();
    for &tid in &tids {
        for (k, line) in event_lines(g, tid).enumerate() {
            if let EventLine::Label(e, label) = line {
                positions.insert(e, k);
                if let LabelEnum::RecvMsg(r) = label {
                    if let (true, Some(send)) = (visible_tids.contains(&tid), r.rf()) {
                        read_by_visible.insert(send);
                    }
                }
            }
        }
    }
    let mut out = String::from("[");
    for (t, &tid) in tids.iter().enumerate() {
        if t > 0 {
            out.push(',');
        }
        let name = g.thread_name(tid).map_or_else(|| "null".to_owned(), json_string);
        out.push_str(&format!(
            "{{\"name\":{name},\"daemon\":{},\"events\":[",
            g.is_thread_daemon(tid)
        ));
        for (k, line) in event_lines(g, tid).enumerate() {
            if k > 0 {
                out.push(',');
            }
            let (me, label) = match line {
                EventLine::End => {
                    out.push_str("{\"e\":\"END\"}");
                    continue;
                }
                EventLine::Label(e, label) => (e, label),
            };
            let ev = match label {
                LabelEnum::Begin(_) => "{\"e\":\"BEGIN\"}".to_owned(),
                LabelEnum::End(_) => "{\"e\":\"END\"}".to_owned(),
                LabelEnum::Block(_) => "{\"e\":\"BLK\"}".to_owned(),
                LabelEnum::TCreate(c) => {
                    let child = index.get(&c.cid()).ok_or("a created thread is unknown")?;
                    format!("{{\"e\":\"TCREATE\",\"child\":{child}}}")
                }
                LabelEnum::TJoin(j) => {
                    let child = index.get(&j.cid()).ok_or("a joined thread is unknown")?;
                    format!("{{\"e\":\"TJOIN\",\"child\":{child}}}")
                }
                LabelEnum::SendMsg(s) => {
                    let dest = s
                        .loc()
                        .as_thread_id()
                        .ok_or("unsupported event send to a non-thread destination")?;
                    let to = index.get(&dest).ok_or("a send destination is unknown")?;
                    let v = match encode_generic(s.val(), &names) {
                        Ok(v) => v,
                        Err(e) if visible_tids.contains(&tid) || read_by_visible.contains(&me) => {
                            return refused(format!("a visible value is not encodable: {e:?}"));
                        }
                        // The value's own `Debug`, not its wrapper's.
                        Err(_) => format!("{{\"opaque\":{}}}", json_string(&format!("{:?}", s.val().val))),
                    };
                    format!("{{\"e\":\"SEND\",\"to\":{to},\"v\":{v}}}")
                }
                LabelEnum::RecvMsg(r) => {
                    let mode = if r.is_non_blocking() { "try" } else { "block" };
                    let rf = match r.rf() {
                        None => "null".to_owned(),
                        Some(send) => {
                            if !matches!(g.label(send), LabelEnum::SendMsg(_)) {
                                return refused("a receive does not read a send");
                            }
                            let k = positions.get(&send).ok_or("a receive reads an omitted send")?;
                            let t = index.get(&send.thread).ok_or("a sender is unknown")?;
                            format!("[{t},{k}]")
                        }
                    };
                    format!("{{\"e\":\"RECV\",\"mode\":\"{mode}\",\"rf\":{rf}}}")
                }
                LabelEnum::CToss(c) => format!("{{\"e\":\"NONDET\",\"n\":2,\"i\":{}}}", usize::from(c.result())),
                LabelEnum::Choice(c) => {
                    let (lo, hi) = (*c.range().start(), *c.range().end());
                    // `n` in a wider type: `0..=usize::MAX` has `usize::MAX + 1` options.
                    format!(
                        "{{\"e\":\"NONDET\",\"n\":{},\"i\":{},\"lo\":{lo}}}",
                        u128::from(hi as u64 - lo as u64) + 1,
                        c.result() - lo
                    )
                }
                _ => return refused("an event the walk emits has no JSON form"),
            };
            out.push_str(&ev);
        }
        out.push_str("]}");
    }
    out.push(']');
    Ok(out)
}

/// `--graphs PATH [--graphs-limit N]`.
#[derive(Clone, Debug)]
pub(crate) struct GraphStoreOpts {
    pub(crate) path: PathBuf,
    pub(crate) limit: Option<usize>,
    pub(crate) run: RunIdentity,
}

/// A graph waiting for the end of the export: its line, its first execution's completion number,
/// and its `threads`, or why it is refused.
struct Pending {
    line: String,
    iteration: usize,
    threads: Result<String, String>,
}

/// The store being built during an export, written once the export has succeeded.
pub(crate) struct StoreBuilder {
    opts: GraphStoreOpts,
    visible: Vec<String>,
    pending: Vec<Pending>,
    accepted: usize,
    /// Walk and encoding time.
    pub(crate) time: Duration,
}

/// What a written store holds, for the measurement block.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct StoreReport {
    pub(crate) written: usize,
    pub(crate) refused: usize,
    pub(crate) ms: u128,
    /// One `graphs: refused <n>: <reason>` line per refused graph, for the caller to print.
    pub(crate) messages: Vec<String>,
}

impl StoreReport {
    /// The three tool-specific measurement keys.
    pub(crate) fn append(&self, block: &mut String) {
        block.push_str(&format!(
            "graphs_written: {}\ngraphs_refused: {}\ngraphs_ms: {}\n",
            self.written, self.refused, self.ms
        ));
    }
}

impl StoreBuilder {
    pub(crate) fn new(opts: GraphStoreOpts, visible: &[String]) -> Self {
        StoreBuilder { opts, visible: visible.to_vec(), pending: Vec::new(), accepted: 0, time: Duration::ZERO }
    }

    /// Whether a new distinct line still gets a graph.
    pub(crate) fn wants(&self) -> bool {
        self.opts.limit.is_none_or(|n| self.accepted < n)
    }

    /// Time spent rendering a line for the store (added to [`StoreBuilder::time`]).
    pub(crate) fn time_line(&mut self, d: Duration) {
        self.time += d;
    }

    /// The first execution `g` with the summary line `line` (its completion number `iteration`).
    pub(crate) fn add(&mut self, g: &ExecutionGraph, line: String, iteration: usize) {
        let threads = threads_json(g, &self.visible);
        if threads.is_ok() {
            self.accepted += 1;
        }
        self.pending.push(Pending { line, iteration, threads });
    }

    /// Writes the store beside an export whose header is `header` and whose lines, sorted, are
    /// `lines` (the export file's lines 2, 3, ...). Refusals are listed in the report.
    pub(crate) fn finish(self, header: &str, lines: &[String]) -> Result<StoreReport, String> {
        let t = Instant::now();
        let mut text = format!(
            "{{\"witness_store\":1,\"export\":{header},\"run\":{}}}\n",
            self.opts.run.json(None)
        );
        let mut report = StoreReport::default();
        for p in &self.pending {
            let number = lines.binary_search(&p.line).ok().map(|i| i + 2);
            let threads = match (&p.threads, number) {
                (_, None) => Err("the line is not in the export".to_owned()),
                (Ok(th), Some(_)) => Ok(th),
                (Err(e), Some(_)) => Err(e.clone()),
            };
            match threads {
                Ok(th) => {
                    text.push_str(&format!(
                        "{{\"witness\":1,\"line\":{},\"export\":{header},\"run\":{},\
                         \"join\":null,\"nearest\":null,\"threads\":{th}}}\n",
                        json_string(&p.line),
                        self.opts.run.json(Some(p.iteration))
                    ));
                    report.written += 1;
                }
                Err(e) => {
                    let n = number.map_or_else(|| "-".to_owned(), |n| n.to_string());
                    report.messages.push(format!("graphs: refused {n}: {e}"));
                    report.refused += 1;
                }
            }
        }
        write_replacing(&self.opts.path, &text)?;
        report.ms = (self.time + t.elapsed()).as_millis();
        Ok(report)
    }
}

/// The store with its identity line only (`--graphs-limit 0`, also on the partitioned export).
pub(crate) fn write_identity_only(opts: &GraphStoreOpts, header: &str) -> Result<StoreReport, String> {
    let t = Instant::now();
    let text =
        format!("{{\"witness_store\":1,\"export\":{header},\"run\":{}}}\n", opts.run.json(None));
    write_replacing(&opts.path, &text)?;
    Ok(StoreReport { ms: t.elapsed().as_millis(), ..StoreReport::default() })
}

/// The whole file or its earlier content: `<path>.tmp`, then a rename.
fn write_replacing(path: &Path, text: &str) -> Result<(), String> {
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
        format!("graphs: {}: {e}", path.display())
    })
}
