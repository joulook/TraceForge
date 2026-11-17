//! Execution witnesses, rendered only for requested uncovered completions.

use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;

use super::interchange::{encode_generic, record_thread_names, ThreadName, ThreadNames};

pub(crate) struct Writer {
    path: PathBuf,
    directory: bool,
    seen: HashSet<String>,
    staged: Vec<(PathBuf, PathBuf)>,
    created_directory: bool,
}

impl Writer {
    pub(crate) fn new(path: String) -> Self {
        Self {
            directory: path.ends_with('/'),
            path: path.into(),
            seen: HashSet::new(),
            staged: Vec::new(),
            created_directory: false,
        }
    }

    pub(crate) fn finished(&self) -> bool {
        !self.directory && !self.seen.is_empty()
    }

    pub(crate) fn write(
        &mut self, g: &ExecutionGraph, iteration: usize, line: &str,
    ) -> Result<(), String> {
        if self.finished() || self.seen.contains(line) {
            return Ok(());
        }
        let text = render(g, iteration, line)?;
        let path = if self.directory {
            let absent = !self.path.exists();
            std::fs::create_dir_all(&self.path)
                .map_err(|e| format!("witness: {}: {e}", self.path.display()))?;
            self.created_directory |= absent;
            self.path.join(format!("witness-{}.txt", self.seen.len() + 1))
        } else {
            self.path.clone()
        };
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let parent = path.parent().unwrap_or_else(|| std::path::Path::new("."));
        let (staging, mut file) = loop {
            let candidate = parent.join(format!(
                ".traceforge-witness-{}-{}.tmp", std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            if candidate == path { continue; }
            match std::fs::OpenOptions::new().write(true).create_new(true).open(&candidate) {
                Ok(file) => break (candidate, file),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(format!("witness: {}: {e}", path.display())),
            }
        };
        self.staged.push((staging, path.clone()));
        file.write_all(text.as_bytes())
            .map_err(|e| format!("witness: {}: {e}", path.display()))?;
        self.seen.insert(line.to_owned());
        Ok(())
    }

    /// Publish in selection order only after the caller accepts the run's final status.
    pub(crate) fn finish(&mut self) -> Result<(), String> {
        for (staging, destination) in &self.staged {
            std::fs::rename(staging, destination)
                .map_err(|e| format!("witness: {}: {e}", destination.display()))?;
        }
        self.staged.clear();
        Ok(())
    }
}

impl Drop for Writer {
    fn drop(&mut self) {
        for (staging, _) in &self.staged {
            let _ = std::fs::remove_file(staging);
        }
        if self.created_directory {
            // Remove only an empty directory created by this writer, never user contents.
            let _ = std::fs::remove_dir(&self.path);
        }
    }
}

fn printable(s: &str) -> Result<(), String> {
    if s.chars().any(|c| c.is_control() || matches!(c, '\u{2028}' | '\u{2029}')) {
        return Err("witness: a name or message contains a control character or line separator"
            .to_owned());
    }
    Ok(())
}

fn printable_value(v: &serde_json::Value) -> Result<(), String> {
    match v {
        serde_json::Value::String(s) => printable(s),
        serde_json::Value::Array(xs) => xs.iter().try_for_each(printable_value),
        serde_json::Value::Object(xs) => xs.values().try_for_each(printable_value),
        _ => Ok(()),
    }
}

fn emitted(l: &LabelEnum) -> bool {
    match l {
        LabelEnum::Begin(_) | LabelEnum::End(_) | LabelEnum::TCreate(_)
        | LabelEnum::TJoin(_) | LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_)
        | LabelEnum::CToss(_) | LabelEnum::Block(_) => true,
        LabelEnum::Choice(c) => c.range().start() != c.range().end(),
        _ => false,
    }
}

/// One printable event, including the main thread's implicit end.
enum EventLine<'a> {
    Label(Event, &'a LabelEnum),
    End,
}

/// Classifies events without inspecting names or encoding payloads. Rendering
/// and measurement share omissions, terminal suppression and the implicit end.
fn event_lines(
    g: &ExecutionGraph, tid: crate::ThreadId,
) -> impl Iterator<Item = EventLine<'_>> {
    let mut next = 0;
    let mut ended = false;
    let mut finished = false;
    std::iter::from_fn(move || {
        while next < g.thread_size(tid) {
            let e = Event::new(tid, next as u32);
            next += 1;
            let label = g.label(e);
            if !emitted(label) || (ended && matches!(label, LabelEnum::End(_))) {
                continue;
            }
            ended |= matches!(label, LabelEnum::End(_) | LabelEnum::Block(_));
            return Some(EventLine::Label(e, label));
        }
        if !finished && !ended && tid == crate::thread::main_thread_id() {
            finished = true;
            return Some(EventLine::End);
        }
        None
    })
}

/// Witness event lines and sends/receives, even when text rendering would fail.
/// No text, names, payload encoding or collection allocation is needed.
pub(crate) fn counts(g: &ExecutionGraph) -> (u128, u128) {
    let mut events = 0;
    let mut messages = 0;
    for thread in g.threads.iter() {
        for line in event_lines(g, thread.tid) {
            events += 1;
            if matches!(line, EventLine::Label(_, LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_))) {
                messages += 1;
            }
        }
    }
    (events, messages)
}

fn render(g: &ExecutionGraph, iteration: usize, line: &str) -> Result<String, String> {
    let tids: Vec<_> = g.thread_ids().into_iter().collect();
    let mut names = HashMap::new();
    let mut positions = HashMap::new();
    let mut threads = ThreadNames::new();
    record_thread_names(g, &mut threads);
    for (t, &tid) in tids.iter().enumerate() {
        let name = g.thread_name(tid)
            .ok_or_else(|| "witness: an unnamed thread cannot be printed".to_owned())?;
        printable(name)?;
        names.insert(tid, (t, name));
        // Invisible messages may carry daemon identities; their names are still printable.
        threads.insert(tid.to_number(), ThreadName::Named(name.to_owned()));
        for (k, line) in event_lines(g, tid).enumerate() {
            if let EventLine::Label(e, _) = line {
                positions.insert(e, k);
            }
        }
    }
    let mut text = format!("uncovered summary (iteration {iteration}): {line}\n");
    for &tid in &tids {
        let (t, name) = names[&tid];
        let daemon = if g.is_thread_daemon(tid) { ", daemon" } else { "" };
        text.push_str(&format!("thread \"{name}\"[tid={t}{daemon}]:\n"));
        for (k, line) in event_lines(g, tid).enumerate() {
            let label = match line {
                EventLine::End => {
                    text.push_str(&format!("\t({t}, {k}): END\n"));
                    continue;
                }
                EventLine::Label(_, label) => label,
            };
            let event = match label {
                LabelEnum::Begin(_) => "BEGIN".to_owned(),
                LabelEnum::End(_) => "END".to_owned(),
                LabelEnum::Block(_) => "BLK".to_owned(),
                LabelEnum::TCreate(c) => {
                    let (child, name) = names[&c.cid()];
                    format!("TCREATE({child}:\"{name}\")")
                }
                LabelEnum::TJoin(j) => format!("TJOIN({})", names[&j.cid()].0),
                LabelEnum::SendMsg(s) => {
                    let dest = s.loc().as_thread_id().ok_or_else(||
                        "witness: a send destination is not a thread".to_owned())?;
                    let name = names.get(&dest).ok_or_else(||
                        "witness: a send destination is unknown".to_owned())?.1;
                    let value = encode_generic(s.val(), &threads)
                        .map_err(|e| format!("witness: {e}"))?;
                    let decoded = serde_json::from_str(&value)
                        .map_err(|e| format!("witness: invalid encoded value: {e}"))?;
                    printable_value(&decoded)?;
                    format!("SEND({name}, {value})")
                }
                LabelEnum::RecvMsg(r) => match r.rf() {
                    None => "RECV() [TIMEOUT]".to_owned(),
                    Some(send) => {
                        if !matches!(g.label(send), LabelEnum::SendMsg(_)) {
                            return Err("witness: receive does not name a send".to_owned());
                        }
                        let (sender, name) = names[&send.thread];
                        format!("RECV() [({sender}, {}) {name}]", positions[&send])
                    }
                },
                LabelEnum::CToss(c) => format!("NONDET {}", usize::from(c.result())),
                LabelEnum::Choice(c) => {
                    format!("NONDET {}", c.result() - c.range().start())
                }
                _ => unreachable!("conformance: classified witness event has no renderer"),
            };
            text.push_str(&format!("\t({t}, {k}): {event}\n"));
        }
    }
    Ok(text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event_label::{Block, BlockType, CToss, Choice, Sample, Unique};
    use crate::loc::CommunicationModel;

    fn scratch() -> PathBuf {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "tf-witness-staging-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    // Mutant: replace the staging write with a destination write.
    #[test]
    fn staging_preserves_destination_until_finish() {
        for directory in [false, true] {
            let dir = scratch();
            let target = if directory { dir.join("witness-1.txt") } else { dir.join("w") };
            std::fs::write(&target, b"sentinel").unwrap();
            let path = if directory { format!("{}/", dir.display()) }
                else { target.display().to_string() };
            let g = ExecutionGraph::new();
            let mut writer = Writer::new(path);
            writer.write(&g, 1, "summary").unwrap();
            assert_eq!(std::fs::read(&target).unwrap(), b"sentinel",
                "conformance: staging leaves destination untouched");
            assert_eq!(writer.staged.len(), 1, "conformance: one staged file");
            writer.finish().unwrap();
            assert_eq!(std::fs::read_to_string(&target).unwrap(), render(&g, 1, "summary").unwrap(),
                "conformance: publication keeps rendered bytes");
            drop(writer);
            assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1,
                "conformance: publication removes staging");
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    // Mutant: omit removal of pending staging files from Drop.
    #[test]
    fn unwind_discards_staging() {
        let dir = scratch();
        let target = dir.join("w");
        std::fs::write(&target, b"sentinel").unwrap();
        let result = std::panic::catch_unwind(|| {
            let mut writer = Writer::new(target.display().to_string());
            writer.write(&ExecutionGraph::new(), 1, "summary").unwrap();
            panic!("conformance: simulate an early unwind");
        });
        assert!(result.is_err(), "conformance: the fixture unwinds");
        assert_eq!(std::fs::read(&target).unwrap(), b"sentinel",
            "conformance: unwind preserves destination");
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1,
            "conformance: unwind removes staging");
        std::fs::remove_dir_all(dir).unwrap();
    }

    // Mutant: ignore a publication rename failure and return success.
    #[test]
    fn publish_error_removes_remaining_staging() {
        let dir = scratch();
        let mut writer = Writer::new(format!("{}/", dir.display()));
        let g = ExecutionGraph::new();
        writer.write(&g, 1, "first").unwrap();
        writer.write(&g, 2, "second").unwrap();
        let target = dir.join("witness-2.txt");
        std::fs::create_dir(&target).unwrap();
        let error = std::fs::rename(&writer.staged[1].0, &target).unwrap_err();
        assert_eq!(writer.finish(), Err(format!("witness: {}: {error}", target.display())),
            "conformance: publication reports the destination and OS error");
        drop(writer);
        assert_eq!(std::fs::read_to_string(dir.join("witness-1.txt")).unwrap(),
            render(&g, 1, "first").unwrap(), "conformance: prior rename remains published");
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 2,
            "conformance: failed publication removes pending staging");
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn omitted_labels_leave_contiguous_positions() {
        let mut g = ExecutionGraph::new();
        let tid = crate::thread::main_thread_id();
        g.add_label(LabelEnum::Sample(Sample::new(
            Event::new(tid, 1), serde_json::json!(3), vec![],
        )));
        g.add_label(LabelEnum::Unique(Unique::new(
            Event::new(tid, 2), CommunicationModel::LocalOrder,
        )));
        g.add_label(LabelEnum::Choice(Choice::new(Event::new(tid, 3), &mut (7..=7))));
        g.add_label(LabelEnum::CToss(CToss::new(Event::new(tid, 4), false)));
        assert_eq!(render(&g, 9, "summary").unwrap(), concat!(
            "uncovered summary (iteration 9): summary\n",
            "thread \"main\"[tid=0]:\n\t(0, 0): BEGIN\n",
            "\t(0, 1): NONDET 0\n\t(0, 2): END\n"
        ), "conformance: omitted labels consume no position");
        assert_eq!(counts(&g), (3, 0), "conformance: BEGIN, NONDET and implicit END");
        g.add_label(LabelEnum::Block(Block::new(Event::new(tid, 5), BlockType::Assume)));
        assert!(render(&g, 9, "summary").unwrap().ends_with("\t(0, 2): BLK\n"),
            "conformance: blocked main has no end");
        assert_eq!(counts(&g), (3, 0), "conformance: BLK replaces implicit END");
    }
}
