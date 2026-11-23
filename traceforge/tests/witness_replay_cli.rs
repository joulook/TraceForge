//! `<bin> replay`: one guided execution along a witness graph, through the CLI.
//!
//! Graphs come from this binary's own stores (`export --graphs`), from `conf-join
//! --witness-dir` and from `online --out --graphs`; mutated copies of them, and a program whose
//! behaviour is changed between export and replay, must deviate with a given kind at a given
//! position.
mod wg_common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use traceforge::program::{run_cli, Program};
use traceforge::Nondet;
use wg_common::*;

/// How the `drift` program differs from its exported form (0: not at all).
static DRIFT: AtomicUsize = AtomicUsize::new(0);

/// Held by every test that runs `drift`, since they share [`DRIFT`].
static DRIFT_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn drift_lock() -> std::sync::MutexGuard<'static, ()> {
    DRIFT_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

/// Held by the tests that set [`MARK`].
static MARK_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn mark_lock() -> std::sync::MutexGuard<'static, ()> {
    MARK_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

/// Where the `mark` program records that it ran.
static MARK: std::sync::Mutex<Option<PathBuf>> = std::sync::Mutex::new(None);

/// `rich`: main creates `u`, a daemon `d`, a blocked visible `x` and the visible `v`, which
/// tosses, chooses, creates `w`, sends to it, receives its reply, polls (⊥) and sends to `x`.
fn rich() {
    let u = named("u", || {});
    let d = traceforge::thread::Builder::new().name("d".to_owned()).spawn_daemon(|| {}).unwrap();
    let x = named("x", || {
        let _ = traceforge::recv_msg_block::<usize>();
        let _ = traceforge::recv_msg_block::<usize>();
    });
    let xid = x.thread().id();
    let v = named("v", move || {
        let c = (3..6).nondet();
        let b = traceforge::nondet() as usize;
        let _ = (7..8).nondet();
        let parent = me();
        let w = named("w", move || {
            let m = traceforge::recv_msg_block::<usize>();
            traceforge::send_msg(parent, m + 100);
        });
        traceforge::send_msg(w.thread().id(), c * 2 + b);
        let r = traceforge::recv_msg_block::<usize>();
        let _ = traceforge::recv_msg::<usize>();
        traceforge::send_msg(xid, r);
        w.join().unwrap();
    });
    v.join().unwrap();
    u.join().unwrap();
    d.join().unwrap();
}

/// `drift`: `v` chooses `c` in 0..4 (0..3 under drift 7), creates `w` (`w2` under 6), sends
/// `c + 10` to it (`c + 11` under 1; to itself under 2), sends 99 to itself (not under 4), may
/// toss first (under 3) and panics after its sends under 5. `w` polls once.
fn drift() {
    let m = DRIFT.load(Ordering::SeqCst);
    named("v", move || {
        let c = if m == 7 { (0..3).nondet() } else { (0..4).nondet() };
        if m == 3 { let _ = traceforge::nondet(); }
        let w = named(if m == 6 { "w2" } else { "w" }, move || {
            if m == 9 { panic!("later thread"); }
            if m != 8 { let _ = traceforge::recv_msg::<usize>(); }
        });
        let dest = if m == 2 { me() } else { w.thread().id() };
        traceforge::send_msg(dest, c + if matches!(m, 1 | 8 | 9) { 11 } else { 10 });
        if m != 4 { traceforge::send_msg(me(), 99usize); }
        if m == 5 { panic!("drift"); }
        w.join().unwrap();
    }).join().unwrap();
}

/// `fifo2`: `p` sends 1 then 2 to `v`, which receives once.
fn fifo2() {
    let v = named("v", || { let _ = traceforge::recv_msg_block::<usize>(); });
    let vid = v.thread().id();
    named("p", move || {
        traceforge::send_msg(vid, 1usize);
        traceforge::send_msg(vid, 2usize);
    }).join().unwrap();
    v.join().unwrap();
}

fn body(variant: &str) {
    match variant {
        "rich" => rich(),
        "drift" => drift(),
        "fifo2" => fifo2(),
        // `long`: `v` sends once; `h` sends 1100 unread messages, past the default thread threshold
        "long" => {
            let v = named("v", || traceforge::send_msg(me(), 1usize));
            named("h", || { for i in 0..1100usize { traceforge::send_msg(me(), i); } }).join().unwrap();
            v.join().unwrap();
        }
        // `perm`: `v` waits for a message nobody sends; `j` joins `k`, which waits likewise; `q`
        // meanwhile sends three messages to itself. Only `q` is joined.
        "perm" => {
            let v = named("v", || { let _ = traceforge::recv_msg_block::<usize>(); });
            let j = named("j", || {
                let k = named("k", || { let _ = traceforge::recv_msg_block::<usize>(); });
                k.join().unwrap();
            });
            let q = named("q", || { for i in 0..3usize { traceforge::send_msg(me(), i); } });
            q.join().unwrap();
            let _ = (v, j);
        }
        // `ones`: `v` takes 200 one-option choices, then sends once
        "ones" => {
            named("v", || {
                for _ in 0..200 { let _ = (5..6).nondet(); }
                traceforge::send_msg(me(), 1usize);
            }).join().unwrap();
        }
        // `mark`: writes the marker file (when one is set), then as `fifo2`
        "mark" => {
            if let Some(p) = MARK.lock().unwrap().clone() { std::fs::write(p, b"ran").unwrap(); }
            fifo2();
        }
        // a specification for `fifo2`'s visible thread: it receives nothing
        "none" => named("v", || {}).join().unwrap(),
        other => panic!("unknown variant {other}"),
    }
}

fn program() -> Program<'static> {
    Program {
        visible: &|a| match a.first().map(String::as_str) {
            Some("rich") => vec!["v".to_owned(), "x".to_owned()],
            _ => vec!["v".to_owned()],
        },
        spec: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
        imp: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || body(&v)) },
    }
}

fn cli(args: &[&str]) -> (String, u8) {
    run_cli(&program(), &args.iter().map(|s| s.to_string()).collect::<Vec<_>>())
}

/// Runs in a child process only (see `wg_common::child`).
#[test]
fn child_process_entry() {
    let Ok(_) = std::env::var("WG_CHILD") else { return };
    if let Ok(d) = std::env::var("WG_DRIFT") { DRIFT.store(d.parse().unwrap(), Ordering::SeqCst); }
    let args = std::env::var("WG_ARGS").unwrap();
    let args: Vec<&str> = if args.is_empty() { vec![] } else { args.split('\u{1f}').collect() };
    let (text, code) = cli(&args);
    std::fs::write(std::env::var("WG_OUT").unwrap(), text).unwrap();
    std::process::exit(code.into());
}

/// The graph lines of `export impl --graphs` of `variant` (in process, `source` unknown).
fn store(dir: &Path, variant: &str, side: &str) -> (PathBuf, Vec<String>) {
    let out = dir.join(format!("{variant}-{side}.jsonl"));
    let g = dir.join(format!("{variant}-{side}.jsonl.graphs.jsonl"));
    let (t, c) = cli(&["export", side, "--out", out.to_str().unwrap(), "--graphs", g.to_str().unwrap(),
        "--seed", "1", "--", variant]);
    assert_eq!(c, 0, "{t}");
    (out, read_lines(&g).into_iter().skip(1).collect())
}

fn write(dir: &Path, name: &str, text: &str) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, format!("{text}\n")).unwrap();
    p
}

/// `replay --graph <g> <flags…>`: (stdout, code).
fn replay(g: &Path, flags: &[&str]) -> (String, u8) {
    let mut a = vec!["replay", "--graph", g.to_str().unwrap()];
    a.extend(flags);
    cli(&a)
}

fn total_events(g: &J) -> usize {
    let J::Arr(ts) = g.get("threads") else { panic!() };
    ts.iter().map(|t| match t.get("events") { J::Arr(e) => e.len(), _ => 0 }).sum()
}

fn threads(g: &J) -> usize {
    match g.get("threads") { J::Arr(t) => t.len(), _ => 0 }
}

/// The text before the measurement block, and the block's keys.
fn split(t: &str) -> (String, Vec<String>) {
    let (a, b) = t.split_once("--- measurements\n").unwrap_or((t, ""));
    (a.to_owned(), b.lines().filter_map(|l| l.split_once(':')).map(|(k, _)| k.to_owned()).collect())
}

fn reproduced(g: &Path, flags: &[&str]) {
    let gj = parse(std::fs::read_to_string(g).unwrap().trim_end());
    let (t, c) = replay(g, flags);
    let (head, keys) = split(&t);
    assert_eq!((head.as_str(), c), (format!("replay: reproduced ({} events, {} threads)\n",
        total_events(&gj), threads(&gj)).as_str(), 0), "{}", g.display());
    assert_eq!(keys, ["wall_ms", "peak_rss_kb", "replay_events"], "{t}");
    assert_eq!(block_value(&t, "replay_events"), Some(total_events(&gj).to_string()));
}

// ---------------------------------------------------------------- round trips --

#[test]
fn every_stored_graph_replays() {
    let _drift = drift_lock();
    let dir = scratch();
    for v in ["rich", "drift", "fifo2"] {
        for side in ["impl", "spec"] {
            let (_, graphs) = store(&dir, v, side);
            assert!(!graphs.is_empty());
            for (i, g) in graphs.iter().enumerate() {
                let p = write(&dir, &format!("{v}-{side}-{i}.json"), g);
                reproduced(&p, &["--allow-source-change"]);
            }
        }
    }
}

#[test]
fn graphs_written_by_conf_join_and_online_replay() {
    let dir = scratch();
    let (spec, _) = store(&dir, "none", "spec");
    let (imp, graphs) = store(&dir, "fifo2", "impl");
    assert_eq!(graphs.len(), 1);
    let w = dir.join("w");
    let out = {
        let _r = spawn_guard();
        Command::new(env!("CARGO_BIN_EXE_conf-join")).args(["--decide", "--witness-dir", w.to_str().unwrap(),
            spec.to_str().unwrap(), imp.to_str().unwrap()]).output().unwrap()
    };
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    let written: Vec<PathBuf> = std::fs::read_dir(&w).unwrap().map(|e| e.unwrap().path())
        .filter(|p| p.to_string_lossy().ends_with(".graph.json")).collect();
    assert_eq!(written.len(), 1, "{written:?}");
    for p in &written { reproduced(p, &["--allow-source-change"]); }
    // online --out --graphs
    let f = dir.join("on.jsonl");
    let g = dir.join("on.g");
    let (t, c) = cli(&["online", "--spec", spec.to_str().unwrap(), "--out", f.to_str().unwrap(),
        "--graphs", g.to_str().unwrap(), "--", "fifo2"]);
    assert_eq!(c, 1, "{t}"); // `reports`
    assert!(t.contains("verdict:    reports\n"), "{t}");
    let lines: Vec<String> = read_lines(&g).into_iter().skip(1).collect();
    assert!(!lines.is_empty());
    for (i, l) in lines.iter().enumerate() {
        reproduced(&write(&dir, &format!("on-{i}.json"), l), &["--allow-source-change"]);
    }
}

// ------------------------------------------------------------------ refusals --

/// A stored `drift` graph, with `edit` applied to its text.
fn edited(dir: &Path, name: &str, edit: impl Fn(&str) -> String) -> PathBuf {
    let (_, graphs) = store(dir, "drift", "impl");
    let g = edit(&graphs[0]);
    write(dir, name, &g)
}

fn refused(t: &str, c: u8, what: &str) {
    assert_eq!(c, 2, "{what}: {t}");
    let first = t.lines().next().unwrap();
    assert!(first.starts_with("program: replay: "), "{what}: {t}");
    assert!(!t.contains("replay: reproduced") && !t.contains("replay: deviation"), "{what}: no run");
    assert!(t.lines().nth(1).is_some_and(|l| l.starts_with("usage: <bin> replay --graph FILE")), "{what}: {t}");
}

#[test]
fn refusals_exit_two_before_running() {
    let _drift = drift_lock();
    DRIFT.store(0, Ordering::SeqCst);
    let dir = scratch();
    let set = |key: &str, val: &str| {
        let key = key.to_owned();
        let val = val.to_owned();
        move |g: &str| {
            // The field of `run`, not of `export`.
            let run = g.find(",\"run\":{").unwrap();
            let at = run + g[run..].find(&format!("\"{key}\":")).unwrap() + key.len() + 3;
            let end = at + if g[at..].starts_with('"') { g[at + 1..].find('"').unwrap() + 2 } else { g[at..].find(',').unwrap() };
            format!("{}{val}{}", &g[..at], &g[end..])
        }
    };
    let cases: Vec<(&str, PathBuf, Vec<&str>)> = vec![
        ("G3 break", edited(&dir, "g3.json", |g| g.replacen("\"events\":[{\"e\":\"BEGIN\"},", "\"events\":[", 1)), vec!["--allow-source-change", "--allow-tool-change"]),
        ("tool", edited(&dir, "tool.json", set("tool", "\"jmc\"")), vec!["--allow-source-change", "--allow-tool-change"]),
        ("entry", edited(&dir, "entry.json", set("entry", "\"other\"")), vec!["--allow-source-change", "--allow-tool-change"]),
        ("side", edited(&dir, "side.json", set("side", "\"both\"")), vec!["--allow-source-change", "--allow-tool-change"]),
        ("model", edited(&dir, "model.json", set("model", "\"mailbox\"")), vec!["--allow-source-change", "--allow-tool-change"]),
        ("args", edited(&dir, "args.json", |g| g.to_owned()), vec!["--allow-source-change", "--allow-tool-change", "--", "other"]),
        ("args empty", edited(&dir, "args2.json", |g| g.to_owned()), vec!["--allow-source-change", "--allow-tool-change", "--"]),
        ("source unknown", edited(&dir, "src.json", |g| g.to_owned()), vec![]),
        ("source unknown, tool flag only", edited(&dir, "src2.json", |g| g.to_owned()), vec!["--allow-tool-change"]),
        ("tool commit", edited(&dir, "commit.json", set("tool_commit", "\"abc\"")), vec!["--allow-source-change"]),
        ("tool commit unknown", edited(&dir, "commit2.json", set("tool_commit", "\"unknown\"")), vec!["--allow-source-change"]),
        ("missing file", dir.join("nope.json"), vec![]),
    ];
    for (what, g, flags) in cases {
        let (t, c) = replay(&g, &flags);
        refused(&t, c, what);
    }
    // Explicit ARGS equal to the graph's are accepted.
    let g = edited(&dir, "ok.json", |g| g.to_owned());
    let (t, c) = replay(&g, &["--allow-source-change", "--", "drift"]);
    assert_eq!(c, 0, "{t}");
    // Bad arguments.
    for args in [vec!["replay"], vec!["replay", "--graph"], vec!["replay", "--bogus"],
                 vec!["replay", "--graph", g.to_str().unwrap(), "--report"]] {
        let (t, c) = cli(&args);
        refused(&t, c, &format!("{args:?}"));
    }
    // Both changes need both flags, each its own.
    let both = edited(&dir, "both.json", set("tool_commit", "\"abc\""));
    for (flags, code) in [(vec![], 2), (vec!["--allow-tool-change"], 2), (vec!["--allow-source-change"], 2),
                          (vec!["--allow-tool-change", "--allow-source-change"], 0)] {
        let rep = dir.join(format!("r{}.json", flags.len()));
        let mut f = flags.clone();
        let rs = rep.to_str().unwrap().to_owned();
        f.extend(["--report", &rs]);
        let (t, c) = replay(&both, &f);
        assert_eq!(c, code, "{flags:?}: {t}");
        if code == 0 {
            let r = parse(std::fs::read_to_string(&rep).unwrap().trim_end());
            assert_eq!(bytes(r.get("warnings")), format!("[{},\"source-change\"]",
                serde_json::to_string(&format!("tool-change: abc -> {}", expected_commit())).unwrap()));
        } else {
            assert!(!rep.exists(), "no report for a refusal");
        }
    }
}

#[test]
fn the_manifest_decides_source_refusals() {
    let dir = scratch();
    let bin = child_binary(&dir, "tf_replay");
    let a = "0123456789abcdef0123456789abcdef";
    let manifest = dir.join("tf_replay.SOURCE.md5");
    std::fs::write(&manifest, format!("# root r\n{a}  src/main.rs\n")).unwrap();
    let out = dir.join("e.jsonl");
    let gs = dir.join("e.g");
    let (t, e, c) = child(&bin, "", &["export", "impl", "--out", out.to_str().unwrap(), "--graphs",
        gs.to_str().unwrap(), "--", "rich"]);
    assert_eq!((c, e.as_str()), (0, ""), "{t}");
    let graphs: Vec<String> = read_lines(&gs).into_iter().skip(1).collect();
    let g = write(&dir, "g.json", &graphs[0]);
    // Same manifest: no flag needed, no warning.
    let rep = dir.join("rep.json");
    let (t, e, c) = child(&bin, "", &["replay", "--graph", g.to_str().unwrap(), "--report", rep.to_str().unwrap()]);
    assert_eq!((c, e.as_str()), (0, ""), "{t}");
    assert!(std::fs::read_to_string(&rep).unwrap().ends_with(",\"warnings\":[]}\n"));
    // Another digest in the graph: refused, and the tool flag does not help.
    let other = write(&dir, "other.json", &graphs[0].replacen(a, "ffffffffffffffffffffffffffffffff", 1));
    for flags in [vec![], vec!["--allow-tool-change"]] {
        let mut args = vec!["replay", "--graph", other.to_str().unwrap()];
        args.extend(flags.iter());
        let (t, _, c) = child(&bin, "", &args);
        refused(&t, c as u8, "another digest");
    }
    let (t, _, c) = child(&bin, "", &["replay", "--graph", other.to_str().unwrap(), "--allow-source-change"]);
    assert_eq!(c, 0, "{t}");
    // A manifest older than the binary reads as unknown: refused, with its stderr line.
    let bt = std::fs::metadata(&bin).unwrap().modified().unwrap();
    std::fs::File::options().write(true).open(&manifest).unwrap()
        .set_modified(bt - std::time::Duration::from_secs(60)).unwrap();
    let (t, e, c) = child(&bin, "", &["replay", "--graph", g.to_str().unwrap()]);
    refused(&t, c as u8, "stale manifest");
    assert_eq!(e, format!("graphs: manifest {}: older than the binary\n", manifest.display()));
}

// ---------------------------------------------------------------- deviations --

/// The `drift` graph whose choice is 0, changed so that `w`'s poll reads `v`'s message: an
/// execution the program also has (the store keeps the first one, where `w` reads ⊥).
fn drift_graph(dir: &Path) -> String {
    DRIFT.store(0, Ordering::SeqCst);
    let (_, graphs) = store(dir, "drift", "impl");
    let g = graphs.into_iter().find(|g| {
        bytes(parse(g).get("threads").at(1).get("events").at(1)) == "{\"e\":\"NONDET\",\"n\":4,\"i\":0,\"lo\":0}"
    }).expect("the drift graph");
    let polled = "{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":null}";
    assert_eq!(bytes(parse(&g).get("threads").at(2).get("events").at(1)), polled);
    g.replacen(polled, "{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":[1,3]}", 1)
}

/// Replays `g` and checks the deviation line and the report; mismatches are collected in `bad`.
fn deviates(bad: &mut Vec<String>, dir: &Path, name: &str, g: &str, at: (usize, usize), thread: &str, kind: &str,
    expected: &str, actual: Option<&str>) {
    let p = write(dir, name, g);
    let rep = dir.join(format!("{name}.report"));
    let (t, c) = replay(&p, &["--allow-source-change", "--report", rep.to_str().unwrap()]);
    let line = format!("replay: deviation at ({}, {}) thread \"{thread}\": {kind}: expected {expected}, got {}\n",
        at.0, at.1, actual.unwrap_or("nothing"));
    let (head, _) = split(&t);
    println!("{name}: exit {c}: {head}");
    if (head.as_str(), c) != (line.as_str(), 1) {
        bad.push(format!("{name}: got {head:?} exit {c}, want {line:?}"));
        return;
    }
    let js = |s: Option<&str>| s.map_or("null".to_owned(), |s| serde_json::to_string(s).unwrap());
    let want = format!(
        "{{\"replay\":1,\"graph\":{},\"result\":\"deviation\",\"at\":[{},{}],\"thread\":{},\"kind\":\"{kind}\",\
         \"expected\":{},\"actual\":{},\"warnings\":[\"source-change\"]}}\n",
        serde_json::to_string(p.to_str().unwrap()).unwrap(), at.0, at.1, js(Some(thread)), js(Some(expected)), js(actual));
    let got = std::fs::read_to_string(&rep).unwrap_or_default();
    if got != want { bad.push(format!("{name}: report {got:?}, want {want:?}")); }
}

#[test]
fn mutated_graphs_deviate_with_kind_and_position() {
    let _drift = drift_lock();
    let dir = scratch();
    let g = drift_graph(&dir);
    let mut bad = Vec::new();
    // The derivation of `drift` under drift 0, choice 0 (w's poll reads v's first send):
    // v (t1): BEGIN, NONDET, TCREATE(2:"w"), SEND(w, 10), SEND(v, 99), TJOIN(2), END
    // w (t2): BEGIN, RECV() [(1, 3) v], END
    let ev = |t: usize, k: usize| bytes(parse(&g).get("threads").at(t).get("events").at(k));
    assert_eq!(ev(1, 3), "{\"e\":\"SEND\",\"to\":2,\"v\":10}");
    assert_eq!(ev(1, 4), "{\"e\":\"SEND\",\"to\":1,\"v\":99}");
    // a changed send value
    deviates(&mut bad, &dir, "value", &g.replacen("{\"e\":\"SEND\",\"to\":2,\"v\":10}", "{\"e\":\"SEND\",\"to\":2,\"v\":12}", 1),
        (1, 3), "v", "value", "SEND(w, 12)", Some("SEND(w, 10)"));
    // a changed destination (the unread send)
    deviates(&mut bad, &dir, "dest", &g.replacen("{\"e\":\"SEND\",\"to\":1,\"v\":99}", "{\"e\":\"SEND\",\"to\":2,\"v\":99}", 1),
        (1, 4), "v", "dest", "SEND(w, 99)", Some("SEND(v, 99)"));
    // a changed choice index: the program then sends 12
    deviates(&mut bad, &dir, "choice", &g.replacen("\"n\":4,\"i\":0,\"lo\":0", "\"n\":4,\"i\":2,\"lo\":0", 1),
        (1, 3), "v", "value", "SEND(w, 10)", Some("SEND(w, 12)"));
    // a changed thread name
    deviates(&mut bad, &dir, "name", &g.replacen("{\"name\":\"w\"", "{\"name\":\"q\"", 1),
        (2, 0), "q", "child", "q", Some("w"));
    // a truncated thread: v ends after its first send
    let trunc = g.replacen("{\"e\":\"SEND\",\"to\":1,\"v\":99},{\"e\":\"TJOIN\",\"child\":2},{\"e\":\"END\"}",
        "{\"e\":\"END\"}", 1);
    deviates(&mut bad, &dir, "trunc", &trunc, (1, 4), "v", "overrun", "END", Some("SEND(v, 99)"));
    // an extra event: w sends once more before its end
    let extra = g.replacen("{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":[1,3]},{\"e\":\"END\"}",
        "{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":[1,3]},{\"e\":\"SEND\",\"to\":2,\"v\":5},{\"e\":\"END\"}", 1);
    deviates(&mut bad, &dir, "extra", &extra, (2, 2), "w", "early-end", "SEND(w, 5)", Some("END"));
    // another receive mode
    deviates(&mut bad, &dir, "mode", &g.replacen("\"mode\":\"try\",\"rf\":[1,3]", "\"mode\":\"block\",\"rf\":[1,3]", 1),
        (2, 1), "w", "event", "RECV() [(1, 3) v]", Some("RECV() (non-blocking)"));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn a_receive_from_a_send_it_cannot_read_is_unavailable() {
    let dir = scratch();
    let (_, graphs) = store(&dir, "fifo2", "impl");
    assert_eq!(graphs.len(), 1, "FIFO: v reads p's first message");
    let g = &graphs[0];
    // v (t1): BEGIN, RECV() [(2, 1) p], END; p (t2): BEGIN, SEND(v, 1), SEND(v, 2), END
    assert!(g.contains("{\"e\":\"RECV\",\"mode\":\"block\",\"rf\":[2,1]}"), "{g}");
    let m = g.replacen("\"rf\":[2,1]", "\"rf\":[2,2]", 1);
    let mut bad = Vec::new();
    deviates(&mut bad, &dir, "rf", &m, (1, 1), "v", "unavailable", "RECV() [(2, 2) p]", Some("RECV()"));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn a_blocked_thread_recorded_as_ended_is_a_status_deviation() {
    let dir = scratch();
    let (_, graphs) = store(&dir, "rich", "impl");
    let g = &graphs[0];
    // x (t3) blocks at its second receive: BEGIN, RECV, BLK.
    let x = bytes(parse(g).get("threads").at(3));
    assert!(x.ends_with("{\"e\":\"BLK\"}]}"), "{x}");
    let m = g.replacen(&x, &x.replacen("{\"e\":\"BLK\"}", "{\"e\":\"END\"}", 1), 1);
    // x is blocked for good at a blocking receive: its event is BLK, or the waiting receive.
    let mut bad = Vec::new();
    deviates(&mut bad, &dir, "status", &m, (3, 2), "x", "status", "END", Some("BLK"));
    let mut bad2 = Vec::new();
    deviates(&mut bad2, &dir, "status2", &m, (3, 2), "x", "status", "END", Some("RECV() (waiting)"));
    assert!(bad.is_empty() || bad2.is_empty(), "{}\n{}", bad.join("\n"), bad2.join("\n"));
}

#[test]
fn a_changed_program_deviates_under_allow_source_change() {
    let _drift = drift_lock();
    let dir = scratch();
    let g = drift_graph(&dir);
    let p = write(&dir, "g.json", &g);
    let cases: Vec<(usize, (usize, usize), &str, &str, &str, Option<&str>)> = vec![
        (1, (1, 3), "v", "value", "SEND(w, 10)", Some("SEND(w, 11)")),
        (2, (1, 3), "v", "dest", "SEND(w, 10)", Some("SEND(v, 10)")),
        (3, (1, 2), "v", "event", "TCREATE(2:\"w\")", Some("NONDET (a toss)")),
        (4, (1, 4), "v", "event", "SEND(v, 99)", Some("TJOIN(2)")),
        (6, (2, 0), "w", "child", "w", Some("w2")),
        (7, (1, 1), "v", "options", "NONDET 0", Some("NONDET (over 0..=2)")),
    ];
    let mut got = Vec::new();
    for (m, at, thread, kind, expected, actual) in &cases {
        DRIFT.store(*m, Ordering::SeqCst);
        let (t, c) = replay(&p, &["--allow-source-change"]);
        let want = format!("replay: deviation at ({}, {}) thread \"{thread}\": {kind}: expected {expected}, got {}",
            at.0, at.1, actual.unwrap_or("nothing"));
        got.push((m, c, t.lines().next().unwrap_or("").to_owned(), want));
    }
    DRIFT.store(0, Ordering::SeqCst);
    for (m, c, line, want) in &got {
        println!("drift {m}: exit {c}: {line}\n   want: {want}");
    }
    let bad: Vec<String> = got.iter().filter(|(_, c, line, want)| (*c, line) != (1, want))
        .map(|(m, c, line, want)| format!("drift {m}: exit {c} {line:?}, want {want:?}")).collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn a_program_that_panics_in_replay_is_a_failed_run() {
    let _drift = drift_lock();
    // In a child process, as the binary would run: exit 1 and no `replay:` line.
    let dir = scratch();
    let bin = child_binary(&dir, "tf_drift");
    let g = drift_graph(&dir);
    let entry = format!("\"entry\":{}", serde_json::to_string(&this_entry()).unwrap());
    let g = g.replacen(&entry, "\"entry\":\"tf_drift\"", 1);
    let p = write(&dir, "g.json", &g);
    let out = dir.join("t.cli-out");
    let r = {
        let _r = spawn_guard();
        Command::new(&bin).args(["--exact", "child_process_entry", "--nocapture", "--test-threads", "1"])
            .env("WG_CHILD", "1").env("WG_DRIFT", "5")
            .env("WG_ARGS", ["replay", "--graph", p.to_str().unwrap(), "--allow-source-change"].join("\u{1f}"))
            .env("WG_OUT", &out).output().unwrap()
    };
    let text = std::fs::read_to_string(&out).unwrap_or_default();
    println!("exit {:?}\n--- cli\n{text}--- stdout\n{}--- stderr\n{}", r.status,
        String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
    assert_eq!(r.status.code(), Some(1), "a failed run exits 1");
    assert!(!text.contains("replay: ") && !String::from_utf8_lossy(&r.stdout).contains("replay: "));
    assert!(text.lines().any(|l| l.ends_with("replay failed: the program panicked: drift")), "{text}");
}

#[test]
fn reproduced_report_and_opaque_warnings() {
    let _drift = drift_lock();
    let dir = scratch();
    let g = drift_graph(&dir);
    let p = write(&dir, "g.json", &g);
    reproduced(&p, &["--allow-source-change"]);
    let rep = dir.join("r.json");
    let (t, c) = replay(&p, &["--allow-source-change", "--report", rep.to_str().unwrap()]);
    assert_eq!(c, 0, "{t}");
    assert_eq!(std::fs::read_to_string(&rep).unwrap(), format!(
        "{{\"replay\":1,\"graph\":{},\"result\":\"reproduced\",\"at\":null,\"thread\":null,\"kind\":null,\
         \"expected\":null,\"actual\":null,\"warnings\":[\"source-change\"]}}\n",
        serde_json::to_string(p.to_str().unwrap()).unwrap()));
    // An invisible send written opaque is not compared, with a warning naming it: `fifo2`'s
    // second send (2, 2) is read by nobody.
    let (_, graphs) = store(&dir, "fifo2", "impl");
    let o = write(&dir, "o.json", &graphs[0].replacen("{\"e\":\"SEND\",\"to\":1,\"v\":2}",
        "{\"e\":\"SEND\",\"to\":1,\"v\":{\"opaque\":\"x\"}}", 1));
    let rep2 = dir.join("r2.json");
    let (t, c) = replay(&o, &["--allow-source-change", "--report", rep2.to_str().unwrap()]);
    assert_eq!(c, 0, "{t}");
    let r = parse(std::fs::read_to_string(&rep2).unwrap().trim_end());
    assert_eq!(bytes(r.get("warnings")), "[\"source-change\",\"opaque-not-compared at (2, 2)\"]");
    // A visible send cannot be opaque (G8): refused.
    let v = write(&dir, "v.json", &g.replacen("{\"e\":\"SEND\",\"to\":1,\"v\":99}", "{\"e\":\"SEND\",\"to\":1,\"v\":{\"opaque\":\"x\"}}", 1));
    let (t, c) = replay(&v, &["--allow-source-change"]);
    refused(&t, c, "opaque in a visible send");
    // The other subcommands' usage is the earlier usage plus nothing else: checked against the
    // reference build outside this suite.
}

/// Prints the CLI texts that must stay as they were, for comparison with a reference build
/// (same argument lists as there). Ignored.
#[test]
#[ignore]
fn usage_dump() {
    for args in [vec![], vec!["nosuch"], vec!["export"], vec!["count", "impl", "--bogus"], vec!["online"],
                 vec!["conf", "--bogus"], vec!["row"]] {
        let (t, c) = cli(&args);
        println!("=== {args:?} -> {c}\n{t}");
    }
}

#[test]
fn the_threshold_comes_from_the_graph() {
    let dir = scratch();
    let out = dir.join("l.jsonl");
    let g = dir.join("l.g");
    let (t, c) = cli(&["export", "impl", "--out", out.to_str().unwrap(), "--graphs", g.to_str().unwrap(),
        "--threshold", "5000", "--", "long"]);
    assert_eq!(c, 0, "{t}");
    let graph = read_lines(&g).remove(1);
    assert!(graph.contains("\"options\":{\"threshold\":5000}"), "{graph}");
    reproduced(&write(&dir, "l.json", &graph), &["--allow-source-change"]);
    // With the default threshold the run stops: a failed run.
    let low = graph.replacen("\"options\":{\"threshold\":5000}", "\"options\":{}", 1);
    let (t, c) = replay(&write(&dir, "low.json", &low), &["--allow-source-change"]);
    assert_eq!(c, 1, "{t}");
    assert!(!t.contains("replay: reproduced"), "{t}");
}

// ------------------------------------------------------------- round-01 review --

#[test]
fn the_earlier_thread_deviation_wins_over_a_later_early_end() {
    let _drift = drift_lock();
    let dir = scratch();
    let g = drift_graph(&dir);
    DRIFT.store(8, Ordering::SeqCst);
    let (t, c) = replay(&write(&dir, "g.json", &g), &["--allow-source-change"]);
    DRIFT.store(0, Ordering::SeqCst);
    // v (t1) offers SEND(w, 11) at (1, 3) while w (t2) would end without its poll at (2, 1).
    assert_eq!((t.lines().next().unwrap(), c),
        ("replay: deviation at (1, 3) thread \"v\": value: expected SEND(w, 10), got SEND(w, 11)", 1), "{t}");
}

#[test]
fn a_later_thread_panic_is_a_failed_run() {
    // Documented: a panic during a probe ends the replay as a failed run, even when an earlier
    // thread would have deviated first.
    let _drift = drift_lock();
    let dir = scratch();
    let bin = child_binary(&dir, "tf_drift9");
    let g = drift_graph(&dir);
    let entry = format!("\"entry\":{}", serde_json::to_string(&this_entry()).unwrap());
    let p = write(&dir, "g.json", &g.replacen(&entry, "\"entry\":\"tf_drift9\"", 1));
    let out = dir.join("t.cli-out");
    let r = {
        let _r = spawn_guard();
        Command::new(&bin).args(["--exact", "child_process_entry", "--nocapture", "--test-threads", "1"])
            .env("WG_CHILD", "1").env("WG_DRIFT", "9")
            .env("WG_ARGS", ["replay", "--graph", p.to_str().unwrap(), "--allow-source-change"].join("\u{1f}"))
            .env("WG_OUT", &out).output().unwrap()
    };
    let text = std::fs::read_to_string(&out).unwrap_or_default();
    println!("exit {:?}\n--- cli\n{text}--- stderr\n{}", r.status, String::from_utf8_lossy(&r.stderr));
    assert_eq!(r.status.code(), Some(1));
    assert!(!text.contains("replay: "), "{text}");
    assert!(text.lines().any(|l| l.ends_with("replay failed: the program panicked: later thread")), "{text}");
}

#[test]
fn permanent_receive_and_join_blocks_beside_other_work_reproduce() {
    let dir = scratch();
    let (_, graphs) = store(&dir, "perm", "impl");
    assert!(!graphs.is_empty());
    for (i, g) in graphs.iter().enumerate() {
        let j = parse(g);
        // v ends BLK at its receive; j ends BLK at its join; k ends BLK; q ends normally.
        let last = |t: usize| match j.get("threads").at(t).get("events") { J::Arr(e) => bytes(e.last().unwrap()), _ => unreachable!() };
        let name = |t: usize| bytes(j.get("threads").at(t).get("name"));
        for t in 1..threads(&j) {
            let want = if name(t) == "\"q\"" { "{\"e\":\"END\"}" } else { "{\"e\":\"BLK\"}" };
            assert_eq!(last(t), want, "thread {t} {}", name(t));
        }
        reproduced(&write(&dir, &format!("perm-{i}.json"), g), &["--allow-source-change"]);
    }
}

#[test]
fn two_hundred_one_option_choices_reproduce() {
    let dir = scratch();
    let (_, graphs) = store(&dir, "ones", "impl");
    assert_eq!(graphs.len(), 1);
    // The choices are not recorded: v is BEGIN, SEND, END.
    assert_eq!(bytes(parse(&graphs[0]).get("threads").at(1).get("events")),
        "[{\"e\":\"BEGIN\"},{\"e\":\"SEND\",\"to\":1,\"v\":1},{\"e\":\"END\"}]");
    reproduced(&write(&dir, "ones.json", &graphs[0]), &["--allow-source-change"]);
}

#[test]
fn malformed_run_identity_is_refused_before_the_program_runs() {
    let _mark = mark_lock();
    let dir = scratch();
    let (_, graphs) = store(&dir, "mark", "impl");
    let g = &graphs[0];
    let marker = dir.join("ran");
    *MARK.lock().unwrap() = Some(marker.clone());
    let run_field = |key: &str, value: &str| -> String {
        let run = g.find(",\"run\":{").unwrap();
        let at = run + g[run..].find(&format!("\"{key}\":")).unwrap() + key.len() + 3;
        let rest = &g[at..];
        let end = if rest.starts_with('"') { rest[1..].find('"').unwrap() + 2 }
            else if rest.starts_with('{') || rest.starts_with('[') {
                let close = if rest.starts_with('{') { '}' } else { ']' };
                rest.find(close).unwrap() + 1
            } else { rest.find(',').unwrap() };
        format!("{}{value}{}", &g[..at], &g[at + end..])
    };
    let cases: Vec<(&str, String)> = vec![
        ("a non-string arg", run_field("args", "[\"mark\",false]")),
        ("args not an array", run_field("args", "\"mark\"")),
        ("seed beyond u64", run_field("options", "{\"seed\":18446744073709551616}")),
        ("seed a string", run_field("options", "{\"seed\":\"1\"}")),
        ("threshold beyond u32", run_field("options", "{\"threshold\":4294967296}")),
        ("model null", run_field("model", "null")),
        ("model a number", run_field("model", "3")),
        ("side null", run_field("side", "null")),
        ("missing entry", g.replacen(&format!(",\"entry\":{}", serde_json::to_string(&this_entry()).unwrap()), "", 1)),
        ("entry a number", run_field("entry", "7")),
        ("tool_commit null", run_field("tool_commit", "null")),
    ];
    let mut bad = Vec::new();
    for (what, text) in &cases {
        assert_ne!(text, g, "{what}: the edit applies");
        let _ = std::fs::remove_file(&marker);
        let p = write(&dir, &format!("{}.json", what.replace(' ', "-")), text);
        let (t, c) = replay(&p, &["--allow-source-change", "--allow-tool-change"]);
        if c != 2 || marker.exists() || !t.starts_with("program: replay: ") {
            bad.push(format!("{what}: exit {c}, ran {}: {}", marker.exists(), t.lines().next().unwrap_or("")));
        }
    }
    // The control: the unedited graph runs the program.
    let _ = std::fs::remove_file(&marker);
    let (t, c) = replay(&write(&dir, "ok.json", g), &["--allow-source-change"]);
    assert_eq!(c, 0, "{t}");
    assert!(marker.exists(), "the control runs the program");
    *MARK.lock().unwrap() = None;
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn a_root_only_source_change_needs_no_flag() {
    let dir = scratch();
    let bin = child_binary(&dir, "tf_root");
    let a = "0123456789abcdef0123456789abcdef";
    std::fs::write(dir.join("tf_root.SOURCE.md5"), format!("# root r\n{a}  src/main.rs\n")).unwrap();
    let gs = dir.join("e.g");
    let (t, e, c) = child(&bin, "", &["export", "impl", "--out", dir.join("e.jsonl").to_str().unwrap(),
        "--graphs", gs.to_str().unwrap(), "--", "fifo2"]);
    assert_eq!((c, e.as_str()), (0, ""), "{t}");
    let g = read_lines(&gs).remove(1);
    assert!(g.contains("\"source\":{\"root\":\"r\","), "{g}");
    let moved = write(&dir, "moved.json", &g.replacen("\"source\":{\"root\":\"r\",", "\"source\":{\"root\":\"elsewhere\",", 1));
    let rep = dir.join("rep.json");
    let (t, e, c) = child(&bin, "", &["replay", "--graph", moved.to_str().unwrap(), "--report", rep.to_str().unwrap()]);
    assert_eq!((c, e.as_str()), (0, ""), "{t}");
    assert!(std::fs::read_to_string(&rep).unwrap().ends_with(",\"warnings\":[]}\n"));
}

// ------------------------------------------------------------- round-02 review --

fn plus_2_64(text: &str, key: &str) -> String {
    let at = text.find(key).unwrap_or_else(|| panic!("{key}")) + key.len();
    let end = at + text[at..].find(|c: char| !c.is_ascii_digit()).unwrap();
    let n: u128 = text[at..end].parse().unwrap();
    format!("{}{}{}", &text[..at], n + (1u128 << 64), &text[end..])
}

#[test]
fn oversized_indices_and_bad_join_or_nearest_are_refused_before_running() {
    let _mark = mark_lock();
    let dir = scratch();
    let (_, graphs) = store(&dir, "mark", "impl");
    let g = graphs[0].clone();
    let marker = dir.join("ran2");
    *MARK.lock().unwrap() = Some(marker.clone());
    let rf_index = {
        let at = g.find("\"rf\":[").unwrap() + 6;
        let comma = at + g[at..].find(',').unwrap();
        format!("{}{}", &g[..comma], plus_2_64(&g[comma..], ","))
    };
    let join = |j: &str| g.replacen(",\"join\":null,", &format!(",\"join\":{j},"), 1);
    let cases: Vec<(&str, String)> = vec![
        ("SEND to", plus_2_64(&g, "{\"e\":\"SEND\",\"to\":")),
        ("TCREATE child", plus_2_64(&g, "{\"e\":\"TCREATE\",\"child\":")),
        ("TJOIN child", plus_2_64(&g, "{\"e\":\"TJOIN\",\"child\":")),
        ("rf thread", plus_2_64(&g, "\"rf\":[")),
        ("rf index", rf_index),
        ("model garbage", g.replacen("\"model\":\"fifo\"", "\"model\":\"garbage\"", 1)),
        ("join {tool:17}", join("{\"tool\":17}")),
        ("join only unknown", join("{\"x\":1}")),
        ("join false-alarm", join("{\"tool\":\"traceforge\",\"tool_commit\":\"c\",\"mode\":\"plain\",\"class\":\"not-found\",\"decide\":{\"outcome\":\"false-alarm\",\"k\":1,\"k_min\":1,\"states\":0,\"witness\":null},\"against\":{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:spec\",\"size\":\"none\",\"visible\":[\"v\"],\"roles\":[\"v\"],\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1},\"against_run\":null}")),
        ("join bad witness position", join("{\"tool\":\"traceforge\",\"tool_commit\":\"c\",\"mode\":\"plain\",\"class\":\"not-found\",\"decide\":{\"outcome\":\"violation\",\"k\":1,\"k_min\":1,\"states\":0,\"witness\":[[0,\"v\"]]},\"against\":{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:spec\",\"size\":\"none\",\"visible\":[\"v\"],\"roles\":[\"v\"],\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1},\"against_run\":null}")),
        ("nearest [17]", g.replacen(",\"nearest\":null,", ",\"nearest\":[17],", 1)),
    ];
    let mut bad = Vec::new();
    for (what, text) in &cases {
        assert_ne!(text, &g, "{what}: the edit applies");
        let _ = std::fs::remove_file(&marker);
        let (t, c) = replay(&write(&dir, &format!("{}.json", what.replace([' ', '{', '}', ':', '[', ']'], "_")), text),
            &["--allow-source-change", "--allow-tool-change"]);
        if c != 2 || marker.exists() || !t.starts_with("program: replay: ") {
            bad.push(format!("{what}: exit {c}, ran {}: {}", marker.exists(), t.lines().next().unwrap_or("")));
        }
    }
    // A valid join with unknown members is accepted and the program runs.
    let _ = std::fs::remove_file(&marker);
    let ok = join("{\"tool\":\"traceforge\",\"tool_commit\":\"c\",\"mode\":\"merge\",\"class\":\"no-slot\",\"zz\":0,\"decide\":null,\"against\":{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:spec\",\"size\":\"none\",\"visible\":[\"v\"],\"roles\":[\"v\"],\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1},\"against_run\":null}");
    let (t, c) = replay(&write(&dir, "okjoin.json", &ok), &["--allow-source-change"]);
    let ran = marker.exists();
    *MARK.lock().unwrap() = None;
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    assert_eq!(c, 0, "{t}");
    assert!(ran);
}

#[test]
fn a_join_predecessor_orders_the_first_deviation() {
    let _drift = drift_lock();
    let dir = scratch();
    let mut bad = Vec::new();
    // drift: main joins w (t2) instead of v (t1); w sends once more before its end. w's extra
    // event is reached before main's join can be taken.
    let g = drift_graph(&dir);
    let m = g.replacen("{\"e\":\"TJOIN\",\"child\":1}", "{\"e\":\"TJOIN\",\"child\":2}", 1)
        .replacen("{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":[1,3]},{\"e\":\"END\"}",
            "{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":[1,3]},{\"e\":\"SEND\",\"to\":2,\"v\":5},{\"e\":\"END\"}", 1);
    assert_ne!(m, g);
    deviates(&mut bad, &dir, "drift-join", &m, (2, 2), "w", "early-end", "SEND(w, 5)", Some("END"));
    // fifo2: main's second join is TJOIN(2); p (t2) sends once more before its end.
    let (_, graphs) = store(&dir, "fifo2", "impl");
    let f = &graphs[0];
    let main = bytes(parse(f).get("threads").at(0).get("events"));
    assert_eq!(main, "[{\"e\":\"BEGIN\"},{\"e\":\"TCREATE\",\"child\":1},{\"e\":\"TCREATE\",\"child\":2},{\"e\":\"TJOIN\",\"child\":2},{\"e\":\"TJOIN\",\"child\":1},{\"e\":\"END\"}]");
    let m = f.replacen("{\"e\":\"TJOIN\",\"child\":2},{\"e\":\"TJOIN\",\"child\":1}", "{\"e\":\"TJOIN\",\"child\":2},{\"e\":\"TJOIN\",\"child\":2}", 1)
        .replacen("{\"e\":\"SEND\",\"to\":1,\"v\":2},{\"e\":\"END\"}", "{\"e\":\"SEND\",\"to\":1,\"v\":2},{\"e\":\"SEND\",\"to\":1,\"v\":3},{\"e\":\"END\"}", 1);
    deviates(&mut bad, &dir, "fifo2-join", &m, (2, 3), "p", "early-end", "SEND(v, 3)", Some("END"));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn a_creation_predecessor_orders_the_first_deviation() {
    // fifo2 with v (t1) given an extra first-position check: v's TCREATE is main's (0, 1). Main
    // is changed to create p (t2) first; then main's (0, 1) deviates (child) before anything of
    // v or p is judged.
    let dir = scratch();
    let (_, graphs) = store(&dir, "fifo2", "impl");
    let f = &graphs[0];
    let m = f.replacen("{\"e\":\"TCREATE\",\"child\":1},{\"e\":\"TCREATE\",\"child\":2}",
        "{\"e\":\"TCREATE\",\"child\":2},{\"e\":\"TCREATE\",\"child\":1}", 1);
    assert_ne!(&m, f);
    let mut bad = Vec::new();
    deviates(&mut bad, &dir, "create", &m, (0, 1), "main", "child", "TCREATE(2:\"p\")", Some("TCREATE(1:\"v\")"));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn main_recorded_blocked_but_ending_is_a_status_deviation() {
    let _drift = drift_lock();
    let dir = scratch();
    let g = drift_graph(&dir);
    // main: BEGIN, TCREATE(1:"v"), TJOIN(1), END -> BLK at (0, 3)
    let m = g.replacen("{\"e\":\"TJOIN\",\"child\":1},{\"e\":\"END\"}", "{\"e\":\"TJOIN\",\"child\":1},{\"e\":\"BLK\"}", 1);
    assert_ne!(m, g);
    let mut bad = Vec::new();
    deviates(&mut bad, &dir, "main-blk", &m, (0, 3), "main", "status", "BLK", Some("END"));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

// ------------------------------------------------------------- round-03 review --

const SPEC_HDR: &str = "{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:spec\",\"size\":\"none\",\"visible\":[\"v\"],\"roles\":[\"v\"],\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1}";

#[test]
fn bad_against_online_decide_and_export_are_refused_before_running() {
    let _mark = mark_lock();
    let dir = scratch();
    let (_, graphs) = store(&dir, "mark", "impl");
    let g = graphs[0].clone();
    let marker = dir.join("ran3");
    *MARK.lock().unwrap() = Some(marker.clone());
    let join = |j: String| g.replacen(",\"join\":null,", &format!(",\"join\":{j},"), 1);
    let base = |mode: &str, class: &str, decide: &str, against: &str, run: &str| format!(
        "{{\"tool\":\"traceforge\",\"tool_commit\":\"c\",\"mode\":\"{mode}\",\"class\":{class},\"decide\":{decide},\"against\":{against},\"against_run\":{run}}}");
    let dv = "{\"outcome\":\"violation\",\"k\":1,\"k_min\":1,\"states\":0,\"witness\":[[\"v\",0]]}";
    let cases: Vec<(&str, String)> = vec![
        ("online join with a decide", join(base("online", "null", dv, SPEC_HDR, "null"))),
        ("against {format:1}", join(base("plain", "\"not-found\"", "null", "{\"format\":1}", "null"))),
        ("against_run {tool:17}", join(base("plain", "\"not-found\"", "null", SPEC_HDR, "{\"tool\":17}"))),
        ("export with an unknown key", g.replacen(",\"encoding\":1},\"run\":", ",\"encoding\":1,\"x\":1},\"run\":", 1)),
        ("export with an online field", g.replacen(",\"encoding\":1},\"run\":", ",\"uncovered_total\":0,\"encoding\":1},\"run\":", 1)),
    ];
    let mut bad = Vec::new();
    for (what, text) in &cases {
        assert_ne!(text, &g, "{what}: the edit applies");
        let _ = std::fs::remove_file(&marker);
        let (t, c) = replay(&write(&dir, &format!("{}.json", what.replace([' ', '{', '}', ':'], "_")), text),
            &["--allow-source-change", "--allow-tool-change"]);
        if c != 2 || marker.exists() { bad.push(format!("{what}: exit {c}, ran {}: {}", marker.exists(), t.lines().next().unwrap_or(""))); }
    }
    // controls: a valid online join, and an against_run that is this store's own run
    let own_run = bytes(parse(&g).get("run"));
    for (what, text) in [("online join", join(base("online", "null", "null", SPEC_HDR, "null"))),
                         ("against_run a run", join(base("merge", "\"no-slot\"", "null", SPEC_HDR, &own_run)))] {
        let _ = std::fs::remove_file(&marker);
        let (t, c) = replay(&write(&dir, &format!("ok-{}.json", what.replace(' ', "_")), &text), &["--allow-source-change"]);
        if c != 0 || !marker.exists() { bad.push(format!("control {what}: exit {c}: {}", t.lines().next().unwrap_or(""))); }
    }
    *MARK.lock().unwrap() = None;
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// Index of the thread named `n` in a graph.
fn tindex(g: &J, n: &str) -> usize {
    (0..threads(g)).find(|&t| g.get("threads").at(t).get("name") == &J::Str(n.into())).unwrap_or_else(|| panic!("{n}"))
}

#[test]
fn a_terminal_deviation_of_a_predecessor_comes_first() {
    let dir = scratch();
    let (_, graphs) = store(&dir, "perm", "impl");
    let g = graphs[0].clone();
    let gj = parse(&g);
    let (v, j, k) = (tindex(&gj, "v"), tindex(&gj, "j"), tindex(&gj, "k"));
    let events = |t: usize| bytes(gj.get("threads").at(t).get("events"));
    println!("v={v} j={j} k={k}\nmain {}\nj {}\nk {}", events(0), events(j), events(k));
    let mut bad = Vec::new();
    // (a) j: BEGIN, TCREATE(k), BLK -> BEGIN, TCREATE(k), TJOIN(k), END; k: BEGIN, BLK -> BEGIN, END.
    let je = events(j);
    assert!(je.ends_with(",{\"e\":\"BLK\"}]"), "{je}");
    let je2 = format!("{},{{\"e\":\"TJOIN\",\"child\":{k}}},{{\"e\":\"END\"}}]", &je[..je.len() - ",{\"e\":\"BLK\"}]".len()]);
    let ke = events(k);
    assert_eq!(ke, "[{\"e\":\"BEGIN\"},{\"e\":\"BLK\"}]");
    let a = g.replacen(&format!("\"events\":{je}"), &format!("\"events\":{je2}"), 1)
        .replacen("\"name\":\"k\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"BLK\"}]", "\"name\":\"k\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"END\"}]", 1);
    assert_ne!(a, g);
    let mut b1 = Vec::new();
    deviates(&mut b1, &dir, "perm-a", &a, (k, 1), "k", "status", "END", Some("BLK"));
    let mut b2 = Vec::new();
    deviates(&mut b2, &dir, "perm-a2", &a, (k, 1), "k", "status", "END", Some("RECV() (waiting)"));
    if !(b1.is_empty() || b2.is_empty()) { bad.extend(b1); bad.extend(b2); }
    // (b) v: BEGIN, BLK -> BEGIN, END; main gets TJOIN(v) before its END; v's status in the line
    // becomes done.
    let me = events(0);
    let me2 = format!("{},{{\"e\":\"TJOIN\",\"child\":{v}}},{{\"e\":\"END\"}}]", &me[..me.len() - ",{\"e\":\"END\"}]".len()]);
    let b = g.replacen(&format!("\"events\":{me}"), &format!("\"events\":{me2}"), 1)
        .replacen("\"name\":\"v\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"BLK\"}]", "\"name\":\"v\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"END\"}]", 1)
        .replacen("\\\"v\\\":\\\"blocked\\\"", "\\\"v\\\":\\\"done\\\"", 1);
    assert_ne!(b, g);
    let mut b1 = Vec::new();
    deviates(&mut b1, &dir, "perm-b", &b, (v, 1), "v", "status", "END", Some("BLK"));
    let mut b2 = Vec::new();
    deviates(&mut b2, &dir, "perm-b2", &b, (v, 1), "v", "status", "END", Some("RECV() (waiting)"));
    if !(b1.is_empty() || b2.is_empty()) { bad.extend(b1); bad.extend(b2); }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

// ------------------------------------------------------------- round-04 review --

#[test]
fn a_thread_name_is_judged_only_once_its_creation_is_replayed() {
    let dir = scratch();
    let (_, graphs) = store(&dir, "perm", "impl");
    let g = graphs[0].clone();
    let gj = parse(&g);
    let (v, j, k) = (tindex(&gj, "v"), tindex(&gj, "j"), tindex(&gj, "k"));
    let rename = |x: &str| x.replacen("{\"name\":\"k\",", "{\"name\":\"k2\",", 1);
    let mut bad = Vec::new();
    // Rename only: k's name differs where its creation is replayed.
    deviates(&mut bad, &dir, "rename-only", &rename(&g), (k, 0), "k2", "child", "k2", Some("k"));
    // v's BLK -> END; j joins v before creating k; k renamed. v's status comes first, and k's
    // creation is never replayed, so its name is never judged.
    let a = rename(&g)
        .replacen("{\"name\":\"v\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"BLK\"}]", "{\"name\":\"v\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"END\"}]", 1)
        .replacen(&format!("{{\"e\":\"TCREATE\",\"child\":{k}}}"), &format!("{{\"e\":\"TJOIN\",\"child\":{v}}},{{\"e\":\"TCREATE\",\"child\":{k}}}"), 1)
        .replacen("\\\"v\\\":\\\"blocked\\\"", "\\\"v\\\":\\\"done\\\"", 1);
    let _ = j;
    let mut b1 = Vec::new();
    deviates(&mut b1, &dir, "gated", &a, (v, 1), "v", "status", "END", Some("BLK"));
    let mut b2 = Vec::new();
    deviates(&mut b2, &dir, "gated2", &a, (v, 1), "v", "status", "END", Some("RECV() (waiting)"));
    if !(b1.is_empty() || b2.is_empty()) { bad.extend(b1); bad.extend(b2); }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

// ------------------------------------------------------------- round-05 review --

#[test]
fn a_waiting_thread_whose_next_event_is_enabled_is_compared_at_once() {
    let dir = scratch();
    let (_, graphs) = store(&dir, "perm", "impl");
    let g = graphs[0].clone();
    let gj = parse(&g);
    let (v, j, q, k) = (tindex(&gj, "v"), tindex(&gj, "j"), tindex(&gj, "q"), tindex(&gj, "k"));
    let ev = |t: usize| bytes(gj.get("threads").at(t).get("events"));
    // v: BEGIN, BLK; j: BEGIN, TCREATE(k), BLK; q: BEGIN, SEND(q, 0), SEND(q, 1), SEND(q, 2), END
    assert_eq!(ev(v), "[{\"e\":\"BEGIN\"},{\"e\":\"BLK\"}]");
    assert_eq!(ev(j), format!("[{{\"e\":\"BEGIN\"}},{{\"e\":\"TCREATE\",\"child\":{k}}},{{\"e\":\"BLK\"}}]"));
    let q0 = format!("{{\"e\":\"SEND\",\"to\":{q},\"v\":0}}");
    assert!(ev(q).starts_with(&format!("[{{\"e\":\"BEGIN\"}},{q0},")), "{}", ev(q));
    let v_send = |x: &str| x.replacen("{\"name\":\"v\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"BLK\"}]",
        &format!("{{\"name\":\"v\",\"daemon\":false,\"events\":[{{\"e\":\"BEGIN\"}},{{\"e\":\"SEND\",\"to\":{v},\"v\":42}},{{\"e\":\"BLK\"}}]"), 1);
    let j_send = |x: &str| x.replacen(&format!("{{\"e\":\"TCREATE\",\"child\":{k}}},{{\"e\":\"BLK\"}}"),
        &format!("{{\"e\":\"TCREATE\",\"child\":{k}}},{{\"e\":\"SEND\",\"to\":{j},\"v\":42}},{{\"e\":\"BLK\"}}"), 1);
    let j_join_q = |x: &str| x.replacen(&format!("{{\"e\":\"TCREATE\",\"child\":{k}}},{{\"e\":\"BLK\"}}"),
        &format!("{{\"e\":\"TCREATE\",\"child\":{k}}},{{\"e\":\"TJOIN\",\"child\":{q}}},{{\"e\":\"BLK\"}}"), 1);
    let q99 = |x: &str| x.replacen(&q0, &format!("{{\"e\":\"SEND\",\"to\":{q},\"v\":99}}"), 1);
    let mut bad = Vec::new();
    // both changes: v's recorded send comes first, against the waiting receive
    deviates(&mut bad, &dir, "v-and-q", &q99(&v_send(&g)), (v, 1), "v", "event", "SEND(v, 42)", Some("RECV() (waiting)"));
    // the single-change controls
    deviates(&mut bad, &dir, "v-only", &v_send(&g), (v, 1), "v", "event", "SEND(v, 42)", Some("RECV() (waiting)"));
    deviates(&mut bad, &dir, "q-only", &q99(&g), (q, 1), "q", "value", "SEND(q, 99)", Some("SEND(q, 0)"));
    // j's recorded send against its waiting join, before q's value
    deviates(&mut bad, &dir, "j-and-q", &q99(&j_send(&g)), (j, 2), "j", "event", "SEND(j, 42)", Some(&format!("TJOIN({k})")));
    // a waiting join of k where the record joins q: child, once q's end is replayed
    deviates(&mut bad, &dir, "j-joins-q", &j_join_q(&g), (j, 2), "j", "child", &format!("TJOIN({q})"), Some(&format!("TJOIN({k})")));
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}
